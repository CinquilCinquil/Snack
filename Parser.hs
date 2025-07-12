module Main (main) where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class
import TokenParser
import Funcs -- includes types and functions
import System.Environment
import Control.Monad
import Data.Data

---------------------------------------------------
----------------- Parsers for non-terminals
---------------------------------------------------

program :: ParsecT [InfoAndToken] MyState IO ([Token])
program = do
            --a <- importToken
            b <- typesToken -- types:
            c <- declsToken -- declarations:
            d <- declarations_op
            e <- mainToken -- main:
            (_, f) <- stmts
            eof
            liftIO (putStrLn "---------\nParsing Complete: ")
            return $ b:[c] ++ d ++ [e] ++ f

parse_block :: ParsecT [InfoAndToken] MyState IO (MyState, [Token])
parse_block = do
            (h_type, h) <- block
            s <- getState
            return (s, h)
  
parse_exp_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, FunctionBody, [Token], MyState)
parse_exp_rule = do
                (a_type, a_value, a_body, a) <- exp_rule
                s <- getState
                return (a_type, a_value, a_body, a, s)

----------------- Declarations Functions and Globals -----------------

declarations_op :: ParsecT [InfoAndToken] MyState IO ([Token])
declarations_op = (do a <- declarations; return a) <|> (return [])

declarations :: ParsecT [InfoAndToken] MyState IO ([Token])
declarations = do
                a <- declaration
                b <- declarations_op -- remaining decls
                return (a ++ b)

declaration :: ParsecT [InfoAndToken] MyState IO ([Token])
declaration = (do
              b <- idToken
              c <- colonToken
              d <- types
              e <- semiColonToken
              --
              s <- getState; pos <- getPosition
              updateState (symtable_insert_variable (b, d, get_default_value pos s d, []))
              liftIO (putStrLn "declaration:")
              print_state
              --
              return (b:c:d:[e]))
              <|>
              (do
              a <- fun_decl
              liftIO (putStrLn "fun_declaration:")
              print_state
              return a)
              <|>
              (do
              a <- struct_decl
              liftIO (putStrLn "struct_declaration:")
              print_state
              return a)

----------------- Main -----------------

decl_or_atrib_or_access_or_call :: ParsecT [InfoAndToken] MyState IO ([Token])
decl_or_atrib_or_access_or_call = do
                          a <- idToken
                          b <- decl_or_atrib a <|> struct_attrib a <|> (do (_, _, b) <- function_call a; c <- semiColonToken; return (b ++ [c]))
                          return b

decl_or_atrib :: Token -> ParsecT [InfoAndToken] MyState IO ([Token])
decl_or_atrib a = do
                b <- init_or_decl a
                c <- semiColonToken
                return ((a:b) ++ [c])

init_or_decl :: Token -> ParsecT [InfoAndToken] MyState IO ([Token])
init_or_decl id_token = (do -- Assignment
                a <- assignToken
                (exp_type, exp_value, _, b) <- exp_rule
                --
                s <- getState; pos <- getPosition
                type_check pos s check_eq id_token exp_type
                updateState (symtable_update_variable (id_token, exp_value, dontChangeFunctionBody))
                --
                return (a:b))
                <|>
                (do -- Declaration
                a <- colonToken
                b <- types
                (exp_type, exp_value, c) <- atrib_opt b
                --
                s <- getState; pos <- getPosition
                updateState (symtable_insert_variable (id_token, b, get_default_value pos s b, []))
                --
                s' <- getState; pos' <- getPosition
                type_check pos' s' check_eq id_token exp_type
                let var_value = if c == [] then get_default_value pos' s' b else exp_value
                updateState (symtable_update_variable (id_token, var_value, dontChangeFunctionBody))
                print_state
                --
                return (a:b:c))

atrib_opt :: MyType -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
atrib_opt _type = (do
            a <- assignToken
            (exp_type, exp_value, _, b) <- exp_rule
            return (exp_type, exp_value, a:b)) <|> (return (_type, defaultValue, []))

struct_attrib :: Token -> ParsecT [InfoAndToken] MyState IO ([Token])
struct_attrib a = do
                s <- getState; pos <- getPosition
                let (Id name) = a
                let vars = case lookup_var pos name s of 
                            (_, _, StructLiteral vars, _) -> vars
                            _ -> error_msg "dame5" []
                --
                (_, _, _, b_struct_tree) <- struct_access' a vars
                --
                c <- assignToken
                (d_type, d_value, _, d) <- exp_rule
                e <- semiColonToken
                --
                pos' <- getPosition
                updateState (update_struct pos' b_struct_tree (d_type, d_value))
                print_state
                --
                return (b_struct_tree ++ [c] ++ d ++ [e])

stmts :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
stmts = do
        (a_type, a) <- stmt
        (b_type, b) <- stmts_op
        -- If only one of them is unit then the return type is the other's
        s <- getState; pos <- getPosition
        if a_type == Unit || b_type == Unit then do
          let resulting_type = (if a_type /= b_type then (if a_type == Unit then b_type else a_type) else a_type)
          return (resulting_type, a ++ b)
        else do 
          type_check pos s check_eq a_type b_type
          return (a_type, a ++ b)

stmts_op :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
stmts_op = (do a <- stmts; return a) <|> (return (Unit, []))

-- (return_type, tokens)
stmt :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
stmt = (do a <- decl_or_atrib_or_access_or_call; return (Unit, a))
   <|> (do a <- struct_decl; return (Unit, a))
   <|> (do a <- structures; return a)
   <|> (do -- Return
    a <- returnToken
    (b_type, b_value, _, b) <- exp_rule
    c <- semiColonToken
    --
    s <- getState; pos <- getPosition
    when (get_flag s) $ do updateState (set_return_value pos b_value)
    --
    return (b_type, (a:b) ++ [c]))
   <|> (do -- Print
    a <- printToken
    (_, b_value, _, b) <- exp_rule
    c <- semiColonToken
    --
    s <- getState
    when (get_flag s) $ liftIO (putStrLn $ showLiteral b_value)
    --
    return (Unit, (a:b) ++ [c]))
   <|> (do -- Read
    a <- readToken
    (_, b_value, _, b:bs) <- term
    c <- semiColonToken
    --
    s <- getState
    when (get_flag s) $ do
      line <- liftIO (getLine)
      let value = read_literal line
      -- Type checking
      s <- getState; pos <- getPosition; let (Id b_name) = b
      when (not $ (toConstr value) == (toConstr b_value)) $ do
        error_msg "Type of eaten value '%' does not match type of '%'. Line: % Column: %" [showLiteral value, b_name, showLine pos, showColumn pos]
      --
      updateState (symtable_update_variable (b, value, dontChangeFunctionBody))
    --
    return (Unit, (a:b:bs) ++ [c]))

fun_decl :: ParsecT [InfoAndToken] MyState IO [Token]
fun_decl = do
        a <- funToken
        b <- idToken
        c <- openParenthesesToken
        --
        updateState (symtable_insert_variable (b, Unit, UnitLiteral (), []))
        --
        updateState (add_current_scope_name "fun")
        updateState (set_flag False)
        --
        (d_types, _, d) <- (do a <- params; return a) <|> (return ([], [], []))
        e <- closeParenthesesToken
        f <- colonToken
        g <- types
        --
        updateState (symtable_update_variable_type (b, g)) -- TODO: 'g' is only the return type, add param types?
        --
        (h_type, h) <- block
        --
        let (Id func_name) = b
        s <- getState; pos <- getPosition
        type_check_with_msg (replace '%' [func_name] "In function '%' return: ") pos s check_eq h_type g
        --
        updateState (remove_current_scope_name)
        updateState (set_flag True)
        --
        updateState (symtable_update_variable (b, dontChangeValue, d ++ [EndOfParamsToken] ++ h))
        --
        return ([a, b, c] ++ d ++ [e, f, g] ++ h)

params :: ParsecT [InfoAndToken] MyState IO ([MyType], [Value], [Token])
params = do
        a <- idToken
        b <- colonToken
        c <- types
        --
        s <- getState; pos <- getPosition
        updateState (symtable_insert_variable (a, c, get_default_value pos s c, []))
        --
        (d_type, d_value, d) <- atrib_opt c
        --
        s' <- getState; pos' <- getPosition
        let var_value = if d == [] then get_default_value pos' s' c else d_value
        updateState (symtable_update_variable (a, var_value, dontChangeFunctionBody))
        liftIO (putStrLn "params_declaration:")
        print_state
        --
        (e_types, e_values, e) <- params_op
        return (d_type:e_types, d_value:e_values, (a:b:[c]) ++ d ++ e)

params_op :: ParsecT [InfoAndToken] MyState IO ([MyType], [Value], [Token])
params_op = (do
            a <- commaToken
            (b_types, b_values, b) <- params
            return (b_types, b_values, (a:b))) <|> (return ([], [], []))

struct_decl :: ParsecT [InfoAndToken] MyState IO [Token]
struct_decl = do
            a <- structToken
            b <- idToken
            --
            updateState (symtable_insert_variable (b, Struct, StructLiteral [], []))
            --
            updateState (add_current_scope_name "struct")
            --
            c <- struct_block
            --
            s <- getState
            let (Node _ struct_vars _) = search_scope_tree (get_current_scope_name s) (get_current_scope_tree s)
            --
            updateState (remove_current_scope_name)
            --
            updateState (symtable_update_variable (b, StructLiteral struct_vars, dontChangeFunctionBody))
            --
            d <- semiColonToken
            return ((a:b:c) ++ [d])

struct_block :: ParsecT [InfoAndToken] MyState IO [Token]
struct_block = do
              a <- openBracketsToken
              b <- declarations_op
              c <- closeBracketsToken
              return ((a:b) ++ [c])

----------------- Expressions -----------------

exp_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, FunctionBody, [Token])
exp_rule = (do
           (a_type, a_value, a_body, a) <- term
           (b_type, b_value, b) <- relational_remaining_recursive (a_type, a_value, a)
           if a == b then return (a_type, a_value, a_body, a) else return (b_type, b_value, noFuncBody, b))
           <|>
           (do
           (a_type, a_value, a_body, a) <- exp_base
           (b_type, b_value, b) <- relational_remaining (a_type, a_value, a)
           if b == [] then return (a_type, a_value, a_body, a) else return (b_type, b_value, noFuncBody, b))

exp_base :: ParsecT [InfoAndToken] MyState IO (MyType, Value, FunctionBody, [Token])
exp_base = (do (a_type, a_value, a) <- uminus_remaining; return (a_type, a_value, noFuncBody, a))
           <|> (do
           a <- openParenthesesToken
           (b_type, b_value, b_body, b) <- exp_rule
           c <- closeParenthesesToken
           return (b_type, b_value, b_body, [a] ++ b ++ [c]))
           <|> (do -- toInt
            a <- toIntToken
            b <- openParenthesesToken
            (_, c_value, c_body, c) <- exp_rule
            d <- closeParenthesesToken
            --
            let new_value = to_int c_value
            --
            return (Int, new_value, c_body, (a:b:c) ++ [d]))
           <|> (do -- toFloat
            a <- toFloatToken
            b <- openParenthesesToken
            (_, c_value, c_body, c) <- exp_rule
            d <- closeParenthesesToken
            --
            let new_value = to_float c_value
            --
            return (Float, new_value, c_body, (a:b:c) ++ [d]))
            <|> (do -- toString
            a <- toStringToken
            b <- openParenthesesToken
            (_, c_value, c_body, c) <- exp_rule
            d <- closeParenthesesToken
            --
            let new_value = to_string c_value
            --
            return (TString, new_value, c_body, (a:b:c) ++ [d]))
            <|> (do -- toBool
            a <- toBoolToken
            b <- openParenthesesToken
            (_, c_value, c_body, c) <- exp_rule
            d <- closeParenthesesToken
            --
            let new_value = to_bool c_value
            --
            return (TBool, new_value, c_body, (a:b:c) ++ [d]))
            <|> (do -- toChar
            a <- toCharToken
            b <- openParenthesesToken
            (_, c_value, c_body, c) <- exp_rule
            d <- closeParenthesesToken
            --
            let new_value = to_char c_value
            --
            return (TChar, new_value, c_body, (a:b:c) ++ [d]))

term :: ParsecT [InfoAndToken] MyState IO (MyType, Value, FunctionBody, [Token])
term = (do (_type, value, a) <- literal; return (_type, value, noFuncBody, [a]))
      <|> (do s <- getState; a <- struct_access_or_function_call (get_current_scope s); return a)

struct_access_or_function_call :: [Var] -> ParsecT [InfoAndToken] MyState IO (MyType, Value, FunctionBody, [Token])
struct_access_or_function_call vars = do
      a <- idToken
      b <- (do (b_type, b_value, b) <- function_call a; return (b_type, b_value, noFuncBody, b)) <|> (struct_access' a vars)
      return b

struct_access :: [Var] -> ParsecT [InfoAndToken] MyState IO (MyType, Value, FunctionBody, [Token])
struct_access vars = do
                (Id name) <- idToken
                --
                s <- getState
                case get_var_info_from_scope name vars of 
                  (name, _, StructLiteral attrbs, _) -> do
                      b <- struct_access' (Id name) attrbs
                      return b
                  _ -> do
                    pos <- getPosition
                    error_msg "Variable '%' is not a struct! Error #5. Line: % Column: %" [name, showLine pos, showColumn pos]

struct_access' :: Token -> [Var] -> ParsecT [InfoAndToken] MyState IO (MyType, Value, FunctionBody, [Token])
struct_access' a vars = (do
      b <- periodToken
      (c_type, c_value, c_body, c) <- struct_access vars
      --
      let (attrb_type, attrb_value, attrb_body) = case c of
                                        [(Id last_in_chain)] -> do 
                                          let (_, attrb_type, attrb_value, attrb_body) = get_var_info_from_scope last_in_chain vars
                                          (attrb_type, attrb_value, attrb_body)
                                        _ -> (c_type, c_value, c_body)
      --
      return (attrb_type, attrb_value, attrb_body, a:b:c))
      <|> (do
      s <- getState; pos <- getPosition
      let (Id name) = a
      let (_, a_type, a_value, a_body) = lookup_var pos name s
      return (a_type, a_value, a_body, [a]))

function_call :: Token -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
function_call a = do
  b <- openParenthesesToken
  -- Type checking
  s <- getState
  pos <- getPosition
  let (Id func_name) = a
  let (_, func_type, _, func_code) = lookup_var pos func_name s
  let (func_params, func_params_types, func_body) = get_params func_code
  (c_types, c_values, c_bodies, c) <- args_rule_opt
  check_param_amount pos func_params c_types
  check_types (type_check pos s check_eq) c_types func_params_types
  -- Semantics
  let is_executing = get_flag s
  when is_executing $ do
        updateState (add_current_scope_name "fun")
        updateState (load_params func_params func_params_types c_values c_bodies)
        updateState (add_call_to_stack func_name)
        --
        s' <- getState
        x <- parse_function func_name func_body s'
        --
        updateState (remove_current_scope_name)
  --
  s' <- getState; pos' <- getPosition
  let result_value = if is_executing then get_return_value pos' s' else NoneToken
  -- when is_executing $ desempilhar
  --
  d <- closeParenthesesToken
  return (func_type, result_value, (a:b:c) ++ [d])

args_rule_opt :: ParsecT [InfoAndToken] MyState IO ([MyType], [Value], [FunctionBody], [Token])
args_rule_opt = (do
                (exp_type, exp_value, exp_body, a) <- exp_rule
                (b_types, b_values, b_bodies, b) <- args_rule
                return (exp_type:b_types, exp_value:b_values, exp_body:b_bodies, a ++ b))
                <|> return ([], [], [], [])

args_rule :: ParsecT [InfoAndToken] MyState IO ([MyType], [Value], [FunctionBody], [Token])
args_rule = (do
            a <- commaToken
            (b_types, b_values, b_bodies, b) <- args_rule_opt
            return (b_types, b_values, b_bodies, a:b))
            <|> return ([], [], [], [])

relational_remaining_recursive :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
relational_remaining_recursive a = (do
                        b <- relational_remaining a
                        if b == a
                        then return a
                        else do
                          x <- relational_remaining_recursive b
                          return x)

relational_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
relational_rule = do
                  (a_type, a_value, a_body, a) <- term <|> exp_base
                  b <- relational_remaining (a_type, a_value, a)
                  return b

relational_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
relational_remaining (a_type, a_value, a) = (do
              b <- rel_op
              (c_type, c_value, c) <- relational_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_eq a_type c_type
              let result_value = if (get_flag s) then doOpOnTokens a_value c_value b else NoneToken
              --
              return (TBool, result_value, a ++ [b] ++ c))
              <|> (do x <- or_remaining (a_type, a_value, a); return x)

or_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
or_rule = do
          (a_type, a_value, a_body, a) <- term <|> exp_base
          b <- or_remaining (a_type, a_value, a)
          return b

or_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
or_remaining (a_type, a_value, a) = (do
              b <- orToken
              (c_type, c_value, c) <- or_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_bool a_type c_type
              let result_value = if (get_flag s) then doOpOnTokens a_value c_value b else NoneToken
              --
              return (TBool, result_value, a ++ [b] ++ c))
              <|> (do x <- and_remaining (a_type, a_value, a); return x)

and_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
and_rule = do
          (a_type, a_value, a_body, a) <- term <|> exp_base
          b <- and_remaining (a_type, a_value, a)
          return b

and_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
and_remaining (a_type, a_value, a) = (do
              b <- andToken
              (c_type, c_value, c) <- and_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_bool a_type c_type
              let result_value = if (get_flag s) then doOpOnTokens a_value c_value b else NoneToken
              --
              return (TBool, result_value, a ++ [b] ++ c))
              <|> (do x <- arithm_remaining (a_type, a_value, a); return x)

arithm_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
arithm_rule = do
            (a_type, a_value, a_body, a) <- term <|> exp_base
            b <- arithm_remaining (a_type, a_value, a)
            return b

arithm_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
arithm_remaining (a_type, a_value, a) = (do
              b <- sum_or_minus
              (c_type, c_value, c) <- arithm_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = if (get_flag s) then doOpOnTokens a_value c_value b else NoneToken
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> (do x <- mult_remaining (a_type, a_value, a); return x)

mult_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
mult_rule = do
            (a_type, a_value, a_body, a) <- term <|> exp_base
            b <- mult_remaining (a_type, a_value, a)
            return b

mult_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
mult_remaining (a_type, a_value, a) = (do
              b <- mult_or_div
              (c_type, c_value, c) <- mult_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = if (get_flag s) then doOpOnTokens a_value c_value b else NoneToken
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> (do x <- pow_remaining (a_type, a_value, a); return x)

pow_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
pow_rule = do
            (a_type, a_value, a_body, a) <- term <|> exp_base
            b <- pow_remaining (a_type, a_value, a)
            return b

pow_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
pow_remaining (a_type, a_value, a) = (do
              b <- powToken
              (c_type, c_value, c) <- pow_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = if (get_flag s) then doOpOnTokens a_value c_value b else NoneToken
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> return (a_type, a_value, a)

-- and 'not'
uminus_remaining :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
uminus_remaining = (do
            a <- minusToken
            (b_type, b_value, _, b) <- term <|> exp_base
            --
            s <- getState; pos <- getPosition
            type_check pos s check_arithm b_type b_type
            let result_value = if (get_flag s) then doOpOnToken b_value a else NoneToken
            --
            return (b_type, result_value, a:b))
            <|>
            (do 
            a <- notToken
            (b_type, b_value, _, b) <- term <|> exp_base
            --
            s <- getState; pos <- getPosition
            type_check pos s check_bool b_type TBool
            let result_value = if (get_flag s) then doOpOnToken b_value a else NoneToken
            --
            return (TBool, result_value, a:b))

sum_or_minus :: ParsecT [InfoAndToken] MyState IO (Token)
sum_or_minus = (do a <- sumToken; return a) <|> (do a <- minusToken; return a)

mult_or_div :: ParsecT [InfoAndToken] MyState IO (Token)
mult_or_div = (do a <- divToken; return a) <|> (do a <- multToken; return a)

rel_op :: ParsecT [InfoAndToken] MyState IO (Token)
rel_op = (do a <- leqToken; return a)
    <|>  (do a <- geqToken; return a)
    <|>  (do a <- equalsToken; return a)
    <|>  (do a <- smallerToken; return a)
    <|>  (do a <- greaterToken; return a)
    <|>  (do a <- differentToken; return a)

----------------- Structures -----------------

structures :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
structures = (do a <- if_rule; return a)
          <|> (do a <- for_rule; return a) 
          <|> (do a <- while_rule; return a)
          <|> (do a <- repeat_rule; return a)
          <|> (do a <- match_rule; return a)

block :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
block = do
      a <- openBracketsToken
      (b_type, b) <- stmts_op
      c <- closeBracketsToken
      return (b_type, (a:b) ++ [c])

if_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
if_rule = do
        a <- ifToken
        (b_type, b_value, _, b) <- exp_rule
        --
        s <- getState; pos <- getPosition
        type_check pos s check_eq b_type TBool
        --
        updateState (add_current_scope_name "if")
        --
        s' <- getState;
        let (BoolLiteral boolean_value) = b_value
        if (get_flag s') then updateState (set_flag boolean_value) else updateState (set_flag False)
        (c_type, c) <- block
        --
        updateState (remove_current_scope_name)
        --
        if (get_flag s') then updateState (set_flag (not boolean_value)) else updateState (set_flag False)
        (d_type, d) <- else_op
        --
        s <- getState; pos <- getPosition
        type_check_with_msg "In If-Else return: " pos s check_eq c_type d_type
        --
        return (c_type, (a:b) ++ c ++ d)

else_op :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
else_op = (do
          a <- elseToken
          --
          updateState (add_current_scope_name "else")
          --
          (b_type, b) <- (do a <- if_rule; return a) <|> (do a <- block; return a)
          --
          updateState (remove_current_scope_name)
          --
          return (b_type, (a:b))) <|> (return (Unit, []))

for_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
for_rule = do
    -- Initial structure. Ex: for i : int in [1..2] step 1
    a <- forToken
    --
    updateState (add_current_scope_name "for")
    --
    (b_type, b) <- for_declaration
    c <- inToken
    (d_type, (start_value, end_value, cond_op), d) <- range_rule
    e <- stepToken
    (f_type, f_value, _, f) <- exp_rule -- WARNING: step semantics is executed even if the block isn't
    -- Type check
    s <- getState; pos <- getPosition
    type_check pos s check_eq b_type d_type
    type_check pos s check_eq b_type f_type
    -- Block
    updateState (set_flag False)
    (g_type, g) <- block
    updateState (set_flag $ get_flag s)
    -- Semantics
    -- dealing with a left-open interval
    let start_value_increment = (if (head d) == OpenSquareBrackets then (get_literal b_type (IntLiteral 0)) else f_value)
    let start_value' = doOpOnTokens start_value start_value_increment Sum
    let (BoolLiteral cond) = doOpOnTokens start_value' end_value cond_op
    let (Id counter_name) = (head b)
    let cond_exp = [Id counter_name, cond_op, (get_literal b_type end_value)]
    s' <- getState
    when ((get_flag s') && cond) $ do
      -- initializing counter
      updateState(symtable_update_variable (Id counter_name, start_value', dontChangeFunctionBody))
      --
      s'' <- getState
      let increment_exp = [Id counter_name, Assign, Id counter_name, Sum, f_value, SemiColon]
      let g' = (reverse $ tail $ reverse g) ++ increment_exp ++ [CloseBrackets]
      parse_structure "for" g' s'' cond_exp
    --
    updateState (remove_current_scope_name)
    return (g_type, (a:b) ++ b ++ [c] ++ d ++ (e:f) ++ g)

-- TODO: put a step option
range_rule :: ParsecT [InfoAndToken] MyState IO (MyType, (Value, Value, Token), [Token])
range_rule = (do -- Range with brackets
          a <- openSquareBracketsToken <|> openParenthesesToken
          (b_type, b_value, _, b) <- exp_rule
          c <- twoDotsToken
          (d_type, d_value, _, d) <- exp_rule
          e <- closeSquareBracketsToken <|> closeParenthesesToken
          --
          s <- getState; pos <- getPosition
          type_check pos s check_eq b_type d_type
          when (not $ isArithm b_type) $ do error_msg "Range values must be Arithmetic! Line: % Column: %" [showLine pos, showColumn pos]
          --
          let op = if e == CloseSquareBrackets then Leq else Smaller
          return (d_type, (b_value, d_value, op), [a] ++ b ++ [c] ++ d ++ [e]))
          -- <|> TODO-OPTIONAL: a 'for-each' range like a list of elements

for_declaration :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
for_declaration = do
              b <- idToken
              c <- colonToken
              d <- types
              --
              s <- getState; pos <- getPosition
              updateState (symtable_insert_variable (b, d, get_default_value pos s d, []))
              --
              liftIO (putStrLn "for_declaration:")
              print_state
              return (d, (b:c:[d]))

while_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
while_rule = do
        -- Initial structure. Ex: While i > 0
        a <- whileToken
        --
        updateState (add_current_scope_name "while")
        --
        (b_type, b_value, _, b) <- exp_rule
        -- Type check
        s <- getState; pos <- getPosition
        type_check pos s check_eq b_type TBool
        -- Block
        updateState (set_flag False)
        (c_type, c) <- block
        updateState (set_flag $ get_flag s)
        -- Semantics
        let (BoolLiteral cond) = b_value
        s' <- getState
        when ((get_flag s') && cond) $ do parse_structure "while" c s' b
        --
        updateState (remove_current_scope_name)
        return (c_type, (a:b) ++ c)

repeat_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
repeat_rule = do
        a <- repeatToken
        --
        updateState (add_current_scope_name "repeat")
        (b_type, b_value, _, b) <- exp_rule
        --
        if isIntegral b_type then do
          -- Block
          s <- getState
          updateState (set_flag False)
          (c_type, c) <- block
          updateState (set_flag $ get_flag s)
          -- Semantics
          updateState(symtable_insert_variable(Id "$i", Int, (to_int b_value), [])) -- hidden counter variable
          let (IntLiteral repetition_value) = (to_int b_value)
          let cond = repetition_value > 0
          let cond_exp = [Id "$i", Greater, IntLiteral 0]
          s' <- getState
          when ((get_flag s') && cond) $ do
            let increment_exp = [Id "$i", Assign, Id "$i", Minus, IntLiteral 1, SemiColon]
            let c' = (reverse $ tail $ reverse c) ++ increment_exp ++ [CloseBrackets]
            parse_structure "repeat" c' s' cond_exp
          --
          updateState (remove_current_scope_name)
          return (c_type, (a:b) ++ c)
        else do
          pos <- getPosition
          error_msg "Expression in Repeat must be integral! Line: % Column: %" [showLine pos, showColumn pos]

match_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
match_rule = do
        a <- matchToken
        b <- idToken
        c <- withToken
        --
        updateState (add_current_scope_name "match")
        --
        (d_type, d) <- match_block b
        --
        updateState (remove_current_scope_name)
        return (d_type, (a:b:c:d))

match_block :: Token -> ParsecT [InfoAndToken] MyState IO (MyType, [Token])
match_block id_token = do
        a <- openBracketsToken
        (b_type, b) <- form_blocks_opt id_token
        c <- closeBracketsToken
        return (b_type, (a:b) ++ [c])

form_blocks_opt :: Token -> ParsecT [InfoAndToken] MyState IO (MyType, [Token])
form_blocks_opt id_token = (do
                        a <- formToken
                        --
                        updateState (add_current_scope_name "form")
                        --
                        (b_type, b) <- form_blocks_start id_token
                        return (b_type, (a:b))) <|> (return (Unit, []))

form_blocks_start :: Token -> ParsecT [InfoAndToken] MyState IO (MyType, [Token])
form_blocks_start id_token = (do
                a <- idToken
                b <- openParenthesesToken
                c <- idsOpt
                -- TODO: check if the number of arguments match that of the type of id_token
                d <- closeParenthesesToken
                (e_type, e) <- form_block id_token
                return (e_type, (a:b:c) ++ (d:e)))
                <|>
                (do
                (a_type, _, a) <- literal
                --
                s <- getState; pos <- getPosition
                let (Id id_token_name) = id_token
                let (_, id_token_type, _, _) = lookup_var pos id_token_name s
                type_check pos s check_eq id_token_type a_type
                --
                (b_type, b) <- form_block id_token
                return (b_type, (a:b)))

form_block :: Token -> ParsecT [InfoAndToken] MyState IO (MyType, [Token])
form_block id_token = do
            a <- colonToken
            (b_type, b) <- stmts_op
            --
            updateState (remove_current_scope_name) -- end of previous form
            --
            (c_type, c) <- form_blocks_opt id_token
            --
            s <- getState; pos <- getPosition
            type_check_with_msg "In Match-Form return: " pos s check_eq b_type c_type
            --
            return (c_type, (a:b) ++ c)

idsOpt :: ParsecT [InfoAndToken] MyState IO [Token]
idsOpt = (do a <- idToken; b <- ids; return (a:b)) <|> (return [])

ids :: ParsecT [InfoAndToken] MyState IO [Token]
ids = (do a <- commaToken
          b <- idToken
          c <- ids
          return (a:b:c)) <|> (return [])

----------------- Others -----------------

--literals :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
--literals = (do a <- literal; return a) <|> (do a <- literals; return a)

literal :: ParsecT [InfoAndToken] MyState IO (MyType, Value, Token)
literal = (do a <- natLiteralToken; return (Nat, a, a))
  <|> (do a <- intLiteralToken; return (Int, a, a))
  <|> (do a <- stringLiteralToken; return (TString, a, a))
  <|> (do a <- floatLiteralToken; return (Float, a, a))
  <|> (do a <- charLiteralToken; return (TChar, a, a))
  <|> (do a <- boolLiteralToken; return (TBool, a, a))
  -- <|> (do a <- openParenthesesToken; b <- closeParenthesesToken; return (Unit, UnitLiteral (), UnitLiteral ()))
  <|> fail "Not a valid literal"

types :: ParsecT [InfoAndToken] MyState IO (Token)
types =
  (do a <- natToken; return a)
  <|> (do a <- intToken; return a)
  <|> (do a <- stringToken; return a)
  <|> (do a <- floatToken; return a ) 
  <|> (do a <- charToken; return a)
  <|> (do a <- boolToken; return a)
  <|> (do a <- typeToken; return a)
  <|> (do a <- unitToken; return a)
  <|> (do
    (Id name) <- idToken
    s <- getState; pos <- getPosition
    check_var_is_declared pos name s
    return (Id name))
  <|> fail "Not a valid type"

dontChangeFunctionBody = [NoneToken]
noFuncBody = [NoneToken]
dontChangeValue = NoneToken

---------------------------------------------------
----------------- Parser invocation
---------------------------------------------------

initialState = [(Node "root" [] NoChildren, [], [], [], 0, ["root"], True)]
defaultValue = StringLiteral "Default Value"

parse_function :: Name -> [Token] -> MyState -> ParsecT [InfoAndToken] MyState IO ()
parse_function func_name func_body s = do
  result <- liftIO (runParserT parse_block s (replace '%' [func_name] "Parsing error inside '%' call!") (to_infoAndToken func_body))
  let new_state = case result of
                Left err -> error (show err)
                Right (new_state, ans) -> new_state
  updateState(\s -> new_state)
  return ()

parse_structure :: Name -> [Token] -> MyState -> [Token] -> ParsecT [InfoAndToken] MyState IO ()
parse_structure structure_name structure_body s cond_exp = do
  -- Parsing structure body
  result <- liftIO (runParserT parse_block s (replace '%' [structure_name] "Parsing error inside '%'!") (to_infoAndToken structure_body))
  let new_state = case result of
                Left err -> error (show err)
                Right (new_state, ans) -> new_state
  updateState(\s -> new_state)
  -- Parsing conditional expression
  result' <- liftIO (runParserT parse_exp_rule new_state (replace '%' [structure_name] "Parsing error in '%' conditional expression!") (to_infoAndToken cond_exp))
  let (new_state', BoolLiteral cond_value) = case result' of
                                    Left err -> error (show err)
                                    Right (_, exp_value, _, _, new_state') -> (new_state', exp_value)
  updateState(\s -> new_state')
  -- Recursive call
  when cond_value $ do parse_structure structure_name structure_body new_state' cond_exp
  --
  return ()

main :: IO ()
main = do
  args <- getArgs
  case args of 
    [filename] -> do
      tokensAndInfo <- getTokens filename
      result <- runParserT program initialState "Parsing error!" tokensAndInfo
      case result of
      { Left err -> print err;
        Right ans -> print ans
      }
    _ -> putStrLn "Please inform the input filename. Closing application..."