module Main (main) where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class
import TokenParser
import Funcs -- includes types and functions
import System.Environment
import Control.Monad

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
            liftIO (putStrLn "Parsing Complete: ")
            return $ b:[c] ++ d ++ [e] ++ f

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
              s <- getState
              updateState (symtable_insert_variable (b, d, get_default_value s d, []))
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

decl_or_atrib_or_access :: ParsecT [InfoAndToken] MyState IO ([Token])
decl_or_atrib_or_access = do
                          a <- idToken
                          b <- decl_or_atrib a <|> struct_attrib a
                          return (a:b)

decl_or_atrib :: Token -> ParsecT [InfoAndToken] MyState IO ([Token])
decl_or_atrib a = do
                b <- init_or_decl a
                c <- semiColonToken
                return ((a:b) ++ [c])

init_or_decl :: Token -> ParsecT [InfoAndToken] MyState IO ([Token])
init_or_decl id_token = (do -- Assignment
                a <- assignToken
                (exp_type, exp_value, b) <- exp_rule
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
                s <- getState
                updateState (symtable_insert_variable (id_token, b, get_default_value s b, []))
                --
                s' <- getState; pos <- getPosition
                type_check pos s' check_eq id_token exp_type
                let var_value = if c == [] then get_default_value s' b else exp_value
                updateState (symtable_update_variable (id_token, var_value, dontChangeFunctionBody))
                print_state
                --
                return (a:b:c))

atrib_opt :: MyType -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
atrib_opt _type = (do
            a <- assignToken
            (exp_type, exp_value, b) <- exp_rule
            return (exp_type, exp_value, a:b)) <|> (return (_type, defaultValue, []))

struct_attrib :: Token -> ParsecT [InfoAndToken] MyState IO ([Token])
struct_attrib a = do
                s <- getState
                let (Id name) = a
                let vars = case lookup_var name s of 
                            (_, _, StructLiteral vars, _) -> vars
                            _ -> error_msg "dame5" []
                --
                (_, _, b_struct_tree) <- struct_access' a vars
                --
                c <- assignToken
                (d_type, d_value, d) <- exp_rule
                e <- semiColonToken
                --
                updateState (update_struct b_struct_tree (d_type, d_value))
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
stmt = (do a <- decl_or_atrib_or_access; return (Unit, a))
   <|> (do a <- fun_decl; return (Unit, a))
   <|> (do a <- struct_decl; return (Unit, a))
   <|> (do a <- structures; return a)
   <|> (do
    a <- returnToken
    (b_type, _, b) <- exp_rule
    -- TODO: when semantic -> return value to function call
    c <- semiColonToken
    return (b_type, (a:b) ++ [c]))
   <|> (do
    s <- getState
    a <- printToken
    (_, b_value, b) <- exp_rule
    c <- semiColonToken
    when (get_flag s) $ liftIO (putStrLn $ showLiteral b_value)
    return (Unit, (a:b) ++ [c])
   )

exp_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
exp_rule = (do
           a <- term
           b <- relational_remaining_recursive a
           return b)
           <|>
           (do
           a <- exp_base
           (b_type, b_value, b) <- relational_remaining a
           if b == [] then return a else return (b_type, b_value, b))

exp_base :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
exp_base = (do a <- uminus_remaining; return a)
           <|>
           (do a <- function_call; return a)
           <|> (do
           a <- openParenthesesToken
           (b_type, b_value, b) <- exp_rule
           c <- closeParenthesesToken
           return (b_type, b_value, [a] ++ b ++ [c]))

struct_access :: [Var] -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
struct_access vars = do
                (Id name) <- idToken
                --
                s <- getState
                let vars' = case get_var_info_from_scope name vars of 
                              (name, _, StructLiteral attrbs, _) -> attrbs
                              _ -> error_msg "Variable '%' is not a struct. Error #5" [name]
                b <- struct_access' (Id name) vars'
                return b

struct_access' :: Token -> [Var] -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
struct_access' a vars = (do
                b <- periodToken
                (c_type, c_value, c) <- struct_access vars
                --
                let (attrb_type, attrb_value) = case c of
                                                  [(Id last_in_chain)] -> do 
                                                    let (_, attrb_type, attrb_value, _) = get_var_info_from_scope last_in_chain vars
                                                    (attrb_type, attrb_value)
                                                  _ -> (c_type, c_value)
                --
                return (attrb_type, attrb_value, a:b:c))
                <|> (do
                  s <- getState
                  let (Id name) = a
                  let (_, a_type, a_value, _) = lookup_var name s
                  return (a_type, a_value, [a]))

term :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
term = (do (_type, value, a) <- literal; return (_type, value, [a]))
      <|> (do s <- getState; a <- struct_access (get_current_scope s); return a)

function_call :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
function_call = fail "samba"

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
                  a <- term <|> exp_base
                  b <- relational_remaining a
                  return b

relational_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
relational_remaining (a_type, a_value, a) = (do
              b <- rel_op
              (c_type, c_value, c) <- relational_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_eq a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (TBool, result_value, a ++ [b] ++ c))
              <|> (do x <- or_remaining (a_type, a_value, a); return x)

or_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
or_rule = do
          a <- term <|> exp_base
          b <- or_remaining a
          return b

or_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
or_remaining (a_type, a_value, a) = (do
              b <- orToken
              (c_type, c_value, c) <- or_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_bool a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (TBool, result_value, a ++ [b] ++ c))
              <|> (do x <- and_remaining (a_type, a_value, a); return x)

and_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
and_rule = do
          a <- term <|> exp_base
          b <- and_remaining a
          return b

and_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
and_remaining (a_type, a_value, a) = (do
              b <- andToken
              (c_type, c_value, c) <- and_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_bool a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (TBool, result_value, a ++ [b] ++ c))
              <|> (do x <- arithm_remaining (a_type, a_value, a); return x)

arithm_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
arithm_rule = do
            a <- term <|> exp_base
            b <- arithm_remaining a
            return b

arithm_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
arithm_remaining (a_type, a_value, a) = (do
              b <- sum_or_minus
              (c_type, c_value, c) <- arithm_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> (do x <- mult_remaining (a_type, a_value, a); return x)

mult_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
mult_rule = do
            a <- term <|> exp_base
            b <- mult_remaining a
            return b

mult_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
mult_remaining (a_type, a_value, a) = (do
              b <- mult_or_div
              (c_type, c_value, c) <- mult_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> (do x <- pow_remaining (a_type, a_value, a); return x)

pow_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
pow_rule = do
            a <- term <|> exp_base
            b <- pow_remaining a
            return b

pow_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
pow_remaining (a_type, a_value, a) = (do
              b <- powToken
              (c_type, c_value, c) <- pow_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> return (a_type, a_value, a)

-- and 'not'
uminus_remaining :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
uminus_remaining = (do
            a <- minusToken
            (b_type, b_value, b) <- term <|> exp_base
            --
            s <- getState; pos <- getPosition
            type_check pos s check_arithm b_type b_type
            let result_value = doOpOnToken b_value a
            --
            return (b_type, result_value, a:b))
            <|>
            (do 
            a <- notToken
            (b_type, b_value, b) <- term <|> exp_base
            --
            s <- getState; pos <- getPosition
            type_check pos s check_bool b_type TBool
            let result_value = doOpOnToken b_value a
            --
            return (TBool, result_value, a:b))

sum_or_minus :: ParsecT [InfoAndToken] MyState IO (Token)
sum_or_minus = (do a <- sumToken; return a) <|> (do a <- minusToken; return a)

mult_or_div :: ParsecT [InfoAndToken] MyState IO (Token)
mult_or_div = (do a <- divToken; return a) <|> (do a <- multToken; return a)

rel_op :: ParsecT [InfoAndToken] MyState IO (Token)
rel_op = (do a <- leqToken; return a)
    <|>  (do a <- geqToken; return a)
    <|>  (do a <- compToken; return a)
    <|>  (do a <- smallerToken; return a)
    <|>  (do a <- greaterToken; return a)
    <|>  (do a <- differentToken; return a)

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
        (b_type, b_value, b) <- exp_rule
        --
        s <- getState; pos <- getPosition
        type_check pos s check_eq b_type TBool
        --
        updateState (add_current_scope_name "if")
        --
        s' <- getState;
        if (get_flag s') then updateState (set_flag b_value) else updateState (set_flag False)
        (c_type, c) <- block
        --
        updateState (remove_current_scope_name)
        --
        if (get_flag s') then updateState (set_flag (not b_value)) else updateState (set_flag False)
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
        a <- forToken
        --
        updateState (add_current_scope_name "for")
        (b_type, b) <- for_declaration
        c <- inToken
        (d_type, d) <- range_rule
        --
        s <- getState; pos <- getPosition
        type_check pos s check_eq b_type d_type
        --
        (e_type, e) <- block
        --
        updateState (remove_current_scope_name)
        return (e_type, (a:b) ++ b ++ [c] ++ d ++ e)

range_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
range_rule = (do -- Range with brackets
          a <- openSquareBracketsToken
          (b_type, b_value, b) <- exp_rule
          c <- twoDotsToken
          (d_type, d_value, d) <- exp_rule
          e <- closeSquareBracketsToken
          --
          s <- getState; pos <- getPosition
          type_check pos s check_eq b_type d_type
          --
          return (d_type, [a] ++ b ++ [c] ++ d ++ [e]))
          <|> -- Range with parantheses
          (do
          a <- openParenthesesToken
          (b_type, b_value, b) <- exp_rule
          c <- twoDotsToken
          (d_type, d_value, d) <- exp_rule
          e <- closeParenthesesToken
          --
          s <- getState; pos <- getPosition
          type_check pos s check_eq b_type d_type
          --
          return (d_type, [a] ++ b ++ [c] ++ d ++ [e]))

for_declaration :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
for_declaration = do
              b <- idToken
              c <- colonToken
              d <- types
              s <- getState
              updateState (symtable_insert_variable (b, d, get_default_value s d, []))
              liftIO (putStrLn "for_declaration:")
              print_state
              return (d, (b:c:[d]))

while_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
while_rule = do
        a <- whileToken
        --
        updateState (add_current_scope_name "while")
        (b_type, b_value, b) <- exp_rule
        --
        s <- getState; pos <- getPosition
        type_check pos s check_eq b_type TBool
        --
        (c_type, c) <- block
        --
        updateState (remove_current_scope_name)
        return (c_type, (a:b) ++ c)

repeat_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
repeat_rule = do
        a <- repeatToken
        --
        updateState (add_current_scope_name "repeat")
        (b_type, b_value, b) <- exp_rule
        --
        s <- getState; pos <- getPosition
        if isIntegral b_type then do
          --
          (c_type, c) <- block
          --
          updateState (remove_current_scope_name)
          return (c_type, (a:b) ++ c)
        else
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
                let (_, id_token_type, _, _) = lookup_var id_token_name s
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

fun_decl :: ParsecT [InfoAndToken] MyState IO [Token]
fun_decl = do
        a <- funToken
        b <- idToken
        c <- openParenthesesToken
        --
        updateState (symtable_insert_variable (b, Unit, UnitLiteral (), []))
        --
        updateState (add_current_scope_name "fun")
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
        s <- getState; pos <- getPosition
        type_check_with_msg "In function return: " pos s check_eq h_type g
        --
        updateState (remove_current_scope_name)
        --
        updateState (symtable_update_variable (b, dontChangeValue, d ++ h))
        --
        return ([a, b, c] ++ d ++ [e, f, g] ++ h)

params :: ParsecT [InfoAndToken] MyState IO ([MyType], [Value], [Token])
params = do
        b <- idToken
        c <- colonToken
        d <- types
        --
        s <- getState
        updateState (symtable_insert_variable (b, d, get_default_value s d, []))
        --
        (e_type, e_value, e) <- atrib_opt d
        --
        s' <- getState
        let var_value = if e == [] then get_default_value s' d else e_value
        updateState (symtable_update_variable (b, var_value, dontChangeFunctionBody))
        liftIO (putStrLn "params_declaration:")
        print_state
        --
        (f_types, f_values, f) <- params_op
        return (e_type:f_types, e_value:f_values, (b:c:[d]) ++ e ++ f)

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

----------------- Others -----------------

--literals :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
--literals = (do a <- literal; return a) <|> (do a <- literals; return a)

literal :: ParsecT [InfoAndToken] MyState IO (MyType, Value, Token)
literal = (do a <- natLiteralToken; return (Nat, a, a))
  <|> (do a <- intLiteralToken; return (Int, a, a))
  <|> (do a <- stringLiteralToken; return (String, a, a))
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
    s <- getState
    check_var_is_declared name s
    return (Id name))
  <|> fail "Not a valid type"

dontChangeFunctionBody = [NoneToken]
dontChangeValue = NoneToken

---------------------------------------------------
----------------- Parser invocation
---------------------------------------------------

initialState = [(Node "root" [] NoChildren, [], [], [], 0, ["root"])]
defaultValue = StringLiteral "Default Value"

parser :: [InfoAndToken] -> IO (Either ParseError [Token])
parser tokens = runParserT program initialState "Parsing error!" tokens

main :: IO ()
main = do
  args <- getArgs
  case args of 
    [filename] -> do
      tokensAndInfo <- getTokens filename
      result <- parser tokensAndInfo
      case result of
      { Left err -> print err;
        Right ans -> print ans
      }
    _ -> putStrLn "Please inform the input filename. Closing application..."