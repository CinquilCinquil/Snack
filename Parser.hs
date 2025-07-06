module Main (main) where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class
import TokenParser
import Funcs -- includes types and functions
import System.Environment

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
              s <- getState
              updateState (symtable_insert_variable (b, d, get_default_value d, []))
              liftIO (putStrLn "declaration:")
              print_state
              return (b:c:d:[e]))
              <|>
              (do
              a <- fun_decl
              liftIO (putStrLn "fun_declaration:")
              print_state
              return a)

----------------- Main -----------------

decl_or_atrib :: ParsecT [InfoAndToken] MyState IO ([Token])
decl_or_atrib = do
                a <- idToken
                b <- init_or_decl a
                c <- semiColonToken
                liftIO (putStrLn "decl_or_atrib:")
                print_state
                return ((a:b) ++ [c])

init_or_decl :: Token -> ParsecT [InfoAndToken] MyState IO ([Token])
init_or_decl id_token = (do -- Assignment
                a <- assignToken
                (exp_type, exp_value, b) <- exp_rule
                --
                s <- getState; pos <- getPosition
                type_check pos s check_eq id_token exp_type
                updateState (symtable_update_variable (id_token, exp_value, []))
                --
                return (a:b))
                <|>
                (do -- Declaration
                a <- colonToken
                b <- types
                (exp_type, exp_value, c) <- atrib_opt b
                --
                updateState (symtable_insert_variable (id_token, b, get_default_value b, []))
                --
                s <- getState; pos <- getPosition
                type_check pos s check_eq id_token exp_type
                let var_value = if c == [] then get_default_value b else exp_value
                updateState (symtable_update_variable (id_token, var_value, []))
                --
                return (a:b:c))

atrib_opt :: MyType -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
atrib_opt _type = (do
            a <- assignToken
            (exp_type, exp_value, b) <- exp_rule
            return (exp_type, exp_value, a:b)) <|> (return (_type, defaultValue, []))

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

stmt :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
stmt = (do a <- decl_or_atrib; return (Unit, a))
   <|> (do a <- fun_decl; return (Unit, a))
   <|> (do a <- structures; return a)
   <|> (do
    a <- returnToken
    (b_type, _, b) <- exp_rule
    -- TODO: when semantic -> return value to function call
    c <- semiColonToken
    return (b_type, (a:b) ++ [c]))

exp_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
exp_rule = (do a <- boolean_and_arithm_exp; return a)
       <|> (do a <- function_call; return a)
       <|> (do
        a <- openParenthesesToken
        (b_type, b_value, b) <- exp_rule
        c <- closeParenthesesToken
        return (b_type, b_value, [a] ++ b ++ [c]))

term :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
term = (do (_type, value, a) <- literal; return (_type, value, [a]))
      <|> (do
        (Id a_name) <- idToken
        s <- getState
        let (_, a_type, a_value, _) = lookup_var a_name s
        return (a_type, a_value, [(Id a_name)]))

function_call :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
function_call = fail "samba"

boolean_and_arithm_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
boolean_and_arithm_exp = (do
                      (a_type, a_value, a) <- term
                      b <- boolean_and_arithm_exp_remaining (a_type, a_value, a)
                      return b)
                      <|> (do a <- boolean_exp; return a)

boolean_and_arithm_exp_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
boolean_and_arithm_exp_remaining (a_type, a_value, a) = (do
                  b <- rel_op
                  (c_type, c_value, c) <- boolean_and_arithm_exp
                  --
                  s <- getState; pos <- getPosition
                  type_check pos s check_eq a_type c_type
                  let result_value = doOpOnTokens a_value c_value b
                  --
                  return (TBool, result_value, a ++ [b] ++ c))
                  <|> (return (a_type, a_value, a))

boolean_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
boolean_exp = (do
              (a_type, a_value, a) <- term
              b <- boolean_exp_remaining (a_type, a_value, a)
              return b)
              <|> (do a <- and_exp; return a)

boolean_exp_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
boolean_exp_remaining (a_type, a_value, a) = (do
                  b <- orToken
                  (c_type, c_value, c) <- boolean_exp
                  --
                  s <- getState; pos <- getPosition
                  type_check pos s check_bool a_type c_type
                  let result_value = doOpOnTokens a_value c_value b
                  --
                  return (TBool, result_value, a ++ [b] ++ c))
                  <|> (return (a_type, a_value, a))

and_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
and_exp = (do
          (a_type, a_value, a) <- term
          b <- and_exp_remaining (a_type, a_value, a)
          return b)
          <|> (do a <- arithm_exp; return a)

and_exp_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
and_exp_remaining (a_type, a_value, a) = (do
                  b <- andToken
                  (c_type, c_value, c) <- and_exp
                  --
                  s <- getState; pos <- getPosition
                  type_check pos s check_bool a_type c_type
                  let result_value = doOpOnTokens a_value c_value b
                  --
                  return (TBool, result_value, a ++ [b] ++ c))
                  <|> (return (a_type, a_value, a))

arithm_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
arithm_exp = (do
             (a_type, a_value, a) <- term
             b <- arithm_exp_remaining (a_type, a_value, a)
             return b)
             <|> (do a <- mult_exp; return a)

arithm_exp_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
arithm_exp_remaining (a_type, a_value, a) = (do
              b <- sum_or_minus
              (c_type, c_value, c) <- arithm_exp
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (c_type, result_value,  a ++ [b] ++ c))
            <|> (return (a_type, a_value, a))

mult_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
mult_exp = (do
            (a_type, a_value, a) <- term
            b <- mult_exp_remaining (a_type, a_value, a)
            return b)
          <|> (do a <- pow_exp; return a)

mult_exp_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
mult_exp_remaining (a_type, a_value, a) = (do
              b <- mult_or_div
              (c_type, c_value, c) <- mult_exp
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> (return (a_type, a_value, a))

pow_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
pow_exp = (do
           (a_type, a_value, a) <- term
           b <- pow_exp_remaining (a_type, a_value, a)
           return b)
        <|> (do a <- uminus_exp; return a)

pow_exp_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
pow_exp_remaining (a_type, a_value, a) = (do
              b <- powToken
              (c_type, c_value, c) <- pow_exp
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> (return (a_type, a_value, a))

-- and 'not'
uminus_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
uminus_exp = (do
              a <- minusToken
              (b_type, b_value, b) <- exp_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm b_type b_type
              let result_value = doOpOnToken b_value a
              --
              return (b_type, result_value, a:b))
              <|>
              (do 
              a <- notToken
              (b_type, b_value, b) <- exp_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_bool b_type TBool
              let result_value = doOpOnToken b_value a
              --
              return (TBool, result_value, a:b))
              <|> (do a <- term; return a)

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
        (c_type, c) <- block
        --
        updateState (remove_current_scope_name)
        --
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
              updateState (symtable_insert_variable (b, d, get_default_value d, []))
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
        updateState (symtable_update_variable_type (b, g)) -- TODO: symtable_update_variable_type
        --
        (h_type, h) <- block
        --
        s <- getState; pos <- getPosition
        type_check_with_msg "In function return: " pos s check_eq h_type g
        --
        updateState (remove_current_scope_name)
        --
        updateState (symtable_update_variable (b, h))
        --
        return ([a, b, c] ++ d ++ [e, f, g] ++ h)

params :: ParsecT [InfoAndToken] MyState IO ([MyType], [Value], [Token])
params = do
        b <- idToken
        c <- colonToken
        d <- types
        --
        updateState (symtable_insert_variable (b, d, get_default_value d, []))
        --
        (e_type, e_value, e) <- atrib_opt d
        let var_value = if e == [] then get_default_value d else e_value
        updateState (symtable_update_variable (b, var_value, []))
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
  <|> (do a <- openParenthesesToken; b <- closeParenthesesToken; return (Unit, UnitLiteral (), UnitLiteral ()))
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
  <|> fail "Not a valid type"

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