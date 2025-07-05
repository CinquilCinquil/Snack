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
            f <- stmts
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
declaration = do
              b <- idToken
              c <- colonToken
              d <- types
              e <- semiColonToken
              s <- getState
              updateState (symtable_insert_variable (b, d, get_default_value d))
              liftIO (putStrLn "declaration:")
              print_state
              return (b:c:d:[e])

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
                updateState (symtable_update_variable (id_token, exp_value))
                --
                return (a:b))
                <|>
                (do -- Declaration
                a <- colonToken
                b <- types
                (exp_type, exp_value, c) <- atrib_opt b
                --
                updateState (symtable_insert_variable (id_token, b, get_default_value b))
                --
                s <- getState; pos <- getPosition
                type_check pos s check_eq id_token exp_type
                let var_value = if c == [] then get_default_value b else exp_value
                updateState (symtable_update_variable (id_token, var_value))
                --
                return (a:b:c))

atrib_opt :: MyType -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
atrib_opt _type = (do
            a <- assignToken
            (exp_type, exp_value, b) <- exp_rule
            return (exp_type, exp_value, a:b)) <|> (return (_type, defaultValue, []))

stmts :: ParsecT [InfoAndToken] MyState IO ([Token])
stmts = do
        a <- stmt
        b <- stmts_op
        return (a ++ b)

stmts_op :: ParsecT [InfoAndToken] MyState IO ([Token])
stmts_op = (do a <- stmts; return a) <|> (return [])

stmt :: ParsecT [InfoAndToken] MyState IO ([Token])
stmt = (do a <- decl_or_atrib; return a) <|> (do a <- structures;return a)

types :: ParsecT [InfoAndToken] MyState IO (Token)
types =
  (do a <- natToken; return a)
  <|> (do a <- intToken; return a)
  <|> (do a <- stringToken; return a)
  <|> (do a <- floatToken; return a ) 
  <|> (do a <- charToken; return a)
  <|> (do a <- boolToken; return a)
  <|> (do a <- typeToken; return a)
  <|> fail "Not a valid type"

exp_rule :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
exp_rule = (do a <- boolean_arithm_exp; return a)
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
        let (_, a_type, a_value) = lookup_var a_name s
        return (a_type, a_value, [(Id a_name)]))

function_call :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
function_call = fail "samba"

boolean_arithm_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
boolean_arithm_exp = (do
                      (a_type, a_value, a) <- term
                      b <- boolean_arithm_exp_remaining (a_type, a_value, a)
                      return b)
                      <|> (do a <- arithm_exp; return a)

boolean_arithm_exp_remaining :: (MyType, Value, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
boolean_arithm_exp_remaining (a_type, a_value, a) = (do
                  b <- rel_op
                  (c_type, c_value, c) <- exp_rule
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
    <|>  (do a <- andToken; return a)
    <|>  (do a <- orToken; return a)
    <|>  (do a <- differentToken; return a)

structures :: ParsecT [InfoAndToken] MyState IO [Token]
structures = (do a <- if_rule; return a)
          <|> (do a <- for_rule; return a) 
          <|> (do a <- while_rule; return a)
          <|> (do a <- repeat_rule; return a)
          <|> (do a <- match_rule; return a)

block :: ParsecT [InfoAndToken] MyState IO [Token]
block = do
      a <- openBracketsToken
      b <- stmts_op
      c <- closeBracketsToken
      return ((a:b) ++ [c])

if_rule :: ParsecT [InfoAndToken] MyState IO [Token]
if_rule = do
        a <- ifToken
        (b_type, b_value, b) <- exp_rule
        s <- getState; pos <- getPosition
        type_check pos s check_eq b_type TBool
        --
        updateState (add_current_scope_name "if")
        --
        c <- block
        --
        updateState (remove_current_scope_name)
        --
        d <- else_op
        --
        return ((a:b) ++ c ++ d)

else_op :: ParsecT [InfoAndToken] MyState IO [Token]
else_op = (do
          a <- elseToken
          --
          updateState (add_current_scope_name "else")
          --
          b <- (do a <- if_rule; return a) <|> (do a <- block; return a)
          --
          updateState (remove_current_scope_name)
          --
          return (a:b)) <|> (return [])

for_rule :: ParsecT [InfoAndToken] MyState IO [Token]
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
        e <- block
        --
        updateState (remove_current_scope_name)
        return ((a:b) ++ b ++ [c] ++ d ++ e)

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
              updateState (symtable_insert_variable (b, d, get_default_value d))
              liftIO (putStrLn "for_declaration:")
              print_state
              return (d, (b:c:[d]))

while_rule :: ParsecT [InfoAndToken] MyState IO [Token]
while_rule = do
        a <- whileToken
        --
        updateState (add_current_scope_name "while")
        (b_type, b_value, b) <- exp_rule
        --
        s <- getState; pos <- getPosition
        type_check pos s check_eq b_type TBool
        --
        c <- block
        --
        updateState (remove_current_scope_name)
        return ((a:b) ++ c)

repeat_rule :: ParsecT [InfoAndToken] MyState IO [Token]
repeat_rule = do
        a <- repeatToken
        --
        updateState (add_current_scope_name "repeat")
        (b_type, b_value, b) <- exp_rule
        --
        s <- getState; pos <- getPosition
        if isIntegral b_type then do
          --
          c <- block
          --
          updateState (remove_current_scope_name)
          return ((a:b) ++ c)
        else
          error_msg "Expression in Repeat must be integral! Line: % Column: %" [showLine pos, showColumn pos]

match_rule :: ParsecT [InfoAndToken] MyState IO [Token]
match_rule = do
        a <- matchToken
        b <- idToken
        c <- withToken
        --
        updateState (add_current_scope_name "match")
        --
        d <- match_block
        --
        updateState (remove_current_scope_name)
        return (a:b:c:d)

match_block :: ParsecT [InfoAndToken] MyState IO [Token]
match_block = do
        a <- openBracketsToken
        b <- form_blocks_opt
        c <- closeBracketsToken
        return ((a:b) ++ [c])

form_blocks_opt :: ParsecT [InfoAndToken] MyState IO [Token]
form_blocks_opt = (do a <- formToken; b <- form_blocks_start; return (a:b)) <|> (return [])

form_blocks_start :: ParsecT [InfoAndToken] MyState IO [Token]
form_blocks_start = (do
                a <- idToken
                b <- openParenthesesToken
                c <- idsOpt
                -- TODO: check if the arguments match with the informed type at match_rule
                d <- closeParenthesesToken
                e <- form_block
                return ((a:b:c) ++ (d:e)))
                <|>
                (do
                (_, _, a) <- literal
                b <- form_block
                return (a:b))

form_block :: ParsecT [InfoAndToken] MyState IO [Token]
form_block = do
            a <- colonToken
            b <- stmts_op
            c <- form_blocks_opt
            return ((a:b) ++ c)

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
literal = (do NatLiteral n <- natLiteralToken; return (Nat, NatLiteral (n + 1), NatLiteral n))
  <|> (do a <- intLiteralToken; return (Int, a, a))
  <|> (do a <- stringLiteralToken; return (String, a, a))
  <|> (do a <- floatLiteralToken; return (Float, a, a))
  <|> (do a <- charLiteralToken; return (TChar, a, a))
  <|> (do a <- boolLiteralToken; return (TBool, a, a))
  <|> fail "Not a valid literal"

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