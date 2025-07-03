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
                (exp_type, exp_value, c) <- atrib_opt -- TODO: also return type and put type check
                --
                s <- getState; pos <- getPosition
                type_check pos s check_eq id_token exp_type
                let var_value = if c == [] then get_default_value b else exp_value
                updateState (symtable_insert_variable (id_token, b, var_value))
                --
                return (a:b:c))

atrib_opt :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
atrib_opt = (do
            a <- assignToken
            (exp_type, exp_value, b) <- exp_rule
            s <- getState; pos <- getPosition
            return (exp_type, exp_value, a:b)) <|> (return (String, defaultValue, []))

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
exp_rule = (do a <- arithm_exp; return a) <|> (do a <- function_call; return a)
       <|> (do
        a <- openParenthesesToken
        b <- exp_rule
        c <- closeParenthesesToken
        return b)

term :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
term = (do (_type, value, a) <- literal; return (_type, value, [a])) <|> (do a <- idToken; return (String, defaultValue, [a]))

function_call :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
function_call = fail "samba"

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
              s <- getState; pos <- getPosition
              --
              type_check pos s check_arithm a_type c_type
              let result_value = doOpOnTokens a_value c_value b
              --
              return (c_type, result_value, a ++ [b] ++ c))
            <|> (return (a_type, a_value, a))

uminus_exp :: ParsecT [InfoAndToken] MyState IO (MyType, Value, [Token])
uminus_exp = (do
              a <- minusToken
              (b_type, b_value, b) <- exp_rule
              --
              s <- getState; pos <- getPosition
              type_check pos s check_arithm b_type b_type
              let result_value = b_value -- TODO: Unary op
              --
              return (b_type, result_value, a:b))
            <|> (do a <- term; return a)

sum_or_minus :: ParsecT [InfoAndToken] MyState IO (Token)
sum_or_minus = (do a <- sumToken; return a) <|> (do a <- minusToken; return a)

mult_or_div :: ParsecT [InfoAndToken] MyState IO (Token)
mult_or_div = (do a <- divToken; return a) <|> (do a <- multToken; return a)

structures :: ParsecT [InfoAndToken] MyState IO [Token]
structures = (do a <- if_rule; return a)

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
          b <- block
          --
          updateState (remove_current_scope_name)
          --
          return (a:b)) <|> (return [])

block :: ParsecT [InfoAndToken] MyState IO [Token]
block = do
      a <- openBracketsToken
      b <- stmts_op
      c <- closeBracketsToken
      return ((a:b) ++ [c])

----------------- Others -----------------

--literals :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
--literals = (do a <- literal; return a) <|> (do a <- literals; return a)

literal :: ParsecT [InfoAndToken] MyState IO (MyType, Value, Token)
literal = (do a <- natLiteralToken; return (Nat, a, a)) -- TODO: qnd a pessoa escreve S1 dá a entender q ela escreveu '2', mas por enquanto ela escreveu '1'. Consertar isso
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