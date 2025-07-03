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
                (exp_type, b) <- exp_rule
                s <- getState; pos <- getPosition
                type_check pos s check_eq id_token exp_type
                updateState (symtable_update_variable (id_token, get_value_from_exp b s))
                return (a:b))
                <|>
                (do -- Declaration
                a <- colonToken
                b <- types
                (_exp, c) <- atrib_opt -- TODO: also return type and put type check
                s <- getState
                --let var_value = if c == [] then get_default_value b else get_value_from_exp _exp s
                let var_value = get_default_value b
                updateState (symtable_insert_variable (id_token, b, var_value))
                return (a:b:c))

atrib_opt :: ParsecT [InfoAndToken] MyState IO ([Token], [Token])
atrib_opt = (do
            a <- assignToken
            (exp_type, b) <- exp_rule
            -- TODO: update symbol table
            return (b, a:b)) <|> (return ([], []))

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

exp_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
exp_rule = (do a <- arithm_exp; return a) <|> (do a <- function_call; return a)
       <|> (do
        a <- openParenthesesToken
        b <- exp_rule
        c <- closeParenthesesToken
        return b)

term :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
term = (do (_type, a) <- literal; return (_type, [a])) <|> (do a <- idToken; return (String, [a]))

function_call :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
function_call = fail "samba"

arithm_exp :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
arithm_exp = (do
              (a_type, a) <- term
              b <- arithm_exp_remaining (a_type, a)
              return b)
            <|> (do a <- mult_exp; return a)

arithm_exp_remaining :: (MyType, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, [Token])
arithm_exp_remaining (a_type, a) = (do
              b <- sum_or_minus
              (c_type, c) <- arithm_exp
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              return (c_type, a ++ [b] ++ c))
            <|> (return (a_type, a))

mult_exp :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
mult_exp = (do
            (a_type, a) <- term
            b <- mult_exp_remaining (a_type, a)
            return b)
          <|> (do a <- pow_exp; return a)

mult_exp_remaining :: (MyType, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, [Token])
mult_exp_remaining (a_type, a) = (do
              b <- mult_or_div
              (c_type, c) <- mult_exp
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              return (c_type, a ++ [b] ++ c))
            <|> (return (a_type, a))

pow_exp :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
pow_exp = (do
           (a_type, a) <- term
           b <- pow_exp_remaining (a_type, a)
           return b)
        <|> (do a <- uminus_exp; return a)

pow_exp_remaining :: (MyType, [Token]) -> ParsecT [InfoAndToken] MyState IO (MyType, [Token])
pow_exp_remaining (a_type, a) = (do
              b <- powToken
              (c_type, c) <- pow_exp
              s <- getState; pos <- getPosition
              type_check pos s check_arithm a_type c_type
              return (c_type, a ++ [b] ++ c))
            <|> (return (a_type, a))

uminus_exp :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
uminus_exp = (do
              a <- minusToken
              (b_type, b) <- exp_rule
              s <- getState; pos <- getPosition
              type_check pos s check_arithm b_type b_type
              return (b_type, a:b))
            <|> (do a <- term; return a)

sum_or_minus :: ParsecT [InfoAndToken] MyState IO (Token)
sum_or_minus = (do a <- sumToken; return a) <|> (do a <- minusToken; return a)

mult_or_div :: ParsecT [InfoAndToken] MyState IO (Token)
mult_or_div = (do a <- divToken; return a) <|> (do a <- multToken; return a)

structures :: ParsecT [InfoAndToken] MyState IO [Token]
structures = (do a <- if_rule; return a) -- TODO: fix Parser.exe: Prelude.read: no parse when reading if

if_rule :: ParsecT [InfoAndToken] MyState IO [Token]
if_rule = do
        a <- ifToken
        (b_type, b) <- exp_rule
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

literal :: ParsecT [InfoAndToken] MyState IO (MyType, Token)
literal = (do a <- natLiteralToken; return (Nat, a)) -- TODO: qnd a pessoa escreve S1 dá a entender q ela escreveu '2', mas por enquanto ela escreveu '1'. Consertar isso
  <|> (do a <- intLiteralToken; return (Int, a))
  <|> (do a <- stringLiteralToken; return (String, a))
  <|> (do a <- floatLiteralToken; return (Float, a))
  <|> (do a <- charLiteralToken; return (TChar, a))
  <|> (do a <- boolLiteralToken; return (TBool, a))
  <|> fail "Not a valid literal"

---------------------------------------------------
----------------- Parser invocation
---------------------------------------------------

initialState = [(Node "root" [] NoChildren, [], [], [], 0, ["root"])]

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