module Main (main) where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class
import TokenParser
import System.Environment

--- Tipos

type MyState = (Variables, Stack, Types, Subprograms, PC)
--
type Variables = [(Name, [Var])] -- (Scope name, Variables)
type Stack = [(Name, PC)]
type Types = [(Name, [Form])]
type Subprograms = [(Name, MyType, Args, Int)] -- (Name, return type, arguments, start line)
type PC = Int
--
type Name = String
type Var = (String, Value, MyType, Address)
type Value = Token
type MyType = Token
type Form = (Name, Args)
type Args = ()
type Address = ()

-- parsers para os não-terminais

program :: ParsecT [InfoAndToken] MyState IO ([Token])
program = do
            --a <- importToken
            b <- typesToken -- types:
            c <- declsToken -- declarations:
            d <- declarations
            e <- mainToken -- main:
            -- f <- stmts
            eof
            return $ b:[c] ++ d ++ [e]

declarations :: ParsecT [InfoAndToken] MyState IO ([Token])
declarations = (do
                b <- idToken
                c <- colonToken
                d <- types
                e <- semiColonToken
                updateState(symtable_insert_variable "$root" (b, d, get_default_value d))
                s <- getState
                liftIO (print s)
                remaining_decls <- declarations
                return (b:c:d:e:remaining_decls)) <|> (return [])

types :: ParsecT [InfoAndToken] MyState IO (Token)
types =
  (do a <- natToken; return a) <|> (do a <- intToken; return a) <|> (do a <- stringToken; return a)
  <|> (do a <- floatToken; return a ) <|> (do a <- charToken; return a) <|> (do a <- boolToken; return a)
  <|> (do a <- typeToken; return a) <|> fail "Not a valid type"

-- funções para a tabela de símbolos        

symtable_insert_variable :: Name -> (Token, Token, Value) -> MyState -> MyState
symtable_insert_variable scopeName var (vars, stack, types, subprograms, pc) =
   (append_to_scope scopeName var vars, stack, types, subprograms, pc)

append_to_scope :: Name -> (Token, Token, Value) -> Variables -> Variables
append_to_scope scopeName var [] = [(scopeName, [makeVar var])]
append_to_scope scopeName var ((xscopeName, xvars):xs) = 
  if scopeName == xscopeName then (xscopeName, (makeVar var):xvars):xs
  else (xscopeName, xvars):(append_to_scope scopeName var xs)

makeVar :: (Token, Token, Value) -> Var --(String, Value, MyType, Address)
makeVar (Id name, type_, value) = (name, value, type_, ())                           


-- TODO: adapt to MyState
--symtable_update :: MyState -> MyState -> MyState
--symtable_update _ _ = fail "variable not found"
--symtable_update (id1, v1) ((id2, v2):t) = 
                               --if id1 == id2 then (id1, v1) : t
                               --else (id2, v2) : symtable_update (id1, v1) t

--symtable_remove :: MyState -> MyState -> MyState
--symtable_remove _ _ = fail "variable not found"
--symtable_remove (id1, v1) ((id2, v2):t) = 
                               --if id1 == id2 then t
                               --else (id2, v2) : symtable_remove (id1, v1) t    


-- funções para verificação de tipos

get_default_value :: Token -> Token
get_default_value Int = IntLiteral 0

-- invocação do parser para o símbolo de partida 

initialState = ([], [], [], [], 0)

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