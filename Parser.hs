module Main (main) where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class
import TokenParser
import System.Environment

--- Tipos

type MyState = (Variables, Stack, Types, Subprograms, PC, Name) -- (..., PC, Scope name)
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
            f <- stmts
            -- f <- stmts
            eof
            return $ b:[c] ++ d ++ [e]

declarations :: ParsecT [InfoAndToken] MyState IO ([Token])
declarations = (do
                updateState (set_current_scope_name "$root")
                a <- declaration
                remaining_decls <- declarations
                return (a ++ remaining_decls)) <|> (return [])

declaration :: ParsecT [InfoAndToken] MyState IO ([Token])
declaration = (do
              b <- idToken
              c <- colonToken
              d <- types
              e <- semiColonToken
              s <- getState
              updateState (symtable_insert_variable (get_current_scope_name s) (b, d, get_default_value d))
              print_state
              return (b:c:d:[e])) <|> (return [])

assign :: ParsecT [InfoAndToken] MyState IO ([Token])
assign = do
        a <- idToken
        b <- assignToken
        c <- intLiteralToken
        d <- semiColonToken
        s <- getState
        --updateState (symtable_update_variable (get_current_scope_name s) (b, d, get_default_value d))
        print_state
        return (a:b:c:[d])

stmts :: ParsecT [InfoAndToken] MyState IO ([Token])
stmts = ((do a <- declaration; return a) <|> (do a <- assign; return a))

types :: ParsecT [InfoAndToken] MyState IO (Token)
types =
  (do a <- natToken; return a) <|> (do a <- intToken; return a) <|> (do a <- stringToken; return a)
  <|> (do a <- floatToken; return a ) <|> (do a <- charToken; return a) <|> (do a <- boolToken; return a)
  <|> (do a <- typeToken; return a) <|> fail "Not a valid type"

-- funções para a tabela de símbolos

print_state :: ParsecT [InfoAndToken] MyState IO ()
print_state = do
              s <- getState
              liftIO (print s)

set_current_scope_name :: Name -> MyState -> MyState
set_current_scope_name name (vars, stack, types, subprograms, pc, sn) =
  (vars, stack, types, subprograms, pc, name)

get_current_scope_name :: MyState -> Name
get_current_scope_name (vars, stack, types, subprograms, pc, sn) = sn

symtable_insert_variable :: Name -> (Token, Token, Value) -> MyState -> MyState
symtable_insert_variable scopeName var (vars, stack, types, subprograms, pc, sn) =
   (append_to_scope scopeName var vars, stack, types, subprograms, pc, sn)

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

initialState = ([], [], [], [], 0, "$root")

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