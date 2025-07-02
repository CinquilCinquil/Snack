module Main (main) where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class
import TokenParser
import System.Environment

---------------------------------------------------
----------------- Types
---------------------------------------------------

type MyState = [(Variables, Stack, Types, Subprograms, PC, ScopeName)] -- (..., PC, Scope name)
--
type Variables = ScopeTree -- (Scope name, Variables)
type Stack = [(Name, PC)]
type Types = [(Name, [Form])]
type Subprograms = [(Name, MyType, Args, Int)] -- (Name, return _type, arguments, start line)
type PC = Int
type ScopeName = [String]
--
data ScopeTree =
  Node Name [Var] ScopeTree -- Name  [Var]  Children
  | NoChildren
  deriving (Eq,Show) 
type Name = String
type Var = (String, Value, MyType)
type Value = Token
type MyType = Token
type Form = (Name, Args)
type Args = ()

---------------------------------------------------
----------------- Parsers for the non-terminals
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
            return $ b:[c] ++ d ++ [e]

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
              print_state
              return (b:c:d:[e])

----------------- Main -----------------

decl_or_atrib :: ParsecT [InfoAndToken] MyState IO ([Token])
decl_or_atrib = do
                a <- idToken
                b <- init_or_decl a
                print_state
                return (a:b)

init_or_decl :: Token -> ParsecT [InfoAndToken] MyState IO ([Token])
init_or_decl id_token = (do -- Assignment
                a <- assignToken
                (exp_type, b) <- exp_rule
                s <- getState
                type_check id_token s exp_type
                updateState (symtable_update_variable (id_token, get_value_from_exp b s))
                return (a:b))
                <|>
                (do -- Declaration
                a <- colonToken
                b <- types
                (_exp, c) <- atrib_opt -- TODO: also return type
                s <- getState
                let var_value = if c == [] then get_default_value b else get_value_from_exp _exp s
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
        b <- semiColonToken
        c <- stmts_op
        return (a ++ (b:c))

stmts_op :: ParsecT [InfoAndToken] MyState IO ([Token])
stmts_op = (do a <- stmts; return a) <|> (return [])

stmt :: ParsecT [InfoAndToken] MyState IO ([Token])
stmt = (do a <- decl_or_atrib; return a)

types :: ParsecT [InfoAndToken] MyState IO (Token)
types =
  (do a <- natToken; return a) <|> (do a <- intToken; return a) <|> (do a <- stringToken; return a)
  <|> (do a <- floatToken; return a ) <|> (do a <- charToken; return a) <|> (do a <- boolToken; return a)
  <|> (do a <- typeToken; return a) <|> fail "Not a valid type"


exp_rule :: ParsecT [InfoAndToken] MyState IO (MyType, [Token])
exp_rule = return (String, [])

---------------------------------------------------
----------------- Functions for the symbol table
---------------------------------------------------

----------------- Insert -----------------

-- (Identifier token, Type token, value) -> ...
symtable_insert_variable :: (Token, Token, Value) -> MyState -> MyState
symtable_insert_variable var [(vars, sk, ts, sp, pc, scope_name)] = [(append_to_scope scope_name var vars, sk, ts, sp, pc, scope_name)]

-- Scope name -> (Identifier token, Type token, value) -> ...
append_to_scope :: ScopeName -> (Token, Token, Value) -> Variables -> Variables
append_to_scope (scope_namex:[]) var (Node name vars children) =
  if scope_namex == name then (Node name (append_to_variables var vars) children)
  else error ("Scope '" ++ (show $ scope_namex) ++ "' not found !")
append_to_scope scope_name _ NoChildren = error ("Scope '" ++ (show $ scope_name) ++ "' not found !")
append_to_scope (scope_namex:scope_namexs) var (Node name vars children) =
  if scope_namex == name then append_to_scope scope_namexs var children
  else error ("Scope '" ++ (show $ scope_namex:scope_namexs) ++ "' not found !")

-- (Identifier token, Type token, value) -> ...
append_to_variables :: (Token, Token, Value) -> [Var] -> [Var]
append_to_variables var [] = [makeVar var]
append_to_variables var (varx:varxs) =
  let (Id name, _, _) = var in
  let (namex, typex, _) = varx in
  if name == namex then error ("Variable with name '" ++ name ++ "' already declared as " ++ (show typex) ++ " !")
  else (varx : append_to_variables var varxs)

-- Turns tokens into a Var type
makeVar :: (Token, Token, Value) -> Var
makeVar (Id name, type_, value) = (name, value, type_)

----------------- Search -----------------

-- wrapper for lookup_var'
lookup_var :: Name -> MyState -> Var
lookup_var var_name [(vars, sk, ts, sp, pc, scope_name)] = lookup_var' var_name vars scope_name

-- searches tree bottom-up
lookup_var' :: Name -> Variables -> ScopeName -> Var
lookup_var' var_name vars [] = get_var_info_from_scope "$The entire file$" var_name []
lookup_var' var_name vars (scope_namex:scope_namexs) =
  do
  case search_scope_tree (scope_namex:scope_namexs) vars of
    NoChildren -> var_error;
    (Node namex varsx childrenx) -> let (namey, typey, valuey) = get_var_info_from_scope namex var_name varsx in 
      if namey == "" then lookup_var' var_name vars scope_namexs else (namey, typey, valuey)

-- searches for a certain node of the tree
search_scope_tree :: ScopeName -> Variables -> ScopeTree
search_scope_tree [] node = node
search_scope_tree scope_name NoChildren = error ("Scope '" ++ (show $ scope_name) ++ "' not found !")
search_scope_tree (scope_namex:scope_namexs) (Node name vars children) = 
  if scope_namex == name then search_scope_tree scope_namexs children
  else error ("Scope '" ++ (show $ scope_namex:scope_namexs) ++ "' not found !")

-- OBS: scope_name here is not a list like in MyState, its the name of a single strucure, like 'if' or a function name
get_var_info_from_scope :: Name -> Name -> [Var] -> Var
get_var_info_from_scope scope_name var_name [] = var_error
get_var_info_from_scope scope_name var_name (varx:varxs) = let (namex, valuex, typex) = varx in
  if var_name == namex then (namex, valuex, typex) else get_var_info_from_scope scope_name var_name varxs

----------------- Semantic -----------------

get_value_from_exp :: [Token] -> MyState -> Token
get_value_from_exp expression [(vars, sk, ts, sp, pc, sn)] = IntLiteral 0

type_check :: Token -> MyState -> MyType -> ParsecT [InfoAndToken] MyState IO ()
type_check (Id var_name) s _type =
  case lookup_var var_name s of
    var_error -> fail ("Variable '" ++ var_name ++ "' not declared!");
    (_, _, var_type) -> if var_type == _type
      then return ()
      else fail ("Types '" ++ (show var_type) ++ "' and '" ++ (show _type) ++ "' do not match!")

symtable_update_variable :: (Token, Value) -> MyState -> MyState
symtable_update_variable _ s = s

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

-- updateState (add_current_scope_name "sla")

get_default_value :: Token -> Token
get_default_value Int = IntLiteral 0

----------------- Others -----------------

print_state :: ParsecT [InfoAndToken] MyState IO ()
print_state = do
              s <- getState
              liftIO (print s)

add_current_scope_name :: Name -> MyState -> MyState
add_current_scope_name name [(vars, sk, ts, sp, pc, scope_name)] = [(vars, sk, ts, sp, pc, scope_name ++ [name])]

remove_current_scope_name :: MyState -> MyState
remove_current_scope_name [(vars, sk, ts, sp, pc, scope_name)] = [(vars, sk, ts, sp, pc, reverse $ tail $ reverse scope_name)]

var_error = ("", ErrorToken, ErrorToken)

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