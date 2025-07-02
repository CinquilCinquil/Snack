module Funcs where

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
----------------- Functions for the symbol table
---------------------------------------------------

----------------- Insert -----------------

-- (Identifier token, Type token, value) -> ...
symtable_insert_variable :: (Token, Token, Value) -> MyState -> MyState
symtable_insert_variable var [(vars, sk, ts, sp, pc, scope_name)] = [(append_to_scope scope_name var vars, sk, ts, sp, pc, scope_name)]

-- Scope name -> (Identifier token, Type token, value) -> Tree node -> ...
append_to_scope :: ScopeName -> (Token, Token, Value) -> Variables -> Variables
-- Base:
append_to_scope (scope_namex:[]) var (Node name vars children) =
  if scope_namex == name then (Node name (append_to_variables var vars) children) -- insertion successful
  else error_msg "Scope '%' not found!" [scope_namex]
append_to_scope scope_name _ NoChildren = error_msg "Scope '%' not found!" [show scope_name]
-- Induction:
append_to_scope (scope_namex:scope_namexs) var (Node name vars children) =
  if scope_namex == name then append_to_scope scope_namexs var children
  else error_msg "Scope '%' not found!" [show (scope_namex:scope_namexs)]

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
lookup_var' var_name vars [] = var_error
lookup_var' var_name vars (scope_namex:scope_namexs) =
  case search_scope_tree (scope_namex:scope_namexs) vars of
    NoChildren -> var_error
    (Node node_name node_vars _) ->
      case get_var_info_from_scope node_name var_name node_vars of
        (_, _, ErrorToken) -> lookup_var' var_name vars scope_namexs -- search in current scope failed, go one up
        var -> var -- search successful

-- searches for a certain node of the tree
search_scope_tree :: ScopeName -> Variables -> ScopeTree
search_scope_tree [] _ = NoChildren -- not found
search_scope_tree _ NoChildren = NoChildren -- not found
search_scope_tree (scope_namex:scope_namexs) (Node name vars children) = 
  if scope_namex == name then -- search successful
    if scope_namexs == [] then (Node name vars children) else NoChildren -- not found
    else NoChildren -- not found

-- OBS: scope_name here is not a list like in MyState, its the name of a single strucure, like 'if' or a function name
get_var_info_from_scope :: Name -> Name -> [Var] -> Var
get_var_info_from_scope scope_name var_name [] = var_error
get_var_info_from_scope scope_name var_name (varx:varxs) = let (namex, valuex, typex) = varx in
  if var_name == namex then (namex, valuex, typex) else get_var_info_from_scope scope_name var_name varxs

----------------- Semantic -----------------

get_value_from_exp :: [Token] -> MyState -> Token
get_value_from_exp expression [(vars, sk, ts, sp, pc, sn)] = IntLiteral 0

type_check :: Token -> MyState -> MyType -> ParsecT [InfoAndToken] MyState IO ()
type_check (Id var_name) state _type = do
  case lookup_var var_name state of
    (_, _, ErrorToken) -> fail (replace '%' [var_name] "Variable '%' not declared!")
    (_, _, var_type) -> if var_type == _type
        then return ()
        else fail (replace '%' [show var_type, show _type] "Types '%' and '%' do not match!")

symtable_update_variable :: (Token, Value) -> MyState -> MyState
symtable_update_variable _ s = s

--symtable_remove :: MyState -> MyState -> MyState
--symtable_remove _ _ = fail "variable not found"
--symtable_remove (id1, v1) ((id2, v2):t) = 
                               --if id1 == id2 then t
                               --else (id2, v2) : symtable_remove (id1, v1) t    

-- updateState (add_current_scope_name "sla")

get_default_value :: Token -> Token
get_default_value Nat = NatLiteral 0
get_default_value Int = IntLiteral 0
get_default_value String = StringLiteral ""
get_default_value TChar = CharLiteral 'a'
get_default_value Float = FloatLiteral 0.0
get_default_value Bool = BoolLiteral False

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

error_msg :: String -> [String] -> a
error_msg msg args = error (replace '%' args msg)

replace :: Char -> [String] -> String -> String
replace _ [] msg = msg
replace _ _ [] = []
replace c (x:xs) (msgx:msgxs) = if c == msgx then (x ++ (replace c xs msgxs))
                                else (msgx:replace c (x:xs) msgxs)