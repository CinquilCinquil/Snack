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
type Var = (Name, MyType, Value, FunctionBody)
type FunctionBody = [Token]
type Value = Token
type MyType = Token
type Form = (Name, Args)
type Args = ()

---------------------------------------------------
----------------- Functions for the symbol table
---------------------------------------------------

----------------- Insert -----------------

-- (Identifier token, Type token, value) -> ...
symtable_insert_variable :: (Token, Token, Value, FunctionBody) -> MyState -> MyState
symtable_insert_variable var [(vars, sk, ts, sp, pc, scope_name)] = [(append_to_scope scope_name var vars, sk, ts, sp, pc, scope_name)]

-- Scope name -> (Identifier token, Type token, value) -> Tree node -> ...
append_to_scope :: ScopeName -> (Token, Token, Value, FunctionBody) -> Variables -> Variables
-- Base:
append_to_scope (scope_namex:[]) var (Node name vars children) =
  if scope_namex == name then (Node name (append_to_variables var vars) children) -- insertion successful
  else error_msg "In var declaration, scope '%' not found!" [scope_namex]
append_to_scope scope_name _ NoChildren = error_msg "In var declaration, scope '%' not found!" [show scope_name]
-- Induction:
append_to_scope (scope_namex:scope_namexs) var (Node name vars children) =
  if scope_namex == name then (Node name vars (append_to_scope scope_namexs var children))
  else error_msg "In var declaration, scope '%' not found!" [show (scope_namex:scope_namexs)]

-- (Identifier token, Type token, value) -> ...
append_to_variables :: (Token, Token, Value, FunctionBody) -> [Var] -> [Var]
append_to_variables var [] = [makeVar var]
append_to_variables var (varx:varxs) =
  let (Id name, _, _, _) = var in
  let (namex, typex, _, _) = varx in
  if name == namex then error_msg "Variable with name '%' already declared as a '%'" [name, show typex]
  else (varx : append_to_variables var varxs)

-- Turns tokens into a Var type
makeVar :: (Token, Token, Value, FunctionBody) -> Var
makeVar (Id name, type_, value, funcb) = (name, type_, value, funcb)

add_current_scope_name :: Name -> MyState -> MyState
add_current_scope_name name [(vars, sk, ts, sp, pc, scope_name)] =
  case append_scope vars scope_name name of
    NoChildren -> error_msg "Failed adding to scope" []
    new_vars -> [(new_vars, sk, ts, sp, pc, scope_name ++ [name])]

remove_current_scope_name :: MyState -> MyState
remove_current_scope_name [(vars, sk, ts, sp, pc, scope_name)] = 
  [(symtable_remove_scope scope_name vars, sk, ts, sp, pc, reverse $ tail $ reverse scope_name)]

append_scope :: Variables -> ScopeName -> Name -> Variables
append_scope NoChildren _ _ = NoChildren
append_scope (Node _ _ NoChildren) [] _ = NoChildren
append_scope (Node name vars NoChildren) (scope_namex:[]) new_scope_name = 
  if name == scope_namex then (Node name vars (Node new_scope_name [] NoChildren))
  else NoChildren
append_scope (Node name vars children) (scope_namex:scope_namexs) new_scope_name = 
  if name == scope_namex then (Node name vars (append_scope children scope_namexs new_scope_name))
  else NoChildren
append_scope _ _ _ = NoChildren

----------------- Search -----------------

-- wrapper for lookup_var'
lookup_var :: Name -> MyState -> Var
lookup_var var_name [(vars, sk, ts, sp, pc, scope_name)] = lookup_var' var_name vars scope_name

-- searches tree bottom-up
lookup_var' :: Name -> Variables -> ScopeName -> Var
lookup_var' var_name vars [] = var_error
lookup_var' var_name vars scope_name =
  case search_scope_tree scope_name vars of
    NoChildren -> var_error
    (Node node_name node_vars _) ->
      case get_var_info_from_scope node_name var_name node_vars of
        (_, _, ErrorToken, _) -> lookup_var' var_name vars (reverse $ tail $ reverse scope_name) -- search in current scope failed, go one up
        var -> var -- search successful

-- searches for a certain node of the tree
search_scope_tree :: ScopeName -> Variables -> ScopeTree
search_scope_tree [] _ = NoChildren -- not found
search_scope_tree _ NoChildren = NoChildren -- not found
search_scope_tree (scope_namex:scope_namexs) (Node name vars children) = 
  if scope_namex == name then -- up until now search is successful
    if scope_namexs == [] then (Node name vars children) else search_scope_tree scope_namexs children -- search is successful
    else NoChildren -- not found

-- OBS: scope_name here is not a list like in MyState, its the name of a single strucure, like 'if' or a function name
get_var_info_from_scope :: Name -> Name -> [Var] -> Var
get_var_info_from_scope scope_name var_name [] = var_error
get_var_info_from_scope scope_name var_name (varx:varxs) = let (namex, typex, valuex, funcbx) = varx in
  if var_name == namex then (namex, typex, valuex, funcbx) else get_var_info_from_scope scope_name var_name varxs

----------------- Update -------------------

-- wrapper for symtable_update_variable'
symtable_update_variable :: (Token, Value, FunctionBody) -> MyState -> MyState
symtable_update_variable (Id var_name, value, funcb) [(vars, sk, ts, sp, pc, scope_name)] = do
  [(symtable_update_variable' scope_name (var_name, value, funcb) vars, sk, ts, sp, pc, scope_name)]

-- updates tree bottom-up
symtable_update_variable' :: ScopeName -> (Name, Value, FunctionBody) -> Variables -> Variables
symtable_update_variable' _ (name, _, _) NoChildren = error_msg "Variable '%' not found" [name]
symtable_update_variable' [] (name, _, _) _ = error_msg "Variable '%' not found" [name]
symtable_update_variable' scope_name var vars =
  case update_scope_tree scope_name vars var of
    NoChildren -> symtable_update_variable' (reverse $ tail $ reverse scope_name) var vars -- search in current scope failed, go one up
    new_vars -> new_vars -- search successful

-- updates a certain node of the tree
update_scope_tree :: ScopeName -> Variables -> (Name, Value, FunctionBody) -> ScopeTree
update_scope_tree [] _ _ = NoChildren -- not found
update_scope_tree _ NoChildren _ = NoChildren -- not found
update_scope_tree (scope_namex:scope_namexs) (Node name vars children) var = 
  if scope_namex == name then -- up until now search is successful
    if scope_namexs == [] then (Node name (update_in_variables var vars) children) else (Node name vars (update_scope_tree scope_namexs children var))  -- search is successful
    else NoChildren -- not found

-- (variable name, value) -> ...
update_in_variables :: (Name, Value, FunctionBody) -> [Var] -> [Var]
update_in_variables _ [] = []
update_in_variables (name, value, funcb) (varx:varxs) =
  let (namex, typex, _, funcbx) = varx in
  if name == namex then ((namex, typex, value, if funcb == [] then funcbx else funcb):varxs) else (varx : update_in_variables (name, value, funcb) varxs)

symtable_remove_scope :: ScopeName -> Variables -> Variables
symtable_remove_scope _ NoChildren = error_msg "dame" []
symtable_remove_scope [] _ = error_msg "dame" []
symtable_remove_scope (scope_namex:[]) (Node name vars children) = 
  if scope_namex == name then NoChildren 
  else error_msg "dame" []
symtable_remove_scope (scope_namex:scope_namexs) (Node name vars children) = 
  if scope_namex == name then (Node name vars (symtable_remove_scope scope_namexs children))
  else error_msg "dame" []

----------------- Semantic -----------------

get_value_from_exp :: [Token] -> MyState -> Token
get_value_from_exp expression [(vars, sk, ts, sp, pc, sn)] = IntLiteral 0

-- wrapper for type_check'
-- pos -> State -> type checking function -> type or identifier token -> type or identifier token -> ...
type_check :: SourcePos -> MyState -> (String -> SourcePos -> MyType -> MyType -> Bool) -> Token -> Token -> ParsecT [InfoAndToken] MyState IO ()
type_check pos state check var_name _type = type_check' "" pos state check var_name _type

-- wrapper for type_check'
type_check_with_msg :: String -> SourcePos -> MyState -> (String -> SourcePos -> MyType -> MyType -> Bool) -> Token -> Token -> ParsecT [InfoAndToken] MyState IO ()
type_check_with_msg extra_msg pos state check var_name _type = type_check' extra_msg pos state check var_name _type

type_check' :: String -> SourcePos -> MyState -> (String -> SourcePos -> MyType -> MyType -> Bool) -> Token -> Token -> ParsecT [InfoAndToken] MyState IO ()
-- TODO: _type (Id var_name) case 
-- TODO: (Id var_name) (Id var_name) case 
type_check' extra_msg pos state check (Id var_name) _type = do
  case lookup_var var_name state of
    (_, _, ErrorToken, _) -> error_msg "Variable '%' not declared! Line: % Column: %" [var_name, showLine pos, showColumn pos]
    (_, var_type, _, _) -> if check extra_msg pos var_type _type then return () else error ""
type_check' extra_msg pos state check type1 type2 = if check extra_msg pos type1 type2 then return () else error ""

check_eq :: String -> SourcePos -> MyType -> MyType -> Bool
check_eq extra_msg pos t1 t2 = if t1 == t2 then True
else error_msg "% Types '%' and '%' do not match! Line: % Column: %" [extra_msg, show t1, show t2, showLine pos, showColumn pos]

check_arithm :: String -> SourcePos -> MyType -> MyType -> Bool
check_arithm extra_msg pos t1 t2 = if (check_eq extra_msg pos t1 t2) && (isArithm t1) && (isArithm t2) then True
else error_msg "% Types '%' and/or '%' are not arithmetic! Line: % Column: %" [extra_msg, show t1, show t2, showLine pos, showColumn pos]

check_integral :: String -> SourcePos -> MyType -> MyType -> Bool
check_integral extra_msg pos t1 t2 = if (check_eq extra_msg pos t1 t2) && (isIntegral t2) then True
else error_msg "Types '%' and/or '%' are not integral! Line: % Column: %" [extra_msg, show t1, show t2, showLine pos, showColumn pos]

check_bool :: String -> SourcePos -> MyType -> MyType -> Bool
check_bool extra_msg pos t1 t2 = if (check_eq extra_msg pos t1 t2) && (t2 == TBool) then True
else error_msg "Types '%' and/or '%' are not boolean! Line: % Column: %" [extra_msg, show t1, show t2, showLine pos, showColumn pos]

-- TODO: support type equivalence!?
isArithm :: MyType -> Bool
isArithm Nat = True
isArithm Int = True
isArithm Float = True
isArithm _ = False 

-- TODO: support type equivalence!?
isIntegral :: MyType -> Bool
isIntegral Nat = True
isIntegral Int = True
isIntegral _ = False

get_default_value :: Token -> Token
get_default_value Nat = NatLiteral 0
get_default_value Int = IntLiteral 0
get_default_value String = StringLiteral ""
get_default_value TChar = CharLiteral '\a'
get_default_value Float = FloatLiteral 0.0
get_default_value TBool = BoolLiteral False
get_default_value Unit = UnitLiteral ()

doOpOnTokens :: Token -> Token -> Token -> Token
doOpOnTokens (NatLiteral x) (NatLiteral y) op
  | isOrd op = BoolLiteral (doOpOrd x y op)
  | otherwise = NatLiteral (doOpIntegral x y op)
--
doOpOnTokens (IntLiteral x) (IntLiteral y) op
  | isOrd op = BoolLiteral (doOpOrd x y op)
  | otherwise = IntLiteral (doOpIntegral x y op)
--
doOpOnTokens (FloatLiteral x) (FloatLiteral y) op 
  | isOrd op = BoolLiteral (doOpOrd x y op)
  | otherwise = FloatLiteral (doOpFloating x y op)
--
doOpOnTokens (BoolLiteral x) (BoolLiteral y) op 
  | isEq op = BoolLiteral (doOpEq x y op)
  | otherwise = BoolLiteral (doOpBoolean x y op)
--
doOpOnTokens (StringLiteral x) (StringLiteral y) op = BoolLiteral (doOpEq x y op)
-- ...

doOpOnToken :: Token -> Token -> Token
doOpOnToken (NatLiteral x) op = NatLiteral (doUnaryOpIntegral x op)
doOpOnToken (IntLiteral x) op = IntLiteral (doUnaryOpIntegral x op)
doOpOnToken (FloatLiteral x) op = FloatLiteral (doUnaryOpFloating x op)
doOpOnToken (BoolLiteral x) op = BoolLiteral (doUnaryOpBoolean x op)

isEq :: Token -> Bool
isEq Comp = True
isEq Different = True
isEq _ = False

isOrd :: Token -> Bool
isOrd Leq = True
isOrd Geq = True
isOrd Smaller = True
isOrd Greater = True
isOrd op = isEq op

doOpEq :: Eq a => a -> a -> Token -> Bool
doOpEq x y Comp = x == y
doOpEq x y Different = x /= y

doOpOrd :: Ord a => a -> a -> Token -> Bool
doOpOrd x y Leq = x <= y
doOpOrd x y Geq = x >= y
doOpOrd x y Smaller = x < y
doOpOrd x y Greater = x > y
doOpOrd x y op = doOpEq x y op

doOpIntegral :: Integral a => a -> a -> Token -> a
doOpIntegral x y Sum = x + y
doOpIntegral x y Minus = x - y
doOpIntegral x y Mult = x * y
doOpIntegral x y Pow = x ^ y
doOpIntegral _ _ Div = error_msg "'/' operator not allowed for integral types" []

doOpFloating :: Floating a => a -> a -> Token -> a
doOpFloating x y Sum = x + y
doOpFloating x y Minus = x - y
doOpFloating x y Mult = x * y
doOpFloating x y Div = x / y
doOpFloating x y Pow = x ** y

doOpBoolean :: Bool -> Bool -> Token -> Bool
doOpBoolean x y And = x && y
doOpBoolean x y Or = x || y

doUnaryOpIntegral :: Integral a => a -> Token -> a
doUnaryOpIntegral x Minus = -x

doUnaryOpFloating :: Floating a => a -> Token -> a
doUnaryOpFloating x Minus = -x

doUnaryOpBoolean :: Bool -> Token -> Bool
doUnaryOpBoolean x Not = not x

----------------- Others -----------------

print_state :: ParsecT [InfoAndToken] MyState IO ()
print_state = do
              s <- getState
              liftIO (print s)

var_error = ("", ErrorToken, ErrorToken, [])

error_msg :: String -> [String] -> a
error_msg msg args = error ("\n##### ERROR ######\n\n" ++ (replace '%' args msg) ++ "\n\n##########")

replace :: Char -> [String] -> String -> String
replace _ [] msg = msg
replace _ _ [] = []
replace c (x:xs) (msgx:msgxs) = if c == msgx then (x ++ (replace c xs msgxs))
                                else (msgx:replace c (x:xs) msgxs)


showLine = show . sourceLine
showColumn = show . sourceColumn