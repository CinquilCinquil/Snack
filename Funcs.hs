module Funcs where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class
import TokenParser
import System.Environment

---------------------------------------------------
----------------- Types
---------------------------------------------------

type MyState = [(Variables, Stack, Types, Subprograms, PC, ScopeName, Bool)] -- (..., PC, Scope name, isRunning)
--
type Variables = ScopeTree -- (Scope name, Variables)
type Stack = [(Name, PC, Value)]
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
symtable_insert_variable var [(vars, sk, ts, sp, pc, scope_name, flag)] = [(append_to_scope scope_name var vars, sk, ts, sp, pc, scope_name, flag)]

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
add_current_scope_name name [(vars, sk, ts, sp, pc, scope_name, flag)] =
  case append_scope vars scope_name name of
    NoChildren -> error_msg "Failed adding to scope" []
    new_vars -> [(new_vars, sk, ts, sp, pc, scope_name ++ [name], flag)]

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

load_params :: [Name] -> [MyType] -> [Value] -> [FunctionBody] -> MyState -> MyState
load_params [] [] [] [] s = s
load_params (x:xs) (y:ys) (z:zs) (w:ws) s = load_params xs ys zs ws (symtable_insert_variable (Id x, y, z, w) s)

add_call_to_stack :: Name -> MyState -> MyState
add_call_to_stack func_name [(vars, sk, ts, sp, pc, sn, flag)] = [(vars, (func_name, 0, StringLiteral "c"):sk, ts, sp, pc, sn, flag)]

----------------- Search -----------------

-- wrapper for lookup_var'
lookup_var :: SourcePos -> Name -> MyState -> Var
lookup_var pos var_name [(vars, sk, ts, sp, pc, scope_name, flag)] = 
  case lookup_var' var_name vars scope_name of
    (_, _, ErrorToken, _) -> error_msg "Variable '%' not declared! Line: % Column: %. Error #0" [var_name, showLine pos, showColumn pos]
    var -> var

-- searches tree bottom-up
lookup_var' :: Name -> Variables -> ScopeName -> Var
lookup_var' var_name vars [] = var_error
lookup_var' var_name vars scope_name =
  case search_scope_tree scope_name vars of
    NoChildren -> var_error
    (Node node_name node_vars _) ->
      case get_var_info_from_scope var_name node_vars of
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

get_var_info_from_scope :: Name -> [Var] -> Var
get_var_info_from_scope var_name [] = var_error
get_var_info_from_scope var_name (varx:varxs) = let (namex, typex, valuex, funcbx) = varx in
  if var_name == namex then (namex, typex, valuex, funcbx) else get_var_info_from_scope var_name varxs

get_current_scope_name :: MyState -> ScopeName
get_current_scope_name [(vars, sk, ts, sp, pc, scope_name, flag)] = scope_name

get_current_scope :: MyState -> [Var]
get_current_scope [(Node _ vars _, sk, ts, sp, pc, scope_name, flag)] = vars

get_current_scope_tree :: MyState -> Variables
get_current_scope_tree [(vars, sk, ts, sp, pc, scope_name, flag)] = vars

check_var_is_declared :: SourcePos -> Name -> MyState -> ParsecT [InfoAndToken] MyState IO ()
check_var_is_declared pos var_name s = do
  let x = lookup_var pos var_name s -- WARNING: might be ignored due to lazy-eval
  return ()

----------------- Update -------------------

-- wrapper for symtable_update_variable'
symtable_update_variable :: (Token, Value, FunctionBody) -> MyState -> MyState
symtable_update_variable (Id var_name, value, funcb) [(vars, sk, ts, sp, pc, scope_name, flag)] = do
  [(symtable_update_variable' scope_name (var_name, NoneToken, value, funcb) vars, sk, ts, sp, pc, scope_name, flag)]

-- updates tree bottom-up
symtable_update_variable' :: ScopeName -> (Name, MyType, Value, FunctionBody) -> Variables -> Variables
symtable_update_variable' _ (name, _, _, _) NoChildren = error_msg "Variable '%' not found" [name]
symtable_update_variable' [] (name, _, _, _) _ = error_msg "Variable '%' not found" [name]
symtable_update_variable' scope_name var vars =
  case update_scope_tree scope_name vars var of
    NoChildren -> symtable_update_variable' (reverse $ tail $ reverse scope_name) var vars -- search in current scope failed, go one up
    new_vars -> new_vars -- search successful

-- updates a certain node of the tree
update_scope_tree :: ScopeName -> Variables -> (Name, MyType, Value, FunctionBody) -> ScopeTree
update_scope_tree [] _ _ = NoChildren -- not found
update_scope_tree _ NoChildren _ = NoChildren -- not found
update_scope_tree (scope_namex:scope_namexs) (Node name vars children) var = 
  if scope_namex == name then -- up until now search is successful
    if scope_namexs == [] then do
      case update_in_variables var vars of
        [] -> NoChildren -- not found
        new_vars -> (Node name new_vars children)  -- search is successful
    else case update_scope_tree scope_namexs children var of
      NoChildren -> NoChildren -- not found
      new_children -> (Node name vars new_children)  -- search is successful
  else NoChildren -- not found

update_attr new prev = if new /= NoneToken then new else prev
-- (variable name, type, value, funcbody) -> ...
update_in_variables :: (Name, MyType, Value, FunctionBody) -> [Var] -> [Var]
update_in_variables _ [] = []
update_in_variables (name, _type, value, funcb) (varx:varxs) =
  let (namex, typex, valuex, funcbx) = varx in
  if name == namex
  then ((namex, update_attr _type typex, update_attr value valuex, if (head funcb) /= NoneToken then funcb else funcbx):varxs)
  else case update_in_variables (name, _type, value, funcb) varxs of
    [] -> []
    varxs_new -> (varx : varxs_new)

symtable_update_variable_type :: (Token, MyType) -> MyState -> MyState
symtable_update_variable_type (Id var_name, _type) [(vars, sk, ts, sp, pc, scope_name, flag)] = do
  [(symtable_update_variable' scope_name (var_name, _type, NoneToken, [NoneToken]) vars, sk, ts, sp, pc, scope_name, flag)]

update_struct :: SourcePos -> [Token] -> (MyType, Value) -> MyState -> MyState
update_struct pos [] _ _ = error_msg "Failure updating struct! Line: % Column: %" [showLine pos, showColumn pos]
update_struct pos (father_struct:access_chain) var_info s = do
  let (Id father_struct_name) = father_struct
  let filtered_access_chain = filter (\x -> x /= Period) access_chain
  --
  let (_, _, StructLiteral attrbs, _) = lookup_var pos father_struct_name s
  let new_struct_literal = struct_chain_traversal_and_update pos attrbs filtered_access_chain var_info
  --
  symtable_update_variable (Id father_struct_name, new_struct_literal, [NoneToken]) s

struct_chain_traversal_and_update :: SourcePos -> [Var] -> [Token] -> (MyType, Value) -> Token
struct_chain_traversal_and_update pos _ [] _ = error_msg "Failure traversing struct chain Error #7 ! Line: % Column: %" [showLine pos, showColumn pos]
struct_chain_traversal_and_update pos [] _ _ = error_msg "Failure traversing struct chain Error #8 ! Line: % Column: %" [showLine pos, showColumn pos]
--
struct_chain_traversal_and_update pos attrbs [(Id t_name)] (var_type, var_value) =
  if var_is_attrb_of_struct attrbs t_name then do
    let new_var_value = (t_name, NoneToken, var_value, [NoneToken])
    -- TODO: type check this (var_type == t_name.type)
    StructLiteral (update_in_variables new_var_value attrbs)
  else error_msg "Failure traversing struct chain Error #9. Variable '%' is not an attribute! Line: % Column: %" [t_name, showLine pos, showColumn pos]
--
struct_chain_traversal_and_update pos attrbs ((Id t_name):ts) var_info =
  if var_is_attrb_of_struct attrbs t_name then do
    case get_var_info_from_scope t_name attrbs of
      (varx_name, _, StructLiteral attrbs', _) -> do
        let new_var_value = (varx_name, NoneToken, struct_chain_traversal_and_update pos attrbs' ts var_info, [NoneToken])
        StructLiteral (update_in_variables new_var_value attrbs)
      (varx_name, _, _, _) -> error_msg "Variable '%' is not struct. Error #4" [varx_name]
  else error_msg "'%' is not an attribute of '%'. Error #3" [t_name, show ts]

var_is_attrb_of_struct :: [Var] -> Name -> Bool
var_is_attrb_of_struct [] _ = False
var_is_attrb_of_struct ((varx_name, _, _, _):varxs) name = if varx_name == name then True else var_is_attrb_of_struct varxs name

----------------- Remove -------------------

remove_current_scope_name :: MyState -> MyState
remove_current_scope_name [(vars, sk, ts, sp, pc, scope_name, flag)] = 
  [(symtable_remove_scope scope_name vars, sk, ts, sp, pc, reverse $ tail $ reverse scope_name, flag)]

symtable_remove_scope :: ScopeName -> Variables -> Variables
symtable_remove_scope scope_name NoChildren = error_msg "Failure in leaving scope '%'" [show scope_name]
symtable_remove_scope [] _ = error_msg "Failure in leaving scope" []
symtable_remove_scope (scope_namex:[]) (Node name vars children) = 
  if scope_namex == name then NoChildren 
  else error_msg "Failure in leaving scope '%'" [scope_namex]
symtable_remove_scope (scope_namex:scope_namexs) (Node name vars children) = 
  if scope_namex == name then (Node name vars (symtable_remove_scope scope_namexs children))
  else error_msg "Failure in leaving scope '%'" [scope_namex]

----------------- Semantic -----------------

get_flag :: MyState -> Bool
get_flag [(vars, sk, ts, sp, pc, sn, flag)] = flag

set_flag :: Bool -> MyState -> MyState
set_flag flag [(vars, sk, ts, sp, pc, sn, old_flag)] = [(vars, sk, ts, sp, pc, sn, flag)]

get_return_value :: SourcePos -> MyState -> Value
get_return_value pos [(_, stack, _, _, _, _, _)] = 
  case stack of
    [] -> error_msg "Trying to get return value but there isn't an instance in stack! Error #10. Line: % Column: %" [showLine pos, showColumn pos]
    ((_, _, value):xs) -> value

set_return_value :: SourcePos -> Value -> MyState -> MyState
set_return_value pos value [(vars, stack, ts, sp, pc, sn, flag)] = 
  case stack of
    [] -> error_msg "Trying to set return value but there isn't an instance in stack! Error #11. Line: % Column: %" [showLine pos, showColumn pos]
    ((name, pc, _):xs) -> [(vars, (name, pc, value):xs, ts, sp, pc, sn, flag)]

get_value_from_exp :: [Token] -> MyState -> Token
get_value_from_exp expression [(vars, sk, ts, sp, pc, sn, flag)] = IntLiteral 0

get_default_value :: SourcePos -> MyState -> Token -> Token
get_default_value _ _ Nat = NatLiteral 0
get_default_value _ _ Int = IntLiteral 0
get_default_value _ _ String = StringLiteral ""
get_default_value _ _ TChar = CharLiteral '\a'
get_default_value _ _ Float = FloatLiteral 0.0
get_default_value _ _ TBool = BoolLiteral False
get_default_value _ _ Unit = UnitLiteral ()
get_default_value pos s (Id name) = do
  let (_, _, attrbs, _) = lookup_var pos name s
  attrbs
--get_default_value pos s (Type _) = ...

-- gets function code and returns: params, param types, function body
get_params :: [Token] -> ([Name], [Token], [Token])
get_params [] = ([], [], [])
get_params (Comma:xs) = get_params xs
get_params (EndOfParamsToken:xs) = ([], [], xs)
get_params (id:Colon:the_type:xs) = do
  let id_name = case id of
                  (Id name) -> name
                  x -> error_msg "Invalid Param '%' ! Error #1" [show x]
  let (params, param_types, func_body) = get_params xs
  (id_name:params, the_type:param_types, func_body)
get_params _ = error_msg "Invalid params in function call! Error #2" []

check_param_amount :: SourcePos -> [a] -> [b] -> ParsecT [InfoAndToken] MyState IO ()
check_param_amount pos a b = if (length a) == (length b)
  then return ()
  else error_msg "Wrong number of arguments in function call! Line: % Column: %" [showLine pos, showColumn pos]

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
    let (_, var_type, _, _) = lookup_var pos var_name state
    if check extra_msg pos var_type _type then return () else error ""
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

showLiteral :: Token -> String
showLiteral (NatLiteral x) = show x
showLiteral (IntLiteral x) = show x
showLiteral (FloatLiteral x) = show x
showLiteral (BoolLiteral x) = show x
showLiteral (StringLiteral x) = show x
showLiteral (CharLiteral x) = show x
showLiteral (UnitLiteral x) = show x
showLiteral NoneToken = "No Value"
showLiteral x = show x


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

check_types :: (Token -> Token -> ParsecT [InfoAndToken] MyState IO ()) -> [Token] -> [Token] -> ParsecT [InfoAndToken] MyState IO ()
check_types _ [] [] = return ()
check_types f (x:xs) (y:ys) = do
  f x y
  check_types f xs ys

to_infoAndToken :: [Token] -> [InfoAndToken]
to_infoAndToken xs = map (\s -> ((0, 0), s)) xs