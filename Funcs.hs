module Funcs where

import Lexer
import Text.Parsec
import Text.Read (readMaybe)
import Control.Monad.IO.Class
import TokenParser
import System.Environment
import Data.Char(digitToInt, isNumber, toLower, intToDigit)

---------------------------------------------------
----------------- Types
---------------------------------------------------

type MyState = [(Variables, Stack, [TypeInfo], Subprograms, PC, ScopeName, Bool)] -- (..., PC, Scope name, isRunning)
--
type Variables = ScopeTree -- (Scope name, Variables)
type Stack = [(Name, [(Token, Value)], Value)]
type TypeInfo = (Name, [Name], [TForm]) -- Name, Params, Forms
type Subprograms = [(Name, MyType, [Var], Int)] -- (Name, return _type, arguments, start line)
type PC = Int
type ScopeName = [String]
--
data ScopeTree =
  Node Name [Var] ScopeTree -- Name  [Var]  Children
  | NoChildren
  deriving (Eq,Show) 
type Name = String
type Var = (Name, MyType, Value, FunctionBody)
type FunctionBody = [InfoAndToken]
type Value = Token
type MyType = Token
data TForm = TForm (Token, [MyType]) deriving(Eq, Show)

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

add_call_to_stack :: Name -> [(Token, Value)] -> MyState -> MyState
add_call_to_stack func_name ref_params [(vars, sk, ts, sp, pc, sn, flag)] =
   [(vars, (func_name, ref_params, UnitLiteral ()):sk, ts, sp, pc, sn, flag)]

-- wrapper for symtable_insert_type'
symtable_insert_type :: Name -> [Name] -> MyState -> MyState
symtable_insert_type type_name type_params [(vars, sk, ts, sp, pc, sn, flag)] = 
  [(vars, sk, symtable_insert_type' ts type_name type_params, sp, pc, sn, flag)]

symtable_insert_type' :: [TypeInfo] -> Name -> [Name] -> [TypeInfo]
symtable_insert_type' [] type_name type_params = [(type_name, type_params, [])]
symtable_insert_type' (x:xs) type_name type_params = do
  let (namex, _, _) = x
  if namex == type_name then error_msg "Type '%' already declared!" [type_name]
  else (x:symtable_insert_type' xs type_name type_params)

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

check_var_is_struct :: SourcePos -> Name -> MyState -> ParsecT [InfoAndToken] MyState IO ()
check_var_is_struct pos var_name s = do
  case lookup_var pos var_name s of
    (_, _, StructLiteral _, _) -> return ()
    (name, _, _, _) -> error_msg "Variable '%' is not a struct! Line: % Column: %" [name, showLine pos, showColumn pos]

-- wrapper for lookup_type'
lookup_type :: MyState -> Name -> TypeInfo
lookup_type [(vars, sk, ts, sp, pc, scope_name, flag)] type_name = lookup_type' ts type_name

lookup_type' :: [TypeInfo] -> Name -> TypeInfo
lookup_type' [] _ = ("", [], [])
lookup_type' (x:xs) type_name = do
  let (namex, _, _) = x
  if namex == type_name then x else lookup_type' xs type_name

-- wrapper for lookup_type_constructor'
lookup_type_constructor :: MyState -> Name -> (Name, [Name], [MyType])
lookup_type_constructor [(vars, sk, ts, sp, pc, scope_name, flag)] cons_name = lookup_type_constructor' ts cons_name

lookup_type_constructor' :: [TypeInfo] -> Name -> (Name, [Name], [MyType])
lookup_type_constructor' [] _ = ("", [], [])
lookup_type_constructor' (x:xs) cons_name = do
  let (namex, paramsx, formsx) = x
  case cons_name `is_form_of` formsx of
    ("", _) -> lookup_type_constructor' xs cons_name
    (_, args) -> (namex, paramsx, args)

is_form_of :: Name -> [TForm] -> (Name, [MyType])
is_form_of _ [] = ("", [])
is_form_of cons_name (x:xs) = do
  let (TForm (Id form_name, args)) = x
  if form_name == cons_name then (form_name, args) else cons_name `is_form_of` xs

check_types_are_declared :: SourcePos -> MyState -> [Name] -> ParsecT [InfoAndToken] MyState IO ()
check_types_are_declared _ _ [] = return ()
check_types_are_declared pos s (x:xs) = 
  case lookup_type s x of
    ("", _, _) -> error_msg "Type '%' is not declared! Line: % Column: %" [x, showLine pos, showColumn pos]
    _ -> check_types_are_declared pos s xs

get_pass_by_value_result_variables :: MyState -> ([Token], [Value])
get_pass_by_value_result_variables [(vars, [], ts, sp, pc, scope_name, flag)] = 
  error_msg "Failed to retrieve stack variables, it is empty ! Erro #15" []
get_pass_by_value_result_variables [(vars, x:xs, ts, sp, pc, scope_name, flag)] = do
  let (_, vars_and_values, _) = x
  unzip vars_and_values

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
is_body func = case (head func) of
                      (_, NoneToken) -> False
                      _ -> True
-- (variable name, type, value, funcbody) -> ...
update_in_variables :: (Name, MyType, Value, FunctionBody) -> [Var] -> [Var]
update_in_variables _ [] = []
update_in_variables (name, _type, value, funcb) (varx:varxs) =
  let (namex, typex, valuex, funcbx) = varx in
  if name == namex
  then ((namex, update_attr _type typex, update_attr value valuex, if is_body funcb then funcb else funcbx):varxs)
  else case update_in_variables (name, _type, value, funcb) varxs of
    [] -> []
    varxs_new -> (varx : varxs_new)

symtable_update_variable_type :: (Token, MyType) -> MyState -> MyState
symtable_update_variable_type (Id var_name, _type) [(vars, sk, ts, sp, pc, scope_name, flag)] = do
  [(symtable_update_variable' scope_name (var_name, _type, NoneToken, noFuncBody) vars, sk, ts, sp, pc, scope_name, flag)]

update_struct :: SourcePos -> [Token] -> (MyType, Value) -> MyState -> MyState
update_struct pos [] _ _ = error_msg "Failure updating struct! Line: % Column: %" [showLine pos, showColumn pos]
update_struct pos (father_struct:access_chain) var_info s = do
  let (Id father_struct_name) = father_struct
  let filtered_access_chain = filter (\x -> x /= Period) access_chain
  --
  let (_, _, StructLiteral attrbs, _) = lookup_var pos father_struct_name s
  let new_struct_literal = struct_chain_traversal_and_update pos attrbs filtered_access_chain var_info
  --
  symtable_update_variable (Id father_struct_name, new_struct_literal, noFuncBody) s

struct_chain_traversal_and_update :: SourcePos -> [Var] -> [Token] -> (MyType, Value) -> Token
struct_chain_traversal_and_update pos _ [] _ = error_msg "Failure traversing struct chain Error #7 ! Line: % Column: %" [showLine pos, showColumn pos]
struct_chain_traversal_and_update pos [] _ _ = error_msg "Failure traversing struct chain Error #8 ! Line: % Column: %" [showLine pos, showColumn pos]
--
struct_chain_traversal_and_update pos attrbs [(Id t_name)] (var_type, var_value) =
  if var_is_attrb_of_struct attrbs t_name then do
    let new_var_value = (t_name, NoneToken, var_value, noFuncBody)
    -- TODO: type check this (var_type == t_name.type)
    StructLiteral (update_in_variables new_var_value attrbs)
  else error_msg "Failure traversing struct chain Error #9. Variable '%' is not an attribute! Line: % Column: %" [t_name, showLine pos, showColumn pos]
--
struct_chain_traversal_and_update pos attrbs ((Id t_name):ts) var_info =
  if var_is_attrb_of_struct attrbs t_name then do
    case get_var_info_from_scope t_name attrbs of
      (varx_name, _, StructLiteral attrbs', _) -> do
        let new_var_value = (varx_name, NoneToken, struct_chain_traversal_and_update pos attrbs' ts var_info, noFuncBody)
        StructLiteral (update_in_variables new_var_value attrbs)
      (varx_name, _, _, _) -> error_msg "Variable '%' is not struct. Error #4" [varx_name]
  else error_msg "'%' is not an attribute of '%'. Error #3" [t_name, show ts]

var_is_attrb_of_struct :: [Var] -> Name -> Bool
var_is_attrb_of_struct [] _ = False
var_is_attrb_of_struct ((varx_name, _, _, _):varxs) name = if varx_name == name then True else var_is_attrb_of_struct varxs name

-- wrapper for symtable_update_type'
symtable_update_type :: Name -> [TForm] -> MyState -> MyState
symtable_update_type type_name forms [(vars, sk, ts, sp, pc, sn, flag)] = 
  [(vars, sk, symtable_update_type' ts type_name forms, sp, pc, sn, flag)] 
  
symtable_update_type' :: [TypeInfo] -> Name -> [TForm] -> [TypeInfo]
symtable_update_type' [] _ _ = error_msg "dame6" []
symtable_update_type' (x:xs) type_name forms = do
  let (namex, params, _) = x
  if (namex == type_name) then do
    ((type_name, params, forms):xs) -- TODO: check if names on forms are valid!
  else (x:symtable_update_type' xs type_name forms)

update_matrix_value :: SourcePos -> Value -> [Int] -> Value -> Value
update_matrix_value pos _ [] _ = error_msg "Index out of bounds! Error #12. Line: % Column: %" [showLine pos, showColumn pos]
update_matrix_value pos (MatrixLiteral t content) [c] new_value = (MatrixLiteral t (update_matrix_content pos content new_value c))
update_matrix_value pos (MatrixLiteral t content) (c:cs) new_value = do
  let (_, q) = get_ith_from_matrix pos (MatrixLiteral t content) c
  let k = (update_matrix_value pos q cs new_value)
  (MatrixLiteral t (update_matrix_content pos content k c))

update_matrix_content :: SourcePos -> [Value] -> Value -> Int -> [Value]
update_matrix_content pos [] _ _ = error_msg "Index out of bounds! Error #13. Line: % Column: %" [showLine pos, showColumn pos]
update_matrix_content pos (x:xs) new_value 0 = new_value:xs
update_matrix_content pos (x:xs) new_value n = x:(update_matrix_content pos xs new_value (n - 1))

assign_variables :: [Token] -> [Value] -> MyState -> MyState
assign_variables [] [] s = s
assign_variables (x:xs) (y:ys) s = assign_variables xs ys (symtable_update_variable (x, y, noFuncBody) s)

map_ref_values_to_stack :: MyState -> MyState
map_ref_values_to_stack [(vars, [], ts, sp, pc, scope_name, flag)] = 
  error_msg "Failed to retrieve stack variables, it is empty ! Erro #16" []
map_ref_values_to_stack [(vars, (x:xs), ts, sp, pc, scope_name, flag)] = do
  let (a, vars_and_values, b) = x
  let (vars', _) = unzip vars_and_values
  let lookup_var'' (Id name) = case lookup_var' name vars scope_name of
                                (_, _, ErrorToken, _) -> do
                                  error_msg "Variable '%' declared with '?' not found in '%'" [name, show scope_name]
                                (_, _, value, _) -> value
  let new_values = map lookup_var'' vars'
  let new_x = (a, zip vars' new_values, b)
  [(vars, (new_x:xs), ts, sp, pc, scope_name, flag)]

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

pop_stack :: MyState -> MyState
pop_stack [(vars, [], ts, sp, pc, scope_name, flag)] = error_msg "Failed to pop stack!" []
pop_stack [(vars, sk:sks, ts, sp, pc, scope_name, flag)] = [(vars, sks, ts, sp, pc, scope_name, flag)]

----------------- Semantic -----------------

get_flag :: MyState -> Bool
get_flag [(vars, sk, ts, sp, pc, sn, flag)] = flag

set_flag :: Bool -> MyState -> MyState
set_flag flag [(vars, sk, ts, sp, pc, sn, old_flag)] = [(vars, sk, ts, sp, pc, sn, flag)]

false_flag_if f = if f then set_flag False else (\s -> s)

getStateFlag :: ParsecT [InfoAndToken] MyState IO (Bool)
getStateFlag = do
    s <- getState
    return (get_flag s)

get_return_value :: SourcePos -> MyState -> Value
get_return_value pos [(_, stack, _, _, _, _, _)] = 
  case stack of
    [] -> error_msg "Trying to get return value but there isn't an instance in stack! Error #10. Line: % Column: %" [showLine pos, showColumn pos]
    ((_, _, value):xs) -> value

set_return_value :: SourcePos -> Value -> MyState -> MyState
set_return_value pos value [(vars, stack, ts, sp, pc, sn, flag)] = 
  case stack of
    [] -> error_msg "Trying to set return value but there isn't an instance in stack! Error #11. Line: % Column: %" [showLine pos, showColumn pos]
    ((name, ref_params, _):xs) -> [(vars, (name, ref_params, value):xs, ts, sp, pc, sn, flag)]

get_value_from_exp :: [Token] -> MyState -> Token
get_value_from_exp expression [(vars, sk, ts, sp, pc, sn, flag)] = IntLiteral 0

get_default_value :: SourcePos -> MyState -> Token -> Token
get_default_value _ _ Nat = NatLiteral 0
get_default_value _ _ Int = IntLiteral 0
get_default_value _ _ TString = StringLiteral ""
get_default_value _ _ TChar = CharLiteral '\a'
get_default_value _ _ Float = FloatLiteral 0.0
get_default_value _ _ TBool = BoolLiteral False
get_default_value _ _ Unit = UnitLiteral ()
get_default_value pos s (Matrix t dim) = MatrixLiteral t (initialize_matrix pos s t dim)
get_default_value pos s (Id name) = do
  case lookup_type s name of
    ("", _, _) -> do -- Case: Variable
      let (_, _, attrbs, _) = lookup_var pos name s
      attrbs
    (_, type_params, forms) -> get_default_value pos s (Type name (map (\s -> Id s) type_params)) -- Case: Type name
get_default_value pos s (Type type_name type_params) = 
  case lookup_type s type_name of
    ("", _, _) -> do
      error_msg "Type '%' not found in search for default type value! Line: % Column: %" [type_name, showLine pos, showColumn pos]
    (_, _, type_forms) -> do
      case get_first_non_recursive_form type_name type_forms of
        TForm (Id "", _) -> do
          let msg = "Type '%' does not have non-recursive type form, therefore it cannot be initialized with a default value!"
          let code_pos = " Line: % Column: %"
          error_msg (msg ++ code_pos) [type_name, showLine pos, showColumn pos]
        TForm (Id cons_name, cons_args) -> TypeLiteral cons_name (map (get_default_value pos s) cons_args) []

get_first_non_recursive_form :: Name -> [TForm] -> TForm
get_first_non_recursive_form _ [] = TForm (Id "", [])
get_first_non_recursive_form type_name (t:ts) = do
  let (TForm (Id cons_name, cons_args)) = t
  if (Id type_name) `is_in_list` cons_args
  then get_first_non_recursive_form type_name ts
  else t

initialize_matrix :: SourcePos -> MyState -> MyType -> [Int] -> [Token]
initialize_matrix _ _ _ [] = []
initialize_matrix pos s t [n] = list_of_n_mxlit n (get_default_value pos s t)
initialize_matrix pos s t (n:ns) = list_of_n_mxlit n (MatrixLiteral t (initialize_matrix pos s t ns))

list_of_n_mxlit :: Int -> Token -> [Token]
list_of_n_mxlit 0 tk = []
list_of_n_mxlit n tk = tk:(list_of_n_mxlit (n - 1) tk)


-- gets function code and returns: params, param types, function body
get_params :: [InfoAndToken] -> ([Name], [Name], [Token], [InfoAndToken])
get_params [] = ([], [], [], [])
get_params (((_, _), Comma):xs) = get_params xs
get_params (((_, _), EndOfParamsToken):xs) = ([], [], [], xs)
get_params (((_, _), id):((_, _), colon_or_question):((_, _), the_type):xs) = do
  let id_name = case id of
                  (Id name) -> name
                  x -> error_msg "Invalid Param '%' ! Error #1.2" [show x]
  let (params, ref_params, param_types, func_body) = get_params xs
  case colon_or_question of 
    Question -> (id_name:params, id_name:ref_params, the_type:param_types, func_body)
    Colon -> (id_name:params, ref_params, the_type:param_types, func_body)
    _ -> error_msg "Invalid params in function call! Error #2.1" []
get_params _ = error_msg "Invalid params in function call! Error #2.2" []

check_param_amount :: SourcePos -> [a] -> [b] -> ParsecT [InfoAndToken] MyState IO ()
check_param_amount pos a b = if (length a) == (length b)
  then return ()
  else error_msg "Wrong number of arguments in function call or type constructor! Line: % Column: %" [showLine pos, showColumn pos]

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
else error_msg "% Types '%' and/or '%' are not integral! Line: % Column: %" [extra_msg, show t1, show t2, showLine pos, showColumn pos]

check_bool :: String -> SourcePos -> MyType -> MyType -> Bool
check_bool extra_msg pos t1 t2 = if (check_eq extra_msg pos t1 t2) && (t2 == TBool) then True
else error_msg "% Types '%' and/or '%' are not boolean! Line: % Column: %" [extra_msg, show t1, show t2, showLine pos, showColumn pos]

check_correct_ref_values :: SourcePos -> [Name] -> [Name] -> [Token] -> ParsecT [InfoAndToken] MyState IO ()
check_correct_ref_values _ _ [] _ = return ()
check_correct_ref_values pos (x:xs) (y:ys) (z:zs) = do
  if x `is_in_list` (y:ys) then do
    case z of
      (Id _) -> check_correct_ref_values pos xs ys zs
      _ -> error_msg "Cannot use literals when passing by reference ! Line: % Column: %" [showLine pos, showColumn pos]
  else check_correct_ref_values pos xs (y:ys) zs

-- TODO: support type equivalence!?
isArithm :: MyType -> Bool
isArithm Nat = True
isArithm Int = True
isArithm Float = True
isArithm TString = True
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
doOpOnTokens (StringLiteral x) (StringLiteral y) op
  | op == Concat = StringLiteral (x ++ y)
  | isEq op = BoolLiteral (doOpEq x y op)
  | otherwise = error_msg "Operation '%' is not supported for string" [show op]
-- ...

doOpOnToken :: Token -> Token -> Token
doOpOnToken (NatLiteral x) op = NatLiteral (doUnaryOpIntegral x op)
doOpOnToken (IntLiteral x) op = IntLiteral (doUnaryOpIntegral x op)
doOpOnToken (FloatLiteral x) op = FloatLiteral (doUnaryOpFloating x op)
doOpOnToken (BoolLiteral x) op = BoolLiteral (doUnaryOpBoolean x op)

isEq :: Token -> Bool
isEq Equals = True
isEq Different = True
isEq _ = False

isOrd :: Token -> Bool
isOrd Leq = True
isOrd Geq = True
isOrd Smaller = True
isOrd Greater = True
isOrd op = isEq op

doOpEq :: Eq a => a -> a -> Token -> Bool
doOpEq x y Equals = x == y
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
doOpIntegral x y Modulo = x `mod` y
doOpIntegral _ _ Div = error_msg "'/' operator not allowed for integral types" []
doOpIntegral _ _ z = error_msg "Non-supported operator % for integrals" [show z]

doOpFloating :: Floating a => a -> a -> Token -> a
doOpFloating x y Sum = x + y
doOpFloating x y Minus = x - y
doOpFloating x y Mult = x * y
doOpFloating x y Div = x / y
doOpFloating x y Pow = x ** y
doOpFloating _ _ z = error_msg "Non-supported operator % for floats" [show z]

doOpBoolean :: Bool -> Bool -> Token -> Bool
doOpBoolean x y And = x && y
doOpBoolean x y Or = x || y
doOpBoolean _ _ z = error_msg "Non-supported operator % for booleans" [show z]

doUnaryOpIntegral :: Integral a => a -> Token -> a
doUnaryOpIntegral x Minus = -x

doUnaryOpFloating :: Floating a => a -> Token -> a
doUnaryOpFloating x Minus = -x

doUnaryOpBoolean :: Bool -> Token -> Bool
doUnaryOpBoolean x Not = not x

showLiteral :: Token -> String
showLiteral (Id x) = x
showLiteral (NatLiteral x) = show x
showLiteral (IntLiteral x) = show x
showLiteral (FloatLiteral x) = show x
showLiteral (BoolLiteral x) = show x
showLiteral (StringLiteral x) = show x
showLiteral (CharLiteral x) = show x
showLiteral (UnitLiteral x) = show x
showLiteral (TypeLiteral cons_name args params) = do
  let args_str = foldl (++) "" $ map (\s -> showLiteral s ++ ", ") args
  cons_name ++ "(" ++ args_str ++ ")"
showLiteral (MatrixLiteral t content) = show_matrix "" content
showLiteral NoneToken = "No Value"
showLiteral x = show x

show_matrix :: String -> [Token] -> String
show_matrix space [] = ""
show_matrix space (x:xs) =
  case x of
    (MatrixLiteral _ content) -> space ++ "\n" ++ (show_matrix (space ++ "-") content) ++ (show_matrix space xs)
    lit -> (show_matrix_literal (x:xs))

show_matrix_literal :: [Token] -> String
show_matrix_literal [] = "\n"
show_matrix_literal (x:xs) = (showLiteral x) ++ " " ++ (show_matrix_literal xs)

read_literal :: String -> Token
read_literal s
  | Just x <- readMaybe s :: Maybe Int = IntLiteral x
  | Just x <- readMaybe s :: Maybe Float = FloatLiteral x
  | Just x <- readMaybe s :: Maybe Bool = BoolLiteral x
  | Just x <- readMaybe s :: Maybe Char = CharLiteral x
  | Just x <- readMaybe s :: Maybe () = UnitLiteral x
  -- TODO: READ NAT
  | otherwise = StringLiteral s

to_int :: Token -> Token
to_int (NatLiteral x) = IntLiteral x
to_int (IntLiteral x) = IntLiteral x
to_int (FloatLiteral x) = IntLiteral (floor x)
to_int (BoolLiteral x) = if x then IntLiteral 1 else IntLiteral 0
to_int (CharLiteral x) = IntLiteral (digitToInt x)
to_int (UnitLiteral x) = IntLiteral 1
to_int (StringLiteral x) = do
  if foldl (&&) True (map isNumber x) then IntLiteral (read x) else error_msg "Cannot convert '%' to Int" [x]
to_int x = error_msg "Invalid conversion of '%' to Int" [show x]

to_float :: Token -> Token
to_float (NatLiteral x) = FloatLiteral (fromIntegral x)
to_float (IntLiteral x) = FloatLiteral (fromIntegral x)
to_float (FloatLiteral x) = FloatLiteral x
to_float (BoolLiteral x) = if x then FloatLiteral 1.0 else FloatLiteral 0.0
to_float (CharLiteral x) = FloatLiteral (fromIntegral $ digitToInt x)
to_float (UnitLiteral x) = FloatLiteral 1.0
to_float (StringLiteral x) = do
  if foldl (&&) True (map (\s -> isNumber s || s == '.') x)
    then FloatLiteral (read x)
    else error_msg "Cannot convert '%' to Float" [x]
to_float x = error_msg "Invalid conversion of '%' to Float" [show x]

to_string :: Token -> Token
to_string x = StringLiteral (showLiteral x)

to_bool :: Token -> Token
to_bool (NatLiteral x) = BoolLiteral (not $ x == 0)
to_bool (IntLiteral x) = BoolLiteral (not $ x == 0)
to_bool (FloatLiteral x) = BoolLiteral (not $ x == 0.0)
to_bool (BoolLiteral x) = BoolLiteral x
to_bool (CharLiteral x) = do 
  let lower_case_x = toLower x
  if (lower_case_x == 't') then BoolLiteral True else 
    if (lower_case_x == 'f') then BoolLiteral False else
      error_msg "Invalid conversion of '%' to Bool" [show x]
to_bool (UnitLiteral x) = BoolLiteral False
to_bool (StringLiteral x) = do
  if length x == 1 then
    to_bool $ CharLiteral (head x)
  else
    error_msg "Invalid conversion of '%' to Bool" [x]

to_char :: Token -> Token
to_char (NatLiteral x) = CharLiteral (intToDigit x)
to_char (IntLiteral x) = CharLiteral (intToDigit x)
to_char (FloatLiteral x) = CharLiteral (intToDigit $ floor x)
to_char (BoolLiteral x) = CharLiteral (if x then 'T' else 'F')
to_char (CharLiteral x) = CharLiteral x
to_char (StringLiteral x) = do
  if length x == 1 then CharLiteral (head x) else error_msg "Invalid conversion of '%' to Char" [x] 

get_literal :: MyType -> Value -> Token
--get_literal Nat v = to_nat v
get_literal Int v = to_int v
get_literal Float v = to_float v
get_literal TBool v = to_bool v
get_literal TChar v = to_char v
get_literal TString v = to_string v
get_literal Unit _ = UnitLiteral ()
--get_literal (Matrix t dim) _ = MatrixLiteral t (initialize_matrix t dim)

-- TODO: to_nat

is_type_name :: SourcePos -> MyState -> Value -> Bool
is_type_name _ _ Nat = True
is_type_name _ _ Int = True
is_type_name _ _ Float = True
is_type_name _ _ TBool = True
is_type_name _ _ TChar = True
is_type_name _ _ TString = True
is_type_name _ _ Unit = True
is_type_name _ _ (Matrix _ _) = True
is_type_name pos s (Id name) =
  case lookup_type s name of
    ("", _, _) -> error_msg "dame4" [] -- TODO: usar o pos
    _ -> True

-- cons args -> params -> params values -> arg types
get_cons_arg_types :: [MyType] -> [Name] -> [MyType] -> [MyType]
get_cons_arg_types [] [] [] = []
get_cons_arg_types [] _ _ = error_msg "Insufficient type parameters!" [] -- TODO: put pos
get_cons_arg_types (x:xs) (y:ys) (z:zs) = do
  case x of 
    (Id type_name) -> do
      if type_name `is_in_list` (y:ys)
      -- case: Type parameter
      then z : (get_cons_arg_types xs ys zs)
      -- case: User created type name
      else (Type type_name (map (\t -> Id t) (y:ys))) : (get_cons_arg_types xs (y:ys) (z:zs))
    -- case: Primitive type
    primitive -> primitive : (get_cons_arg_types xs (y:ys) (z:zs))

get_ith_from_matrix :: SourcePos -> Token -> Int -> (MyType, Token)
get_ith_from_matrix pos (MatrixLiteral _ []) _ = 
  error_msg "Index out of bounds! Line: % Column: %" [showLine pos, showColumn pos]
get_ith_from_matrix pos (MatrixLiteral t (x:_)) 0 = do
  case x of
    (MatrixLiteral t' tks) -> (Matrix t' (get_dim tks), x)
    _ -> (t, x)
get_ith_from_matrix pos (MatrixLiteral t (x:xs)) i = get_ith_from_matrix pos (MatrixLiteral t xs) (i - 1)
get_ith_from_matrix pos x _ = 
  error_msg "Invalid access using square brackets for '%'! Line: % Column: %" [showLiteral x, showLine pos, showColumn pos]

get_dim :: [Token] -> [Int]
get_dim [] = []
get_dim xs = do
  case (head xs) of
    (MatrixLiteral _ tks) -> (length xs):(get_dim tks)
    _ -> [length xs]

get_ref_args :: Eq b => [a] -> [b] -> [b] -> [a]
get_ref_args _ _ [] = []
get_ref_args (x:xs) (y:ys) (z:zs) = do
  if y `is_in_list` (z:zs) then x:(get_ref_args xs ys zs) else (get_ref_args xs ys zs)

-- TODO: adapt for when function call is present
get_arg_names :: [Token] -> [Token]
get_arg_names [] = []
get_arg_names xs = get_arg_names' 0 xs

get_arg_names' :: Int -> [Token] -> [Token]
get_arg_names' _ [] = []
get_arg_names' 0 (x:xs) = do
  case x of
    Comma -> get_arg_names xs
    OpenParentheses -> get_arg_names' 1 xs
    value -> x:(get_arg_names xs)
get_arg_names' n (x:xs) = do
  case x of
    Comma -> get_arg_names' n xs
    OpenParentheses -> get_arg_names' (n + 1) xs
    CloseParentheses -> get_arg_names' (n - 1) xs
    value -> get_arg_names' n xs

condense_extensive_types :: [InfoAndToken] -> [InfoAndToken]
condense_extensive_types [] = []
condense_extensive_types (a:b:c:d:xs) = do
  case map snd [a, b, c, d] of
    [(Matrix Unit []), Smaller, x, Greater] -> do
      (fst a, Matrix x (get_dimensions_from_tokens $ map snd xs)):(condense_extensive_types' xs)
    [a', b', c', d'] -> a:(condense_extensive_types (b:c:d:xs))
condense_extensive_types (x:xs) = x:xs

condense_extensive_types' :: [InfoAndToken] -> [InfoAndToken]
condense_extensive_types' (((_, _), OpenParentheses):xs) = condense_extensive_types' xs
condense_extensive_types' (((_, _), CloseParentheses):xs) = condense_extensive_types xs
condense_extensive_types' (((_, _), _):xs) = condense_extensive_types' xs

get_dimensions_from_tokens :: [Token] -> [Int]
get_dimensions_from_tokens [] = []
get_dimensions_from_tokens (OpenParentheses:xs) = get_dimensions_from_tokens xs
get_dimensions_from_tokens (CloseParentheses:xs) = []
get_dimensions_from_tokens (Comma:xs) = get_dimensions_from_tokens xs
get_dimensions_from_tokens ((IntLiteral x):xs) = x:(get_dimensions_from_tokens xs)

----------------- Others -----------------

dontChangeFunctionBody = [((0, 0), NoneToken)] :: [(InfoAndToken)]
noFuncBody = [((0, 0), NoneToken)] :: [(InfoAndToken)]
dontChangeValue = NoneToken

print_state :: ParsecT [InfoAndToken] MyState IO ()
print_state = do
              s <- getState
              liftIO (putStrLn $ "The State: " ++ (show s) ++ ". ")

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

is_in_list x list_ = case list_ of
                      [] -> False
                      (e:ls) -> x == e || is_in_list x ls


get_matrix_int_values pos x = do
    let x_value = (\(IntLiteral x) -> x) x
    if x_value < 0 
      then error_msg "Only positive values allowed at matrix dimensions! Line: % Column: %" [showLine pos, showColumn pos] 
    else x_value