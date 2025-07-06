{
module Lexer (Token(..), InfoAndToken(..), AlexPosn(..), alexScanTokens, getTokens) where
import System.IO
}

%wrapper "posn"

$D = [0-9]
$L = [a-zA-Z]

-- Alex returns in each right-hand side: AlexPosn -> String
tokens :-

  $white+                               ;
  "--".*.                               ;
  -- Punctuations / Parantheses
  ","                                   { \p _ -> (getLC p, Comma)}
  :                                     { \p _ -> (getLC p, Colon)}
  ";"                                   { \p _ -> (getLC p, SemiColon)}
  "."                                   { \p _ -> (getLC p, Period)}
  "("                                   { \p _ -> (getLC p, OpenParentheses)}
  ")"                                   { \p _ -> (getLC p, CloseParentheses)}
  "["                                   { \p _ -> (getLC p, OpenSquareBrackets)}
  "]"                                   { \p _ -> (getLC p, CloseSquareBrackets)}
  "{"                                   { \p _ -> (getLC p, OpenBrackets)}
  "}"                                   { \p _ -> (getLC p, CloseBrackets)}
  "..."                                 { \p _ -> (getLC p, Ellipsis)}
  ".."                                  { \p _ -> (getLC p, TwoDots)}
  -- Structures
  if                                    { \p _ -> (getLC p, If) }
  then                                  { \p _ -> (getLC p, Then) }
  else                                  { \p _ -> (getLC p, Else) }
  for                                   { \p _ -> (getLC p, For) }
  do                                    { \p _ -> (getLC p, Do) }
  in                                    { \p _ -> (getLC p, In) }
  while                                 { \p _ -> (getLC p, While) }
  switch                                { \p _ -> (getLC p, Switch) }
  case                                  { \p _ -> (getLC p, Case) }
  repeat                                { \p _ -> (getLC p, Repeat) }
  match                                 { \p _ -> (getLC p, Match) }
  with                                  { \p _ -> (getLC p, With) }
  form                                  { \p _ -> (getLC p, Form) }
  -- Operations / Relations
  ":="                                  { \p _ -> (getLC p, Assign) }
  "=="                                  { \p _ -> (getLC p, Comp) }
  "="                                   { \p _ -> (getLC p, Equals) }
  "<="                                  { \p _ -> (getLC p, Leq) }
  ">="                                  { \p _ -> (getLC p, Geq) }
  ">"                                   { \p _ -> (getLC p, Greater) }
  "<"                                   { \p _ -> (getLC p, Smaller) }
  "not"                                 { \p _ -> (getLC p, Not) }
  "and"                                 { \p _ -> (getLC p, And)}
  "or"                                  { \p _ -> (getLC p, Or)}
  "=/="                                 { \p _ -> (getLC p, Different)}
  "+"                                   { \p _ -> (getLC p, Sum) }
  "-"                                   { \p _ -> (getLC p, Minus) }
  "/"                                   { \p _ -> (getLC p, Div) }
  "*"                                   { \p _ -> (getLC p, Mult) }
  "^"                                   { \p _ -> (getLC p, Pow) }
  -- Declarations
  fun                                   { \p _ -> (getLC p, Fun) }
  vars                                  { \p _ -> (getLC p, Vars) }
  -- Types
  type                                  { \p s -> (getLC p, Type s) }
  nat                                   { \p _ -> (getLC p, Nat) }
  int                                   { \p _ -> (getLC p, Int) }
  string                                { \p _ -> (getLC p, String) }
  float                                 { \p _ -> (getLC p, Float) }
  bool                                  { \p _ -> (getLC p, TBool) }
  unit                                  { \p _ -> (getLC p, Unit) }
  -- Literals
  O	                                    { \p s -> (getLC p, NatLiteral 0) }
  S$D+	                                { \p s -> (getLC p, NatLiteral $ 1 + (read (tail s))) }
  $D+	                                  { \p s -> (getLC p, IntLiteral (read s)) }
  ($D+"."$D+)(e[\+\-]$D$D)?	            { \p s -> (getLC p, FloatLiteral (read s)) }
  \"([^\"\\]|\\.)*\"                    { \p s -> (getLC p, StringLiteral $ read s) }
  \'.+\'                                { \p s -> (getLC p, CharLiteral (read s)) }
  "true"|"false"                        { \p s -> (getLC p, BoolLiteral (s == "true")) }
  
  -- missing other primary types such as unit, empty, matrix...

  -- Others
  $L[$L $D \_ \']*	                    { \p s -> (getLC p, Id s) }
  import                                { \p _ -> (getLC p, Import) }
  types:                                { \p _ -> (getLC p, Types) }
  decls:                                { \p _ -> (getLC p, Decls) }
  main:                                 { \p _ -> (getLC p, Main) }
  return                                { \p _ -> (getLC p, Return) }
{

-- The token type:
type InfoAndToken = ((Int, Int), Token)

data Token =
  -- Punctuations / Parantheses
  Comma |
  Colon   |
  SemiColon |
  Period |
  Pipe |
  OpenParentheses |
  CloseParentheses |
  OpenSquareBrackets |
  CloseSquareBrackets |
  OpenBrackets |
  CloseBrackets |
  Ellipsis |                        -- ...
  TwoDots  |                        -- ..
  -- Structures
  If  |
  Then |
  Else |
  For |
  Do |
  In |
  While |
  Switch |
  Case |
  Repeat |
  Match |
  With |
  Form |
  -- Operations / Relations
  Assign |
  Comp |
  Equals |
  Greater |
  Smaller |
  Leq |
  Geq |
  Not |
  And |
  Or |
  Different |
  Sum |
  Minus |
  Div |
  Mult |
  Pow |
  -- Declarations
  Fun |
  Vars |
  -- Types
  Type String |
  Nat |
  Int |
  String |
  TChar |
  Float |
  TBool |
  Unit |
  -- Literals
  NatLiteral Int |
  IntLiteral Int |
  StringLiteral String |
  CharLiteral Char |
  FloatLiteral Float |
  BoolLiteral Bool |
  UnitLiteral () |
  -- Others
  Id String |
  Import |
  Types |
  Decls |
  Main |
  Return |
  ErrorToken
  deriving (Eq,Show)

getLC (AlexPn _ l c) = (l, c)

getTokens fn = do
    fh <- openFile fn ReadMode;
    s <- hGetContents fh;
    return (alexScanTokens s)

}