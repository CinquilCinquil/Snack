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
  "|"                                   { \p _ -> (getLC p, Pipe)}
  "("                                   { \p _ -> (getLC p, OpenParentheses)}
  ")"                                   { \p _ -> (getLC p, CloseParentheses)}
  "["                                   { \p _ -> (getLC p, OpenSquareBrackets)}
  "]"                                   { \p _ -> (getLC p, CloseSquareBrackets)}
  "{"                                   { \p _ -> (getLC p, OpenBrackets)}
  "}"                                   { \p _ -> (getLC p, CloseBrackets)}
  "..."                                 { \p _ -> (getLC p, Ellipsis)}
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
  -- Operations / Relations
  ":="                                  { \p _ -> (getLC p, Assign) }
  "="                                   { \p _ -> (getLC p, Equals) }
  ">"                                   { \p _ -> (getLC p, Greater) }
  "<"                                   { \p _ -> (getLC p, Smaller) }
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
  -- Literals
  S$D+	                                { \p s -> (getLC p, NatLiteral (read s)) }
  $D+	                                  { \p s -> (getLC p, IntLiteral (read s)) }
  ($D+"."$D+)(e[\+\-]$D$D)?	            { \p s -> (getLC p, FloatLiteral (read s)) }
  \".*\"                                { \p s -> (getLC p, StringLiteral (read s)) }
  \'.+\'                                { \p s -> (getLC p, CharLiteral (read s)) }
  "true"|"false"                        { \p s -> (getLC p, BoolLiteral (s == "true")) }
  --"True"|"False"                            { \p s -> (getLC p, BoolLiteral $ (\b -> if b == "True" then True else False) (read s)) }
  
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
  -- Operations / Relations
  Assign |
  Equals |
  Greater |
  Smaller |
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
  -- Literals
  NatLiteral Int |
  IntLiteral Int |
  StringLiteral String |
  CharLiteral Char |
  FloatLiteral Float |
  BoolLiteral Bool |
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