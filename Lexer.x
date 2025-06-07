{
module Lexer (Token(..), AlexPosn(..), alexScanTokens, getTokens) where
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
  ","                                   { \p _ -> (p, Comma)}
  :                                     { \p _ -> (p, Colon)}
  ";"                                   { \p _ -> (p, SemiColon)}
  "."                                   { \p _ -> (p, Period)}
  "|"                                   { \p _ -> (p, Pipe)}
  "("                                   { \p _ -> (p, OpenParentheses)}
  ")"                                   { \p _ -> (p, CloseParentheses)}
  "["                                   { \p _ -> (p, OpenSquareBrackets)}
  "]"                                   { \p _ -> (p, CloseSquareBrackets)}
  "{"                                   { \p _ -> (p, OpenBrackets)}
  "}"                                   { \p _ -> (p, CloseBrackets)}
  "..."                                 { \p _ -> (p, Ellipsis)}
  -- Structures
  if                                    { \p _ -> (p, If) }
  then                                  { \p _ -> (p, Then) }
  else                                  { \p _ -> (p, Else) }
  for                                   { \p _ -> (p, For) }
  do                                    { \p _ -> (p, Do) }
  in                                    { \p _ -> (p, In) }
  while                                 { \p _ -> (p, While) }
  switch                                { \p _ -> (p, Switch) }
  case                                  { \p _ -> (p, Case) }
  -- Operations / Relations
  ":="                                  { \p _ -> (p, Assign) }
  "="                                   { \p _ -> (p, Equals) }
  ">"                                   { \p _ -> (p, Greater) }
  "<"                                   { \p _ -> (p, Smaller) }
  "+"                                   { \p _ -> (p, Sum) }
  "-"                                   { \p _ -> (p, Minus) }
  "/"                                   { \p _ -> (p, Div) }
  "*"                                   { \p _ -> (p, Mult) }
  "^"                                   { \p _ -> (p, Pow) }
  -- Declarations
  fun                                   { \p _ -> (p, Fun) }
  vars                                  { \p _ -> (p, Vars) }
  -- Types
  type                                  { \p s -> (p, Type s) }
  nat                                   { \p _ -> (p, Nat) }
  int                                   { \p _ -> (p, Int) }
  string                                { \p _ -> (p, String) }
  float                                 { \p _ -> (p, Float) }
  -- Literals
  $D+	                                  { \p s -> (p, NatLiteral (read s)) }
  ($D+"."$D+)(e[\+\-]$D$D)?	            { \p s -> (p, FloatLiteral (read s)) }
  \".*\"                                { \p s -> (p, StringLiteral (read s)) }
  \'.+\'                                { \p s -> (p, CharLiteral (read s)) }
  true|false                            { \p s -> (p, BoolLiteral $ (\b -> if b == "true" then True else False) (read s)) }
  
  -- missing other primary types such as unit, empty, matrix...

  -- Others
  $L[$L $D \_ \']*	                    { \p s -> (p, Id s) }
  import                                { \p _ -> (p, Import) }
  types\:                               { \p _ -> (p, Types) }
  decls\:                               { \p _ -> (p, Decls) }
  main\:                                { \p _ -> (p, Main) }
{

-- The token type:
type TokenAndInfo = (AlexPosn, Token)

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
  Main
  deriving (Eq,Show)

getTokens fn = do
    fh <- openFile fn ReadMode;
    s <- hGetContents fh;
    return (alexScanTokens s)
}