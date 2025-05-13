{
  module Main (main, Token(..), AlexPosn(..), alexScanTokens) where
}

%wrapper "posn"

$digit = 0-9       -- digits
$alpha = [a-zA-Z]  -- alphabetic characters

-- Alex returns in each right-hand side: AlexPosn -> String
tokens :-

  \n                                    {\p _ -> (p, LineBreak)} -- a gente vai manter isso mesmo?
  $white+                               ;
  "--".*.                               ;
  -- Punctuations / Parantheses
  ","                                   { \p _ -> (p, Comma)}
  :                                     { \p _ -> (p, Colon)}
  ";"                                   { \p _ -> (p, SemiColon)}
  "."                                   { \p _ -> (p, Period)}
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
  $digit+	                            { \p s -> (p, IntLiteral (read s)) }
  -- TODO: others
  -- Others
  $alpha [$alpha $digit \_ \']*	        { \p s -> (p, Id s) }
  import                                { \p _ -> (p, Import) }
  main                                  { \p _ -> (p, Main) }

{

-- The token type:
type TokenAndInfo = (AlexPosn, Token)

data Token =
  -- Punctuations / Parantheses
  Comma |
  Colon   |
  SemiColon |
  Period |
  OpenParentheses |
  CloseParentheses |
  OpenSquareBrackets |
  CloseSquareBrackets |
  OpenBrackets |
  CloseBrackets |
  Ellipsis |                        -- ...
  LineBreak |
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
  Float |
  -- Literals
  NatLiteral Int | -- vcs concordam q o NatLiteral recebe um Int?
  IntLiteral Int |
  StringLiteral String |
  FloatLiteral Float |
  -- Others
  Id String |
  Import |
  Main
  deriving (Eq,Show)

main = do
  s <- getContents
  print (alexScanTokens s)
}