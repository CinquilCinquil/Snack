{
{-# LANGUAGE DeriveDataTypeable #-}
module Lexer (Token(..), InfoAndToken(..), AlexPosn(..), alexScanTokens, getTokens) where
import Data.Data
import System.IO
}

%wrapper "posn"

$D = [0-9]
$L = [a-zA-Z]

-- Alex returns in each right-hand side: AlexPosn -> String
tokens :-

  $white+                               ;
  "--".+                                ;
  -- Punctuations / Parantheses
  ","                                   { \p _ -> (getLC p, Comma)}
  ":"                                   { \p _ -> (getLC p, Colon)}
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
  "?"                                   { \p _ -> (getLC p, Question)}
  -- Structures
  if                                    { \p _ -> (getLC p, If) }
  then                                  { \p _ -> (getLC p, Then) }
  else                                  { \p _ -> (getLC p, Else) }
  for                                   { \p _ -> (getLC p, For) }
  step                                  { \p _ -> (getLC p, Step) }
  in                                    { \p _ -> (getLC p, In) }
  while                                 { \p _ -> (getLC p, While) }
  switch                                { \p _ -> (getLC p, Switch) }
  case                                  { \p _ -> (getLC p, Case) }
  repeat                                { \p _ -> (getLC p, Repeat) }
  match                                 { \p _ -> (getLC p, Match) }
  with                                  { \p _ -> (getLC p, With) }
  form                                  { \p _ -> (getLC p, Form) }
  ofForm                                { \p _ -> (getLC p, OfForm) }
  -- Operations / Relations
  "toInt"                               { \p _ -> (getLC p, ToIntToken) }
  "toFloat"                             { \p _ -> (getLC p, ToFloatToken) }
  "toString"                            { \p _ -> (getLC p, ToStringToken) }
  "toBool"                              { \p _ -> (getLC p, ToBoolToken) }
  "toChar"                              { \p _ -> (getLC p, ToCharToken) }
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
  nat                                   { \p _ -> (getLC p, Nat) }
  int                                   { \p _ -> (getLC p, Int) }
  string                                { \p _ -> (getLC p, TString) }
  char                                  { \p _ -> (getLC p, TChar) }
  float                                 { \p _ -> (getLC p, Float) }
  bool                                  { \p _ -> (getLC p, TBool) }
  unit                                  { \p _ -> (getLC p, Unit) }
  struct                                { \p s -> (getLC p, Struct) }
  matrix                                { \p s -> (getLC p, Matrix Unit []) }
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
  "return"                              { \p _ -> (getLC p, Return) }
  "import"                              { \p _ -> (getLC p, Import) }
  "types:"                              { \p _ -> (getLC p, Types) }
  "decls:"                              { \p _ -> (getLC p, Decls) }
  "main:"                               { \p _ -> (getLC p, Main) }
  "spit"                                { \p _ -> (getLC p, Print) }
  "eat"                                 { \p _ -> (getLC p, Read) }
  $L[$L $D \_ \']*	                    { \p s -> (getLC p, Id s) }
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
  Question |                        -- ?
  -- Structures
  If  |
  Then |
  Else |
  For |
  Step |
  In |
  While |
  Switch |
  Case |
  Repeat |
  Match |
  With |
  Form |
  OfForm |
  -- Operations / Relations
  ToIntToken |
  ToFloatToken |
  ToStringToken |
  ToBoolToken |
  ToCharToken |
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
  Type String [Token] | -- Name, Params
  Nat |
  Int |
  TString |
  TChar |
  Float |
  TBool |
  Unit |
  Struct |
  Matrix Token [Int] |
  -- Literals
  NatLiteral Int |
  IntLiteral Int |
  StringLiteral String |
  CharLiteral Char |
  FloatLiteral Float |
  BoolLiteral Bool |
  UnitLiteral () |
  StructLiteral [(String, Token, Token, [Token])] | -- [(Name, Type, Value, FunctionBody)]
  MatrixLiteral Token [Token] |
  TypeLiteral String [Token] [Token] | -- Constructor name, args, params
  -- Others
  Id String |
  Return |
  Import |
  Types |
  Decls |
  Main |
  Print |
  Read |
  ErrorToken |
  NoneToken |
  EndOfParamsToken
  deriving (Eq,Show,Data)

getLC (AlexPn _ l c) = (l, c)

getTokens fn = do
    fh <- openFile fn ReadMode;
    s <- hGetContents fh;
    return (alexScanTokens s)

}