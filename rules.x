{
  module Main (main, Token(..), AlexPosn(..), alexScanTokens) where
}

%wrapper "posn"

$digit = 0-9       -- digits
$alpha = [a-zA-Z]  -- alphabetic characters

-- Alex returns in each right-hand side: AlexPosn -> String
tokens :-

  $white+                               ;
  "--".*.                               ;
  let                                   { \p _ -> (p, Let) }
  in                                    { \p _ -> (p, In) }
  $digit+	                            { \p s -> (p, Int (read s)) }
  =                                     { \p _ -> (p, Equals) }
  "+"                                   { \p _ -> (p, Sum) }
  $alpha [$alpha $digit \_ \']*	        { \p s -> (p, Id s) }

{

-- The token type:
type TokenAndInfo = (AlexPosn, Token)

data Token =
  Let |
  In     |
  Begin   |
  End     |
  Colon   |
  SemiColon |
  Assign    | 
  If  |
  Then |
  Greater |
  Equals |
  Sum |
  Type String |
  Id String |
  Int Int |
  String String
  deriving (Eq,Show)

main = do
  s <- getContents
  print (alexScanTokens s)
}