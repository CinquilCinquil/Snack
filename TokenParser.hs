module TokenParser where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class

update_pos :: SourcePos -> InfoAndToken -> [InfoAndToken] -> SourcePos
update_pos pos _ (((nextline, nextcolumn), _):_) = setSourceColumn (setSourceLine pos nextline) nextcolumn
update_pos pos _ []       = pos                    -- Fim do código-fonte

tokenParser :: Token -> ParsecT [InfoAndToken] st IO (Token)
tokenParser token = tokenPrim show update_pos get_token where
  get_token (info, token_) = if token_ == token then Just token else Nothing

---------------------------------------------------
----------------- Parsers for terminals
---------------------------------------------------

-- Punctuations / Parantheses

commaToken = tokenParser Comma
colonToken = tokenParser Colon
semiColonToken = tokenParser SemiColon
periodToken = tokenParser Period
openParenthesesToken = tokenParser OpenParentheses
closeParenthesesToken = tokenParser CloseParentheses
openSquareBracketsToken = tokenParser OpenSquareBrackets
closeSquareBracketsToken = tokenParser CloseSquareBrackets
openBracketsToken = tokenParser OpenBrackets
closeBracketsToken = tokenParser CloseBrackets
ellipsisToken = tokenParser Ellipsis
twoDotsToken = tokenParser TwoDots
questionToken = tokenParser Question

-- Structures

ifToken = tokenParser If
thenToken = tokenParser Then
elseToken = tokenParser Else
forToken = tokenParser For
stepToken = tokenParser Step
inToken = tokenParser In
whileToken = tokenParser While
switchToken = tokenParser Switch
caseToken = tokenParser Case
repeatToken = tokenParser Repeat
matchToken = tokenParser Match
withToken = tokenParser With
formToken = tokenParser Form
ofFormToken = tokenParser OfForm

-- Operations / Relations

toIntToken = tokenParser ToIntToken
toFloatToken = tokenParser ToFloatToken
toStringToken = tokenParser ToStringToken
toBoolToken = tokenParser ToBoolToken
toCharToken = tokenParser ToCharToken
errorCmdToken = tokenParser ErrorCmdToken

assignToken = tokenParser Assign
compToken = tokenParser Comp
equalsToken = tokenParser Equals
leqToken = tokenParser Leq
geqToken = tokenParser Geq
greaterToken = tokenParser Greater
smallerToken = tokenParser Smaller
notToken = tokenParser Not
andToken = tokenParser And
orToken = tokenParser Or
differentToken = tokenParser Different
sumToken = tokenParser Sum
minusToken = tokenParser Minus
divToken = tokenParser Div
multToken = tokenParser Mult
powToken = tokenParser Pow

-- Declarations

funToken = tokenParser Fun
varsToken = tokenParser Vars

-- Types

typeToken :: ParsecT [InfoAndToken] st IO (Token)
typeToken = tokenPrim show update_pos get_token where
  get_token (info, Type x y) = Just (Type x y)
  get_token _       = Nothing

natToken = tokenParser Nat
intToken = tokenParser Int
stringToken = tokenParser TString
charToken = tokenParser TChar
floatToken = tokenParser Float
boolToken = tokenParser TBool
unitToken = tokenParser Unit
structToken = tokenParser Struct
matrixToken = tokenParser (Matrix Unit [])

-- Literals

natLiteralToken :: ParsecT [InfoAndToken] st IO (Token)
natLiteralToken = tokenPrim show update_pos get_token where
  get_token (info, NatLiteral x) = Just (NatLiteral x)
  get_token _       = Nothing

intLiteralToken :: ParsecT [InfoAndToken] st IO (Token)
intLiteralToken = tokenPrim show update_pos get_token where
  get_token (info, IntLiteral x) = Just (IntLiteral x)
  get_token _       = Nothing

stringLiteralToken :: ParsecT [InfoAndToken] st IO (Token)
stringLiteralToken = tokenPrim show update_pos get_token where
  get_token (info, StringLiteral x) = Just (StringLiteral x)
  get_token _       = Nothing

charLiteralToken :: ParsecT [InfoAndToken] st IO (Token)
charLiteralToken = tokenPrim show update_pos get_token where
  get_token (info, CharLiteral x) = Just (CharLiteral x)
  get_token _       = Nothing

floatLiteralToken :: ParsecT [InfoAndToken] st IO (Token)
floatLiteralToken = tokenPrim show update_pos get_token where
  get_token (info, FloatLiteral x) = Just (FloatLiteral x)
  get_token _       = Nothing

boolLiteralToken :: ParsecT [InfoAndToken] st IO (Token)
boolLiteralToken = tokenPrim show update_pos get_token where
  get_token (info, BoolLiteral x) = Just (BoolLiteral x)
  get_token _       = Nothing

-- TODO: matrix literal token

-- this would be very cool! like: a : struct := {"x" : 1, "y" : "hello", z : 0.001}
-- structLiteralToken :: ParsecT [InfoAndToken] st IO (Token)
-- structLiteralToken = tokenPrim show update_pos get_token where
--   get_token (info, StructLiteral x) = Just (StructLiteral x)
--   get_token _       = Nothing

-- Others

idToken :: ParsecT [InfoAndToken] st IO (Token)
idToken = tokenPrim show update_pos get_token where
  get_token (info, Id x) = Just (Id x)
  get_token _      = Nothing

importToken = tokenParser Import
typesToken = tokenParser Types
declsToken = tokenParser Decls
mainToken = tokenParser Main
returnToken = tokenParser Return
printToken = tokenParser Print
readToken = tokenParser Read