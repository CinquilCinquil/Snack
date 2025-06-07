module Main (main) where

import Lexer
import Text.Parsec
import Control.Monad.IO.Class
import TokenParser

type SharedBoard = (Token, Token)

-- parsers para os não-terminais

program :: ParsecT [Token] [SharedBoard] IO ([Token])
program = do
            --a <- importToken
            b <- typesToken 
            c <- declsToken
            d <- mainToken
            -- f <- stmts
            eof
            return (b:c:[d])

-- funções para a tabela de símbolos        

symtable_insert :: SharedBoard -> [SharedBoard] -> [SharedBoard]
symtable_insert symbol []  = [symbol]
symtable_insert symbol symtable = symtable ++ [symbol]

symtable_update :: SharedBoard -> [SharedBoard] -> [SharedBoard]
symtable_update _ [] = fail "variable not found"
symtable_update (id1, v1) ((id2, v2):t) = 
                               if id1 == id2 then (id1, v1) : t
                               else (id2, v2) : symtable_update (id1, v1) t

symtable_remove :: SharedBoard -> [SharedBoard] -> [SharedBoard]
symtable_remove _ [] = fail "variable not found"
symtable_remove (id1, v1) ((id2, v2):t) = 
                               if id1 == id2 then t
                               else (id2, v2) : symtable_remove (id1, v1) t                               


-- invocação do parser para o símbolo de partida 

parser :: [Token] -> IO (Either ParseError [Token])
parser tokens = runParserT program [] "Parsing error!" tokens

main :: IO ()
main = do
    tokens <- getTokens "example_program.snack"
    print tokens
    result <- parser $ map snd tokens
    case result of
      { Left err -> print err; 
        Right ans -> print ans
      }