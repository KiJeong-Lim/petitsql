module ParserLib where

import Prelude hiding ((>>=), return)
import Data.Char

-- 8.2 Parser type
type Parser a = String -> [(a,String)]

-- 8.3 Basic 
return :: a -> Parser a
return v = \inp -> [(v,inp)]

failure :: Parser a
failure = \inp -> []

item :: Parser Char
item = \inp -> case inp of
                 [] -> []
                 (x:xs) -> [(x,xs)]

parse :: Parser a -> String -> [(a,String)]
parse p inp = p inp

-- 8.4 Sequencing
(>>=) :: Parser a -> (a -> Parser b) -> Parser b
p >>= f = \inp -> case parse p inp of
                    [] -> []
                    [(v,out)] -> parse (f v) out

p :: Parser (Char,Char)
p = item >>= (\x ->
      item >>= (\_ ->
        item >>= (\y ->
          return (x,y))))

-- 8.5 Choice
(+++) :: Parser a -> Parser a -> Parser a
p +++ q = \inp -> case parse p inp of
                    [] -> parse q inp
                    [(v,out)] -> [(v,out)]

-- 8.6 Library
sat :: (Char -> Bool) -> Parser Char
sat p = item >>= (\x ->
          if p x then return x else failure)


digit :: Parser Char
digit = sat isDigit

lower :: Parser Char
lower = sat isLower

upper :: Parser Char
upper = sat isUpper

letter :: Parser Char
letter = sat isAlpha

alphanum :: Parser Char
alphanum = sat isAlphaNum

char :: Char -> Parser Char
char x = sat (== x)

string :: String -> Parser String
string [] = return []
string (x:xs) = char x >>= (\x ->
                  string xs >>= (\_ ->
                    return (x:xs)))

many :: Parser a -> Parser [a]
many p = many1 p +++ return []

many1 :: Parser a -> Parser [a]
many1 p = p >>= (\v ->
            many p >>= (\vs ->
              return (v:vs)))

ident :: Parser String
ident = lower >>= (\x ->
          many alphanum >>= (\xs ->
            return (x:xs)))

nat :: Parser Int
nat = many1 digit >>= (\xs ->
        return (read xs))

space :: Parser ()      
space = many (sat isSpace) >>= (\_ ->
          return ())


-- 8.7 Handling spaces
token :: Parser a -> Parser a
token p = space >>= (\_ ->
            p >>= (\v ->
              space >>= (\_ ->
                return v)))

identifier :: Parser String
identifier = token ident

natural :: Parser Int
natural = token nat

symbol :: String -> Parser String
symbol xs = token (string xs)
