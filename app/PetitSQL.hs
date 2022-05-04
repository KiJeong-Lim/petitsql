module PetitSQL where

import ParserLib
import Prelude hiding ((>>=),return)

import Data.Maybe

data SQL =
    SQL Cols Tbl (Maybe Pred)
    deriving (Eq,Show)

data Cols =
    Star            -- *
  | Cols [String]   -- column names
  deriving (Eq,Show)

type Tbl = String

data Pred =
    Or Pred Pred
  | Term Term
  deriving (Eq,Show)

data Term =
    Eq Value Value  -- col = x
    deriving (Eq,Show)

data Value =
    ColName String
  | StrVal String
  | IntVal Int
  | Var    String
  deriving (Eq,Show)

-- Printer
printSQL (SQL cols tbl maybePred) =
  concat 
    [ "select "
    , ppCols cols
    , " from "
    , ppTbl tbl
    , ppWhere maybePred
    ]

ppCols Star = "*"
ppCols (Cols []) = ""
ppCols (Cols [c1]) = c1
ppCols (Cols (c1:c2:cs)) = 
  concat
    [ c1
    , ","
    , ppCols (Cols (c2:cs))
    ]

ppTbl tbl = tbl

ppWhere Nothing = ""
ppWhere (Just pred) =
  concat
    [ " where "
    , ppPred pred
    ]
  
ppPred (Term term) = ppTerm term
ppPred (Or p q) =
  concat
    [ ppPred p
    , " or "
    , ppPred q
    ]

ppTerm (Eq v1 v2) =
  concat
    [ ppValue v1
    , " = "
    , ppValue v2
    ]

ppValue (ColName s) = s
ppValue (StrVal s) = ppString s
ppValue (IntVal i) = show i
ppValue (Var x) = "{"++x++"}"

ppString s =
  concat
    [ "\'"
    , ppString1 s
    , "\'"
    ]
  
ppString1 [] = []
ppString1 ('\'':xs) = '\'':'\'':ppString1 xs
ppString1 (x:xs) = x:ppString1 xs


-- Parser

parseSQL :: Parser SQL
parseSQL =
  symbol "select" >>= (\_ ->
  (star +++ columns) >>= (\cols ->
  symbol "from" >>= (\_ ->
  table >>= (\tbl ->
  optWhere >>= (\maybePred ->
  return (SQL cols tbl maybePred))))))

star :: Parser Cols
star =
  symbol "*" >>= (\_ ->
  return Star)

columns :: Parser Cols
columns =
  columns1 >>= (\cols ->
  return (Cols cols))

columns1 :: Parser [String]
columns1 =
  identifier >>= (\col ->
  many (symbol "," >>= (\_ -> identifier)) >>= (\cols ->
  return (col:cols)))
        
table :: Parser String
table = identifier

optWhere :: Parser (Maybe Pred)
optWhere =
  (symbol "where" >>= (\_ ->
  predicate >>= (\pred ->
  return (Just pred))))
  +++
  (return Nothing)

predicate :: Parser Pred
predicate =
  parseterm >>= (\term ->
  predicate1 >>= (\f ->
  return (f (Term term))))
  
predicate1 :: Parser (Pred -> Pred) 
predicate1 =
  (symbol "or" >>= (\_ ->
   predicate >>= (\pred2 ->
   predicate1 >>= (\f ->
   return (\pred1 -> f (Or pred1 pred2))))))
  +++
  (return (\x->x))

parseterm :: Parser Term
parseterm =
  parsevalue >>= (\v1 ->
  symbol "=" >>= (\_ ->
  parsevalue >>= (\v2 ->
  return (Eq v1 v2))))
  
parsevalue :: Parser Value
parsevalue =
  (identifier >>= (\colName ->
   return (ColName colName)))
  +++
  (sqlstring >>= (\sqlstr ->
   return (StrVal sqlstr)))
  +++
  (nat >>= (\i ->
   return (IntVal i)))
  +++
  (symbol "{" >>= (\_ ->
   identifier >>= (\v ->
   symbol "}" >>= (\_ ->
   return (Var v)))))

sqlstring :: Parser String
sqlstring =
  (char '\'') >>= (\_ ->
  sqlstringin >>= (\text ->
  return text))
  

sqlstringin :: Parser String
sqlstringin =
  ((char '\'') >>= (\_ ->
   (char '\'') >>= (\_ ->
   sqlstringin >>= (\text ->
   return ('\'':text)))))
  +++
  ((char '\'') >>= (\_ ->
   (return "")))
  +++
  (item >>= (\c ->
   sqlstringin >>= (\text ->
   return (c:text))))
  
