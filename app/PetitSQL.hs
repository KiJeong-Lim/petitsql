module PetitSQL where

import ParserLib
import Prelude hiding ((>>=),return)

import Data.Maybe

-- Petite SQL
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

--
data StringfiedSQL = StringfiedSQL [StrSQLElem]
  deriving (Eq,Show)
  
data StrSQLElem =
    Text String
  | Hole String         -- variable
  deriving (Eq,Show)

-- Normalize

norm (SQL cols tbl maybePred) =
  SQL cols tbl (normMaybePred maybePred)

normMaybePred Nothing = Nothing
normMaybePred (Just pred) = Just (normPred pred)

normPred (Term term) = Term term
normPred (Or (Term term1) pred2) = Or (Term term1) (normPred pred2)
normPred (Or (Or pred11 pred12) pred2) = normPred (Or pred11 (Or pred12 pred2))


-- Injection
type Env = [(String,Value)]   -- Value is either StrVal or IntVal by the type system.

injection v s sql = applySQL [(v,StrVal s)] sql  -- inject s in sql through v!

applySQL env (SQL cols tbl maybePred) =
  SQL cols tbl (applyMaybePred env maybePred)

applyMaybePred env Nothing = Nothing
applyMaybePred env (Just pred) = Just (applyPred env pred)

applyPred env (Term term) = Term (applyTerm env term)
applyPred env (Or pred1 pred2) =
  Or (applyPred env pred1) (applyPred env pred2)

applyTerm env (Eq v1 v2) = Eq (applyValue env v1) (applyValue env v2)

applyValue env (ColName cn) = ColName cn
applyValue env (StrVal s) = StrVal s
applyValue env (IntVal i) = IntVal i
applyValue env (Var x) =
  case [v | (y,v) <- env, x==y] of
    [] -> Var x
    (v:_) -> v

-- Injection-free

injFree (SQL cols1 tbl1 maybePred1) (SQL cols2 tbl2 maybePred2) =
  cols1==cols2 && tbl1==tbl2 && injFreeMaybePred maybePred1 maybePred2

injFreeMaybePred Nothing Nothing = True
injFreeMaybePred (Just pred1) (Just pred2) = injFreePred pred1 pred2
injFreeMaybePred _ _ = False

injFreePred (Term term1) (Term term2) = injFreeTerm term1 term2
injFreePred (Or pred11 pred12) (Or pred21 pred22) =
  injFreePred pred11 pred21 && injFreePred pred12 pred22
injFreePred _ _ = False

  
injFreeTerm (Eq v11 v12) (Eq v21 v22) =
  injFreeValue v11 v21 && injFreeValue v12 v22

injFreeValue (ColName c1) (ColName c2) = c1==c2
injFreeValue (StrVal s1)  (StrVal s2)  = s1==s2
injFreeValue (IntVal i1)  (IntVal i2)  = i1==i2
injFreeValue (Var x)      _            = True   -- Can be ColName c!
injFreeValue _            (Var x)      = True   -- 
injFreeValue _            _            = False  -- ColName vs StrVale and so on.

-- Printer
printSQL :: SQL -> String
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
  (integer >>= (\i ->
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
  

{-

The following lemma is not always true for sqlstring and ppString. A
 counter-example is:

  sqlstring (ppString "hello" ++ "world")

Under the context of SQL trees, the lemma becomes true because there
is no way to print two strings in sequence with no delimeters.

Lemma String values:
  forall str, theRest. sqlstring (ppString str ++ theRest) == [(str, theRest)].


Examples
  ghci> sqlstring (ppString "hello")
  [("hello","")]
  ghci> sqlstring (ppString "'hello")
  [("'hello","")]
  ghci> sqlstring (ppString "'hello'")
  [("'hello'","")]
  ghci> sqlstring (ppString "'''hello")
  [("'''hello","")]
  ghci> sqlstring (ppString "'hello'" ++ "dffdfd")
  [("'hello'","dffdfd")]
  ghci> sqlstring (ppString "'hello'" ++ "dffdfd")
  [("'hello'","dffdfd")]


Bad examples
  ghci> sqlstring (ppString "'hello'" ++ "'world'")
  [("'hello''world","")]
  ghci> sqlstring (ppString "'hello'" ++ " 'world'")
  [("'hello'"," 'world'")]


Interesting variations
  ghci> sqlstring (ppString "hello" ++ "world")
  [("hello","world")]
  ghci> sqlstring (ppString "hello" ++ "'world")
  [("hello","'world")]
  ghci> sqlstring (ppString "hello" ++ "'world'")
  [("hello'world","")]
  ghci> sqlstring (ppString "hello" ++ "'world" ++ " or " ++ "!!'")
  [("hello'world or !!","")]


Lemma String values:
  forall str, theRest.
     head theRest <> '\''
       ===>  sqlstring (ppString str ++ theRest) == [(str, theRest)].

-}