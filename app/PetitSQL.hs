module PetitSQL where

data SQL =
    SQL Cols Tbl (Maybe Pred)

data Cols =
    Star            -- *
  | Cols [String]   -- column names

type Tbl = String

data Pred =
    Or Pred Pred
  | Term Term

data Term =
    Eq Value Value  -- col = x

data Value =
    ColName String
  | StrVal String
  | IntVal Int
  | Var    String

-- Printer
ppSQL (SQL cols tbl maybePred) =
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
    , " OR "
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
ppValue (Var x) = "$"++x

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

