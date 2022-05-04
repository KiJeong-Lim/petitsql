module Examples where

import PetitSQL

examples =
  [ sql01
  , sql02
  , sql03
  , sql04
  , sql05
  , sql06
  , sql07
  , sql08
  , sql09
  , sql10
  ]
  
sql01 = SQL Star "t" Nothing

sql02 = SQL (Cols ["c1"]) "t" Nothing

sql03 = SQL (Cols ["c1","c2","c3"]) "t" Nothing

sql04 = SQL Star "t" (Just (Term (Eq (ColName "id") (IntVal 123))))

sql05 = SQL Star "t" (Just (Term (Eq (ColName "id") (Var "z"))))

sql06 = SQL Star "t" (Just (Term (Eq (ColName "name") (StrVal "Hong"))))

sql07 = SQL Star "t" (Just (Term (Eq (ColName "name") (Var "z"))))

sql08 = SQL (Cols ["c1"]) "t" Nothing

sql09 = SQL (Cols ["c1","c2","c3"]) "t" Nothing

sql10 = SQL Star "t" (Just (Or (Term (Eq (ColName "name") (StrVal "'abc'")))
                               (Term (Eq (IntVal 1) (IntVal 1))  ) ))

