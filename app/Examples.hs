module Examples where

import PetitSQL

sql1 = SQL Star "t" Nothing

sql2 = SQL (Cols ["c1"]) "t" Nothing

sql3 = SQL (Cols ["c1","c2","c3"]) "t" Nothing

sql4 = SQL Star "t" (Just (Term (Eq (ColName "id") (IntVal 123))))

sql5 = SQL Star "t" (Just (Term (Eq (ColName "id") (Var "z"))))

sql6 = SQL Star "t" (Just (Term (Eq (ColName "name") (StrVal "Hong"))))

sql7 = SQL Star "t" (Just (Term (Eq (ColName "name") (Var "z"))))

sql8 = SQL (Cols ["c1"]) "t" Nothing

sql9 = SQL (Cols ["c1","c2","c3"]) "t" Nothing

sql10 = SQL Star "t" (Just (Or (Term (Eq (ColName "name") (StrVal "'abc'")))
                               (Term (Eq (IntVal 1) (IntVal 1))  ) ))

