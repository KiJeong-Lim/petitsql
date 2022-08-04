module Main where

import PetitSQL
import ParserLib (parse,identifier)

import Test.QuickCheck (quickCheck
                       ,quickCheckResult
                       ,quickCheckWithResult
                       ,stdArgs
                       ,maxSuccess
                       ,Result(Success)
                       ,within
                       ,Testable)
import Test.QuickCheck.Arbitrary       
import Test.QuickCheck.Gen
import Test.QuickCheck.Property

import Test.Hspec
import Test.QuickCheck.Property (property)

main :: IO ()
main = hspec $ do
  describe "SQL injection free?" $ do
    it "For all sql, x, and v, sql is injection-free from injection x v sql" $
      forAll arbitrary $ \sql ->
      forAll arbitrary $ \x ->
      forAll arbitrary $ \v ->
         injFree (norm sql) . norm . sqlFrom . parseSQL . printSQL . injection x v $ sql

    where
      sqlFrom [(sql, "")] = sql
      sqlFrom _           = error "The rest string after paring are not empty."

-- Tree-structured SQL ==> Stringfied SQL

diff :: String -> String -> IO ()
diff [] [] = Prelude.return ()
diff (x:xs) (y:ys)
  | x==y = diff xs ys
  | x/=y = do putStrLn (x:xs)
              putStrLn "and"
              putStrLn (y:ys)

isIdentifier x =
  case parse identifier x of
    ((_,""):[]) -> True
    _ -> False

--
-- QuickCheck
instance Arbitrary SQL where
  arbitrary = do
    cols <- arbitrary
    tbl <- tableName 
    maybePred <- arbitrary
    return (SQL cols tbl maybePred)

tableName = genIdentifier

genIdentifier = do
  c <- choose ('a', 'z')
  len <- choose (0, 10::Int)
  therest <- mapM (\_ -> oneof [ choose ('a', 'z'), choose ('0', '9') ]) [1..len]
  return (c:therest)
  
instance Arbitrary Cols where
  arbitrary = do
    b <- chooseEnum (True,False)
    if b
      then return Star
      else do num <- choose (1,10::Int)
              ss <- mapM (\_ -> genIdentifier) [1..num]
              return $ Cols ss

instance Arbitrary Pred where
  arbitrary = do
    b <- chooseEnum (True,False)
    if b
      then do pred1 <- arbitrary
              pred2 <- arbitrary
              return (Or pred1 pred2)
      else do term <- arbitrary
              return (Term term)

instance Arbitrary Term where
  arbitrary = do val1 <- colNameVal
                 val2 <- arbValue
                 return (Eq val1 val2)

arbValue = do i <- chooseInt (2,4)
              case i of
                -- 1 -> do s <- genIdentifier
                --         return $ ColName s
                2 -> do s <- arbitrary
                        return $ StrVal s
                3 -> do i <- arbitrary
                        return $ IntVal i
                4 -> do v <- genIdentifier
                        return $ Var v
                _ -> error "Should never happen."

colNameVal = do s <- genIdentifier
                return $ ColName s
