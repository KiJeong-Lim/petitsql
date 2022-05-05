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
    it "sql should be equal injection env sql" $
      forAll arbitrary $ \sql ->
      forAll arbitrary $ \x ->
      forAll arbitrary $ \v ->
        {- isIdentifier x ==> collect (x,v,sql) $ -}
        injFree sql (injection x v sql)


isIdentifier x =
  case parse identifier x of
    ((_,""):[]) -> True
    _ -> False

--
-- QuickCheck
instance Arbitrary SQL where
  arbitrary = do
    cols <- arbitrary
    tbl <- arbitrary
    maybePred <- arbitrary
    return (SQL cols tbl maybePred)

instance Arbitrary Cols where
  arbitrary = do
    b <- chooseEnum (True,False)
    if b
      then return Star
      else do ss <- arbitrary
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
  arbitrary = do val1 <- arbitrary
                 val2 <- arbitrary
                 return (Eq val1 val2)

instance Arbitrary Value where
  arbitrary = do i <- chooseInt (1,4)
                 case i of
                   1 -> do s <- arbitrary
                           return $ ColName s
                   2 -> do s <- arbitrary
                           return $ StrVal s
                   3 -> do i <- arbitrary
                           return $ IntVal i
                   4 -> do v <- arbitrary
                           return $ Var v
                   _ -> error "Should never happen."
