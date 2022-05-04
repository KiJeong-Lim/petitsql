module Main where

import ParserLib
import PetitSQL
import Examples

main :: IO ()
main = mapM_ printAndParse examples
 where
   printAndParse sql =
     do let text = printSQL sql
        putStrLn text
        let ((sql',therest):thelist) = parseSQL text
        let text' = printSQL sql'
        putStrLn text'
        putStrLn $ show $ sql==sql'
        putStrLn $ therest
        putStrLn $ show $ length thelist

--putStrLn $ show $ parse (ParserLib.return 1) "abc"
