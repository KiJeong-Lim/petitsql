module Main where

import ParserLib
import PetitSQL
import Examples

main :: IO ()
main = putStrLn $ show $ parse (ParserLib.return 1) "abc"
