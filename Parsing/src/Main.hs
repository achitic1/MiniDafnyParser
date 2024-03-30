module Main where

-- Make sure you run this via `stack run` in the top-level folder.
-- If you run it from `src` or `test` the tests won't be able to 
-- locate the files.

import Syntax
import DafnyParser 

import System.Environment

main :: IO ()
main = do
  c <- test_all
  putStrLn $ show c
  


