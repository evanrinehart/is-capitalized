module Main

import Capitalized

main : IO ()
main = case isCapitalized "Abc" of
  Yes prf => putStrLn "ok"
  No _ => putStrLn "not ok"
  
