module Main

import Capitalized

main : IO ()
main = case isCapitalized "" of
  Yes prf => putStrLn "ok"
  No _ => putStrLn "not ok"
  
