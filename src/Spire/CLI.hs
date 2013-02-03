module Spire.CLI where
import Spire.SurfaceTerm as T

type TypeChecker = Int -> PreTerm -> PreTerm -> Bool

run :: TypeChecker -> IO ()
run isTyped = do
  putStrLn "Warming up the type checker..."
  putStrLn $ "Enter universe level: "
  lv <- getLine
  putStrLn $ "Enter type: "
  tp <- getLine
  putStrLn $ "Enter term: "
  tm <- getLine
  if isTyped (read lv) (read tp) (read tm)
     then putStrLn "Well typed!"
     else putStrLn "Ill typed!"

