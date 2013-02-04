module Spire.CLI where
import Spire.SurfaceTerm as T

type TypeChecker = Int -> PreTerm -> PreTerm -> Maybe String

run :: TypeChecker -> IO ()
run isTyped = do
  putStrLn $ "Enter universe level: "
  lv <- getLine
  putStrLn $ "Enter type: "
  tp <- getLine
  putStrLn $ "Enter term: "
  tm <- getLine
  case isTyped (read lv) (read tp) (read tm) of
     Nothing -> putStrLn "Well typed!"
     Just error -> putStrLn "Ill typed!" >> putStrLn error

