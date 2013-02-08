module Spire.CLI where
import Spire.SurfaceTerm as T

run :: CanonicalTypeChecker -> IO ()
run isTyped = do
  putStrLn $ "Enter type: "
  tp <- getLine
  putStrLn $ "Enter term: "
  tm <- getLine
  case isTyped (read tp) (read tm) of
     Well -> putStrLn "Well typed!"
     Ill subtm error -> do
       putStrLn "Ill typed!"
       putStrLn $ pshow subtm ++ " " ++ error

