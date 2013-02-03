module Spire.CLI where
import Spire.SurfaceTerm as T

run :: (PreTerm -> PreTerm -> Bool) -> IO ()
run isTyped = do
  putStrLn "Warming up the type checker..."
  putStrLn $ "Enter type: "
  tp <- getLine
  putStrLn $ "Enter term: "
  tm <- getLine
  if isTyped (read tp) (read tm)
     then putStrLn "Well typed!"
     else putStrLn "Ill typed!"

