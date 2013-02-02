open import Foreign.Haskell
open import IO.Primitive
module Spire.Main where

postulate run : IO Unit
{-# IMPORT Spire.CLI #-}
{-# COMPILED run Spire.CLI.run #-}

main : IO Unit
main = run
