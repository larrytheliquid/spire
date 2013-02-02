open import Foreign.Haskell
open import IO.Primitive
module spire where

postulate run : IO Unit
{-# IMPORT Spire.CLI #-}
{-# COMPILED run Spire.CLI.run #-}

main : IO Unit
main = run


