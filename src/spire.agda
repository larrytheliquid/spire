open import Foreign.Haskell
open import IO.Primitive
open import Data.Bool
open import Spire.PreTerm
module spire where

postulate run : (PreTerm → PreTerm → Bool) → IO Unit
{-# IMPORT Spire.CLI #-}
{-# COMPILED run Spire.CLI.run #-}

main : IO Unit
main = run isTyped


