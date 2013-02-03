open import Spire.Prelude
open import Spire.PreTerm
module spire where

postulate run : (PreTerm → PreTerm → Bool) → IO Unit
{-# IMPORT Spire.CLI #-}
{-# COMPILED run Spire.CLI.run #-}

main : IO Unit
main = run isTyped


