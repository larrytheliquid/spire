open import Spire.Prelude
open import Spire.PreValue
module spire where

postulate run : CanonicalTypeChecker → IO Unit
{-# IMPORT Spire.CLI #-}
{-# COMPILED run Spire.CLI.run #-}

main : IO Unit
main = run typeCheckCanonical


