module Spire.SurfaceTerm where

data Nat = Zero | Succ Nat
  deriving ( Eq, Show, Read)

data PreTerm =
    Bool | Type
  | Sg PreTerm PreTerm
  | True | False
  | Pair PreTerm PreTerm
  deriving ( Eq, Show, Read )

