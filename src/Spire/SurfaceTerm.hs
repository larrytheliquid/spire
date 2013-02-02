module Spire.SurfaceTerm where

data PreTerm =
    Bool | Type
  | Sg PreTerm PreTerm
  | True | False
  | Pair PreTerm PreTerm



