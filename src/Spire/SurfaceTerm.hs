module Spire.SurfaceTerm where

data Nat = Zero | Succ Nat
  deriving ( Eq, Show, Read)

data PreValue =
    VUnit | VBool | VType
  | VPi PreValue PreValue
  | VSg PreValue PreValue
  | Vconst PreValue

  | Vtt | Vtrue | Vfalse
  | Vlam PreValue
  | Vpair PreValue PreValue
  deriving ( Eq, Show, Read )

data CheckResult a = Well | Ill a String

type CanonicalTypeChecker = PreValue -> PreValue -> CheckResult PreValue

pshow :: PreValue -> String
pshow VUnit = "⊤"
pshow VBool = "Bool"
pshow VType = "Type"
pshow (VPi a b) = "Π " ++ pshow a ++ " " ++ pshow b
pshow (VSg a b) = "Σ " ++ pshow a ++ " " ++ pshow b
pshow (Vconst a) = "const " ++ pshow a
pshow Vtt = "tt"
pshow Vtrue = "true"
pshow Vfalse = "false"
pshow (Vlam f) = "λ → " ++ pshow f
pshow (Vpair a b) = show a ++ " , " ++ show b

