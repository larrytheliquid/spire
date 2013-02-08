open import Spire.Prelude
open import Spire.Value
module Spire.PreValue where

----------------------------------------------------------------------

data PreValue : Set where
  `⊤ `Bool `Type : PreValue
  `Π `Σ : (A B : PreValue) → PreValue
  `const : (B : PreValue) → PreValue

  `tt `true `false : PreValue
  `λ : (f : PreValue) → PreValue
  _`,_ : (a b : PreValue) → PreValue

{-# IMPORT Spire.SurfaceTerm #-}
{-# COMPILED_DATA PreValue Spire.SurfaceTerm.PreValue
  Spire.SurfaceTerm.VUnit Spire.SurfaceTerm.VBool Spire.SurfaceTerm.VType
  Spire.SurfaceTerm.VPi Spire.SurfaceTerm.VSg Spire.SurfaceTerm.Vconst
  Spire.SurfaceTerm.Vtt Spire.SurfaceTerm.Vtrue Spire.SurfaceTerm.Vfalse
  Spire.SurfaceTerm.Vlam Spire.SurfaceTerm.Vpair
  #-}

----------------------------------------------------------------------

data Check Γ (A : Type Γ) : Set where
  well : (x : Value Γ A) → Check Γ A
  ill : (x : PreValue) (msg : String) → Check Γ A

check : ∀ Γ (A : Type Γ) → PreValue → Check Γ A
check Γ `⊤ `tt = well `tt
check Γ `⊤ x = ill x "does not have type ⊤."
check Γ `Bool `true = well `true
check Γ `Bool `false = well `false
check Γ `Bool x = ill x "does not have type Bool."
check Γ (`Π A B) (`λ f) with check (`extend Γ A) B f
check Γ (`Π A B) (`λ f) | well f′ = well (`λ f′)
check Γ (`Π A B) (`λ f) | ill x msg = ill x msg
check Γ (`Π A B) x = ill x "does not have type Π"
check Γ (`Σ A (`const B)) (a `, b) with check Γ A a
check Γ (`Σ A (`const B)) (a `, b) | well a′ with check Γ B b
check Γ (`Σ A (`const B)) (a `, b) | well a′ | well b′ = well (a′ `, b′)
check Γ (`Σ A (`const B)) (a `, b) | well a′ | ill x msg = ill x msg
check Γ (`Σ A (`const B)) (a `, b) | ill x msg = ill x msg
check Γ (`Σ A B) x = ill x "does not have type Σ."
check Γ `Type `⊤ = well (`type `⊤)
check Γ `Type `Bool = well (`type `Bool)
check Γ `Type `Type = well (`type `Type)
check Γ `Type (`Π A B) with check Γ `Type A
check Γ `Type (`Π A B) | well (`type A′) with check (`extend Γ A′) `Type B
check Γ `Type (`Π A B) | well (`type A′) | well (`type B′) = well (`type (`Π A′ B′))
check Γ `Type (`Π A B) | well (`type A′) | ill x msg = ill x msg
check Γ `Type (`Π A B) | ill x msg = ill x msg
check Γ `Type (`Σ A B) with check Γ `Type A
check Γ `Type (`Σ A B) | well (`type A′) with check (`extend Γ A′) `Type B
check Γ `Type (`Σ A B) | well (`type A′) | well (`type B′) = well (`type (`Σ A′ B′))
check Γ `Type (`Σ A B) | well (`type A′) | ill x msg = ill x msg
check Γ `Type (`Σ A B) | ill x msg = ill x msg
check Γ `Type x = ill x "does not have type Type."
check _ _ x = ill x "TODO"

----------------------------------------------------------------------

checkClosed = check `∅

CanonicalTypeChecker = (A a : PreValue) → CheckResult PreValue
typeCheckCanonical : CanonicalTypeChecker
typeCheckCanonical A a with checkClosed `Type A
typeCheckCanonical A a | well (`type A′) with checkClosed A′ a
typeCheckCanonical A a | well (`type A′) | well a′ = well
typeCheckCanonical A a | well (`type A′) | ill x msg = ill x msg
typeCheckCanonical A a | ill x msg = ill x msg


----------------------------------------------------------------------
