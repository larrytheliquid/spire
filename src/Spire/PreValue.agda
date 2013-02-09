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

  `if_then_else_ : (b x y : PreValue) → PreValue

{-# IMPORT Spire.SurfaceTerm #-}
{-# COMPILED_DATA PreValue Spire.SurfaceTerm.PreValue
  Spire.SurfaceTerm.VUnit Spire.SurfaceTerm.VBool Spire.SurfaceTerm.VType
  Spire.SurfaceTerm.VPi Spire.SurfaceTerm.VSg Spire.SurfaceTerm.Vconst
  Spire.SurfaceTerm.Vtt Spire.SurfaceTerm.Vtrue Spire.SurfaceTerm.Vfalse
  Spire.SurfaceTerm.Vlam Spire.SurfaceTerm.Vpair
  Spire.SurfaceTerm.Vif
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
check Γ A (`if b then c₁ else c₂) with check Γ `Bool b
check Γ A (`if b then c₁ else c₂) | well (`neutral b′) with check Γ A c₁ | check Γ A c₂
check Γ A (`if b then c₁ else c₂) | well (`neutral b′) | well c₁′ | well c₂′ =
  well (`neutral (`if b′ then c₁′ else c₂′))
check Γ A (`if b then c₁ else c₂) | well (`neutral b′) | well c₁′ | ill c₂′ msg = ill c₂′ msg
check Γ A (`if b then c₁ else c₂) | well (`neutral b′) | ill c₁′ msg | _ = ill c₁′ msg
check Γ A (`if b then c₁ else c₂) | well x = ill b "is not neutral."
check Γ A (`if b then c₁ else c₂) | ill x msg = ill x msg
check Γ `Type `⊤ = well (`type `⊤)
check Γ `Type `Bool = well (`type `Bool)
check Γ `Type `Type = well (`type `Type)
check Γ `Type (`Π A B) with check Γ `Type A
check Γ `Type (`Π A B) | well (`type A′) with check (`extend Γ A′) `Type B
check Γ `Type (`Π A B) | well (`type A′) | well (`type B′) = well (`type (`Π A′ B′))
check Γ `Type (`Π A B) | well (`type A′) | well (`neutral B′) = well (`type (`Π A′ (`neutral B′)))
check Γ `Type (`Π A B) | well (`type A′) | ill x msg = ill x msg
check Γ `Type (`Π A B) | well (`neutral A′) with check (`extend Γ (`neutral A′)) `Type B
check Γ `Type (`Π A B) | well (`neutral A′) | well (`type B′) = well (`type (`Π (`neutral A′) B′))
check Γ `Type (`Π A B) | well (`neutral A′) | well (`neutral B′) = well (`type (`Π (`neutral A′) (`neutral B′)))
check Γ `Type (`Π A B) | well (`neutral A′) | ill x msg = ill x msg
check Γ `Type (`Π A B) | ill x msg = ill x msg
check Γ `Type (`Σ A B) with check Γ `Type A
check Γ `Type (`Σ A B) | well (`type A′) with check (`extend Γ A′) `Type B
check Γ `Type (`Σ A B) | well (`type A′) | well (`type B′) = well (`type (`Σ A′ B′))
check Γ `Type (`Σ A B) | well (`type A′) | well (`neutral B′) = well (`type (`Σ A′ (`neutral B′)))
check Γ `Type (`Σ A B) | well (`type A′) | ill x msg = ill x msg
check Γ `Type (`Σ A B) | well (`neutral A′) with check (`extend Γ (`neutral A′)) `Type B
check Γ `Type (`Σ A B) | well (`neutral A′) | well (`type B′) = well (`type (`Σ (`neutral A′) B′))
check Γ `Type (`Σ A B) | well (`neutral A′) | well (`neutral B′) = well (`type (`Σ (`neutral A′) (`neutral B′)))
check Γ `Type (`Σ A B) | well (`neutral A′) | ill x msg = ill x msg
check Γ `Type (`Σ A B) | ill x msg = ill x msg
-- TODO check Γ `Type (`neutral n) = ?
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
typeCheckCanonical A a | well (`neutral a′) = well
typeCheckCanonical A a | ill x msg = ill x msg


----------------------------------------------------------------------
