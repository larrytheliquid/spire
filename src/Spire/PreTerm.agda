open import Data.Empty
open import Data.Unit hiding ( _≟_ )
open import Data.Bool hiding ( _≟_ )
open import Data.Nat hiding ( compare ) renaming ( _≟_ to _≟ℕ_ )
open import Data.String hiding ( _≟_ )
open import Data.Product
open import Data.Maybe
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Spire.Type
open import Spire.Term
module Spire.PreTerm where

----------------------------------------------------------------------

data PreTerm : Set where
  `Bool `Type : PreTerm
  `Σ : PreTerm → PreTerm → PreTerm
  `true `false : PreTerm
  _`,_ : PreTerm → PreTerm → PreTerm

{-# IMPORT Spire.SurfaceTerm #-}
{-# COMPILED_DATA PreTerm Spire.SurfaceTerm.PreTerm Bool Type Sg True False Pair #-}

erase : ∀{Γ ℓ Τ} → Term Γ ℓ Τ → PreTerm
erase `Bool = `Bool
erase (`Σ A B) = `Σ (erase A) (erase B)
erase `Type = `Type
erase `true = `true
erase `false = `false
erase (a `, b) = erase a `, erase b

----------------------------------------------------------------------

data Check (Γ : Context) (ℓ : ℕ) (A : Term Γ (suc ℓ) (const `Type)) : PreTerm → Set where
  well :  (e : Term Γ ℓ (eval A)) → Check Γ ℓ A (erase e)
  ill : ∀{v} (msg : String) → Check Γ ℓ A v

check : (Γ : Context) (ℓ : ℕ) (A : Term Γ (suc ℓ) (const `Type)) (v : PreTerm)
  → Check Γ ℓ A v
check Γ zero X `Bool = ill "Bool is not a value in universe level 0."
check Γ (suc ℓ) X `Bool with compare X `Type
check Γ (suc ℓ) ._ `Bool | just refl = well `Bool
check Γ (suc ℓ) X `Bool | nothing = ill "fail"
check Γ (suc ℓ) X `Type with compare X `Type
check Γ (suc ℓ) ._ `Type | just refl = well `Type
check Γ (suc ℓ) X `Type | nothing = ill "fail"
check Γ zero X `Type = ill "Type is not a value in universe level 0."
check Γ (suc ℓ) X (`Σ A B) with check Γ (suc ℓ) `Type A
check Γ (suc ℓ) X (`Σ ._ B) | well A
  with check (extend Γ (suc ℓ) (λ vs → `⟦ eval A vs ⟧)) (suc ℓ) `Type B
check Γ (suc ℓ) X (`Σ ._ ._) | well A | well B with compare X `Type
check Γ (suc ℓ) .`Type (`Σ ._ ._) | well A | well B | just refl
  = well (`Σ A B)
check Γ (suc ℓ) X (`Σ ._ ._) | well A | well B | nothing =
  ill "Σ is not a value in universe level 0."
check Γ (suc ℓ) X (`Σ ._ B) | well A | ill msg = ill msg
check Γ (suc ℓ) X (`Σ A B) | ill msg = ill msg
check Γ zero X (`Σ A B) = ill "fail"
check Γ ℓ X `true with compare X `Bool
check Γ ℓ ._ `true | just refl = well `true
check Γ ℓ X `true | nothing = ill "fail"
check Γ ℓ X `false with compare X `Bool
check Γ ℓ ._ `false | just refl = well `false
check Γ ℓ X `false | nothing = ill "fail"
check Γ ℓ X (a `, b) with isΣ X
check Γ ℓ .(`Σ A B) (a `, b) | just (A , B , refl) with check Γ ℓ A a
check Γ ℓ .(`Σ A B) (._ `, b) | just (A , B , refl) | well a
  with check (extend Γ (suc ℓ) (λ vs → `⟦ eval A vs ⟧)) ℓ B b
check Γ ℓ .(`Σ A B) (.(erase a) `, .(erase b)) | just (A , B , refl) | well a | well b
  = ill "TODO"
check Γ ℓ .(`Σ A B) (.(erase a) `, b) | just (A , B , refl) | well a | ill msg = ill msg
check Γ ℓ .(`Σ A B) (a `, b) | just (A , B , refl) | ill msg = ill msg
check Γ ℓ X (a `, b) | nothing = ill "Checking a pair against a non-Σ."

----------------------------------------------------------------------

checkClosed = check ∅
checkerLevel = 3

isTyped : PreTerm → PreTerm → Bool
isTyped A a with checkClosed (suc checkerLevel) `Type A
isTyped ._ a | well A with checkClosed checkerLevel A a
isTyped .(erase A) .(erase a) | well A | well a = true
isTyped .(erase A) a | well A | ill msg = false
isTyped A a | ill msg = false
