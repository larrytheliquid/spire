open import Spire.Prelude
module Spire.Value where

----------------------------------------------------------------------

data Context : Set
data Type : Context → Set
data Value (Γ : Context) : Type Γ → Set

----------------------------------------------------------------------

data Context where
  `∅ : Context
  `extend : (Γ : Context) → Type Γ → Context

_→TypeΓ : ∀{Γ} → (A : Type Γ) → Set
A →TypeΓ = Type (`extend _ A)

----------------------------------------------------------------------

data Type where
  `⊤ `Bool `Type : ∀{Γ} → Type Γ
  `Π `Σ : ∀{Γ} (A : Type Γ) → (A →TypeΓ) → Type Γ
  `const : ∀{Γ A} → Type Γ → A →TypeΓ

data Value Γ where
  `type : Type Γ → Value Γ `Type
  `tt : Value Γ `⊤
  `true `false : Value Γ `Bool
  `λ : ∀{A} {B : A →TypeΓ}
    → Value (`extend Γ A) B
    → Value Γ (`Π A B)
  _`,_ : ∀{A B}
    (a : Value Γ A)
    → Value Γ B
    → Value Γ (`Σ A (`const B))

----------------------------------------------------------------------
