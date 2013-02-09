open import Spire.Prelude
module Spire.Value where

----------------------------------------------------------------------

data Context : Set
data Type : Context → Set
data Value (Γ : Context) : Type Γ → Set
data Neutral (Γ : Context) : Type Γ → Set

----------------------------------------------------------------------

data Context where
  `∅ : Context
  `extend : (Γ : Context) → Type Γ → Context

----------------------------------------------------------------------

data Type where
  `⊤ `Bool `Type : ∀{Γ} → Type Γ
  `neutral : ∀{Γ} → Neutral Γ `Type → Type Γ
  `Π `Σ : ∀{Γ} (A : Type Γ) → Type (`extend Γ A) → Type Γ
  `const : ∀{Γ A} → Type Γ → Type (`extend Γ A)

----------------------------------------------------------------------

data Value Γ where
  `neutral : ∀{A} → Neutral Γ A → Value Γ A
  `type : Type Γ → Value Γ `Type
  `tt : Value Γ `⊤
  `true `false : Value Γ `Bool
  `λ : ∀{A} {B : Type (`extend Γ A)}
    → Value (`extend Γ A) B
    → Value Γ (`Π A B)
  _`,_ : ∀{A B}
    (a : Value Γ A)
    → Value Γ B
    → Value Γ (`Σ A (`const B))

----------------------------------------------------------------------

data Neutral Γ where
  `if_then_else_ : ∀{A}
    → Neutral Γ `Bool
    → Value Γ A
    → Value Γ A
    → Neutral Γ A


----------------------------------------------------------------------
