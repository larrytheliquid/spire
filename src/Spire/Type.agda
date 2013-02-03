open import Spire.Prelude
module Spire.Type where

----------------------------------------------------------------------

data TypeForm (U : Universe) : Set
⟦_/_⟧ : (U : Universe) → TypeForm U → Set

data TypeForm U where
  `⊥ `⊤ `Bool `ℕ `String : TypeForm U
  `Π `Σ : (A : TypeForm U)
    (B : ⟦ U / A ⟧ → TypeForm U)
    → TypeForm U
  `Type : TypeForm U
  `⟦_⟧ : Codes U → TypeForm U

⟦ U / `⊥ ⟧ = ⊥
⟦ U / `⊤ ⟧ = ⊤
⟦ U / `Bool ⟧ = Bool
⟦ U / `ℕ ⟧ = ℕ
⟦ U / `String ⟧ = String
⟦ U / `Π A B ⟧ = (a : ⟦ U / A ⟧) → ⟦ U / B a ⟧
⟦ U / `Σ A B ⟧ = Σ ⟦ U / A ⟧ (λ a → ⟦ U / B a ⟧)
⟦ U / `Type ⟧ = Codes U
⟦ U / `⟦ A ⟧ ⟧ = Meaning U A

----------------------------------------------------------------------

_`→_ : ∀{U} (A B : TypeForm U) → TypeForm U
A `→ B = `Π A λ _ → B

Level : (ℓ : ℕ) → Universe
Level zero = record { Codes = ⊥ ; Meaning = λ() }
Level (suc ℓ) = record { Codes = TypeForm (Level ℓ)
                       ; Meaning = ⟦_/_⟧ (Level ℓ) }

Type : ℕ → Set
Type ℓ = TypeForm (Level ℓ)

infix 0 ⟦_∣_⟧
⟦_∣_⟧ : (ℓ : ℕ) → Type ℓ → Set
⟦ ℓ ∣ A ⟧ = ⟦ Level ℓ / A ⟧

----------------------------------------------------------------------

case⊥ : {A : Set} → ⊥ → A
case⊥ ()

caseBool : (P : Bool → Set)
  (pt : P true)
  (pf : P false)
  → (b : Bool) → P b
caseBool P pt pf true = pt
caseBool P pt pf false = pf

caseℕ : (P : ℕ → Set)
  (pz : P zero)
  (ps : (n : ℕ) → P n → P (suc n))
  → (n : ℕ) → P n
caseℕ P pz ps zero = pz
caseℕ P pz ps (suc n) = ps n (caseℕ P pz ps n)

lift : ∀{ℓ} {A : Type ℓ} → ⟦ ℓ ∣ A ⟧ → ⟦ suc ℓ ∣ `⟦ A ⟧ ⟧
lift x = x

lower : ∀{ℓ} {A : Type ℓ} → ⟦ suc ℓ ∣ `⟦ A ⟧ ⟧ → ⟦ ℓ ∣ A ⟧
lower x = x

caseType : (P : (ℓ : ℕ) (A : Type ℓ) → Set)
  → ((ℓ : ℕ) → P ℓ `⊥)
  → ((ℓ : ℕ) → P ℓ `⊤)
  → ((ℓ : ℕ) → P ℓ `Bool)
  → ((ℓ : ℕ) → P ℓ `ℕ)
  → ((ℓ : ℕ) → P ℓ `String)
  → ((ℓ : ℕ) (A : Type ℓ) (B : ⟦ ℓ ∣ A ⟧ → Type ℓ)
    (rec₁ : P ℓ A)
    (rec₂ : (a : ⟦ ℓ ∣ A ⟧) → P ℓ (B a))
    → P ℓ (`Π A B))
  → ((ℓ : ℕ) (A : Type ℓ) (B : ⟦ ℓ ∣ A ⟧ → Type ℓ)
    (rec₁ : P ℓ A)
    (rec₂ : (a : ⟦ ℓ ∣ A ⟧) → P ℓ (B a))
    → P ℓ (`Σ A B))
  → ((ℓ : ℕ) → P ℓ `Type)
  → ((ℓ : ℕ) (A : Type ℓ) (rec : P ℓ A) → P (suc ℓ) `⟦ A ⟧)
  → (ℓ : ℕ) (A : Type ℓ) → P ℓ A
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ `⊥ = p⊥ ℓ
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ `⊤ = p⊤ ℓ
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ `Bool = pBool ℓ
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ `ℕ = pℕ ℓ
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ `String = pString ℓ
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ (`Π A B) =
  pΠ ℓ A B (caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ A)
  (λ a → caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ (B a))
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ (`Σ A B) =
  pΣ ℓ A B (caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ A)
  (λ a → caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ (B a))
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ `Type = pType ℓ
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ zero `⟦ () ⟧
caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ (suc ℓ) `⟦ A ⟧ =
  p⟦A⟧ ℓ A (caseType P p⊥ p⊤ pBool pℕ pString pΠ pΣ pType p⟦A⟧ ℓ A)

----------------------------------------------------------------------
