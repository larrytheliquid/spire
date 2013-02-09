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

compareType : ∀{Γ} → (A B : Type Γ) → Maybe (A ≡ B)
compareNeutral : ∀{Γ} {A : Type Γ} → (a b : Neutral Γ A) → Maybe (a ≡ b)
compare : ∀{Γ} {A : Type Γ} → (a b : Value Γ A) → Maybe (a ≡ b)

compareType `⊤ `⊤ = just refl
compareType `Bool `Bool = just refl
compareType `Type `Type = just refl
compareType (`neutral A) (`neutral A′) = cong `neutral <$> compareNeutral A A′
compareType (`Π A B) (`Π A′ B′) with compareType A A′
compareType (`Π A B) (`Π .A B′) | just refl with compareType B B′
compareType (`Π A B) (`Π .A .B) | just refl | just refl = just refl
compareType (`Π A B) (`Π .A B′) | just refl | nothing = nothing
compareType (`Π A B) (`Π A′ B′) | nothing = nothing
compareType (`Σ A B) (`Σ A′ B′) with compareType A A′
compareType (`Σ A B) (`Σ .A B′) | just refl with compareType B B′
compareType (`Σ A B) (`Σ .A .B) | just refl | just refl = just refl
compareType (`Σ A B) (`Σ .A B′) | just refl | nothing = nothing
compareType (`Σ A B) (`Σ A′ B′) | nothing = nothing
compareType (`const A) (`const A′) = cong `const <$> compareType A A′
compareType _ _ = nothing

compareNeutral (`if b then c₁ else c₂) (`if b′ then c₁′ else c₂′) =
  cong₃ `if_then_else_ <$> compareNeutral b b′ <*> compare c₁ c₁′ <*> compare c₂ c₂′

compare (`neutral a) (`neutral a′) = cong `neutral <$> compareNeutral a a′
compare (`type A) (`type A′) = cong `type <$> compareType A A′
compare `tt `tt = just refl
compare `true `true = just refl
compare `false `false = just refl
compare (`λ a) (`λ a′) = cong `λ <$> compare a a′
compare (a `, b) (a′ `, b′) = cong₂ _`,_ <$> compare a a′ <*> compare b b′
compare _ _ = nothing
