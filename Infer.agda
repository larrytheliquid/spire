open import Data.Empty
open import Data.Unit hiding ( _≟_ )
open import Data.Bool hiding ( _≟_ )
open import Data.Nat hiding ( compare ) renaming ( _≟_ to _≟ℕ_ )
open import Data.String hiding ( _≟_ )
open import Data.Product
open import Data.Maybe
open import Function
open import Relation.Nullary
open import Relation.Binary.HeterogeneousEquality
module Infer where

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set
open Universe

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

data Context : Set
Environment : Context → Set

ScopedType : Context → ℕ → Set
ScopedType Γ ℓ = Environment Γ → Type ℓ

data Context where
  ∅ : Context
  extend : (Γ : Context) (ℓ : ℕ) (Τ : ScopedType Γ ℓ) → Context

Environment ∅ = ⊤
Environment (extend Γ ℓ Τ) = Σ (Environment Γ) λ vs → ⟦ ℓ ∣ Τ vs ⟧

data InContext :  (Γ : Context) (ℓ : ℕ) (Τ : ScopedType Γ ℓ) → Set where
 here : ∀{Γ ℓ Τ} → InContext (extend Γ ℓ Τ) ℓ λ vs → Τ (proj₁ vs)
 there : ∀{Γ ℓ Τ ℓ′} {Τ′ : ScopedType Γ ℓ′}
   → InContext Γ ℓ Τ → InContext (extend Γ ℓ′ Τ′) ℓ λ vs → Τ (proj₁ vs)

lookup : ∀{Γ ℓ Τ} → InContext Γ ℓ Τ → (vs : Environment Γ) → ⟦ ℓ ∣ Τ vs ⟧
lookup here (vs , v) = v
lookup (there p) (vs , v) = lookup p vs

ScopedType₂ : (Γ : Context) (ℓ : ℕ) → ScopedType Γ ℓ → Set
ScopedType₂ Γ ℓ Τ = (vs : Environment Γ) → ⟦ ℓ ∣ Τ vs ⟧ → Type ℓ

----------------------------------------------------------------------

data Term (Γ : Context) : (ℓ : ℕ)
  → ScopedType Γ ℓ → Set
eval : ∀{Γ ℓ Τ} → Term Γ ℓ Τ
  → (vs : Environment Γ) → ⟦ ℓ ∣ Τ vs ⟧

data Term Γ where
  {- Type Formation -}
  `Bool : ∀{ℓ}
    → Term Γ (suc ℓ) (const `Type)
  `Σ : ∀{ℓ}
    (A : Term Γ (suc ℓ) (const `Type))
    (B : Term (extend Γ (suc ℓ)  λ vs →
      `⟦ eval A vs ⟧) (suc ℓ) (const `Type))
    → Term Γ (suc ℓ) (const `Type)
  `Type : ∀{ℓ} → Term Γ (suc ℓ) (const `Type)
  -- `⟦_⟧ : ∀{ℓ}
  --   → Term Γ ℓ (const `Type)
  --   → Term Γ (suc ℓ) (const `Type)

  {- Value Introduction -}
  -- `lift : ∀{ℓ Τ} (e : Term Γ ℓ Τ)
  --  → Term Γ (suc ℓ) λ vs → `⟦ Τ vs ⟧
  `true `false : ∀{ℓ} → Term Γ ℓ (const `Bool)
  _`,_ : ∀{ℓ Τ} {Τ′ : ScopedType₂ Γ ℓ Τ}
   (e : Term Γ ℓ Τ)
   (e′ : Term Γ ℓ λ vs → Τ′ vs (eval e vs))
   → Term Γ ℓ λ vs → `Σ (Τ vs) λ v → Τ′ vs v

  {- Value Elimination -}
  -- `lower : ∀{ℓ Τ}
  --   (e : Term Γ (suc ℓ) λ vs → `⟦ Τ vs ⟧)
  --   → Term Γ ℓ Τ
  -- `caseBool : ∀{ℓ}
  --   (P : Term (extend Γ ℓ (const `Bool))
  --     (suc ℓ) (const `Type))
  --   (e₁ : Term Γ ℓ λ vs → eval P (vs , true))
  --   (e₂ : Term Γ ℓ λ vs → eval P (vs , false))
  --   (e : Term Γ ℓ (const `Bool))
  --   → Term Γ ℓ λ vs → eval P (vs , eval e vs)
  `proj₁ : ∀{ℓ Τ} {Τ′ : ScopedType₂ Γ ℓ Τ}
    (e : Term Γ ℓ (λ vs → `Σ (Τ vs) (Τ′ vs)))
    → Term Γ ℓ Τ
  -- `proj₂ : ∀{ℓ}
  --   {Τ : ScopedType Γ ℓ} {Τ′ : ScopedType₂ Γ ℓ Τ}
  --   (e : Term Γ ℓ (λ vs → `Σ (Τ vs) (Τ′ vs)))
  --   → Term Γ ℓ λ vs → Τ′ vs (proj₁ (eval e vs))

{- Type Formation -}
eval `Bool vs = `Bool
eval (`Σ A B) vs = `Σ (eval A vs) λ v → eval B (vs , v)
eval `Type vs = `Type
-- eval `⟦ A ⟧ vs = `⟦ eval A vs ⟧

{- Value Introduction -}
eval `true vs = true
eval `false vs = false
eval (e `, e′) vs = eval e vs , eval e′ vs

{- Value Elimination -}
-- eval (`lower e) vs = eval e vs
-- eval (`caseBool {ℓ} P e₁ e₂ e) vs =
--   caseBool (λ b → ⟦ ℓ ∣ eval P (vs , b) ⟧)
--   (eval e₁ vs) (eval e₂ vs) (eval e vs)
eval (`proj₁ e) vs = proj₁ (eval e vs)
-- eval (`proj₂ e) vs = proj₂ (eval e vs)

----------------------------------------------------------------------

compare : ∀{Γ ℓ A B} (a : Term Γ ℓ A) (b : Term Γ ℓ B) → Maybe (a ≅ b)
compare `Bool `Bool = just refl
compare `Type `Type = just refl
compare `true `true = just refl
compare `false `false = just refl
compare (`Σ A B) (`Σ A′ B′) with compare A A′
compare (`Σ A B) (`Σ ._ B′) | just refl with compare B B′
compare (`Σ A B) (`Σ ._ ._) | just refl | just refl = just refl
compare (`Σ A B) (`Σ ._ B′) | just refl | nothing = nothing
compare (`Σ A B) (`Σ A′ B′) | nothing = nothing
compare (`proj₁ ab) (`proj₁ ab′) with compare ab ab′
compare (`proj₁ ab) (`proj₁ ab′) | just p = nothing -- just (cong `proj₁ p)
compare (`proj₁ ab) (`proj₁ ab′) | nothing = nothing
compare _ _ = nothing

----------------------------------------------------------------------

data PreTerm : Set where
  `Bool : PreTerm
  `Σ : PreTerm → PreTerm → PreTerm
  `Type : PreTerm
  `true `false : PreTerm
  _`,_ : PreTerm → PreTerm → PreTerm
  `proj₁ : PreTerm → PreTerm

erase : ∀{Γ ℓ Τ} → Term Γ ℓ Τ → PreTerm
erase `Bool = `Bool
erase (`Σ A B) = `Σ (erase A) (erase B)
erase `Type = `Type
erase `true = `true
erase `false = `false
erase (a `, b) = erase a `, erase b
erase (`proj₁ ab) = `proj₁ (erase ab)

data Infer (Γ : Context) (ℓ : ℕ) : PreTerm → Set where
  well : (A : Term Γ (suc ℓ) (const `Type)) (e : Term Γ ℓ (eval A)) → Infer Γ ℓ (erase e)
  ill : ∀{v} (msg : String) → Infer Γ ℓ v

isΣ : ∀{Γ ℓ Τ} (X : Term Γ (suc ℓ) Τ) → Maybe (Σ (Term Γ (suc ℓ) (const `Type))
  (λ A → Σ (Term (extend Γ (suc ℓ)  λ vs →
      `⟦ eval A vs ⟧) (suc ℓ) (const `Type))
     (λ B → _≅_ X {B = Term Γ (suc ℓ) (const `Type)} (`Σ A B))))
isΣ (`Σ A B) = just (A , B , refl)
isΣ X = nothing

infer : (Γ : Context) (ℓ : ℕ) (v : PreTerm) → Infer Γ ℓ v
infer Γ (suc ℓ) `Bool = well `Type `Bool
infer Γ zero `Bool = ill "Bool is not a value in universe level 0."
infer Γ (suc ℓ) (`Σ A B) with infer Γ (suc ℓ) A
infer Γ (suc ℓ) (`Σ ._ B) | well A a with compare A `Type
infer Γ (suc ℓ) (`Σ ._ B) | well ._ A | just refl
  with infer (extend Γ (suc ℓ)  λ vs → `⟦ eval A vs ⟧) (suc ℓ) B
infer Γ (suc ℓ) (`Σ ._ ._) | well .`Type A | just refl | well X B
  with compare `Type X
infer Γ (suc ℓ) (`Σ ._ ._) | well ._ A | just refl | well ._ B | just refl
  = well `Type (`Σ A B)
infer Γ (suc ℓ) (`Σ ._ ._) | well ._ A | just refl | well X B | nothing
  = ill "B of Σ A B is not a type."
infer Γ (suc ℓ) (`Σ ._ B) | well .`Type A | just refl | ill msg
  = ill "Type of B of Σ A B is not a type."
infer Γ (suc ℓ) (`Σ ._ B) | well A a | nothing = ill "A of Σ A B is not a type."
infer Γ (suc ℓ) (`Σ A B) | ill msg = ill msg
infer Γ zero (`Σ A B) = ill "Σ is not a value in universe level 0."
infer Γ (suc ℓ) `Type = well `Type `Type
infer Γ zero `Type = ill "Type is not a value in universe level 0."
infer Γ ℓ `true = well `Bool `true
infer Γ ℓ `false = well `Bool `false
infer Γ ℓ (a `, b) with infer Γ ℓ a
infer Γ ℓ (._ `, b) | well A a with infer Γ ℓ b 
infer Γ ℓ (.(erase a) `, .(erase b)) | well A a | well B b with compare B `Type
infer Γ ℓ (.(erase a) `, .(erase b)) | well A a | well .`Type b | just refl = well (`Σ A `Type) (a `, b)
infer Γ ℓ (.(erase a) `, .(erase b)) | well A a | well B b | nothing = ill "B of Σ A B in pair not a type."
infer Γ ℓ (.(erase a) `, b) | well A a | ill msg = ill msg
infer Γ ℓ (a `, b) | ill msg = ill msg
infer Γ ℓ (`proj₁ ab) with infer Γ ℓ ab
infer Γ ℓ (`proj₁ ._) | well AB ab with isΣ AB
infer Γ ℓ (`proj₁ ._) | well ._ ab | just (A , B , refl) = well A (`proj₁ ab)
infer Γ ℓ (`proj₁ ._) | well AB ab | nothing = ill "proj₁ of non-Σ"
infer Γ ℓ (`proj₁ ab) | ill msg = ill msg
