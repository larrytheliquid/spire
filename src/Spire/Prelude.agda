module Spire.Prelude where
{-# IMPORT Spire.SurfaceTerm #-}

----------------------------------------------------------------------

data ⊥ : Set where
record ⊤ : Set where constructor tt

data Bool : Set where true false : Bool
{-# COMPILED_DATA Bool Bool True False #-}
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

----------------------------------------------------------------------

data Maybe (A : Set) : Set where
  just : (x : A) → Maybe A
  nothing : Maybe A
{-# COMPILED_DATA Maybe Maybe Just Nothing #-}

infixl 1 _<*>_
_<*>_ : {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
just f <*> (just x) = just (f x)
_ <*> _ = nothing

infixl 1 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → B) → Maybe B
just x >>= f = just (f x)
nothing >>= f = nothing

infixl 1 _<$>_
_<$>_ : {A B : Set} → (A → B) → Maybe A → Maybe B
f <$> m = m >>= f

----------------------------------------------------------------------

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set
open Universe public

----------------------------------------------------------------------

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : {A B : Set} {a a′ : A} (f : A → B) → a ≡ a′ → f a ≡ f a′
cong f refl = refl

cong₂ : {A B C : Set} {a a′ : A} {b b′ : B}
  (f : A → B → C) → a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
cong₂ f refl refl = refl

cong₃ : {A B C D : Set} {a a′ : A} {b b′ : B} {c c′ : C}
  (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

----------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc : (n : ℕ) → ℕ

{-# COMPILED_DATA ℕ Spire.SurfaceTerm.Nat Spire.SurfaceTerm.Zero Spire.SurfaceTerm.Succ #-}
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n
{-# BUILTIN NATMINUS _∸_ #-}

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n
{-# BUILTIN NATTIMES _*_ #-}

----------------------------------------------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
{-# COMPILED_DATA List [] [] (:) #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

----------------------------------------------------------------------

postulate Int : Set
{-# BUILTIN INTEGER Int #-}
{-# COMPILED_TYPE Int Int #-}

private
  primitive primIntegerAbs : Int → ℕ

abs = primIntegerAbs

----------------------------------------------------------------------

postulate String : Set
{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

private
 primitive
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool

infixr 5 _++_
_++_ = primStringAppend

infix 4 _==_
_==_ = primStringEquality

----------------------------------------------------------------------

data Unit : Set where unit : Unit
{-# COMPILED_DATA Unit () () #-}

postulate IO : Set → Set
{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

----------------------------------------------------------------------

const : {A B : Set} → A → B → A
const x = λ _ → x

----------------------------------------------------------------------

data CheckResult (A : Set) : Set where
  well : CheckResult A
  ill : A → String → CheckResult A
{-# COMPILED_DATA CheckResult Spire.SurfaceTerm.CheckResult
  Spire.SurfaceTerm.Well Spire.SurfaceTerm.Ill
  #-}

----------------------------------------------------------------------
