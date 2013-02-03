module Spire.Prelude where
{-# IMPORT Spire.FFI #-}

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

infix 4 _≅_
data _≅_ {A : Set} (a : A) : {B : Set} → B → Set where
  refl : a ≅ a

----------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc : (n : ℕ) → ℕ

{-# COMPILED_DATA ℕ Spire.FFI.Nat Spire.FFI.Zero Spire.FFI.Succ #-}
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

postulate String : Set
{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

private
 primitive
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool

infixr 5 _++_
_++_ : String → String → String
_++_ = primStringAppend

infix 4 _==_
_==_ : String → String → Bool
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