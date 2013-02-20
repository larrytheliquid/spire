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

----------------------------------------------------------------------

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

infixr 2 _×_ 
_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

<_,_> : {A : Set} {B : A → Set} {C : ∀ {x} → B x → Set}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

----------------------------------------------------------------------

const : {A B : Set} → A → B → A
const x = λ _ → x

curry : {A : Set} {B : A → Set} {C : Σ A B → Set} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : {A : Set} {B : A → Set} {C : Σ A B → Set} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

_∘_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set
open Universe public

----------------------------------------------------------------------

{-
This module is hidden because this entire development
doesn't need Agda's universe levels.
The only reason we define it here is so that we can
bind our propositional equality to the built-in.
-}
module _ where
  infixl 6 _⊔_
  postulate
    Lev : Set
    first  : Lev
    next   : Lev → Lev
    _⊔_   : Lev → Lev → Lev
  
  {-# COMPILED_TYPE Lev ()     #-}
  {-# COMPILED first ()           #-}
  {-# COMPILED next  (\_ -> ())   #-}
  {-# COMPILED _⊔_  (\_ _ -> ()) #-}
  {-# BUILTIN LEVEL     Lev #-}
  {-# BUILTIN LEVELZERO first  #-}
  {-# BUILTIN LEVELSUC  next   #-}
  {-# BUILTIN LEVELMAX  _⊔_   #-}
  
----------------------------------------------------------------------

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

cong : ∀ {A B : Set}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set }
        (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

----------------------------------------------------------------------

private
 primitive
   primTrustMe : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y

trustMe : {A : Set} {x y : A} → x ≡ y
trustMe = primTrustMe

----------------------------------------------------------------------

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : (p : P) → Dec P
  no  : (p : ¬ P) → Dec P

Decidable : Set → Set
Decidable A = (x y : A) → Dec (x ≡ y)

infixr 2 _×-dec_
_×-dec_ : {P : Set} {Q : Set} →
          Dec P → Dec Q → Dec (P × Q)
yes p ×-dec yes q = yes (p , q)
no ¬p ×-dec _     = no (¬p ∘ proj₁)
_     ×-dec no ¬q = no (¬q ∘ proj₂)

mapDec : {P Q : Set} →
       (P → Q) → (Q → P) → Dec P → Dec Q
mapDec f g (yes p) = yes (f p)
mapDec f g (no ¬p) = no (¬p ∘ g)


----------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc : (n : ℕ) → ℕ

{-# COMPILED_DATA ℕ Spire.SurfaceTerm.Nat Spire.SurfaceTerm.Zero Spire.SurfaceTerm.Succ #-}
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

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

infix 4 _≟ℕ_
_≟ℕ_ : Decidable ℕ
zero  ≟ℕ zero   = yes refl
suc m ≟ℕ suc n  with m ≟ℕ n
suc m ≟ℕ suc .m | yes refl = yes refl
suc m ≟ℕ suc n  | no prf   = no (prf ∘ cong pred)
zero  ≟ℕ suc n  = no λ()
suc m ≟ℕ zero   = no λ()

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

infix 4 _==String_
_==String_ = primStringEquality

----------------------------------------------------------------------

data Unit : Set where unit : Unit
{-# COMPILED_DATA Unit () () #-}

postulate IO : Set → Set
{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

----------------------------------------------------------------------
