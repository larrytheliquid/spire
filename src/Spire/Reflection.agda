{- Ripped from the Agda standard library -}
module Spire.Reflection where
open import Spire.Prelude

------------------------------------------------------------------------
-- Names

-- Names.

postulate Name : Set

{-# BUILTIN QNAME Name #-}

private
  primitive
    primQNameEquality : Name → Name → Bool

-- Equality of names is decidable.

infix 4 _==_ _≟-Name_

private

  _==_ : Name → Name → Bool
  _==_ = primQNameEquality

_≟-Name_ : Decidable Name
s₁ ≟-Name s₂ with s₁ == s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

------------------------------------------------------------------------
-- Terms

-- Is the argument visible (explicit), hidden (implicit), or an
-- instance argument?

data Visibility : Set where
  visible hidden instance : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance   #-}

-- Arguments can be relevant or irrelevant.

data Relevance : Set where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

-- Arguments.

data Arg A : Set where
  arg : (v : Visibility) (r : Relevance) (x : A) → Arg A

{-# BUILTIN ARG    Arg #-}
{-# BUILTIN ARGARG arg #-}

-- Terms.

mutual
  data Term : Set where
    -- Variable applied to arguments.
    var     : (x : ℕ) (args : List (Arg Term)) → Term
    -- Constructor applied to arguments.
    con     : (c : Name) (args : List (Arg Term)) → Term
    -- Identifier applied to arguments.
    def     : (f : Name) (args : List (Arg Term)) → Term
    -- Different kinds of λ-abstraction.
    lam     : (v : Visibility) (t : Term) → Term
    -- Pi-type.
    pi      : (t₁ : Arg Type) (t₂ : Type) → Term
    -- A sort.
    sort    : Sort → Term
    -- Anything else.
    unknown : Term

  data Type : Set where
    el : (s : Sort) (t : Term) → Type

  data Sort : Set where
    -- A Set of a given (possibly neutral) level.
    set     : (t : Term) → Sort
    -- A Set of a given concrete level.
    lit     : (n : ℕ) → Sort
    -- Anything else.
    unknown : Sort

{-# BUILTIN AGDASORT            Sort    #-}
{-# BUILTIN AGDATYPE            Type    #-}
{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
{-# BUILTIN AGDATYPEEL          el      #-}
{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

------------------------------------------------------------------------
-- Definitions

postulate
  -- Function definition.
  Function  : Set
  -- Data type definition.
  Data-type : Set
  -- Record type definition.
  Record    : Set

{-# BUILTIN AGDAFUNDEF    Function  #-}
{-# BUILTIN AGDADATADEF   Data-type #-}
{-# BUILTIN AGDARECORDDEF Record    #-}

-- Definitions.

data Definition : Set where
  function     : Function  → Definition
  data-type    : Data-type → Definition
  record′      : Record    → Definition
  constructor′ : Definition
  axiom        : Definition
  primitive′   : Definition

{-# BUILTIN AGDADEFINITION                Definition   #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function     #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type    #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record′      #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR constructor′ #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom        #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       primitive′   #-}

private
  primitive
    primQNameType        : Name → Type
    primQNameDefinition  : Name → Definition
    primDataConstructors : Data-type → List Name

-- The type of the thing with the given name.

type : Name → Type
type = primQNameType

-- The definition of the thing with the given name.

definition : Name → Definition
definition = primQNameDefinition

-- The constructors of the given data type.

constructors : Data-type → List Name
constructors = primDataConstructors

------------------------------------------------------------------------
-- Term equality is decidable

-- Boring helper functions.

private

  cong₂′ : ∀ {A B C : Set} (f : A → B → C) {x y u v} →
          x ≡ y × u ≡ v → f x u ≡ f y v
  cong₂′ f = uncurry (cong₂ f)

  cong₃′ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v r s} →
           x ≡ y × u ≡ v × r ≡ s → f x u r ≡ f y v s
  cong₃′ f (refl , refl , refl) = refl

  arg₁ : ∀ {A v v′ r r′} {x x′ : A} → arg v r x ≡ arg v′ r′ x′ → v ≡ v′
  arg₁ refl = refl

  arg₂ : ∀ {A v v′ r r′} {x x′ : A} → arg v r x ≡ arg v′ r′ x′ → r ≡ r′
  arg₂ refl = refl

  arg₃ : ∀ {A v v′ r r′} {x x′ : A} → arg v r x ≡ arg v′ r′ x′ → x ≡ x′
  arg₃ refl = refl

  cons₁ : ∀ {A : Set} {x y} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
  cons₁ refl = refl

  cons₂ : ∀ {A : Set} {x y} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  cons₂ refl = refl

  var₁ : ∀ {x x′ args args′} → var x args ≡ var x′ args′ → x ≡ x′
  var₁ refl = refl

  var₂ : ∀ {x x′ args args′} → var x args ≡ var x′ args′ → args ≡ args′
  var₂ refl = refl

  con₁ : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → c ≡ c′
  con₁ refl = refl

  con₂ : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → args ≡ args′
  con₂ refl = refl

  def₁ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → f ≡ f′
  def₁ refl = refl

  def₂ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → args ≡ args′
  def₂ refl = refl

  lam₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
  lam₁ refl = refl

  lam₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
  lam₂ refl = refl

  pi₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
  pi₁ refl = refl

  pi₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
  pi₂ refl = refl

  sort₁ : ∀ {x y} → sort x ≡ sort y → x ≡ y
  sort₁ refl = refl

  set₁ : ∀ {x y} → set x ≡ set y → x ≡ y
  set₁ refl = refl

  lit₁ : ∀ {x y} → lit x ≡ lit y → x ≡ y
  lit₁ refl = refl

  el₁ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → s ≡ s′
  el₁ refl = refl

  el₂ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → t ≡ t′
  el₂ refl = refl

_≟-Visibility_ : Decidable Visibility
visible  ≟-Visibility visible  = yes refl
hidden   ≟-Visibility hidden   = yes refl
instance ≟-Visibility instance = yes refl
visible  ≟-Visibility hidden   = no λ()
visible  ≟-Visibility instance = no λ()
hidden   ≟-Visibility visible  = no λ()
hidden   ≟-Visibility instance = no λ()
instance ≟-Visibility visible  = no λ()
instance ≟-Visibility hidden   = no λ()

_≟-Relevance_ : Decidable Relevance
relevant   ≟-Relevance relevant   = yes refl
irrelevant ≟-Relevance irrelevant = yes refl
relevant   ≟-Relevance irrelevant = no λ()
irrelevant ≟-Relevance relevant   = no λ()

mutual
  infix 4 _≟-Term_ _≟-Args_ _≟-ArgType_

  _≟-ArgTerm_ : Decidable (Arg Term)
  arg e r a ≟-ArgTerm arg e′ r′ a′ =
    mapDec (cong₃′ arg)
             < arg₁ , < arg₂ , arg₃ > >
             (e ≟-Visibility e′ ×-dec r ≟-Relevance r′ ×-dec a ≟-Term a′)

  _≟-ArgType_ : Decidable (Arg Type)
  arg e r a ≟-ArgType arg e′ r′ a′ =
    mapDec (cong₃′ arg)
             < arg₁ , < arg₂ , arg₃ > >
             (e ≟-Visibility e′ ×-dec
              r ≟-Relevance r′  ×-dec
              a ≟-Type a′)

  _≟-Args_ : Decidable (List (Arg Term))
  []       ≟-Args []       = yes refl
  (x ∷ xs) ≟-Args (y ∷ ys) = mapDec (cong₂′ _∷_) < cons₁ , cons₂ > (x ≟-ArgTerm y ×-dec xs ≟-Args ys)
  []       ≟-Args (_ ∷ _)  = no λ()
  (_ ∷ _)  ≟-Args []       = no λ()

  _≟-Term_ : Decidable Term
  var x args ≟-Term var x′ args′ = mapDec (cong₂′ var) < var₁ , var₂ > (x ≟ℕ x′          ×-dec args ≟-Args args′)
  con c args ≟-Term con c′ args′ = mapDec (cong₂′ con) < con₁ , con₂ > (c ≟-Name c′       ×-dec args ≟-Args args′)
  def f args ≟-Term def f′ args′ = mapDec (cong₂′ def) < def₁ , def₂ > (f ≟-Name f′       ×-dec args ≟-Args args′)
  lam v t    ≟-Term lam v′ t′    = mapDec (cong₂′ lam) < lam₁ , lam₂ > (v ≟-Visibility v′ ×-dec t ≟-Term t′)
  pi t₁ t₂   ≟-Term pi t₁′ t₂′   = mapDec (cong₂′ pi)  < pi₁  , pi₂  > (t₁ ≟-ArgType t₁′  ×-dec t₂ ≟-Type t₂′)
  sort s     ≟-Term sort s′      = mapDec (cong sort)  sort₁           (s ≟-Sort s′)
  unknown    ≟-Term unknown      = yes refl

  var x args ≟-Term con c args′ = no λ()
  var x args ≟-Term def f args′ = no λ()
  var x args ≟-Term lam v t     = no λ()
  var x args ≟-Term pi t₁ t₂    = no λ()
  var x args ≟-Term sort _      = no λ()
  var x args ≟-Term unknown     = no λ()
  con c args ≟-Term var x args′ = no λ()
  con c args ≟-Term def f args′ = no λ()
  con c args ≟-Term lam v t     = no λ()
  con c args ≟-Term pi t₁ t₂    = no λ()
  con c args ≟-Term sort _      = no λ()
  con c args ≟-Term unknown     = no λ()
  def f args ≟-Term var x args′ = no λ()
  def f args ≟-Term con c args′ = no λ()
  def f args ≟-Term lam v t     = no λ()
  def f args ≟-Term pi t₁ t₂    = no λ()
  def f args ≟-Term sort _      = no λ()
  def f args ≟-Term unknown     = no λ()
  lam v t    ≟-Term var x args  = no λ()
  lam v t    ≟-Term con c args  = no λ()
  lam v t    ≟-Term def f args  = no λ()
  lam v t    ≟-Term pi t₁ t₂    = no λ()
  lam v t    ≟-Term sort _      = no λ()
  lam v t    ≟-Term unknown     = no λ()
  pi t₁ t₂   ≟-Term var x args  = no λ()
  pi t₁ t₂   ≟-Term con c args  = no λ()
  pi t₁ t₂   ≟-Term def f args  = no λ()
  pi t₁ t₂   ≟-Term lam v t     = no λ()
  pi t₁ t₂   ≟-Term sort _      = no λ()
  pi t₁ t₂   ≟-Term unknown     = no λ()
  sort _     ≟-Term var x args  = no λ()
  sort _     ≟-Term con c args  = no λ()
  sort _     ≟-Term def f args  = no λ()
  sort _     ≟-Term lam v t     = no λ()
  sort _     ≟-Term pi t₁ t₂    = no λ()
  sort _     ≟-Term unknown     = no λ()
  unknown    ≟-Term var x args  = no λ()
  unknown    ≟-Term con c args  = no λ()
  unknown    ≟-Term def f args  = no λ()
  unknown    ≟-Term lam v t     = no λ()
  unknown    ≟-Term pi t₁ t₂    = no λ()
  unknown    ≟-Term sort _      = no λ()

  _≟-Type_ : Decidable Type
  el s t ≟-Type el s′ t′ = mapDec (cong₂′ el) < el₁ , el₂ > (s ≟-Sort s′ ×-dec t ≟-Term t′)

  _≟-Sort_ : Decidable Sort
  set t   ≟-Sort set t′  = mapDec (cong set) set₁ (t ≟-Term t′)
  lit n   ≟-Sort lit n′  = mapDec (cong lit) lit₁ (n ≟ℕ n′)
  unknown ≟-Sort unknown = yes refl
  set _   ≟-Sort lit _   = no λ()
  set _   ≟-Sort unknown = no λ()
  lit _   ≟-Sort set _   = no λ()
  lit _   ≟-Sort unknown = no λ()
  unknown ≟-Sort set _   = no λ()
  unknown ≟-Sort lit _   = no λ()

{-
I think this is consistent because it only introduces new equalities,
rather than directly introducing a new value like ⊥.
This belief is entirely handwavy, but this definition suffices for the
current language prototype.
Further, it is restricted to Set₀ so that parametricity is not broken.
-}
_≟_ : {A : Set₀} → Decidable A
x ≟ y with quoteTerm x ≟-Term quoteTerm y
x ≟ y | yes p = yes trustMe
x ≟ y | no p = no whatever
  where postulate whatever : _
