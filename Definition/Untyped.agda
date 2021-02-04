-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --without-K --safe #-}

module Definition.Untyped where

open import Definition.Modality
open import Tools.Nat
open import Tools.Product
open import Tools.List
import Tools.PropositionalEquality as PE

variable
  M : Set
  𝕄 : Modality M
  p q : M

infixl 30 _∙_
infix 30 Π_►_▹_
infix 22 _►_▹▹_
infixr 22 _▹▹_
infix 30 Σ_►_▹_
infix 22 _►_××_
infixr 22 _××_
infix 30 ⟦_⟧_►_▹_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑


-- Typing contexts (snoc-lists, isomorphic to lists).

data Con (A : Set) : Set where
  ε   : Con A              -- Empty context.
  _∙_ : Con A → A → Con A  -- Context extension.

-- Representation of sub elements (in particular sub-terms)

record GenT (A : Set) : Set where
  inductive
  constructor ⟦_,_⟧
  field
    l : Nat -- Shift in de Bruijn index introduced by this term, i.e. number of new variables bound
    t : A   -- Sub term

-- Kinds of terms parameterized over a modality

data Kind (𝕄 : Modality M) : Set where
  Ukind : Kind 𝕄

  Pikind  : M → Kind 𝕄
  Lamkind : M → Kind 𝕄
  Appkind : M → Kind 𝕄

  Sigmakind : M → Kind 𝕄
  Prodkind  :     Kind 𝕄
  Fstkind   :     Kind 𝕄
  Sndkind   :     Kind 𝕄

  Natkind    : Kind 𝕄
  Zerokind   : Kind 𝕄
  Suckind    : Kind 𝕄
  Natreckind : Kind 𝕄

  Unitkind : Kind 𝕄
  Starkind : Kind 𝕄

  Emptykind    :     Kind 𝕄
  Emptyreckind : M → Kind 𝕄

-- Terms are parameterized by a modality and are either:
-- Variables (de Bruijn indices) or
-- Generic terms, formed by their kind and a list of sub-terms

data Term (𝕄 : Modality M) : Set where
  var : (x : Nat) → Term 𝕄
  gen : (k : Kind 𝕄) (c : List (GenT (Term 𝕄))) → Term 𝕄

variable
  e n m t u A B E F G H K : Term 𝕄

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
U : Term 𝕄 -- Universe.
U = gen Ukind []

Π_►_▹_ : {𝕄 : Modality M} (p : M) (A B : Term 𝕄) → Term 𝕄 -- Dependent function type (B is a binder).
Π p ► A ▹ B = gen (Pikind p) (⟦ 0 , A ⟧ ∷ ⟦ 1 , B ⟧ ∷ [])

Σ_►_▹_ : {𝕄 : Modality M} (p : M) (A B : Term 𝕄) → Term 𝕄 -- Dependent sum type (B  is a binder).
Σ p ► A ▹ B = gen (Sigmakind p) (⟦ 0 , A ⟧ ∷ ⟦ 1 , B ⟧ ∷ [])

ℕ     : Term 𝕄 -- Type of natural numbers.
ℕ = gen Natkind []

Empty : Term 𝕄 -- Empty type.
Empty = gen Emptykind []

Unit  : Term 𝕄 -- Unit type.
Unit = gen Unitkind []

-- Lambda-calculus.
lam   : {𝕄 : Modality M} (p : M) (t : Term 𝕄)   → Term 𝕄  -- Function abstraction (binder).
lam p t = gen (Lamkind p) (⟦ 1 , t ⟧ ∷ [])

_►_∘_ : {𝕄 : Modality M} (p : M) (t u : Term 𝕄) → Term 𝕄  -- Application.
p ► t ∘ u = gen (Appkind p) (⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

-- Dependent products
prod : (t u : Term 𝕄) → Term 𝕄
prod t u = gen Prodkind (⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

fst : (t : Term 𝕄) → Term 𝕄
fst t = gen Fstkind (⟦ 0 , t ⟧ ∷ [])

snd : (t : Term 𝕄) → Term 𝕄
snd t = gen Sndkind (⟦ 0 , t ⟧ ∷ [])

-- Introduction and elimination of natural numbers.
zero : Term 𝕄 -- Natural number zero.
zero = gen Zerokind []

suc : (t : Term 𝕄) → Term 𝕄  -- Successor.
suc t = gen Suckind (⟦ 0 , t ⟧ ∷ [])

natrec : (A t u v : Term 𝕄) → Term 𝕄  -- Recursor (A is a binder).
natrec A t u v = gen Natreckind (⟦ 1 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ ⟦ 0 , v ⟧ ∷ [])

-- Unit type
star : Term 𝕄
star = gen Starkind []

-- Empty type
Emptyrec : {𝕄 : Modality M} → (p : M) → (A e : Term 𝕄) → Term 𝕄
Emptyrec p A e = gen (Emptyreckind p) (⟦ 0 , A ⟧ ∷ ⟦ 0 , e ⟧ ∷ [])

-- Binding types

data BindingType : Set where
  BΠ : BindingType
  BΣ : BindingType

⟦_⟧_►_▹_ : {𝕄 : Modality M} → (W : BindingType) → (p : M) → (F G : Term 𝕄) → Term 𝕄
⟦ BΠ ⟧ p ► F ▹ G = Π p ► F ▹ G
⟦ BΣ ⟧ p ► F ▹ G = Σ p ► F ▹ G

-- Injectivity of term constructors w.r.t. propositional equality.

-- If  W p F G = W q H E  then  F = H,  G = E and p = q.

B-PE-injectivity : ∀ W → ⟦ W ⟧ p ► F ▹ G PE.≡ ⟦ W ⟧ q ► H ▹ E
                   → p PE.≡ q × F PE.≡ H × G PE.≡ E
B-PE-injectivity BΠ PE.refl = PE.refl , PE.refl , PE.refl
B-PE-injectivity BΣ PE.refl = PE.refl , PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : suc n PE.≡ suc m → n PE.≡ m
suc-PE-injectivity PE.refl = PE.refl


-- Neutral terms.

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

data Neutral {𝕄 : Modality M} : Term 𝕄 → Set₁ where
  var       : (n : Nat) → Neutral (var n)
  ∘ₙ        : Neutral t → Neutral (p ► t ∘ u)
  fstₙ      : Neutral t → Neutral (fst t)
  sndₙ      : Neutral t → Neutral (snd t)
  natrecₙ   : Neutral n → Neutral (natrec A t u n)
  Emptyrecₙ : Neutral t → Neutral (Emptyrec p A e)


-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Whnf {𝕄 : Modality M} : Term 𝕄 → Set₁ where

  -- Type constructors are whnfs.
  Uₙ     : Whnf U
  Πₙ     : Whnf (Π p ► A ▹ B)
  Σₙ     : Whnf (Σ p ► A ▹ B)
  ℕₙ     : Whnf ℕ
  Unitₙ  : Whnf Unit
  Emptyₙ : Whnf Empty

  -- Introductions are whnfs.
  lamₙ  : Whnf (lam p t)
  zeroₙ : Whnf zero
  sucₙ  : Whnf (suc n)
  starₙ : Whnf star
  prodₙ : Whnf (prod t u)

  -- Neutrals are whnfs.
  ne    : Neutral n → Whnf n


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ne : Neutral K → U PE.≢ K
U≢ne () PE.refl

ℕ≢ne : Neutral K → ℕ PE.≢ K
ℕ≢ne () PE.refl

Empty≢ne : Neutral K → Empty PE.≢ K
Empty≢ne () PE.refl

Unit≢ne : Neutral K → Unit PE.≢ K
Unit≢ne () PE.refl

B≢ne : ∀ W → Neutral K → ⟦ W ⟧ p ► F ▹ G PE.≢ K
B≢ne BΠ () PE.refl
B≢ne BΣ () PE.refl

U≢B : ∀ W → U PE.≢ ⟦ W ⟧ p ► F ▹ G
U≢B BΠ ()
U≢B BΣ ()

ℕ≢B : ∀ W → ℕ PE.≢ ⟦ W ⟧ p ► F ▹ G
ℕ≢B BΠ ()
ℕ≢B BΣ ()

Empty≢B : ∀ W → Empty PE.≢ ⟦ W ⟧ p ► F ▹ G
Empty≢B BΠ ()
Empty≢B BΣ ()

Unit≢B : ∀ W → Unit PE.≢ ⟦ W ⟧ p ► F ▹ G
Unit≢B BΠ ()
Unit≢B BΣ ()

zero≢ne : Neutral t → zero PE.≢ t
zero≢ne () PE.refl

suc≢ne : Neutral t → suc n PE.≢ t
suc≢ne () PE.refl

-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {𝕄 : Modality M} : Term 𝕄 → Set₁ where
  zeroₙ :             Natural zero
  sucₙ  :             Natural (suc t)
  ne    : Neutral n → Natural n


-- A (small) type in whnf is either Π A B, ℕ, or neutral.
-- Large types could also be U.

data Type {𝕄 : Modality M} : Term 𝕄 → Set₁ where
  Πₙ : Type (Π p ► A ▹ B)
  Σₙ : Type (Σ p ► A ▹ B)
  ℕₙ : Type ℕ
  Emptyₙ : Type Empty
  Unitₙ : Type Unit
  ne : Neutral n → Type n

⟦_⟧-type : ∀ (W : BindingType) → Type (⟦ W ⟧ p ► F ▹ G)
⟦ BΠ ⟧-type = Πₙ
⟦ BΣ ⟧-type = Σₙ

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function : Term 𝕄 → Set₁ where
  lamₙ : Function (lam p t)
  ne   : Neutral n → Function n

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product : Term 𝕄 → Set₁ where
  prodₙ : Product (prod t u)
  ne    : Neutral n → Product n

-- These views classify only whnfs.
-- Natural, Type, and Function are a subsets of Whnf.

naturalWhnf : Natural n → Whnf n
naturalWhnf sucₙ = sucₙ
naturalWhnf zeroₙ = zeroₙ
naturalWhnf (ne x) = ne x

typeWhnf : Type A → Whnf A
typeWhnf Πₙ = Πₙ
typeWhnf Σₙ = Σₙ
typeWhnf ℕₙ = ℕₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf Unitₙ = Unitₙ
typeWhnf (ne x) = ne x

functionWhnf : Function t → Whnf t
functionWhnf lamₙ = lamₙ
functionWhnf (ne x) = ne x

productWhnf : Product t → Whnf t
productWhnf prodₙ = prodₙ
productWhnf (ne x) = ne x

⟦_⟧ₙ : (W : BindingType) → Whnf (⟦ W ⟧ p ► F ▹ G)
⟦_⟧ₙ BΠ = Πₙ
⟦_⟧ₙ BΣ = Σₙ


------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Set where
  id    : Wk        -- η : Γ ≤ Γ.
  step  : Wk  → Wk  -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : Wk  → Wk  -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_               :  Wk → Wk → Wk
id     • η′       =  η′
step η • η′       =  step  (η • η′)
lift η • id       =  lift  η
lift η • step η′  =  step  (η • η′)
lift η • lift η′  =  lift  (η • η′)

repeat : ∀ {ℓ} → {A : Set ℓ} → (A → A) → A → Nat → A
repeat f a  0     = a
repeat f a (1+ n) = f (repeat f a n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar η x ∈ dom(Γ).

wkVar : (ρ : Wk) (n : Nat) → Nat
wkVar id       n      = n
wkVar (step ρ) n      = 1+ (wkVar ρ n)
wkVar (lift ρ) 0      = 0
wkVar (lift ρ) (1+ n) = 1+ (wkVar ρ n)

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : (ρ : Wk) (g : List (GenT (Term 𝕄))) → List (GenT (Term 𝕄))
  wkGen ρ [] = []
  wkGen ρ (⟦ l , t ⟧ ∷ g) = ⟦ l , (wk (repeat lift ρ l) t) ⟧ ∷ wkGen ρ g

  wk : (ρ : Wk) (t : Term 𝕄) → Term 𝕄
  wk ρ (var x)   = var (wkVar ρ x)
  wk ρ (gen x c) = gen x (wkGen ρ c)

-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term 𝕄 → Term 𝕄
wk1 = wk (step id)

-- Weakening of a neutral term.

wkNeutral : ∀ ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n)       = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)        = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (fstₙ n)      = fstₙ (wkNeutral ρ n)
wkNeutral ρ (sndₙ n)      = sndₙ (wkNeutral ρ n)
wkNeutral ρ (natrecₙ n)   = natrecₙ (wkNeutral ρ n)
wkNeutral ρ (Emptyrecₙ e) = Emptyrecₙ (wkNeutral ρ e)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ → Natural t → Natural (wk ρ t)
wkNatural ρ sucₙ   = sucₙ
wkNatural ρ zeroₙ  = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ ρ → Type t → Type (wk ρ t)
wkType ρ Πₙ     = Πₙ
wkType ρ Σₙ     = Σₙ
wkType ρ ℕₙ     = ℕₙ
wkType ρ Emptyₙ = Emptyₙ
wkType ρ Unitₙ  = Unitₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ ρ → Function t → Function (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkProduct : ∀ ρ → Product t → Product (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ ρ → Whnf t → Whnf (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ Πₙ      = Πₙ
wkWhnf ρ Σₙ      = Σₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ Unitₙ   = Unitₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ prodₙ   = prodₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ starₙ   = starₙ
wkWhnf ρ (ne x)  = ne (wkNeutral ρ x)

-- Non-dependent version of Π.

_►_▹▹_ : {𝕄 : Modality M} → M → Term 𝕄 → Term 𝕄 → Term 𝕄
p ► A ▹▹ B = Π p ► A ▹ wk1 B

-- Non-dependen version of Π with implicit unit (𝟙) modality.

_▹▹_ : Term 𝕄 → Term 𝕄 → Term 𝕄
_▹▹_ {𝕄 = 𝕄} A B = Π (Modality.𝟙 𝕄) ► A ▹ B

-- Non-dependent products.

_►_××_ : {𝕄 : Modality M} → M → Term 𝕄 → Term 𝕄 → Term 𝕄
p ► A ×× B = Σ p ► A ▹ wk1 B

-- Non-dependent products with implicit unit (𝟙) modality.

_××_ : Term 𝕄 → Term 𝕄 → Term 𝕄
_××_ {𝕄 = 𝕄} A B = Σ (Modality.𝟙 𝕄) ► A ▹ wk1 B


------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : {M : Set} → (𝕄 : Modality M) → Set
Subst 𝕄 = Nat → Term 𝕄

-- Given closed contexts ⊢ Γ and ⊢ Δ,
-- substitutions may be typed via Γ ⊢ σ : Δ meaning that
-- Γ ⊢ σ(x) : (subst σ Δ)(x) for all x ∈ dom(Δ).
--
-- The substitution operation is then typed as follows:
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ subst σ t : subst σ A.
--
-- Although substitutions are untyped, typing helps us
-- to understand the operation on substitutions.

-- We may view σ as the infinite stream σ 0, σ 1, ...

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : subst σ A.

head : Subst 𝕄 → Term 𝕄
head σ = σ 0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst 𝕄 → Subst 𝕄
tail σ n = σ (1+ n)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst 𝕄) (x : Nat) → Term 𝕄
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst 𝕄
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst 𝕄 → Subst 𝕄
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst 𝕄) → Subst 𝕄
liftSubst σ  0     = var 0
liftSubst σ (1+ x) = wk1Subst σ x

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst : Wk → Subst 𝕄
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : (σ : Subst 𝕄) (g : List (GenT (Term 𝕄))) → List (GenT (Term 𝕄))
  substGen σ []              = []
  substGen σ (⟦ l , t ⟧ ∷ g) = ⟦ l , (subst (repeat liftSubst σ l) t) ⟧ ∷ substGen σ g

  subst : (σ : Subst 𝕄) (t : Term 𝕄) → Term 𝕄
  subst σ (var x)   = substVar σ x
  subst σ (gen x c) = gen x (substGen σ c)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst 𝕄 → Term 𝕄 → Subst 𝕄
consSubst σ t  0     = t
consSubst σ t (1+ n) = σ n

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term 𝕄 → Subst 𝕄
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst 𝕄 → Subst 𝕄 → Subst 𝕄
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk → Subst 𝕄 → Subst 𝕄
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst 𝕄 → Wk → Subst 𝕄
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term 𝕄) (s : Term 𝕄) → Term 𝕄
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term 𝕄) (s : Term 𝕄) → Term 𝕄
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t


B-subst : {𝕄 : Modality M} (σ : Subst 𝕄) (W : BindingType) (F G : Term 𝕄) (p : M)
        → subst σ (⟦ W ⟧ p ► F ▹ G) PE.≡ ⟦ W ⟧ p ► (subst σ F) ▹ (subst (liftSubst σ) G)
B-subst σ BΠ F G p = PE.refl
B-subst σ BΣ F G p = PE.refl
