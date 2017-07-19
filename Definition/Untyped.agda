-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --without-K #-}

module Definition.Untyped where

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


infixl 30 _∙_
infix 30 Πₑ_▹_
infixr 22 _▹▹_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑


-- Typing contexts (snoc-lists, isomorphic to lists).

data Con (A : Set) : Set where
  ε   : Con A               -- Empty context.
  _∙_ : Con A → A → Con A  -- Context extension.

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

mutual
  data Term : Set where
    var : (x : Nat) → Term
    gen : (x : Nat) (c : Con TermGen) → Term

  record TermGen : Set where
    inductive
    constructor ⟦_,_⟧
    field
      l : Nat
      t : Term

Uₑ      : Term                     -- Universe.
Uₑ = gen 0 ε

Πₑ_▹_   : (A B : Term)     → Term  -- Dependent function type (B is a binder).
Πₑ A ▹ B = gen 1 (ε ∙ ⟦ 1 , B ⟧ ∙ ⟦ 0 , A ⟧)

ℕₑ      : Term                     -- Type of natural numbers.
ℕₑ = gen 2 ε

lamₑ    : (t : Term)       → Term  -- Function abstraction (binder).
lamₑ t = gen 3 (ε ∙ ⟦ 1 , t ⟧)

_∘ₑ_    : (t u : Term)     → Term  -- Application.
t ∘ₑ u = gen 4 (ε ∙ ⟦ 0 , u ⟧ ∙ ⟦ 0 , t ⟧)

zeroₑ  : Term                     -- Natural number zero.
zeroₑ = gen 5 ε

sucₑ   : (t : Term)       → Term  -- Successor.
sucₑ t = gen 6 (ε ∙ ⟦ 0 , t ⟧)

natrecₑ : (A t u v : Term) → Term  -- Recursor (A is a binder).
natrecₑ A t u v =
  gen 7 (ε ∙ ⟦ 0 , v ⟧ ∙ ⟦ 0 , u ⟧ ∙ ⟦ 0 , t ⟧ ∙ ⟦ 1 , A ⟧)


-- Injectivity of term constructors w.r.t. propositional equality.

-- If  Π F G = Π H E  then  F = H  and  G = E.

Π-PE-injectivity : ∀ {F G H E} → Πₑ F ▹ G PE.≡ Πₑ H ▹ E → F PE.≡ H × G PE.≡ E
Π-PE-injectivity PE.refl = PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : ∀ {n m} → sucₑ n PE.≡ sucₑ m → n PE.≡ m
suc-PE-injectivity PE.refl = PE.refl


-- Neutral terms.

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

data Neutral : Term → Set where
  var    : ∀ n                     → Neutral (var n)
  _∘_    : ∀ {k u}     → Neutral k → Neutral (k ∘ₑ u)
  natrec : ∀ {C c g k} → Neutral k → Neutral (natrecₑ C c g k)


-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Whnf : Term → Set where

  -- Type constructors are whnfs.
  U    : Whnf Uₑ
  Π    : ∀ {A B} → Whnf (Πₑ A ▹ B)
  ℕ    : Whnf ℕₑ

  -- Introductions are whnfs.
  lam  : ∀ {t} → Whnf (lamₑ t)
  zero : Whnf zeroₑ
  suc  : ∀ {t} → Whnf (sucₑ t)

  -- Neutrals are whnfs.
  ne   : ∀ {n} → Neutral n → Whnf n


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ℕ : Uₑ PE.≢ ℕₑ
U≢ℕ ()

U≢Π : ∀ {F G} → Uₑ PE.≢ Πₑ F ▹ G
U≢Π ()

U≢ne : ∀ {K} → Neutral K → Uₑ PE.≢ K
U≢ne () PE.refl

ℕ≢Π : ∀ {F G} → ℕₑ PE.≢ Πₑ F ▹ G
ℕ≢Π ()

ℕ≢ne : ∀ {K} → Neutral K → ℕₑ PE.≢ K
ℕ≢ne () PE.refl

Π≢ne : ∀ {F G K} → Neutral K → Πₑ F ▹ G PE.≢ K
Π≢ne () PE.refl

zero≢suc : ∀ {n} → zeroₑ PE.≢ sucₑ n
zero≢suc ()

zero≢ne : ∀ {k} → Neutral k → zeroₑ PE.≢ k
zero≢ne () PE.refl

suc≢ne : ∀ {n k} → Neutral k → sucₑ n PE.≢ k
suc≢ne () PE.refl


-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural : Term → Set where
  zero  :                     Natural zeroₑ
  suc   : ∀ {t}             → Natural (sucₑ t)
  ne    : ∀ {n} → Neutral n → Natural n

-- A (small) type in whnf is either Π A B, ℕ, or neutral.
-- Large types could also be U.

data Type : Term → Set where
  Π  : ∀ {A B} → Type (Πₑ A ▹ B)
  ℕ  : Type ℕₑ
  ne : ∀{n} → Neutral n → Type n

-- A whnf of type Π A B is either lam t or neutral.

data Function : Term → Set where
  lam : ∀{t} → Function (lamₑ t)
  ne  : ∀{n} → Neutral n → Function n

-- These views classify only whnfs.
-- Natural, Type, and Function are a subsets of Whnf.

naturalWhnf : ∀ {n} → Natural n → Whnf n
naturalWhnf suc = suc
naturalWhnf zero = zero
naturalWhnf (ne x) = ne x

typeWhnf : ∀ {A} → Type A → Whnf A
typeWhnf Π = Π
typeWhnf ℕ = ℕ
typeWhnf (ne x) = ne x

functionWhnf : ∀ {f} → Function f → Whnf f
functionWhnf lam = lam
functionWhnf (ne x) = ne x

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

_•_                :  Wk → Wk → Wk
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar ρ x ∈ dom(Γ).

wkVar : (ρ : Wk) (n : Nat) → Nat
wkVar id       n       = n
wkVar (step ρ) n       = suc (wkVar ρ n)
wkVar (lift ρ) zero    = zero
wkVar (lift ρ) (suc n) = suc (wkVar ρ n)

-- Weakening of terms.
-- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

lifts : Nat → Wk → Wk
lifts zero ρ = ρ
lifts (suc n) ρ = lift (lifts n ρ)

mutual
  wk : (ρ : Wk) (t : Term) → Term
  wk ρ (var x) = var (wkVar ρ x)
  wk ρ (gen x c) = gen x (wkGen ρ c)

  wkGen : (ρ : Wk) (c : Con TermGen) → Con TermGen
  wkGen ρ ε = ε
  wkGen ρ (c ∙ ⟦ l , t ⟧) = wkGen ρ c ∙ ⟦ l , wk (lifts l ρ) t ⟧

-- wk ρ U                = U
-- wk ρ (Π A ▹ B)        = Π wk ρ A ▹ wk (lift ρ) B
-- wk ρ ℕ                = ℕ
-- wk ρ (var x)          = var (wkVar ρ x)
-- wk ρ (lam t)          = lam (wk (lift ρ) t)
-- wk ρ (t ∘ u)          = wk ρ t ∘ wk ρ u
-- wk ρ zero             = zero
-- wk ρ (suc t)          = suc (wk ρ t)
-- wk ρ (natrec A t u v) = natrec (wk (lift ρ) A) (wk ρ t) (wk ρ u) (wk ρ v)

-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term → Term
wk1 = wk (step id)

-- Weakening of a neutral term.

wkNeutral : ∀ {t} ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n)    = var (wkVar ρ n)
wkNeutral ρ (_∘_ n)    = _∘_ (wkNeutral ρ n)
wkNeutral ρ (natrec n) = natrec (wkNeutral ρ n)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ {t} ρ → Natural t → Natural (wk ρ t)
wkNatural ρ suc    = suc
wkNatural ρ zero   = zero
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ {t} ρ → Type t → Type (wk ρ t)
wkType ρ Π      = Π
wkType ρ ℕ      = ℕ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ {t} ρ → Function t → Function (wk ρ t)
wkFunction ρ lam    = lam
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ {t} ρ → Whnf t → Whnf (wk ρ t)
wkWhnf ρ U      = U
wkWhnf ρ Π      = Π
wkWhnf ρ ℕ      = ℕ
wkWhnf ρ lam    = lam
wkWhnf ρ zero   = zero
wkWhnf ρ suc    = suc
wkWhnf ρ (ne x) = ne (wkNeutral ρ x)

-- Non-dependent version of Π.

_▹▹_ : Term → Term → Term
A ▹▹ B = Πₑ A ▹ wk1 B

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : Set
Subst = Nat → Term

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

head : Subst → Term
head σ = σ 0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst → Subst
tail σ n = σ (suc n)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst) (x : Nat) → Term
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst → Subst
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst) → Subst
liftSubst σ zero    = var zero
liftSubst σ (suc x) = wk1Subst σ x

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst : Wk → Subst
toSubst pr x = var (wkVar pr x)

liftSubsts : Nat → Subst → Subst
liftSubsts zero ρ = ρ
liftSubsts (suc n) ρ = liftSubst (liftSubsts n ρ)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.
mutual
  subst : (σ : Subst) (t : Term) → Term
  subst σ (var x) = substVar σ x
  subst σ (gen x c) = gen x (substGen σ c)

  substGen : (σ : Subst) (c : Con TermGen) → Con TermGen
  substGen σ ε = ε
  substGen σ (c ∙ ⟦ l , t ⟧) = substGen σ c ∙ ⟦ l , subst (liftSubsts l σ) t ⟧

-- subst σ U          = U
-- subst σ (Π A ▹ B) = Π subst σ A ▹ subst (liftSubst σ) B
-- subst σ ℕ          = ℕ
-- subst σ (var x)    = substVar σ x
-- subst σ (lam t)    = lam (subst (liftSubst σ) t)
-- subst σ (t ∘ u)    = (subst σ t) ∘ (subst σ u)
-- subst σ zero       = zero
-- subst σ (suc t)    = suc (subst σ t)
-- subst σ (natrec A t u v) =
--   natrec (subst (liftSubst σ) A) (subst σ t) (subst σ u) (subst σ v)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst → Term → Subst
consSubst σ t zero    = t
consSubst σ t (suc n) = σ n

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term → Subst
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst → Subst → Subst
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk → Subst → Subst
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst → Wk → Subst
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term) (s : Term) → Term
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term) (s : Term) → Term
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t
