-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --without-K --safe #-}

module Definition.Untyped where


open import Definition.Modality

open import Tools.Fin
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


-- Typing contexts (length indexed snoc-lists, isomorphic to lists).
-- Terms added to the context are well scoped in the sense that it cannot
-- contain more unbound variables than can be looked up in the context.

data Con (A : Nat → Set) : Nat → Set where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

private
  variable
    n m ℓ : Nat

-- Representation of sub terms using a list of binding levels

data GenTs (A : Nat → Set) : Nat → List Nat → Set where
  []  : {n : Nat} → GenTs A n []
  _∷_ : {n b : Nat} {bs : List Nat} (t : A (b + n)) (ts : GenTs A n bs) → GenTs A n (b ∷ bs)

-- Kinds are indexed on the number of expected sub terms
-- and the number of new variables bound by each sub term

data Kind : (ns : List Nat) → Set where
  Ukind : Kind []

  Pikind  : Kind (0 ∷ 1 ∷ [])
  Lamkind : Kind (1 ∷ [])
  Appkind : Kind (0 ∷ 0 ∷ [])

  Sigmakind : Kind (0 ∷ 1 ∷ [])
  Prodkind  : Kind (0 ∷ 0 ∷ [])
  Fstkind   : Kind (0 ∷ [])
  Sndkind   : Kind (0 ∷ [])

  Natkind    : Kind []
  Zerokind   : Kind []
  Suckind    : Kind (0 ∷ [])
  Natreckind : Kind (1 ∷ 0 ∷ 0 ∷ 0 ∷ [])

  Unitkind : Kind []
  Starkind : Kind []

  Emptykind    : Kind []
  Emptyreckind : Kind (0 ∷ 0 ∷ [])

-- Terms are indexed by its number of unbound variables and are either:
-- de Bruijn style variables or
-- generic terms, formed by their kind and sub terms

data Term (n : Nat) : Set where
  var : (x : Fin n) → Term n
  gen : {bs : List Nat} (k : Kind bs) (c : GenTs Term n bs) → Term n

private
  variable
    A F H t u v : Term n
    B E G       : Term (1+ n)

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
U      : Term n                      -- Universe.
U = gen Ukind []

Π_▹_ : (A : Term n) (B : Term (1+ n)) → Term n  -- Dependent function type (B is a binder).
Π A ▹ B = gen Pikind (A ∷ B ∷ [])

Σ_▹_ : (A : Term n) (B : Term (1+ n)) → Term n  -- Dependent sum type (B is a binder).
Σ A ▹ B = gen Sigmakind (A ∷ B ∷ [])

ℕ      : Term n                      -- Type of natural numbers.
ℕ = gen Natkind []

Empty : Term n                       -- Empty type
Empty = gen Emptykind []

Unit  : Term n                       -- Unit type
Unit = gen Unitkind []

lam    : (t : Term (1+ n)) → Term n  -- Function abstraction (binder).
lam t = gen Lamkind (t ∷ [])

_∘_    : (t u : Term n) → Term n     -- Application.
t ∘ u = gen Appkind (t ∷ u ∷ [])


prod : (t u : Term n) → Term n       -- Dependent products
prod t u = gen Prodkind (t ∷ u ∷ [])

fst : (t : Term n) → Term n          -- First projection
fst t = gen Fstkind (t ∷ [])

snd : (t : Term n) → Term n          -- Second projection
snd t = gen Sndkind (t ∷ [])

-- Introduction and elimination of natural numbers.
zero   : Term n                      -- Natural number zero.
zero = gen Zerokind []

suc    : (t : Term n)       → Term n -- Successor.
suc t = gen Suckind (t ∷ [])

natrec : (A : Term (1+ n)) (t u v : Term n) → Term n  -- Natural number recursor (A is a binder).
natrec A t u v = gen Natreckind (A ∷ t ∷ u ∷ v ∷ [])


star : Term n                        -- Unit element
star = gen Starkind []

Emptyrec : (A e : Term n) → Term n   -- Empty type recursor
Emptyrec A e = gen Emptyreckind (A ∷ e ∷ [])

-- Binding types

data BindingType : Set where
  BΠ : BindingType
  BΣ : BindingType

⟦_⟧_▹_ : BindingType → Term n → Term (1+ n) → Term n
⟦ BΠ ⟧ F ▹ G = Π F ▹ G
⟦ BΣ ⟧ F ▹ G = Σ F ▹ G

-- Injectivity of term constructors w.r.t. propositional equality.

-- If  W p F G = W q H E  then  F = H,  G = E and p = q.

B-PE-injectivity : ∀ W → ⟦ W ⟧ F ▹ G PE.≡ ⟦ W ⟧ H ▹ E → F PE.≡ H × G PE.≡ E
B-PE-injectivity BΠ PE.refl = PE.refl , PE.refl
B-PE-injectivity BΣ PE.refl = PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : suc t PE.≡ suc u → t PE.≡ u
suc-PE-injectivity PE.refl = PE.refl


-- Neutral terms.

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

data Neutral : Term n → Set where
  var       : (x : Fin n) → Neutral (var x)
  ∘ₙ        : Neutral t   → Neutral (t ∘ u)
  fstₙ      : Neutral t   → Neutral (fst t)
  sndₙ      : Neutral t   → Neutral (snd t)
  natrecₙ   : Neutral v   → Neutral (natrec G t u v)
  Emptyrecₙ : Neutral t   → Neutral (Emptyrec A t)


-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Whnf {n : Nat} : Term n → Set where

  -- Type constructors are whnfs.
  Uₙ     : Whnf U
  Πₙ     : Whnf (Π A ▹ B)
  Σₙ     : Whnf (Σ A ▹ B)
  ℕₙ     : Whnf ℕ
  Unitₙ  : Whnf Unit
  Emptyₙ : Whnf Empty

  -- Introductions are whnfs.
  lamₙ  : Whnf (lam t)
  zeroₙ : Whnf zero
  sucₙ  : Whnf (suc t)
  starₙ : Whnf star
  prodₙ : Whnf (prod t u)

  -- Neutrals are whnfs.
  ne    : Neutral t → Whnf t


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ne : Neutral A → U PE.≢ A
U≢ne () PE.refl

ℕ≢ne : Neutral A → ℕ PE.≢ A
ℕ≢ne () PE.refl

Empty≢ne : Neutral A → Empty PE.≢ A
Empty≢ne () PE.refl

Unit≢ne : Neutral A → Unit PE.≢ A
Unit≢ne () PE.refl

B≢ne : ∀ W → Neutral A → ⟦ W ⟧ F ▹ G PE.≢ A
B≢ne BΠ () PE.refl
B≢ne BΣ () PE.refl

U≢B : ∀ W → U PE.≢ ⟦ W ⟧ F ▹ G
U≢B BΠ ()
U≢B BΣ ()

ℕ≢B : ∀ W → ℕ PE.≢ ⟦ W ⟧ F ▹ G
ℕ≢B BΠ ()
ℕ≢B BΣ ()

Empty≢B : ∀ W → Empty PE.≢ ⟦ W ⟧ F ▹ G
Empty≢B BΠ ()
Empty≢B BΣ ()

Unit≢B : ∀ W → Unit PE.≢ ⟦ W ⟧ F ▹ G
Unit≢B BΠ ()
Unit≢B BΣ ()

zero≢ne : Neutral t → zero PE.≢ t
zero≢ne () PE.refl

suc≢ne : Neutral t → suc u PE.≢ t
suc≢ne () PE.refl

-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {n : Nat} : Term n → Set where
  zeroₙ :             Natural zero
  sucₙ  :             Natural (suc t)
  ne    : Neutral t → Natural t


-- A (small) type in whnf is either Π A B, Σ A B, ℕ, Empty, Unit or neutral.
-- Large types could also be U.

data Type {n : Nat} : Term n → Set where
  Πₙ     :             Type (Π A ▹ B)
  Σₙ     :             Type (Σ A ▹ B)
  ℕₙ     :             Type ℕ
  Emptyₙ :             Type Empty
  Unitₙ  :             Type Unit
  ne     : Neutral t → Type t

⟦_⟧-type : ∀ (W : BindingType) → Type (⟦ W ⟧ F ▹ G)
⟦ BΠ ⟧-type = Πₙ
⟦ BΣ ⟧-type = Σₙ

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function {n : Nat} : Term n → Set where
  lamₙ : Function (lam t)
  ne   : Neutral t → Function t

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product {n : Nat} : Term n → Set where
  prodₙ : Product (prod t u)
  ne    : Neutral t → Product t

-- These views classify only whnfs.
-- Natural, Type, Function and Product are a subsets of Whnf.

naturalWhnf : Natural t → Whnf t
naturalWhnf sucₙ   = sucₙ
naturalWhnf zeroₙ  = zeroₙ
naturalWhnf (ne x) = ne x

typeWhnf : Type A → Whnf A
typeWhnf Πₙ     = Πₙ
typeWhnf Σₙ     = Σₙ
typeWhnf ℕₙ     = ℕₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf Unitₙ  = Unitₙ
typeWhnf (ne x) = ne x

functionWhnf : Function t → Whnf t
functionWhnf lamₙ   = lamₙ
functionWhnf (ne x) = ne x

productWhnf : Product t → Whnf t
productWhnf prodₙ  = prodₙ
productWhnf (ne x) = ne x

⟦_⟧ₙ : (W : BindingType) → Whnf (⟦ W ⟧ F ▹ G)
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

data Wk : Nat → Nat → Set where
  id    : {n : Nat} → Wk n n                      -- η : Γ ≤ Γ.
  step  : {n m : Nat} → Wk m n → Wk (1+ m) n      -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : {n m : Nat} → Wk m n → Wk (1+ m) (1+ n) -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  {l m n : Nat} → Wk l m → Wk m n → Wk l n
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

liftn : {k m : Nat} → Wk k m → (n : Nat) → Wk (n + k) (n + m)
liftn ρ Nat.zero = ρ
liftn ρ (1+ n)   = lift (liftn ρ n)

repeat : {A : Set} → (A → A) → A → Nat → A
repeat f a 0 = a
repeat f a (1+ n) = f (repeat f a n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar η x ∈ dom(Γ).

wkVar : {m n : Nat} (ρ : Wk m n) (x : Fin n) → Fin m
wkVar id x            = x
wkVar (step ρ) x      = (wkVar ρ x) +1
wkVar (lift ρ) x0     = x0
wkVar (lift ρ) (x +1) = (wkVar ρ x) +1

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : {m n : Nat} {bs : List Nat} (ρ : Wk m n) (c : GenTs Term n bs) → GenTs Term m bs
  wkGen ρ []                = []
  wkGen ρ (_∷_ {b = b} t c) = (wk (liftn ρ b) t) ∷ (wkGen ρ c)

  wk : {m n : Nat} (ρ : Wk m n) (t : Term n) → Term m
  wk ρ (var x)   = var (wkVar ρ x)
  wk ρ (gen k c) = gen k (wkGen ρ c)


-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term n → Term (1+ n)
wk1 = wk (step id)

-- Weakening of a neutral term.

wkNeutral : ∀ ρ → Neutral t → Neutral {n} (wk ρ t)
wkNeutral ρ (var n)       = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)        = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (fstₙ n)      = fstₙ (wkNeutral ρ n)
wkNeutral ρ (sndₙ n)      = sndₙ (wkNeutral ρ n)
wkNeutral ρ (natrecₙ n)   = natrecₙ (wkNeutral ρ n)
wkNeutral ρ (Emptyrecₙ e) = Emptyrecₙ (wkNeutral ρ e)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ → Natural t → Natural {n} (wk ρ t)
wkNatural ρ sucₙ   = sucₙ
wkNatural ρ zeroₙ  = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ ρ → Type t → Type {n} (wk ρ t)
wkType ρ Πₙ     = Πₙ
wkType ρ Σₙ     = Σₙ
wkType ρ ℕₙ     = ℕₙ
wkType ρ Emptyₙ = Emptyₙ
wkType ρ Unitₙ  = Unitₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ ρ → Function t → Function {n} (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkProduct : ∀ ρ → Product t → Product {n} (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ ρ → Whnf t → Whnf {n} (wk ρ t)
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

_▹▹_ : Term n → Term n → Term n
A ▹▹ B = Π A ▹ wk1 B

-- Non-dependent products.

_××_ : Term n → Term n → Term n
A ×× B = Σ A ▹ wk1 B

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : Nat → Nat → Set
Subst m n = Fin n → Term m

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

head : Subst m (1+ n) → Term m
head σ = σ x0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst m (1+ n) → Subst m n
tail σ x = σ (x +1)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst m n) (x : Fin n) → Term m
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst n n
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst m n → Subst (1+ m) n
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst m n) → Subst (1+ m) (1+ n)
liftSubst σ x0     = var x0
liftSubst σ (x +1) = wk1Subst σ x

liftSubstn : {k m : Nat} → Subst k m → (n : Nat) → Subst (n + k) (n + m)
liftSubstn σ Nat.zero = σ
liftSubstn σ (1+ n)   = liftSubst (liftSubstn σ n)

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst :  Wk m n → Subst m n
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : {bs : List Nat} (σ : Subst m n) (g : GenTs Term n bs) → GenTs Term m bs
  substGen σ  []      = []
  substGen σ (_∷_ {b = b} t ts) = subst (liftSubstn σ b) t ∷ (substGen σ ts)

  subst : (σ : Subst m n) (t : Term n) → Term m
  subst σ (var x)   = substVar σ x
  subst σ (gen x c) = gen x (substGen σ c)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst m n → Term m → Subst m (1+ n)
consSubst σ t  x0    = t
consSubst σ t (x +1) = σ x

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term n → Subst n (1+ n)
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst ℓ m → Subst m n → Subst ℓ n
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk ℓ m → Subst m n → Subst ℓ n
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst ℓ m → Wk m n → Subst ℓ n
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term (1+ n)) (s : Term n) → Term n
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term (1+ n)) (s : Term (1+ n)) → Term (1+ n)
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t


B-subst : (σ : Subst m n) (W : BindingType) (F : Term n) (G : Term (1+ n))
        → subst σ (⟦ W ⟧ F ▹ G) PE.≡ ⟦ W ⟧ (subst σ F) ▹ (subst (liftSubst σ) G)
B-subst σ BΠ F G = PE.refl
B-subst σ BΣ F G = PE.refl
