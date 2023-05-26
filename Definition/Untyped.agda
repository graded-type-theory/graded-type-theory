------------------------------------------------------------------------
-- Raw terms, weakening (renaming) and substitution.
------------------------------------------------------------------------

module Definition.Untyped {a} (M : Set a) where

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.List
open import Tools.PropositionalEquality as PE hiding (subst)

-- Some definitions that do not depend on M are re-exported from
-- Definition.Untyped.NotParametrised.

open import Definition.Untyped.NotParametrised public

private
  variable
    p p′ p₁ p₂ q q₁ q₂ r : M
    n m ℓ : Nat
    b : BinderMode
    s : SigmaMode
    bs bs′ : List _
    ts ts′ : GenTs _ _ _

infix 30 ΠΣ⟨_⟩_,_▷_▹_
infix 30 Π_,_▷_▹_
infix 30 Σ_,_▷_▹_
infix 30 Σₚ_,_▷_▹_
infix 30 Σᵣ_,_▷_▹_
infix 30 Σ⟨_⟩_,_▷_▹_
infix 30 ⟦_⟧_▹_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑
infix 25 _[_,_]
infix 25 _[_]↑²

-- Kinds are indexed on the number of expected sub terms
-- and the number of new variables bound by each sub term

data Kind : (ns : List Nat) → Set a where
  Ukind : Kind []

  Binderkind : (b : BinderMode) (p q : M) → Kind (0 ∷ 1 ∷ [])

  Lamkind : (p : M)   → Kind (1 ∷ [])
  Appkind : (p : M)   → Kind (0 ∷ 0 ∷ [])

  Prodkind    : SigmaMode → (p : M) → Kind (0 ∷ 0 ∷ [])
  Fstkind     : (p : M) → Kind (0 ∷ [])
  Sndkind     : (p : M) → Kind (0 ∷ [])
  Prodreckind : (r p q : M) → Kind (1 ∷ 0 ∷ 2 ∷ [])

  Natkind    : Kind []
  Zerokind   : Kind []
  Suckind    : Kind (0 ∷ [])
  Natreckind : (p q r : M) → Kind (1 ∷ 0 ∷ 2 ∷ 0 ∷ [])

  Unitkind : Kind []
  Starkind : Kind []

  Emptykind    : Kind []
  Emptyreckind : (p : M) → Kind (0 ∷ 0 ∷ [])

-- The type of terms is parametrised by the number of free variables.
-- A term is either a variable (a de Bruijn index) or a generic term,
-- consisting of a kind and a list of sub-terms.

data Term (n : Nat) : Set a where
  var : (x : Fin n) → Term n
  gen : {bs : List Nat} (k : Kind bs) (ts : GenTs Term n bs) → Term n

private
  variable
    A F H t u t′ u′ v : Term n
    B E G             : Term (1+ n)
    k k′              : Kind _

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
pattern U = gen Ukind []
pattern ℕ = gen Natkind []
pattern Empty = gen Emptykind []
pattern Unit = gen Unitkind []

pattern ΠΣ⟨_⟩_,_▷_▹_ b p q F G = gen (Binderkind b p q) (F ∷ G ∷ [])
pattern Π_,_▷_▹_ p q F G = gen (Binderkind BMΠ p q) (F ∷ G ∷ [])
pattern Σₚ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ Σₚ) p q) (F ∷ G ∷ [])
pattern Σᵣ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ Σᵣ) p q) (F ∷ G ∷ [])
pattern Σ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ _) p q) (F ∷ G ∷ [])
pattern Σ⟨_⟩_,_▷_▹_ s p q F G =
  gen (Binderkind (BMΣ s) p q) (F ∷ G ∷ [])

pattern lam p t = gen (Lamkind p) (t ∷ [])
pattern _∘⟨_⟩_ t p u = gen (Appkind p) (t ∷ u ∷ [])
pattern _∘_ t u = gen (Appkind _) (t ∷ u ∷ [])

pattern prodₚ p t u = gen (Prodkind Σₚ p) (t ∷ u ∷ [])
pattern prodᵣ p t u = gen (Prodkind Σᵣ p) (t ∷ u ∷ [])
pattern prod m p t u = gen (Prodkind m p) (t ∷ u ∷ [])
pattern prod! t u = gen (Prodkind _ _) (t ∷ u ∷ [])
pattern fst p t = gen (Fstkind p) (t ∷ [])
pattern snd p t = gen (Sndkind p) (t ∷ [])
pattern prodrec r p q A t u = gen (Prodreckind r p q) (A ∷ t ∷ u ∷ [])

pattern zero = gen Zerokind []
pattern suc t = gen Suckind (t ∷ [])
pattern natrec p q r A z s n = gen (Natreckind p q r) (A ∷ z ∷ s ∷ n ∷ [])

pattern star = gen Starkind []
pattern Emptyrec p A t = gen (Emptyreckind p) (A ∷ t ∷ [])


data BindingType : Set a where
  BM : BinderMode → (p q : M) → BindingType

pattern BΠ p q = BM BMΠ p q
pattern BΠ! = BΠ _ _
pattern BΣ s p q = BM (BMΣ s) p q
pattern BΣ! = BΣ _ _ _
pattern BΣᵣ = BΣ Σᵣ _ _
pattern BΣₚ = BΣ Σₚ _ _

⟦_⟧_▹_ : BindingType → Term n → Term (1+ n) → Term n
⟦ BΠ p q   ⟧ F ▹ G = Π p , q ▷ F ▹ G
⟦ BΣ m p q ⟧ F ▹ G = Σ⟨ m ⟩ p , q ▷ F ▹ G

-- Injectivity of term constructors w.r.t. propositional equality.

-- If  W F G = W' H E  then  F = H,  G = E and W = W'.

B-PE-injectivity : ∀ W W' → ⟦ W ⟧ F ▹ G PE.≡ ⟦ W' ⟧ H ▹ E
                 → F PE.≡ H × G PE.≡ E × W PE.≡ W'
B-PE-injectivity (BΠ p q) (BΠ .p .q) PE.refl =
  PE.refl , PE.refl , PE.refl
B-PE-injectivity (BΣ p q m) (BΣ .p .q .m) PE.refl =
  PE.refl , PE.refl , PE.refl

BΠ-PE-injectivity : ∀ {p p′ q q′} → BΠ p q PE.≡ BΠ p′ q′ → p PE.≡ p′ × q PE.≡ q′
BΠ-PE-injectivity PE.refl = PE.refl , PE.refl

BΣ-PE-injectivity :
  ∀ {p p′ q q′ m m′} →
  BΣ m p q PE.≡ BΣ m′ p′ q′ → p PE.≡ p′ × q PE.≡ q′ × m PE.≡ m′
BΣ-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : suc t PE.≡ suc u → t PE.≡ u
suc-PE-injectivity PE.refl = PE.refl

-- If prod t u = prod t′ u′ then t = t′ and u = u′

prod-PE-injectivity : ∀ {m m′} → prod m p t u PE.≡ prod m′ p′ t′ u′
                    → m PE.≡ m′ × p PE.≡ p′ × t PE.≡ t′ × u PE.≡ u′
prod-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl , PE.refl


-- Neutral terms.

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

data Neutral : Term n → Set a where
  var       : (x : Fin n) → Neutral (var x)
  ∘ₙ        : Neutral t   → Neutral (t ∘⟨ p ⟩ u)
  fstₙ      : Neutral t   → Neutral (fst p t)
  sndₙ      : Neutral t   → Neutral (snd p t)
  natrecₙ   : Neutral v   → Neutral (natrec p q r G t u v)
  prodrecₙ  : Neutral t   → Neutral (prodrec r p q A t u)
  Emptyrecₙ : Neutral t   → Neutral (Emptyrec p A t)


-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Whnf {n : Nat} : Term n → Set a where

  -- Type constructors are whnfs.
  Uₙ     : Whnf U
  ΠΣₙ    : Whnf (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕₙ     : Whnf ℕ
  Unitₙ  : Whnf Unit
  Emptyₙ : Whnf Empty

  -- Introductions are whnfs.
  lamₙ  : Whnf (lam p t)
  zeroₙ : Whnf zero
  sucₙ  : Whnf (suc t)
  starₙ : Whnf star
  prodₙ : Whnf (prod s p t u)

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
B≢ne (BΠ p q) () PE.refl
B≢ne (BΣ m p q) () PE.refl

ΠΣ≢ne : ∀ b → Neutral A → ΠΣ⟨ b ⟩ p , q ▷ F ▹ G PE.≢ A
ΠΣ≢ne BMΠ () PE.refl
ΠΣ≢ne (BMΣ s) () PE.refl

U≢B : ∀ W → U PE.≢ ⟦ W ⟧ F ▹ G
U≢B (BΠ p q) ()
U≢B (BΣ m p q) ()

U≢ΠΣ : ∀ b → U PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
U≢ΠΣ BMΠ ()
U≢ΠΣ (BMΣ s) ()

ℕ≢B : ∀ W → ℕ PE.≢ ⟦ W ⟧ F ▹ G
ℕ≢B (BΠ p q) ()
ℕ≢B (BΣ m p q) ()

ℕ≢ΠΣ : ∀ b → ℕ PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
ℕ≢ΠΣ BMΠ ()
ℕ≢ΠΣ (BMΣ s) ()

Empty≢B : ∀ W → Empty PE.≢ ⟦ W ⟧ F ▹ G
Empty≢B (BΠ p q) ()
Empty≢B (BΣ m p q) ()

Empty≢ΠΣ : ∀ b → Empty PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Empty≢ΠΣ BMΠ ()
Empty≢ΠΣ (BMΣ _) ()

Unit≢B : ∀ W → Unit PE.≢ ⟦ W ⟧ F ▹ G
Unit≢B (BΠ p q) ()
Unit≢B (BΣ m p q) ()

Unit≢ΠΣ : ∀ b → Unit PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Unit≢ΠΣ BMΠ ()
Unit≢ΠΣ (BMΣ _) ()

Π≢Σ : ∀ {m} → Π p₁ , q₁ ▷ F ▹ G PE.≢ Σ⟨ m ⟩ p₂ , q₂ ▷ H ▹ E
Π≢Σ ()

Σₚ≢Σᵣ : Σₚ p₁ , q₁ ▷ F ▹ G PE.≢ Σᵣ p₂ , q₂ ▷ H ▹ E
Σₚ≢Σᵣ ()

zero≢ne : Neutral t → zero PE.≢ t
zero≢ne () PE.refl

suc≢ne : Neutral t → suc u PE.≢ t
suc≢ne () PE.refl

prod≢ne : ∀ {m} → Neutral v → prod m p t u PE.≢ v
prod≢ne () PE.refl

-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {n : Nat} : Term n → Set a where
  zeroₙ :             Natural zero
  sucₙ  :             Natural (suc t)
  ne    : Neutral t → Natural t


-- A (small) type in whnf is either Π A B, Σ A B, ℕ, Empty, Unit or neutral.
-- Large types could also be U.

data Type {n : Nat} : Term n → Set a where
  ΠΣₙ    :             Type (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕₙ     :             Type ℕ
  Emptyₙ :             Type Empty
  Unitₙ  :             Type Unit
  ne     : Neutral t → Type t

⟦_⟧-type : ∀ (W : BindingType) → Type (⟦ W ⟧ F ▹ G)
⟦ BΠ p q ⟧-type = ΠΣₙ
⟦ BΣ m p q ⟧-type = ΠΣₙ

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function {n : Nat} : Term n → Set a where
  lamₙ : Function (lam p t)
  ne   : Neutral t → Function t

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product {n : Nat} : Term n → Set a where
  prodₙ : ∀ {m} → Product (prod m p t u)
  ne    : Neutral t → Product t


-- These views classify only whnfs.
-- Natural, Type, Function and Product are a subsets of Whnf.

naturalWhnf : Natural t → Whnf t
naturalWhnf sucₙ   = sucₙ
naturalWhnf zeroₙ  = zeroₙ
naturalWhnf (ne x) = ne x

typeWhnf : Type A → Whnf A
typeWhnf ΠΣₙ    = ΠΣₙ
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
⟦_⟧ₙ (BΠ p q) = ΠΣₙ
⟦_⟧ₙ (BΣ m p q) = ΠΣₙ

-- Fully normalized natural numbers

data Numeral {n : Nat} : Term n → Set a where
  zeroₙ : Numeral zero
  sucₙ : Numeral t → Numeral (suc t)

------------------------------------------------------------------------
-- Weakening

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : {m n : Nat} {bs : List Nat} (ρ : Wk m n) (c : GenTs (Term) n bs) → GenTs (Term) m bs
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

wkNeutral : ∀ ρ → Neutral t → Neutral {n = n} (wk ρ t)
wkNeutral ρ (var n)       = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)        = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (fstₙ n)      = fstₙ (wkNeutral ρ n)
wkNeutral ρ (sndₙ n)      = sndₙ (wkNeutral ρ n)
wkNeutral ρ (natrecₙ n)   = natrecₙ (wkNeutral ρ n)
wkNeutral ρ (prodrecₙ n)  = prodrecₙ (wkNeutral ρ n)
wkNeutral ρ (Emptyrecₙ e) = Emptyrecₙ (wkNeutral ρ e)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ → Natural t → Natural {n = n} (wk ρ t)
wkNatural ρ sucₙ   = sucₙ
wkNatural ρ zeroₙ  = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ ρ → Type t → Type {n = n} (wk ρ t)
wkType ρ ΠΣₙ    = ΠΣₙ
wkType ρ ℕₙ     = ℕₙ
wkType ρ Emptyₙ = Emptyₙ
wkType ρ Unitₙ  = Unitₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ ρ → Function t → Function {n = n} (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkProduct : ∀ ρ → Product t → Product {n = n} (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ ρ → Whnf t → Whnf {n = n} (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ ΠΣₙ     = ΠΣₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ Unitₙ   = Unitₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ prodₙ   = prodₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ starₙ   = starₙ
wkWhnf ρ (ne x)  = ne (wkNeutral ρ x)




------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from Fin n to terms.

Subst : Nat → Nat → Set a
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

-- We may view σ as the finite stream σ 0, σ 1, ..., σ n

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
  substGen : {bs : List Nat} (σ : Subst m n) (g : GenTs (Term) n bs) → GenTs (Term) m bs
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


-- Substitute the first two variables of a term with other terms.
--
-- If Γ∙A∙B ⊢ t : C, Γ ⊢ s : A and Γ ⊢ s′ : B and  then Γ ⊢ t[s,s′] : C[s,s′]

_[_,_] : (t : Term (1+ (1+ n))) (s s′ : Term n) → Term n
t [ s , s′ ] = subst (consSubst (consSubst idSubst s) s′) t

-- Substitute the first variable with a term and shift remaining variables up by one
-- If Γ ∙ A ⊢ t : A′ and Γ ∙ B ∙ C ⊢ s : A then Γ ∙ B ∙ C ⊢ t[s]↑² : A′

_[_]↑² : (t : Term (1+ n)) (s : Term (1+ (1+ n))) → Term (1+ (1+ n))
t [ s ]↑² = subst (consSubst (wk1Subst (wk1Subst idSubst)) s) t


B-subst : (σ : Subst m n) (W : BindingType) (F : Term n) (G : Term (1+ n))
        → subst σ (⟦ W ⟧ F ▹ G) PE.≡ ⟦ W ⟧ (subst σ F) ▹ (subst (liftSubst σ) G)
B-subst σ (BΠ p q) F G = PE.refl
B-subst σ (BΣ m p q) F G = PE.refl

------------------------------------------------------------------------
-- Some inversion lemmas

-- Inversion of equality for gen.

gen-cong⁻¹ :
  gen {bs = bs} k ts ≡ gen {bs = bs′} k′ ts′ →
  ∃ λ (eq : bs ≡ bs′) →
    PE.subst Kind eq k ≡ k′ ×
    PE.subst (GenTs Term _) eq ts ≡ ts′
gen-cong⁻¹ refl = refl , refl , refl

-- Inversion of equality for _∷_.

∷-cong⁻¹ :
  ∀ {b} {t t′ : Term (b + n)} →
  GenTs._∷_ {A = Term} {b = b} t ts ≡ t′ ∷ ts′ →
  t ≡ t′ × ts ≡ ts′
∷-cong⁻¹ refl = refl , refl
