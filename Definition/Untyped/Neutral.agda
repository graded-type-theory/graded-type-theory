------------------------------------------------------------------------
-- Neutral terms and WHNFs
------------------------------------------------------------------------

open import Definition.Typed.Variant

module Definition.Untyped.Neutral
  {a}
  (M : Set a)
  (type-variant : Type-variant)
  where

open Type-variant type-variant

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

open import Definition.Untyped M

private variable
  p p₁ p₂ q q₁ q₂ r   : M
  n                   : Nat
  b                   : BinderMode
  s                   : Strength
  ρ                   : Wk _ _
  A B E F G H l t u v w : Term _

------------------------------------------------------------------------
-- Neutral terms

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

data Neutral : Term n → Set a where
  var       : (x : Fin n) → Neutral (var x)
  ∘ₙ        : Neutral t   → Neutral (t ∘⟨ p ⟩ u)
  fstₙ      : Neutral t   → Neutral (fst p t)
  sndₙ      : Neutral t   → Neutral (snd p t)
  natrecₙ   : Neutral v   → Neutral (natrec p q r G t u v)
  prodrecₙ  : Neutral t   → Neutral (prodrec r p q A t u)
  emptyrecₙ : Neutral t   → Neutral (emptyrec p A t)
  unitrecₙ  : ¬ Unitʷ-η →
              Neutral t   → Neutral (unitrec p q l A t u)
  Jₙ        : Neutral w   → Neutral (J p q A t B u v w)
  Kₙ        : Neutral v   → Neutral (K p A t B u v)
  []-congₙ  : Neutral v   → Neutral ([]-cong s A t u v)

-- There are no closed neutral terms

noClosedNe : {t : Term 0} → Neutral t → ⊥
noClosedNe (∘ₙ net) = noClosedNe net
noClosedNe (fstₙ net) = noClosedNe net
noClosedNe (sndₙ net) = noClosedNe net
noClosedNe (natrecₙ net) = noClosedNe net
noClosedNe (prodrecₙ net) = noClosedNe net
noClosedNe (emptyrecₙ net) = noClosedNe net
noClosedNe (unitrecₙ _ net) = noClosedNe net
noClosedNe (Jₙ net) = noClosedNe net
noClosedNe (Kₙ net) = noClosedNe net
noClosedNe ([]-congₙ net) = noClosedNe net

------------------------------------------------------------------------
-- Weak head normal forms (WHNFs)

-- These are the (lazy) values of our language.

data Whnf {n : Nat} : Term n → Set a where

  -- Type constructors are whnfs.
  Levelₙ : Whnf Level
  Uₙ     : Whnf (U l)
  ΠΣₙ    : Whnf (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕₙ     : Whnf ℕ
  Unitₙ  : Whnf (Unit s l)
  Emptyₙ : Whnf Empty
  Idₙ    : Whnf (Id A t u)

  -- Introductions are whnfs.
  zeroᵘₙ : Whnf zeroᵘ
  sucᵘₙ : Whnf (sucᵘ t)
  maxᵘₙ : Whnf (t maxᵘ u)
  lamₙ  : Whnf (lam p t)
  zeroₙ : Whnf zero
  sucₙ  : Whnf (suc t)
  starₙ : Whnf (star s l)
  prodₙ : Whnf (prod s p t u)
  rflₙ  : Whnf rfl

  -- Neutrals are whnfs.
  ne    : Neutral t → Whnf t

------------------------------------------------------------------------
-- WHNF inequalities

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

Level≢ne : Neutral A → Level PE.≢ A
Level≢ne () PE.refl

U≢ne : Neutral A → U l PE.≢ A
U≢ne () PE.refl

ℕ≢ne : Neutral A → ℕ PE.≢ A
ℕ≢ne () PE.refl

Empty≢ne : Neutral A → Empty PE.≢ A
Empty≢ne () PE.refl

Unit≢ne : Neutral A → Unit s l PE.≢ A
Unit≢ne () PE.refl

B≢ne : ∀ W → Neutral A → ⟦ W ⟧ F ▹ G PE.≢ A
B≢ne (BΠ p q) () PE.refl
B≢ne (BΣ m p q) () PE.refl

ΠΣ≢ne : ∀ b → Neutral A → ΠΣ⟨ b ⟩ p , q ▷ F ▹ G PE.≢ A
ΠΣ≢ne BMΠ () PE.refl
ΠΣ≢ne (BMΣ s) () PE.refl

Id≢ne : Neutral B → Id A t u PE.≢ B
Id≢ne () PE.refl

Level≢B : ∀ W → Level PE.≢ ⟦ W ⟧ F ▹ G
Level≢B (BΠ p q) ()
Level≢B (BΣ m p q) ()

Level≢ΠΣ : ∀ b → Level PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Level≢ΠΣ BMΠ ()
Level≢ΠΣ (BMΣ s) ()

U≢B : ∀ W → U l PE.≢ ⟦ W ⟧ F ▹ G
U≢B (BΠ p q) ()
U≢B (BΣ m p q) ()

U≢ΠΣ : ∀ b → U l PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
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

Unit≢B : ∀ W → Unit s l PE.≢ ⟦ W ⟧ F ▹ G
Unit≢B (BΠ p q) ()
Unit≢B (BΣ m p q) ()

Unit≢ΠΣ : ∀ b → Unit s l PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Unit≢ΠΣ BMΠ ()
Unit≢ΠΣ (BMΣ _) ()

Id≢⟦⟧▷ : ∀ W → Id A t u PE.≢ ⟦ W ⟧ F ▹ G
Id≢⟦⟧▷ (BΠ _ _)   ()
Id≢⟦⟧▷ (BΣ _ _ _) ()

Id≢ΠΣ : ∀ b → Id A t u PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Id≢ΠΣ BMΠ     ()
Id≢ΠΣ (BMΣ _) ()

Π≢Σ : ∀ {m} → Π p₁ , q₁ ▷ F ▹ G PE.≢ Σ⟨ m ⟩ p₂ , q₂ ▷ H ▹ E
Π≢Σ ()

Σˢ≢Σʷ : Σˢ p₁ , q₁ ▷ F ▹ G PE.≢ Σʷ p₂ , q₂ ▷ H ▹ E
Σˢ≢Σʷ ()

zero≢ne : Neutral t → zero PE.≢ t
zero≢ne () PE.refl

suc≢ne : Neutral t → suc u PE.≢ t
suc≢ne () PE.refl

prod≢ne : ∀ {m} → Neutral v → prod m p t u PE.≢ v
prod≢ne () PE.refl

rfl≢ne : Neutral t → rfl PE.≢ t
rfl≢ne () PE.refl

star≢ne : Neutral t → star s l PE.≢ t
star≢ne () PE.refl

------------------------------------------------------------------------
-- Some WNHF views

-- Note that these views are not recursive.

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {n : Nat} : Term n → Set a where
  zeroₙ :             Natural zero
  sucₙ  :             Natural (suc t)
  ne    : Neutral t → Natural t


-- A type in WHNF is either a universe, a Π-type, a Σ-type, Level, ℕ, Empty,
-- a unit type, an identity type, or neutral.

data Type {n : Nat} : Term n → Set a where
  Levelₙ :             Type Level
  Uₙ     :             Type (U l)
  ΠΣₙ    :             Type (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕₙ     :             Type ℕ
  Emptyₙ :             Type Empty
  Unitₙ  :             Type (Unit s l)
  Idₙ    :             Type (Id A t u)
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

-- Star holds for applications of star as well as neutral terms.

data Star {n : Nat} : Term n → Set a where
  starₙ : Star (star s l)
  ne    : Neutral t → Star t

-- A WHNF of type Id A t u is either rfl or a neutral term.

data Identity {n} : Term n → Set a where
  rflₙ : Identity rfl
  ne   : Neutral t → Identity t

-- A non-dependent eliminator for Identity. Note that the argument of
-- ne is thrown away.

Identity-rec :
  ∀ {a} {A : Set a} →
  Identity t → A → A → A
Identity-rec rflₙ   r n = r
Identity-rec (ne _) r n = n


-- These views classify only WHNFs: Natural, Type, Function, Product,
-- Star and Identity are subsets of Whnf.

naturalWhnf : Natural t → Whnf t
naturalWhnf sucₙ   = sucₙ
naturalWhnf zeroₙ  = zeroₙ
naturalWhnf (ne x) = ne x

typeWhnf : Type A → Whnf A
typeWhnf Levelₙ = Levelₙ
typeWhnf Uₙ     = Uₙ
typeWhnf ΠΣₙ    = ΠΣₙ
typeWhnf ℕₙ     = ℕₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf Unitₙ  = Unitₙ
typeWhnf Idₙ    = Idₙ
typeWhnf (ne x) = ne x

functionWhnf : Function t → Whnf t
functionWhnf lamₙ   = lamₙ
functionWhnf (ne x) = ne x

productWhnf : Product t → Whnf t
productWhnf prodₙ  = prodₙ
productWhnf (ne x) = ne x

starWhnf : Star t → Whnf t
starWhnf starₙ  = starₙ
starWhnf (ne n) = ne n

identityWhnf : Identity t → Whnf t
identityWhnf rflₙ   = rflₙ
identityWhnf (ne n) = ne n

⟦_⟧ₙ : (W : BindingType) → Whnf (⟦ W ⟧ F ▹ G)
⟦_⟧ₙ (BΠ p q) = ΠΣₙ
⟦_⟧ₙ (BΣ m p q) = ΠΣₙ

------------------------------------------------------------------------
-- No-η-equality

-- No-η-equality A holds if A is a type without (top-level)
-- η-equality, either because it is (an application of) a type
-- constructor for a type without η-equality, or because it is
-- neutral.

data No-η-equality {n : Nat} : Term n → Set a where
  Uₙ     : No-η-equality (U l)
  Σʷₙ    : No-η-equality (Σʷ p , q ▷ A ▹ B)
  Emptyₙ : No-η-equality Empty
  ℕₙ     : No-η-equality ℕ
  Unitʷₙ : ¬ Unitʷ-η → No-η-equality (Unitʷ l)
  Idₙ    : No-η-equality (Id A t u)
  neₙ    : Neutral A → No-η-equality A

-- If No-η-equality A holds, then A is a WHNF.

No-η-equality→Whnf : No-η-equality A → Whnf A
No-η-equality→Whnf = λ where
  Uₙ         → Uₙ
  Σʷₙ        → ΠΣₙ
  Emptyₙ     → Emptyₙ
  ℕₙ         → ℕₙ
  (Unitʷₙ _) → Unitₙ
  Idₙ        → Idₙ
  (neₙ n)    → ne n

------------------------------------------------------------------------
-- Weakening

-- Weakening of a neutral term.

wkNeutral : ∀ ρ → Neutral t → Neutral {n = n} (wk ρ t)
wkNeutral ρ (var n)             = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)              = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (fstₙ n)            = fstₙ (wkNeutral ρ n)
wkNeutral ρ (sndₙ n)            = sndₙ (wkNeutral ρ n)
wkNeutral ρ (natrecₙ n)         = natrecₙ (wkNeutral ρ n)
wkNeutral ρ (prodrecₙ n)        = prodrecₙ (wkNeutral ρ n)
wkNeutral ρ (emptyrecₙ e)       = emptyrecₙ (wkNeutral ρ e)
wkNeutral ρ (unitrecₙ not-ok n) = unitrecₙ not-ok (wkNeutral ρ n)
wkNeutral ρ (Jₙ n)              = Jₙ (wkNeutral ρ n)
wkNeutral ρ (Kₙ n)              = Kₙ (wkNeutral ρ n)
wkNeutral ρ ([]-congₙ n)        = []-congₙ (wkNeutral ρ n)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ → Natural t → Natural {n = n} (wk ρ t)
wkNatural ρ sucₙ   = sucₙ
wkNatural ρ zeroₙ  = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ ρ → Type t → Type {n = n} (wk ρ t)
wkType ρ Levelₙ = Levelₙ
wkType ρ Uₙ     = Uₙ
wkType ρ ΠΣₙ    = ΠΣₙ
wkType ρ ℕₙ     = ℕₙ
wkType ρ Emptyₙ = Emptyₙ
wkType ρ Unitₙ  = Unitₙ
wkType ρ Idₙ    = Idₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ ρ → Function t → Function {n = n} (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkProduct : ∀ ρ → Product t → Product {n = n} (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne x) = ne (wkNeutral ρ x)

wkIdentity : Identity t → Identity (wk ρ t)
wkIdentity rflₙ   = rflₙ
wkIdentity (ne n) = ne (wkNeutral _ n)

wkWhnf : ∀ ρ → Whnf t → Whnf {n = n} (wk ρ t)
wkWhnf ρ Levelₙ  = Levelₙ
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ ΠΣₙ     = ΠΣₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ Unitₙ   = Unitₙ
wkWhnf ρ Idₙ     = Idₙ
wkWhnf ρ zeroᵘₙ  = zeroᵘₙ
wkWhnf ρ sucᵘₙ   = sucᵘₙ
wkWhnf ρ maxᵘₙ   = maxᵘₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ prodₙ   = prodₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ starₙ   = starₙ
wkWhnf ρ rflₙ    = rflₙ
wkWhnf ρ (ne x)  = ne (wkNeutral ρ x)

------------------------------------------------------------------------
-- Inversion lemmas for Neutral

opaque

  -- An inversion lemma for _∘⟨_⟩_.

  inv-ne-∘ : Neutral (t ∘⟨ p ⟩ u) → Neutral t
  inv-ne-∘ (∘ₙ n) = n

opaque

  -- An inversion lemma for fst.

  inv-ne-fst : Neutral (fst p t) → Neutral t
  inv-ne-fst (fstₙ n) = n

opaque

  -- An inversion lemma for snd.

  inv-ne-snd : Neutral (snd p t) → Neutral t
  inv-ne-snd (sndₙ n) = n

opaque

  -- An inversion lemma for natrec.

  inv-ne-natrec : Neutral (natrec p q r A t u v) → Neutral v
  inv-ne-natrec (natrecₙ n) = n

opaque

  -- An inversion lemma for prodrec.

  inv-ne-prodrec : Neutral (prodrec r p q A t u) → Neutral t
  inv-ne-prodrec (prodrecₙ n) = n

opaque

  -- An inversion lemma for emptyrec.

  inv-ne-emptyrec : Neutral (emptyrec p A t) → Neutral t
  inv-ne-emptyrec (emptyrecₙ n) = n

opaque

  -- An inversion lemma for unitrec.

  inv-ne-unitrec :
    Neutral (unitrec p q l A t u) → ¬ Unitʷ-η × Neutral t
  inv-ne-unitrec (unitrecₙ not-ok n) = not-ok , n

opaque

  -- An inversion lemma for J.

  inv-ne-J : Neutral (J p q A t B u v w) → Neutral w
  inv-ne-J (Jₙ n) = n

opaque

  -- An inversion lemma for K.

  inv-ne-K : Neutral (K p A t B u v) → Neutral v
  inv-ne-K (Kₙ n) = n

opaque

  -- An inversion lemma for []-cong.

  inv-ne-[]-cong : Neutral ([]-cong s A t u v) → Neutral v
  inv-ne-[]-cong ([]-congₙ n) = n

------------------------------------------------------------------------
-- Inversion lemmas for Whnf

opaque

  -- An inversion lemma for _∘⟨_⟩_.

  inv-whnf-∘ : Whnf (t ∘⟨ p ⟩ u) → Neutral t
  inv-whnf-∘ (ne n) = inv-ne-∘ n

opaque

  -- An inversion lemma for fst.

  inv-whnf-fst : Whnf (fst p t) → Neutral t
  inv-whnf-fst (ne n) = inv-ne-fst n

opaque

  -- An inversion lemma for snd.

  inv-whnf-snd : Whnf (snd p t) → Neutral t
  inv-whnf-snd (ne n) = inv-ne-snd n

opaque

  -- An inversion lemma for natrec.

  inv-whnf-natrec : Whnf (natrec p q r A t u v) → Neutral v
  inv-whnf-natrec (ne n) = inv-ne-natrec n

opaque

  -- An inversion lemma for prodrec.

  inv-whnf-prodrec : Whnf (prodrec r p q A t u) → Neutral t
  inv-whnf-prodrec (ne n) = inv-ne-prodrec n

opaque

  -- An inversion lemma for emptyrec.

  inv-whnf-emptyrec : Whnf (emptyrec p A t) → Neutral t
  inv-whnf-emptyrec (ne n) = inv-ne-emptyrec n

opaque

  -- An inversion lemma for unitrec.

  inv-whnf-unitrec :
    Whnf (unitrec p q l A t u) → ¬ Unitʷ-η × Neutral t
  inv-whnf-unitrec (ne n) = inv-ne-unitrec n

opaque

  -- An inversion lemma for J.

  inv-whnf-J : Whnf (J p q A t B u v w) → Neutral w
  inv-whnf-J (ne n) = inv-ne-J n

opaque

  -- An inversion lemma for K.

  inv-whnf-K : Whnf (K p A t B u v) → Neutral v
  inv-whnf-K (ne n) = inv-ne-K n

opaque

  -- An inversion lemma for []-cong.

  inv-whnf-[]-cong : Whnf ([]-cong s A t u v) → Neutral v
  inv-whnf-[]-cong (ne n) = inv-ne-[]-cong n

------------------------------------------------------------------------
-- An alternate representation of neutral terms, tracking the variable
-- that a neutral term is stuck on

data NeutralAt (x : Fin n) : Term n → Set a where
  var       : NeutralAt x (var x)
  ∘ₙ        : NeutralAt x t   → NeutralAt x (t ∘⟨ p ⟩ u)
  fstₙ      : NeutralAt x t   → NeutralAt x (fst p t)
  sndₙ      : NeutralAt x t   → NeutralAt x (snd p t)
  natrecₙ   : NeutralAt x v   → NeutralAt x (natrec p q r G t u v)
  prodrecₙ  : NeutralAt x t   → NeutralAt x (prodrec r p q A t u)
  emptyrecₙ : NeutralAt x t   → NeutralAt x (emptyrec p A t)
  unitrecₙ  : ¬ Unitʷ-η →
              NeutralAt x t   → NeutralAt x (unitrec p q l A t u)
  Jₙ        : NeutralAt x w   → NeutralAt x (J p q A t B u v w)
  Kₙ        : NeutralAt x v   → NeutralAt x (K p A t B u v)
  []-congₙ  : NeutralAt x v   → NeutralAt x ([]-cong s A t u v)
