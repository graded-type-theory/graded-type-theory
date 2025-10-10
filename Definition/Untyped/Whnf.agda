------------------------------------------------------------------------
-- Weak head-normal forms of terms.
------------------------------------------------------------------------

open import Definition.Typed.Variant

module Definition.Untyped.Whnf
  {a} (M : Set a)
  (type-variant : Type-variant)
  where

open Type-variant type-variant

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

private
  variable
    p q r : M
    n l : Nat
    ∇ ∇′ : DCon (Term 0) _
    ξ : DExt _ _ _
    t u v w A B F G : Term _
    V V′ : Set a
    ρ : Wk _ _
    σ : Subst _ _
    b : BinderMode
    s : Strength

------------------------------------------------------------------------
-- Weak head normal forms (WHNFs)

-- These are the (lazy) values of our language.

data Whnf {m n} (∇ : DCon (Term 0) m) : Term n → Set a where

  -- Type constructors are whnfs.
  Uₙ     : Whnf ∇ (U l)
  ΠΣₙ    : Whnf ∇ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕₙ     : Whnf ∇ ℕ
  Unitₙ  : Whnf ∇ (Unit s l)
  Emptyₙ : Whnf ∇ Empty
  Idₙ    : Whnf ∇ (Id A t u)

  -- Introductions are whnfs.
  lamₙ  : Whnf ∇ (lam p t)
  zeroₙ : Whnf ∇ zero
  sucₙ  : Whnf ∇ (suc t)
  starₙ : Whnf ∇ (star s l)
  prodₙ : Whnf ∇ (prod s p t u)
  rflₙ  : Whnf ∇ rfl

  -- Neutral terms are whnfs.
  ne    : Neutral⁺ ∇ t → Whnf ∇ t

ne-whnf : Neutral V ∇ t → Whnf ∇ t
ne-whnf = ne ∘→ ne↑⁺

------------------------------------------------------------------------
-- Some WNHF views

-- Note that these views are not recursive.

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {m n} (V : Set a) (∇ : DCon (Term 0) m) : Term n → Set a where
  zeroₙ :                 Natural V ∇ zero
  sucₙ  :                 Natural V ∇ (suc t)
  ne    : Neutral V ∇ t → Natural V ∇ t

Natural⁺ : ∀ {m n} → DCon (Term 0) m → Term n → Set a
Natural⁺ = Natural (Lift _ ⊤)

opaque

  natural↑ : V → Natural V′ ∇ t → Natural V ∇ t
  natural↑ ok zeroₙ  = zeroₙ
  natural↑ ok sucₙ   = sucₙ
  natural↑ ok (ne b) = ne (ne↑ ok b)

-- A type in WHNF is either a universe, a Π-type, a Σ-type, ℕ, Empty,
-- a unit type, an identity type, or neutral.

data Type {m n} (V : Set a) (∇ : DCon (Term 0) m) : Term n → Set a where
  Uₙ     :                 Type V ∇ (U l)
  ΠΣₙ    :                 Type V ∇ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕₙ     :                 Type V ∇ ℕ
  Emptyₙ :                 Type V ∇ Empty
  Unitₙ  :                 Type V ∇ (Unit s l)
  Idₙ    :                 Type V ∇ (Id A t u)
  ne     : Neutral V ∇ t → Type V ∇ t

Type⁺ : ∀ {m n} → DCon (Term 0) m → Term n → Set a
Type⁺ = Type (Lift _ ⊤)

opaque

  type↑ : V → Type V′ ∇ t → Type V ∇ t
  type↑ ok Uₙ     = Uₙ
  type↑ ok ΠΣₙ    = ΠΣₙ
  type↑ ok ℕₙ     = ℕₙ
  type↑ ok Emptyₙ = Emptyₙ
  type↑ ok Unitₙ  = Unitₙ
  type↑ ok Idₙ    = Idₙ
  type↑ ok (ne b) = ne (ne↑ ok b)

⟦_⟧-type : ∀ (W : BindingType) → Type V ∇ (⟦ W ⟧ F ▹ G)
⟦ BΠ p q   ⟧-type = ΠΣₙ
⟦ BΣ m p q ⟧-type = ΠΣₙ

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function {m n} (V : Set a) (∇ : DCon (Term 0) m) : Term n → Set a where
  lamₙ :                 Function V ∇ (lam p t)
  ne   : Neutral V ∇ t → Function V ∇ t

Function⁺ : ∀ {m n} → DCon (Term 0) m → Term n → Set a
Function⁺ = Function (Lift _ ⊤)

opaque

  function↑ : V → Function V′ ∇ t → Function V ∇ t
  function↑ ok lamₙ   = lamₙ
  function↑ ok (ne b) = ne (ne↑ ok b)

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product {m n} (V : Set a) (∇ : DCon (Term 0) m) : Term n → Set a where
  prodₙ : ∀ {s}         → Product V ∇ (prod s p t u)
  ne    : Neutral V ∇ t → Product V ∇ t

Product⁺ : ∀ {m n} → DCon (Term 0) m → Term n → Set a
Product⁺ = Product (Lift _ ⊤)

opaque

  product↑ : V → Product V′ ∇ t → Product V ∇ t
  product↑ ok prodₙ  = prodₙ
  product↑ ok (ne b) = ne (ne↑ ok b)

-- Star holds for applications of star as well as neutral terms.

data Star {m n} (V : Set a) (∇ : DCon (Term 0) m) : Term n → Set a where
  starₙ :                 Star V ∇ (star s l)
  ne    : Neutral V ∇ t → Star V ∇ t

Star⁺ : ∀ {m n} → DCon (Term 0) m → Term n → Set a
Star⁺ = Star (Lift _ ⊤)

opaque

  star↑ : V → Star V′ ∇ t → Star V ∇ t
  star↑ ok starₙ  = starₙ
  star↑ ok (ne b) = ne (ne↑ ok b)

-- A WHNF of type Id A t u is either rfl or neutral.

data Identity {m n} (V : Set a) (∇ : DCon (Term 0) m) : Term n → Set a where
  rflₙ :                 Identity V ∇ rfl
  ne   : Neutral V ∇ t → Identity V ∇ t

Identity⁺ : ∀ {m n} → DCon (Term 0) m → Term n → Set a
Identity⁺ = Identity (Lift _ ⊤)

opaque

  identity↑ : V → Identity V′ ∇ t → Identity V ∇ t
  identity↑ ok rflₙ   = rflₙ
  identity↑ ok (ne b) = ne (ne↑ ok b)

-- A non-dependent eliminator for Identity. Note that the argument
-- for the ne case is thrown away.

Identity-rec :
  ∀ {a} {A : Set a} →
  Identity V ∇ t → A → A → A
Identity-rec rflₙ   r b = r
Identity-rec (ne _) r b = b

opaque

  -- Numerals satisfy the predicate Natural⁺.

  Numeral→Natural : Numeral t → Natural⁺ ∇ t
  Numeral→Natural zeroₙ    = zeroₙ
  Numeral→Natural (sucₙ _) = sucₙ

-- These views classify only WHNFs: Natural, Type, Function, Product,
-- Star and Identity are subsets of Whnf.

naturalWhnf : Natural V ∇ t → Whnf ∇ t
naturalWhnf sucₙ   = sucₙ
naturalWhnf zeroₙ  = zeroₙ
naturalWhnf (ne b) = ne-whnf b

typeWhnf : Type V ∇ A → Whnf ∇ A
typeWhnf Uₙ     = Uₙ
typeWhnf ΠΣₙ    = ΠΣₙ
typeWhnf ℕₙ     = ℕₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf Unitₙ  = Unitₙ
typeWhnf Idₙ    = Idₙ
typeWhnf (ne b) = ne-whnf b

functionWhnf : Function V ∇ t → Whnf ∇ t
functionWhnf lamₙ   = lamₙ
functionWhnf (ne b) = ne-whnf b

productWhnf : Product V ∇ t → Whnf ∇ t
productWhnf prodₙ  = prodₙ
productWhnf (ne b) = ne-whnf b

starWhnf : Star V ∇ t → Whnf ∇ t
starWhnf starₙ  = starₙ
starWhnf (ne b) = ne-whnf b

identityWhnf : Identity V ∇ t → Whnf ∇ t
identityWhnf rflₙ   = rflₙ
identityWhnf (ne b) = ne-whnf b

⟦_⟧ₙ : (W : BindingType) → Whnf ∇ (⟦ W ⟧ F ▹ G)
⟦_⟧ₙ (BΠ p q)   = ΠΣₙ
⟦_⟧ₙ (BΣ m p q) = ΠΣₙ

------------------------------------------------------------------------
-- No-η-equality

-- No-η-equality A holds if A is a type without (top-level)
-- η-equality, either because it is (an application of) a type
-- constructor for a type without η-equality, or because it is
-- neutral.

data No-η-equality {m n} (∇ : DCon (Term 0) m) : Term n → Set a where
  Uₙ     :                No-η-equality ∇ (U l)
  Σʷₙ    :                No-η-equality ∇ (Σʷ p , q ▷ A ▹ B)
  Emptyₙ :                No-η-equality ∇ Empty
  ℕₙ     :                No-η-equality ∇ ℕ
  Unitʷₙ : ¬ Unitʷ-η    → No-η-equality ∇ (Unitʷ l)
  Idₙ    :                No-η-equality ∇ (Id A t u)
  neₙ    : Neutral⁺ ∇ A → No-η-equality ∇ A

-- If No-η-equality A holds, then A is a WHNF.

No-η-equality→Whnf : No-η-equality ∇ A → Whnf ∇ A
No-η-equality→Whnf = λ where
  Uₙ         → Uₙ
  Σʷₙ        → ΠΣₙ
  Emptyₙ     → Emptyₙ
  ℕₙ         → ℕₙ
  (Unitʷₙ _) → Unitₙ
  Idₙ        → Idₙ
  (neₙ b)    → ne b

------------------------------------------------------------------------
-- Weakening lemmas

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ → Natural V ∇ t → Natural {n = n} V ∇ (wk ρ t)
wkNatural ρ sucₙ   = sucₙ
wkNatural ρ zeroₙ  = zeroₙ
wkNatural ρ (ne b) = ne (wkNeutral ρ b)

wkType : ∀ ρ → Type V ∇ t → Type {n = n} V ∇ (wk ρ t)
wkType ρ Uₙ     = Uₙ
wkType ρ ΠΣₙ    = ΠΣₙ
wkType ρ ℕₙ     = ℕₙ
wkType ρ Emptyₙ = Emptyₙ
wkType ρ Unitₙ  = Unitₙ
wkType ρ Idₙ    = Idₙ
wkType ρ (ne b) = ne (wkNeutral ρ b)

wkFunction : ∀ ρ → Function V ∇ t → Function {n = n} V ∇ (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne b) = ne (wkNeutral ρ b)

wkProduct : ∀ ρ → Product V ∇ t → Product {n = n} V ∇ (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne b) = ne (wkNeutral ρ b)

wkIdentity : Identity V ∇ t → Identity V ∇ (wk ρ t)
wkIdentity rflₙ   = rflₙ
wkIdentity (ne b) = ne (wkNeutral _ b)

wkWhnf : ∀ ρ → Whnf ∇ t → Whnf {n = n} ∇ (wk ρ t)
wkWhnf ρ Uₙ     = Uₙ
wkWhnf ρ ΠΣₙ    = ΠΣₙ
wkWhnf ρ ℕₙ     = ℕₙ
wkWhnf ρ Emptyₙ = Emptyₙ
wkWhnf ρ Unitₙ  = Unitₙ
wkWhnf ρ Idₙ    = Idₙ
wkWhnf ρ lamₙ   = lamₙ
wkWhnf ρ prodₙ  = prodₙ
wkWhnf ρ zeroₙ  = zeroₙ
wkWhnf ρ sucₙ   = sucₙ
wkWhnf ρ starₙ  = starₙ
wkWhnf ρ rflₙ   = rflₙ
wkWhnf ρ (ne x) = ne (wkNeutral ρ x)

opaque

  -- A weakening lemma for No-η-equality.

  wk-No-η-equality : No-η-equality ∇ A → No-η-equality ∇ (wk ρ A)
  wk-No-η-equality Uₙ            = Uₙ
  wk-No-η-equality Σʷₙ           = Σʷₙ
  wk-No-η-equality Emptyₙ        = Emptyₙ
  wk-No-η-equality ℕₙ            = ℕₙ
  wk-No-η-equality (Unitʷₙ no-η) = Unitʷₙ no-η
  wk-No-η-equality Idₙ           = Idₙ
  wk-No-η-equality (neₙ A-ne)    = neₙ (wkNeutral _ A-ne)

------------------------------------------------------------------------
-- Inversion lemmas

opaque

  -- An inversion lemma for _∘⟨_⟩_.

  inv-whnf-∘ : Whnf ∇ (t ∘⟨ p ⟩ u) → Neutral⁺ ∇ t
  inv-whnf-∘ (ne b) = inv-ne-∘ b

opaque

  -- An inversion lemma for fst.

  inv-whnf-fst : Whnf ∇ (fst p t) → Neutral⁺ ∇ t
  inv-whnf-fst (ne b) = inv-ne-fst b

opaque

  -- An inversion lemma for snd.

  inv-whnf-snd : Whnf ∇ (snd p t) → Neutral⁺ ∇ t
  inv-whnf-snd (ne b) = inv-ne-snd b

opaque

  -- An inversion lemma for natrec.

  inv-whnf-natrec : Whnf ∇ (natrec p q r A t u v) → Neutral⁺ ∇ v
  inv-whnf-natrec (ne b) = inv-ne-natrec b

opaque

  -- An inversion lemma for prodrec.

  inv-whnf-prodrec : Whnf ∇ (prodrec r p q A t u) → Neutral⁺ ∇ t
  inv-whnf-prodrec (ne b) = inv-ne-prodrec b

opaque

  -- An inversion lemma for emptyrec.

  inv-whnf-emptyrec : Whnf ∇ (emptyrec p A t) → Neutral⁺ ∇ t
  inv-whnf-emptyrec (ne b) = inv-ne-emptyrec b

opaque

  -- An inversion lemma for unitrec.

  inv-whnf-unitrec :
    Whnf ∇ (unitrec l p q A t u) → ¬ Unitʷ-η × Neutral⁺ ∇ t
  inv-whnf-unitrec (ne b) = inv-ne-unitrec b

opaque

  -- An inversion lemma for J.

  inv-whnf-J : Whnf ∇ (J p q A t B u v w) → Neutral⁺ ∇ w
  inv-whnf-J (ne b) = inv-ne-J b

opaque

  -- An inversion lemma for K.

  inv-whnf-K : Whnf ∇ (K p A t B u v) → Neutral⁺ ∇ v
  inv-whnf-K (ne b) = inv-ne-K b

opaque

  -- An inversion lemma for []-cong.

  inv-whnf-[]-cong : Whnf ∇ ([]-cong s A t u v) → Neutral⁺ ∇ v
  inv-whnf-[]-cong (ne b) = inv-ne-[]-cong b

------------------------------------------------------------------------
-- Substitution lemmas

opaque

  -- Terms neutral after applying a substitution are neutral before
  -- applying the substitution.

  ne⁺-subst : ∀ {t} → t [ σ ] ≡ u → Neutral⁺ ∇ u → Neutral⁺ ∇ t
  ne⁺-subst {t} ≡u (defn α↦⊘) =
    case subst-defn {t = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ refl) → defn α↦⊘
  ne⁺-subst {t} ≡u (var ok x) =
    case subst-var {t = t} ≡u of λ where
      (x′ , refl , _) → var ok x′
  ne⁺-subst {t} ≡u (∘ₙ b) =
    case subst-∘ {t = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , _ , refl , ≡t′ , _)) → ∘ₙ (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u (fstₙ b) =
    case subst-fst {t = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , refl , ≡t′)) → fstₙ (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u (sndₙ b) =
    case subst-snd {t = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , refl , ≡t′)) → sndₙ (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u (natrecₙ b) =
    case subst-natrec {t = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , _ , _ , _ , refl , _ , _ , _ , ≡t′)) →
        natrecₙ (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u (prodrecₙ b) =
    case subst-prodrec {t = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , _ , _ , refl , _ , ≡t′ , _)) →
        prodrecₙ (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u (emptyrecₙ b) =
    case subst-emptyrec {t = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , _ , refl , _ , ≡t′)) →
        emptyrecₙ (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u (unitrecₙ no-η b) =
    case subst-unitrec {t = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , _ , _ , refl , _ , ≡t′ , _)) →
        unitrecₙ no-η (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u (Jₙ b) =
    case subst-J {w = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , _ , _ , _ , _ , _ , refl , _ , _ , _ , _ , _ , ≡t′)) →
        Jₙ (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u (Kₙ b) =
    case subst-K {w = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , _ , _ , _ , _ , refl , _ , _ , _ , _ , ≡t′)) →
        Kₙ (ne⁺-subst ≡t′ b)
  ne⁺-subst {t} ≡u ([]-congₙ b) =
    case subst-[]-cong {w = t} ≡u of λ where
      (inj₁ (x , refl)) → var⁺ x
      (inj₂ (_ , _ , _ , _ , refl , _ , _ , _ , ≡t′)) →
        []-congₙ (ne⁺-subst ≡t′ b)

opaque

  -- Terms in whnf after applying a substitution are in whnf before
  -- applying the substitution.

  whnf-subst : Whnf ∇ (t [ σ ]) → Whnf ∇ t
  whnf-subst {t} = lemma refl
    where
    lemma : t [ σ ] ≡ u → Whnf ∇ u → Whnf ∇ t
    lemma ≡u Uₙ =
      case subst-U {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ refl) → Uₙ
    lemma ≡u ΠΣₙ =
      case subst-ΠΣ {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ (_ , _ , refl , _)) → ΠΣₙ
    lemma ≡u ℕₙ =
      case subst-ℕ {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ refl) → ℕₙ
    lemma ≡u Unitₙ =
      case subst-Unit {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ refl) → Unitₙ
    lemma ≡u Emptyₙ =
      case subst-Empty {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ refl) → Emptyₙ
    lemma ≡u Idₙ =
      case subst-Id {v = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ (_ , _ , _ , refl , _)) → Idₙ
    lemma ≡u lamₙ =
      case subst-lam {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ (_ , refl , _)) → lamₙ
    lemma ≡u zeroₙ =
      case subst-zero {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ refl) → zeroₙ
    lemma ≡u sucₙ =
      case subst-suc {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ (_ , refl , _)) → sucₙ
    lemma ≡u starₙ =
      case subst-star {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ refl) → starₙ
    lemma ≡u prodₙ =
      case subst-prod {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ (_ , _ , refl , _)) → prodₙ
    lemma ≡u rflₙ =
      case subst-rfl {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var⁺ x)
        (inj₂ refl) → rflₙ
    lemma ≡u (ne b) = ne (ne⁺-subst ≡u b)

------------------------------------------------------------------------
-- WHNFs and inlining

opaque
  unfolding inline

  -- If t is neutral under glassify ∇, then inline ξ t is neutral
  -- under ∇′.

  Neutral-inline : Neutral V (glassify ∇) t → Neutral V ∇′ (inline ξ t)
  Neutral-inline (defn α↦)            = ⊥-elim (glass-↦⊘∈ α↦)
  Neutral-inline (var ok _)           = var ok _
  Neutral-inline (∘ₙ t-ne)            = ∘ₙ (Neutral-inline t-ne)
  Neutral-inline (fstₙ t-ne)          = fstₙ (Neutral-inline t-ne)
  Neutral-inline (sndₙ t-ne)          = sndₙ (Neutral-inline t-ne)
  Neutral-inline (natrecₙ t-ne)       = natrecₙ (Neutral-inline t-ne)
  Neutral-inline (prodrecₙ t-ne)      = prodrecₙ (Neutral-inline t-ne)
  Neutral-inline (emptyrecₙ t-ne)     = emptyrecₙ (Neutral-inline t-ne)
  Neutral-inline (unitrecₙ no-η t-ne) = unitrecₙ no-η
                                          (Neutral-inline t-ne)
  Neutral-inline (Jₙ t-ne)            = Jₙ (Neutral-inline t-ne)
  Neutral-inline (Kₙ t-ne)            = Kₙ (Neutral-inline t-ne)
  Neutral-inline ([]-congₙ t-ne)      = []-congₙ (Neutral-inline t-ne)

opaque
  unfolding inline

  -- If t is in WHNF under glassify ∇, then inline ξ t is in WHNF
  -- under ∇′.

  Whnf-inline : Whnf (glassify ∇) t → Whnf ∇′ (inline ξ t)
  Whnf-inline Uₙ        = Uₙ
  Whnf-inline ΠΣₙ       = ΠΣₙ
  Whnf-inline ℕₙ        = ℕₙ
  Whnf-inline Unitₙ     = Unitₙ
  Whnf-inline Emptyₙ    = Emptyₙ
  Whnf-inline Idₙ       = Idₙ
  Whnf-inline lamₙ      = lamₙ
  Whnf-inline zeroₙ     = zeroₙ
  Whnf-inline sucₙ      = sucₙ
  Whnf-inline starₙ     = starₙ
  Whnf-inline prodₙ     = prodₙ
  Whnf-inline rflₙ      = rflₙ
  Whnf-inline (ne t-ne) = ne (Neutral-inline t-ne)
