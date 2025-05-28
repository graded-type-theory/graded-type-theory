------------------------------------------------------------------------
-- Terms blocked on variables and opaque definitions.
------------------------------------------------------------------------

open import Definition.Typed.Variant

module Definition.Untyped.Neutral
  {a} (M : Set a)
  (type-variant : Type-variant)
  where

open Type-variant type-variant

open import Definition.Untyped M
open import Definition.Untyped.Inversion M

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum renaming (map to ⊎-map)
open import Tools.Unit

private
  variable
    p q r : M
    m n α l : Nat
    ∇ : DCon (Term 0) _
    t u v w A B F G : Term _
    V V′ : Set a
    σ : Subst _ _
    s : Strength

------------------------------------------------------------------------
-- Neutral terms

data Neutral {m n} (V : Set a) (∇ : DCon (Term 0) m) : Term n → Set a where
  defn      : α ↦⊘∷ A ∈ ∇   → Neutral V ∇ (defn α)
  var       : V → ∀ x       → Neutral V ∇ (var x)
  ∘ₙ        : Neutral V ∇ t → Neutral V ∇ (t ∘⟨ p ⟩ u)
  fstₙ      : Neutral V ∇ t → Neutral V ∇ (fst p t)
  sndₙ      : Neutral V ∇ t → Neutral V ∇ (snd p t)
  natrecₙ   : Neutral V ∇ v → Neutral V ∇ (natrec p q r G t u v)
  prodrecₙ  : Neutral V ∇ t → Neutral V ∇ (prodrec r p q A t u)
  emptyrecₙ : Neutral V ∇ t → Neutral V ∇ (emptyrec p A t)
  unitrecₙ  : ¬ Unitʷ-η →
              Neutral V ∇ t → Neutral V ∇ (unitrec l p q A t u)
  Jₙ        : Neutral V ∇ w → Neutral V ∇ (J p q A t B u v w)
  Kₙ        : Neutral V ∇ v → Neutral V ∇ (K p A t B u v)
  []-congₙ  : Neutral V ∇ v → Neutral V ∇ ([]-cong s A t u v)

opaque

  ne→ : (V → V′) → Neutral V ∇ t → Neutral V′ ∇ t
  ne→ f (defn α↦⊘)     = defn α↦⊘
  ne→ f (var ok x)     = var (f ok) x
  ne→ f (∘ₙ b)         = ∘ₙ (ne→ f b)
  ne→ f (fstₙ b)       = fstₙ (ne→ f b)
  ne→ f (sndₙ b)       = sndₙ (ne→ f b)
  ne→ f (natrecₙ b)    = natrecₙ (ne→ f b)
  ne→ f (prodrecₙ b)   = prodrecₙ (ne→ f b)
  ne→ f (emptyrecₙ b)  = emptyrecₙ (ne→ f b)
  ne→ f (unitrecₙ u b) = unitrecₙ u (ne→ f b)
  ne→ f (Jₙ b)         = Jₙ (ne→ f b)
  ne→ f (Kₙ b)         = Kₙ (ne→ f b)
  ne→ f ([]-congₙ b)   = []-congₙ (ne→ f b)

opaque

  ne↑ : V → Neutral V′ ∇ t → Neutral V ∇ t
  ne↑ ok = ne→ (λ _ → ok)

------------------------------------------------------------------------
-- No-confusion lemmas

opaque

  U≢ne : Neutral V ∇ A → U l ≢ A
  U≢ne () refl

opaque

  ℕ≢ne : Neutral V ∇ A → ℕ ≢ A
  ℕ≢ne () refl

opaque

  Empty≢ne : Neutral V ∇ A → Empty ≢ A
  Empty≢ne () refl

opaque

  Unit≢ne : Neutral V ∇ A → Unit s l ≢ A
  Unit≢ne () refl

opaque
  
  B≢ne : ∀ W → Neutral V ∇ A → ⟦ W ⟧ F ▹ G ≢ A
  B≢ne (BΠ p q)   () refl
  B≢ne (BΣ m p q) () refl

opaque

  ΠΣ≢ne : ∀ b → Neutral V ∇ A → ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≢ A
  ΠΣ≢ne BMΠ     () refl
  ΠΣ≢ne (BMΣ s) () refl

opaque

  Id≢ne : Neutral V ∇ B → Id A t u ≢ B
  Id≢ne () refl

opaque

  zero≢ne : Neutral V ∇ t → zero ≢ t
  zero≢ne () refl

opaque

  suc≢ne : Neutral V ∇ t → suc u ≢ t
  suc≢ne () refl

opaque

  prod≢ne : ∀ {m} → Neutral V ∇ v → prod m p t u ≢ v
  prod≢ne () refl

opaque

  rfl≢ne : Neutral V ∇ t → rfl ≢ t
  rfl≢ne () refl

opaque
  
  star≢ne : Neutral V ∇ t → star s l ≢ t
  star≢ne () refl

------------------------------------------------------------------------
-- Weakening lemmas

wkNeutral : ∀ ρ → Neutral V ∇ t → Neutral {n = n} V ∇ (wk ρ t)
wkNeutral ρ (defn α↦⊘)        = defn α↦⊘
wkNeutral ρ (var ok x)        = var ok (wkVar ρ x)
wkNeutral ρ (∘ₙ b)            = ∘ₙ (wkNeutral ρ b)
wkNeutral ρ (fstₙ b)          = fstₙ (wkNeutral ρ b)
wkNeutral ρ (sndₙ b)          = sndₙ (wkNeutral ρ b)
wkNeutral ρ (natrecₙ b)       = natrecₙ (wkNeutral ρ b)
wkNeutral ρ (prodrecₙ b)      = prodrecₙ (wkNeutral ρ b)
wkNeutral ρ (emptyrecₙ b)     = emptyrecₙ (wkNeutral ρ b)
wkNeutral ρ (unitrecₙ no-η b) = unitrecₙ no-η (wkNeutral ρ b)
wkNeutral ρ (Jₙ b)            = Jₙ (wkNeutral ρ b)
wkNeutral ρ (Kₙ b)            = Kₙ (wkNeutral ρ b)
wkNeutral ρ ([]-congₙ b)      = []-congₙ (wkNeutral ρ b)

------------------------------------------------------------------------
-- Inversion lemmas

opaque

  -- An inversion lemma for _∘⟨_⟩_.

  inv-ne-∘ : Neutral V ∇ (t ∘⟨ p ⟩ u) → Neutral V ∇ t
  inv-ne-∘ (∘ₙ b) = b

opaque

  -- An inversion lemma for fst.

  inv-ne-fst : Neutral V ∇ (fst p t) → Neutral V ∇ t
  inv-ne-fst (fstₙ b) = b

opaque

  -- An inversion lemma for snd.

  inv-ne-snd : Neutral V ∇ (snd p t) → Neutral V ∇ t
  inv-ne-snd (sndₙ b) = b

opaque

  -- An inversion lemma for natrec.

  inv-ne-natrec : Neutral V ∇ (natrec p q r A t u v) → Neutral V ∇ v
  inv-ne-natrec (natrecₙ b) = b

opaque

  -- An inversion lemma for prodrec.

  inv-ne-prodrec : Neutral V ∇ (prodrec r p q A t u) → Neutral V ∇ t
  inv-ne-prodrec (prodrecₙ b) = b

opaque

  -- An inversion lemma for emptyrec.

  inv-ne-emptyrec : Neutral V ∇ (emptyrec p A t) → Neutral V ∇ t
  inv-ne-emptyrec (emptyrecₙ b) = b

opaque

  -- An inversion lemma for unitrec.

  inv-ne-unitrec :
    Neutral V ∇ (unitrec l p q A t u) → ¬ Unitʷ-η × Neutral V ∇ t
  inv-ne-unitrec (unitrecₙ no-η b) = no-η , b

opaque

  -- An inversion lemma for J.

  inv-ne-J : Neutral V ∇ (J p q A t B u v w) → Neutral V ∇ w
  inv-ne-J (Jₙ b) = b

opaque

  -- An inversion lemma for K.

  inv-ne-K : Neutral V ∇ (K p A t B u v) → Neutral V ∇ v
  inv-ne-K (Kₙ b) = b

opaque

  -- An inversion lemma for []-cong.

  inv-ne-[]-cong : Neutral V ∇ ([]-cong s A t u v) → Neutral V ∇ v
  inv-ne-[]-cong ([]-congₙ b) = b

------------------------------------------------------------------------
-- Specializations

Neutral⁺ : DCon (Term 0) m → Term n → Set a
Neutral⁺ ∇ t = Neutral (Lift _ ⊤) ∇ t

opaque

  defn⁺ : α ↦⊘∷ A ∈ ∇ → Neutral⁺ {n = n} ∇ (defn α)
  defn⁺ = defn

opaque

  var⁺ : ∀ x → Neutral⁺ {n = n} ∇ (var x)
  var⁺ = var (lift tt)

opaque

  ne↑⁺ : Neutral V ∇ t → Neutral⁺ ∇ t
  ne↑⁺ = ne↑ (lift tt)

Neutral⁻ : DCon (Term 0) m → Term n → Set a
Neutral⁻ ∇ t = Neutral (Lift _ ⊥) ∇ t

opaque

  defn⁻ : α ↦⊘∷ A ∈ ∇ → Neutral⁻ {n = n} ∇ (defn α)
  defn⁻ = defn

opaque

  ne→⁻ : Neutral⁻ ∇ t → Neutral V ∇ t
  ne→⁻ = ne→ (⊥-elim ∘→ Lift.lower)

opaque

  dichotomy-ne : Neutral V ∇ t → Neutral⁻ ∇ t ⊎ V
  dichotomy-ne (defn α↦⊘)        = inj₁ (defn α↦⊘)
  dichotomy-ne (var ok x)        = inj₂ ok
  dichotomy-ne (∘ₙ b)            = ⊎-map ∘ₙ idᶠ (dichotomy-ne b)
  dichotomy-ne (fstₙ b)          = ⊎-map fstₙ idᶠ (dichotomy-ne b)
  dichotomy-ne (sndₙ b)          = ⊎-map sndₙ idᶠ (dichotomy-ne b)
  dichotomy-ne (natrecₙ b)       = ⊎-map natrecₙ idᶠ (dichotomy-ne b)
  dichotomy-ne (prodrecₙ b)      = ⊎-map prodrecₙ idᶠ (dichotomy-ne b)
  dichotomy-ne (emptyrecₙ b)     = ⊎-map emptyrecₙ idᶠ (dichotomy-ne b)
  dichotomy-ne (unitrecₙ no-η b) = ⊎-map (unitrecₙ no-η) idᶠ (dichotomy-ne b)
  dichotomy-ne (Jₙ b)            = ⊎-map Jₙ idᶠ (dichotomy-ne b)
  dichotomy-ne (Kₙ b)            = ⊎-map Kₙ idᶠ (dichotomy-ne b)
  dichotomy-ne ([]-congₙ b)      = ⊎-map []-congₙ idᶠ (dichotomy-ne b)

opaque

  closed-ne : {t : Term 0} → Neutral V ∇ t → Neutral⁻ ∇ t
  closed-ne (defn α↦⊘)        = defn α↦⊘
  closed-ne (var _ ())
  closed-ne (∘ₙ b)            = ∘ₙ (closed-ne b)
  closed-ne (fstₙ b)          = fstₙ (closed-ne b)
  closed-ne (sndₙ b)          = sndₙ (closed-ne b)
  closed-ne (natrecₙ b)       = natrecₙ (closed-ne b)
  closed-ne (prodrecₙ b)      = prodrecₙ (closed-ne b)
  closed-ne (emptyrecₙ b)     = emptyrecₙ (closed-ne b)
  closed-ne (unitrecₙ no-η b) = unitrecₙ no-η (closed-ne b)
  closed-ne (Jₙ b)            = Jₙ (closed-ne b)
  closed-ne (Kₙ b)            = Kₙ (closed-ne b)
  closed-ne ([]-congₙ b)      = []-congₙ (closed-ne b)
