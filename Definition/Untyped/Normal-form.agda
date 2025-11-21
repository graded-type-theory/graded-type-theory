------------------------------------------------------------------------
-- Normal forms
------------------------------------------------------------------------

open import Definition.Typed.Variant

module Definition.Untyped.Normal-form
  {a} (M : Set a)
  (type-variant : Type-variant)
  where

open Type-variant type-variant

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Tools.Fin
open import Tools.Nat
open import Tools.Relation

private variable
  ∇                        : DCon _ _
  A B C c g k l n t t′ u v : Term _
  p q r                    : M
  b                        : BinderMode
  s                        : Strength
  α                        : Nat

mutual

  -- Normal forms.

  data Nf {κ m : Nat} : DCon (Term 0) κ → Term m → Set a where
    Levelₙ : Nf ∇ Level
    zeroᵘₙ : Nf ∇ zeroᵘ
    sucᵘₙ  : Nf ∇ t → Nf ∇ (sucᵘ t)
    Uₙ     : Nf ∇ l → Nf ∇ (U l)
    Liftₙ  : Nf ∇ l → Nf ∇ A → Nf ∇ (Lift l A)
    liftₙ  : Nf ∇ t → Nf ∇ (lift t)
    ΠΣₙ    : Nf ∇ A → Nf ∇ B → Nf ∇ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
    ℕₙ     : Nf ∇ ℕ
    Emptyₙ : Nf ∇ Empty
    Unitₙ  : Nf ∇ (Unit s)
    Idₙ    : Nf ∇ A → Nf ∇ t → Nf ∇ u → Nf ∇ (Id A t u)

    lamₙ   : Nf ∇ t → Nf ∇ (lam q t)
    prodₙ  : Nf ∇ t → Nf ∇ u → Nf ∇ (prod s p t u)
    zeroₙ  : Nf ∇ zero
    sucₙ   : Nf ∇ t → Nf ∇ (suc t)
    starₙ  : Nf ∇ (star s)
    rflₙ   : Nf ∇ rfl

    ne     : NfNeutral ∇ n → Nf ∇ n

  -- Neutral terms for which the "non-neutral parts" are in normal
  -- form.

  data NfNeutral {κ m : Nat} : DCon (Term 0) κ → Term m → Set a where
    var       : (x : Fin m) → NfNeutral ∇ (var x)
    defn      : α ↦⊘∷ A ∈ ∇ → NfNeutral ∇ (defn α)
    supᵘˡₙ    : NfNeutral ∇ t → Nf ∇ u → NfNeutral ∇ (t supᵘ u)
    supᵘʳₙ    : Nf ∇ t → NfNeutral ∇ u → NfNeutral ∇ (sucᵘ t supᵘ u)
    lowerₙ    : NfNeutral ∇ t → NfNeutral ∇ (lower t)
    ∘ₙ        : NfNeutral ∇ k → Nf ∇ u → NfNeutral ∇ (k ∘⟨ q ⟩ u)
    fstₙ      : NfNeutral ∇ t → NfNeutral ∇ (fst p t)
    sndₙ      : NfNeutral ∇ t → NfNeutral ∇ (snd p t)
    natrecₙ   : Nf ∇ C → Nf ∇ c → Nf ∇ g → NfNeutral ∇ k →
                NfNeutral ∇ (natrec p q r C c g k)
    prodrecₙ  : Nf ∇ C → NfNeutral ∇ t → Nf ∇ u →
                NfNeutral ∇ (prodrec r p q C t u)
    emptyrecₙ : Nf ∇ C → NfNeutral ∇ k → NfNeutral ∇ (emptyrec p C k)
    unitrecₙ  : ¬ Unitʷ-η → Nf ∇ C → NfNeutral ∇ t → Nf ∇ u →
                NfNeutral ∇ (unitrec p q A t u)
    Jₙ        : Nf ∇ A → Nf ∇ t → Nf ∇ B → Nf ∇ u → Nf ∇ t′ → NfNeutral ∇ v →
                NfNeutral ∇ (J p q A t B u t′ v)
    Kₙ        : Nf ∇ A → Nf ∇ t → Nf ∇ B → Nf ∇ u → NfNeutral ∇ v →
                NfNeutral ∇ (K p A t B u v)
    []-congₙ  : Nf ∇ l → Nf ∇ A → Nf ∇ t → Nf ∇ u → NfNeutral ∇ v →
                NfNeutral ∇ ([]-cong s l A t u v)

-- If NfNeutral ∇ n holds, then n is neutral.

nfNeutral : NfNeutral ∇ n → Neutral⁺ ∇ n
nfNeutral = λ where
  (var _)                 → var⁺ _
  (defn α↦⊘)              → defn α↦⊘
  (supᵘˡₙ n x)            → supᵘˡₙ (nfNeutral n)
  (supᵘʳₙ x n)            → supᵘʳₙ (nfNeutral n)
  (lowerₙ n)              → lowerₙ (nfNeutral n)
  (∘ₙ n _)                → ∘ₙ (nfNeutral n)
  (fstₙ n)                → fstₙ (nfNeutral n)
  (sndₙ n)                → sndₙ (nfNeutral n)
  (natrecₙ _ _ _ n)       → natrecₙ (nfNeutral n)
  (prodrecₙ _ n _)        → prodrecₙ (nfNeutral n)
  (emptyrecₙ _ n)         → emptyrecₙ (nfNeutral n)
  (unitrecₙ not-ok _ n _) → unitrecₙ not-ok (nfNeutral n)
  (Jₙ _ _ _ _ _ n)        → Jₙ (nfNeutral n)
  (Kₙ _ _ _ _ n)          → Kₙ (nfNeutral n)
  ([]-congₙ _ _ _ _ n)    → []-congₙ (nfNeutral n)

-- Normal forms are in WHNF.

nfWhnf : Nf ∇ n → Whnf ∇ n
nfWhnf = λ where
  Levelₙ      → Levelₙ
  zeroᵘₙ      → zeroᵘₙ
  (sucᵘₙ _)   → sucᵘₙ
  (Uₙ _)      → Uₙ
  (Liftₙ _ _) → Liftₙ
  (liftₙ _)   → liftₙ
  (ΠΣₙ _ _)   → ΠΣₙ
  ℕₙ          → ℕₙ
  Emptyₙ      → Emptyₙ
  Unitₙ       → Unitₙ
  (Idₙ _ _ _) → Idₙ
  (lamₙ _)    → lamₙ
  (prodₙ _ _) → prodₙ
  zeroₙ       → zeroₙ
  (sucₙ _)    → sucₙ
  starₙ       → starₙ
  rflₙ        → rflₙ
  (ne n)      → ne (nfNeutral n)

opaque

  -- Level literals are in normal form.

  Level-literal→Nf : Level-literal l → Nf ∇ l
  Level-literal→Nf = λ where
    zeroᵘ    → zeroᵘₙ
    (sucᵘ l) → sucᵘₙ (Level-literal→Nf l)
