------------------------------------------------------------------------
-- A modality for affine types.
------------------------------------------------------------------------

open import Tools.Bool

open import Graded.Modality.Instances.Zero-one-many true as 𝟘𝟙ω

open import Graded.Mode.Restrictions

module Graded.Modality.Instances.Affine
  (mrs : Mode-restrictions)
  where

open Mode-restrictions mrs

open 𝟘𝟙ω renaming (Zero-one-many to Affine) public

open import Graded.Modality Affine
open import Graded.FullReduction.Assumptions

open import Definition.Typed.Restrictions Affine

open import Tools.Empty
open import Tools.Function
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum
open import Tools.Unit

private variable
  p  : Affine
  rs : Type-restrictions

-- An "affine types" modality.

affineModality : Modality
affineModality = zero-one-many-greatest mrs

-- 𝟘 is the largest element.

≤𝟘 : p ≤ 𝟘
≤𝟘 {p = 𝟘} = refl
≤𝟘 {p = 𝟙} = refl
≤𝟘 {p = ω} = refl

-- An instance of Type-restrictions is suitable for the full reduction
-- theorem if
-- * Σₚ-allowed 𝟘 p implies that 𝟘ᵐ is allowed, and
-- * Σₚ-allowed ω p does not hold.

Suitable-for-full-reduction :
  Type-restrictions → Set
Suitable-for-full-reduction rs =
  (∀ p → Σₚ-allowed 𝟘 p → T 𝟘ᵐ-allowed) ×
  (∀ p → ¬ Σₚ-allowed ω p)
  where
  open Type-restrictions rs

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ Suitable-for-full-reduction
suitable-for-full-reduction rs =
    record rs
      { ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q × T 𝟘ᵐ-allowed × p ≢ ω
      }
  , (λ _ → proj₁ ∘→ proj₂)
  , (λ _ → (_$ refl) ∘→ proj₂ ∘→ proj₂)
  where
  open Type-restrictions rs

-- The full reduction assumptions hold for affineModality and any
-- "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction rs →
  Full-reduction-assumptions affineModality rs
full-reduction-assumptions (𝟘→𝟘ᵐ , ¬ω) = record
  { 𝟙≤𝟘    = λ _ → refl
  ; ≡𝟙⊎𝟙≤𝟘 = λ where
      {p = ω} ok → ⊥-elim (¬ω _ ok)
      {p = 𝟙} _  → inj₁ refl
      {p = 𝟘} ok → inj₂ (refl , 𝟘→𝟘ᵐ _ ok , refl)
  }
