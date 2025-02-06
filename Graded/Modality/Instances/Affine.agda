------------------------------------------------------------------------
-- A modality for affine types.
------------------------------------------------------------------------

open import Tools.Bool
open import Tools.Level

open import Graded.Modality.Instances.Zero-one-many true as 𝟘𝟙ω
open import Graded.Modality.Variant lzero

module Graded.Modality.Instances.Affine
  -- The modality variant.
  (variant : Modality-variant)
  where

open Modality-variant variant

open 𝟘𝟙ω renaming (Zero-one-many to Affine) public

open import Graded.Modality Affine
import Graded.Modality.Properties
open import Graded.FullReduction.Assumptions
import Graded.Usage.Restrictions

import Definition.Typed.Restrictions
open import Definition.Untyped

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  p  : Affine

-- An "affine types" modality.

affineModality : Modality
affineModality = zero-one-many-modality variant

open Definition.Typed.Restrictions affineModality
open Graded.Modality.Properties    affineModality
open Graded.Usage.Restrictions     affineModality

private variable
  rs : Type-restrictions
  us : Usage-restrictions

-- The nr function obtained from zero-one-many-greatest-star-nr is
-- strictly greater than the one obtained from zero-one-many-has-nr.

alternative-greater :
  let nr₁ = zero-one-many-has-nr .Has-nr.nr
      nr₂ = zero-one-many-greatest-star-nr .Has-nr.nr
  in
  (∃₅ λ p r z s n → ¬ nr₁ p r z s n ≡ nr₂ p r z s n) ×
  (∀ p r z s n → nr₁ p r z s n ≤ nr₂ p r z s n)
alternative-greater =
    (𝟘 , 𝟙 , 𝟙 , 𝟘 , 𝟙 , (λ ()))
  , λ where
      𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      𝟘 𝟘 𝟘 𝟘 𝟙 → refl
      𝟘 𝟘 𝟘 𝟘 ω → refl
      𝟘 𝟘 𝟘 𝟙 𝟘 → refl
      𝟘 𝟘 𝟘 𝟙 𝟙 → refl
      𝟘 𝟘 𝟘 𝟙 ω → refl
      𝟘 𝟘 𝟘 ω 𝟘 → refl
      𝟘 𝟘 𝟘 ω 𝟙 → refl
      𝟘 𝟘 𝟘 ω ω → refl
      𝟘 𝟘 𝟙 𝟘 𝟘 → refl
      𝟘 𝟘 𝟙 𝟘 𝟙 → refl
      𝟘 𝟘 𝟙 𝟘 ω → refl
      𝟘 𝟘 𝟙 𝟙 𝟘 → refl
      𝟘 𝟘 𝟙 𝟙 𝟙 → refl
      𝟘 𝟘 𝟙 𝟙 ω → refl
      𝟘 𝟘 𝟙 ω 𝟘 → refl
      𝟘 𝟘 𝟙 ω 𝟙 → refl
      𝟘 𝟘 𝟙 ω ω → refl
      𝟘 𝟘 ω 𝟘 𝟘 → refl
      𝟘 𝟘 ω 𝟘 𝟙 → refl
      𝟘 𝟘 ω 𝟘 ω → refl
      𝟘 𝟘 ω 𝟙 𝟘 → refl
      𝟘 𝟘 ω 𝟙 𝟙 → refl
      𝟘 𝟘 ω 𝟙 ω → refl
      𝟘 𝟘 ω ω 𝟘 → refl
      𝟘 𝟘 ω ω 𝟙 → refl
      𝟘 𝟘 ω ω ω → refl
      𝟘 𝟙 𝟘 𝟘 𝟘 → refl
      𝟘 𝟙 𝟘 𝟘 𝟙 → refl
      𝟘 𝟙 𝟘 𝟘 ω → refl
      𝟘 𝟙 𝟘 𝟙 𝟘 → refl
      𝟘 𝟙 𝟘 𝟙 𝟙 → refl
      𝟘 𝟙 𝟘 𝟙 ω → refl
      𝟘 𝟙 𝟘 ω 𝟘 → refl
      𝟘 𝟙 𝟘 ω 𝟙 → refl
      𝟘 𝟙 𝟘 ω ω → refl
      𝟘 𝟙 𝟙 𝟘 𝟘 → refl
      𝟘 𝟙 𝟙 𝟘 𝟙 → refl
      𝟘 𝟙 𝟙 𝟘 ω → refl
      𝟘 𝟙 𝟙 𝟙 𝟘 → refl
      𝟘 𝟙 𝟙 𝟙 𝟙 → refl
      𝟘 𝟙 𝟙 𝟙 ω → refl
      𝟘 𝟙 𝟙 ω 𝟘 → refl
      𝟘 𝟙 𝟙 ω 𝟙 → refl
      𝟘 𝟙 𝟙 ω ω → refl
      𝟘 𝟙 ω 𝟘 𝟘 → refl
      𝟘 𝟙 ω 𝟘 𝟙 → refl
      𝟘 𝟙 ω 𝟘 ω → refl
      𝟘 𝟙 ω 𝟙 𝟘 → refl
      𝟘 𝟙 ω 𝟙 𝟙 → refl
      𝟘 𝟙 ω 𝟙 ω → refl
      𝟘 𝟙 ω ω 𝟘 → refl
      𝟘 𝟙 ω ω 𝟙 → refl
      𝟘 𝟙 ω ω ω → refl
      𝟘 ω 𝟘 𝟘 𝟘 → refl
      𝟘 ω 𝟘 𝟘 𝟙 → refl
      𝟘 ω 𝟘 𝟘 ω → refl
      𝟘 ω 𝟘 𝟙 𝟘 → refl
      𝟘 ω 𝟘 𝟙 𝟙 → refl
      𝟘 ω 𝟘 𝟙 ω → refl
      𝟘 ω 𝟘 ω 𝟘 → refl
      𝟘 ω 𝟘 ω 𝟙 → refl
      𝟘 ω 𝟘 ω ω → refl
      𝟘 ω 𝟙 𝟘 𝟘 → refl
      𝟘 ω 𝟙 𝟘 𝟙 → refl
      𝟘 ω 𝟙 𝟘 ω → refl
      𝟘 ω 𝟙 𝟙 𝟘 → refl
      𝟘 ω 𝟙 𝟙 𝟙 → refl
      𝟘 ω 𝟙 𝟙 ω → refl
      𝟘 ω 𝟙 ω 𝟘 → refl
      𝟘 ω 𝟙 ω 𝟙 → refl
      𝟘 ω 𝟙 ω ω → refl
      𝟘 ω ω 𝟘 𝟘 → refl
      𝟘 ω ω 𝟘 𝟙 → refl
      𝟘 ω ω 𝟘 ω → refl
      𝟘 ω ω 𝟙 𝟘 → refl
      𝟘 ω ω 𝟙 𝟙 → refl
      𝟘 ω ω 𝟙 ω → refl
      𝟘 ω ω ω 𝟘 → refl
      𝟘 ω ω ω 𝟙 → refl
      𝟘 ω ω ω ω → refl
      𝟙 𝟘 𝟘 𝟘 𝟘 → refl
      𝟙 𝟘 𝟘 𝟘 𝟙 → refl
      𝟙 𝟘 𝟘 𝟘 ω → refl
      𝟙 𝟘 𝟘 𝟙 𝟘 → refl
      𝟙 𝟘 𝟘 𝟙 𝟙 → refl
      𝟙 𝟘 𝟘 𝟙 ω → refl
      𝟙 𝟘 𝟘 ω 𝟘 → refl
      𝟙 𝟘 𝟘 ω 𝟙 → refl
      𝟙 𝟘 𝟘 ω ω → refl
      𝟙 𝟘 𝟙 𝟘 𝟘 → refl
      𝟙 𝟘 𝟙 𝟘 𝟙 → refl
      𝟙 𝟘 𝟙 𝟘 ω → refl
      𝟙 𝟘 𝟙 𝟙 𝟘 → refl
      𝟙 𝟘 𝟙 𝟙 𝟙 → refl
      𝟙 𝟘 𝟙 𝟙 ω → refl
      𝟙 𝟘 𝟙 ω 𝟘 → refl
      𝟙 𝟘 𝟙 ω 𝟙 → refl
      𝟙 𝟘 𝟙 ω ω → refl
      𝟙 𝟘 ω 𝟘 𝟘 → refl
      𝟙 𝟘 ω 𝟘 𝟙 → refl
      𝟙 𝟘 ω 𝟘 ω → refl
      𝟙 𝟘 ω 𝟙 𝟘 → refl
      𝟙 𝟘 ω 𝟙 𝟙 → refl
      𝟙 𝟘 ω 𝟙 ω → refl
      𝟙 𝟘 ω ω 𝟘 → refl
      𝟙 𝟘 ω ω 𝟙 → refl
      𝟙 𝟘 ω ω ω → refl
      𝟙 𝟙 𝟘 𝟘 𝟘 → refl
      𝟙 𝟙 𝟘 𝟘 𝟙 → refl
      𝟙 𝟙 𝟘 𝟘 ω → refl
      𝟙 𝟙 𝟘 𝟙 𝟘 → refl
      𝟙 𝟙 𝟘 𝟙 𝟙 → refl
      𝟙 𝟙 𝟘 𝟙 ω → refl
      𝟙 𝟙 𝟘 ω 𝟘 → refl
      𝟙 𝟙 𝟘 ω 𝟙 → refl
      𝟙 𝟙 𝟘 ω ω → refl
      𝟙 𝟙 𝟙 𝟘 𝟘 → refl
      𝟙 𝟙 𝟙 𝟘 𝟙 → refl
      𝟙 𝟙 𝟙 𝟘 ω → refl
      𝟙 𝟙 𝟙 𝟙 𝟘 → refl
      𝟙 𝟙 𝟙 𝟙 𝟙 → refl
      𝟙 𝟙 𝟙 𝟙 ω → refl
      𝟙 𝟙 𝟙 ω 𝟘 → refl
      𝟙 𝟙 𝟙 ω 𝟙 → refl
      𝟙 𝟙 𝟙 ω ω → refl
      𝟙 𝟙 ω 𝟘 𝟘 → refl
      𝟙 𝟙 ω 𝟘 𝟙 → refl
      𝟙 𝟙 ω 𝟘 ω → refl
      𝟙 𝟙 ω 𝟙 𝟘 → refl
      𝟙 𝟙 ω 𝟙 𝟙 → refl
      𝟙 𝟙 ω 𝟙 ω → refl
      𝟙 𝟙 ω ω 𝟘 → refl
      𝟙 𝟙 ω ω 𝟙 → refl
      𝟙 𝟙 ω ω ω → refl
      𝟙 ω 𝟘 𝟘 𝟘 → refl
      𝟙 ω 𝟘 𝟘 𝟙 → refl
      𝟙 ω 𝟘 𝟘 ω → refl
      𝟙 ω 𝟘 𝟙 𝟘 → refl
      𝟙 ω 𝟘 𝟙 𝟙 → refl
      𝟙 ω 𝟘 𝟙 ω → refl
      𝟙 ω 𝟘 ω 𝟘 → refl
      𝟙 ω 𝟘 ω 𝟙 → refl
      𝟙 ω 𝟘 ω ω → refl
      𝟙 ω 𝟙 𝟘 𝟘 → refl
      𝟙 ω 𝟙 𝟘 𝟙 → refl
      𝟙 ω 𝟙 𝟘 ω → refl
      𝟙 ω 𝟙 𝟙 𝟘 → refl
      𝟙 ω 𝟙 𝟙 𝟙 → refl
      𝟙 ω 𝟙 𝟙 ω → refl
      𝟙 ω 𝟙 ω 𝟘 → refl
      𝟙 ω 𝟙 ω 𝟙 → refl
      𝟙 ω 𝟙 ω ω → refl
      𝟙 ω ω 𝟘 𝟘 → refl
      𝟙 ω ω 𝟘 𝟙 → refl
      𝟙 ω ω 𝟘 ω → refl
      𝟙 ω ω 𝟙 𝟘 → refl
      𝟙 ω ω 𝟙 𝟙 → refl
      𝟙 ω ω 𝟙 ω → refl
      𝟙 ω ω ω 𝟘 → refl
      𝟙 ω ω ω 𝟙 → refl
      𝟙 ω ω ω ω → refl
      ω 𝟘 𝟘 𝟘 𝟘 → refl
      ω 𝟘 𝟘 𝟘 𝟙 → refl
      ω 𝟘 𝟘 𝟘 ω → refl
      ω 𝟘 𝟘 𝟙 𝟘 → refl
      ω 𝟘 𝟘 𝟙 𝟙 → refl
      ω 𝟘 𝟘 𝟙 ω → refl
      ω 𝟘 𝟘 ω 𝟘 → refl
      ω 𝟘 𝟘 ω 𝟙 → refl
      ω 𝟘 𝟘 ω ω → refl
      ω 𝟘 𝟙 𝟘 𝟘 → refl
      ω 𝟘 𝟙 𝟘 𝟙 → refl
      ω 𝟘 𝟙 𝟘 ω → refl
      ω 𝟘 𝟙 𝟙 𝟘 → refl
      ω 𝟘 𝟙 𝟙 𝟙 → refl
      ω 𝟘 𝟙 𝟙 ω → refl
      ω 𝟘 𝟙 ω 𝟘 → refl
      ω 𝟘 𝟙 ω 𝟙 → refl
      ω 𝟘 𝟙 ω ω → refl
      ω 𝟘 ω 𝟘 𝟘 → refl
      ω 𝟘 ω 𝟘 𝟙 → refl
      ω 𝟘 ω 𝟘 ω → refl
      ω 𝟘 ω 𝟙 𝟘 → refl
      ω 𝟘 ω 𝟙 𝟙 → refl
      ω 𝟘 ω 𝟙 ω → refl
      ω 𝟘 ω ω 𝟘 → refl
      ω 𝟘 ω ω 𝟙 → refl
      ω 𝟘 ω ω ω → refl
      ω 𝟙 𝟘 𝟘 𝟘 → refl
      ω 𝟙 𝟘 𝟘 𝟙 → refl
      ω 𝟙 𝟘 𝟘 ω → refl
      ω 𝟙 𝟘 𝟙 𝟘 → refl
      ω 𝟙 𝟘 𝟙 𝟙 → refl
      ω 𝟙 𝟘 𝟙 ω → refl
      ω 𝟙 𝟘 ω 𝟘 → refl
      ω 𝟙 𝟘 ω 𝟙 → refl
      ω 𝟙 𝟘 ω ω → refl
      ω 𝟙 𝟙 𝟘 𝟘 → refl
      ω 𝟙 𝟙 𝟘 𝟙 → refl
      ω 𝟙 𝟙 𝟘 ω → refl
      ω 𝟙 𝟙 𝟙 𝟘 → refl
      ω 𝟙 𝟙 𝟙 𝟙 → refl
      ω 𝟙 𝟙 𝟙 ω → refl
      ω 𝟙 𝟙 ω 𝟘 → refl
      ω 𝟙 𝟙 ω 𝟙 → refl
      ω 𝟙 𝟙 ω ω → refl
      ω 𝟙 ω 𝟘 𝟘 → refl
      ω 𝟙 ω 𝟘 𝟙 → refl
      ω 𝟙 ω 𝟘 ω → refl
      ω 𝟙 ω 𝟙 𝟘 → refl
      ω 𝟙 ω 𝟙 𝟙 → refl
      ω 𝟙 ω 𝟙 ω → refl
      ω 𝟙 ω ω 𝟘 → refl
      ω 𝟙 ω ω 𝟙 → refl
      ω 𝟙 ω ω ω → refl
      ω ω 𝟘 𝟘 𝟘 → refl
      ω ω 𝟘 𝟘 𝟙 → refl
      ω ω 𝟘 𝟘 ω → refl
      ω ω 𝟘 𝟙 𝟘 → refl
      ω ω 𝟘 𝟙 𝟙 → refl
      ω ω 𝟘 𝟙 ω → refl
      ω ω 𝟘 ω 𝟘 → refl
      ω ω 𝟘 ω 𝟙 → refl
      ω ω 𝟘 ω ω → refl
      ω ω 𝟙 𝟘 𝟘 → refl
      ω ω 𝟙 𝟘 𝟙 → refl
      ω ω 𝟙 𝟘 ω → refl
      ω ω 𝟙 𝟙 𝟘 → refl
      ω ω 𝟙 𝟙 𝟙 → refl
      ω ω 𝟙 𝟙 ω → refl
      ω ω 𝟙 ω 𝟘 → refl
      ω ω 𝟙 ω 𝟙 → refl
      ω ω 𝟙 ω ω → refl
      ω ω ω 𝟘 𝟘 → refl
      ω ω ω 𝟘 𝟙 → refl
      ω ω ω 𝟘 ω → refl
      ω ω ω 𝟙 𝟘 → refl
      ω ω ω 𝟙 𝟙 → refl
      ω ω ω 𝟙 ω → refl
      ω ω ω ω 𝟘 → refl
      ω ω ω ω 𝟙 → refl
      ω ω ω ω ω → refl

instance

  -- The "affine types" modality has a well-behaved zero.

  affine-has-well-behaved-zero :
    Has-well-behaved-zero (Modality.semiring-with-meet affineModality)
  affine-has-well-behaved-zero = zero-one-many-has-well-behaved-zero

-- 𝟘 is the largest element.

≤𝟘 : p ≤ 𝟘
≤𝟘 {p = 𝟘} = refl
≤𝟘 {p = 𝟙} = refl
≤𝟘 {p = ω} = refl

-- An instance of Type-restrictions is suitable for the full reduction
-- theorem if
-- * Σˢ-allowed 𝟘 p implies that 𝟘ᵐ is allowed, and
-- * Σˢ-allowed ω p does not hold.

Suitable-for-full-reduction :
  Type-restrictions → Set
Suitable-for-full-reduction rs =
  (∀ p → Σˢ-allowed 𝟘 p → T 𝟘ᵐ-allowed) ×
  (∀ p → ¬ Σˢ-allowed ω p)
  where
  open Type-restrictions rs

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ Suitable-for-full-reduction
suitable-for-full-reduction rs =
    record rs
      { ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q ×
          (b ≡ BMΣ 𝕤 × p ≡ 𝟘 → T 𝟘ᵐ-allowed) ×
          ¬ (b ≡ BMΣ 𝕤 × p ≡ ω)
      ; []-cong-allowed = λ s →
          []-cong-allowed s × T 𝟘ᵐ-allowed
      ; []-cong→Erased = λ (ok₁ , ok₂) →
            []-cong→Erased ok₁ .proj₁ , []-cong→Erased ok₁ .proj₂
          , (λ _ → ok₂) , λ ()
      ; []-cong→¬Trivial =
          𝟘ᵐ.non-trivial ∘→ proj₂
      }
  , (λ _ → (_$ (refl , refl)) ∘→ proj₁ ∘→ proj₂)
  , (λ _ → (_$ (refl , refl)) ∘→ proj₂ ∘→ proj₂)
  where
  open Type-restrictions rs

-- The full reduction assumptions hold for affineModality and any
-- "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction rs →
  Full-reduction-assumptions rs us
full-reduction-assumptions (𝟘→𝟘ᵐ , ¬ω) = record
  { sink⊎𝟙≤𝟘 = λ _ _ → inj₂ refl
  ; ≡𝟙⊎𝟙≤𝟘   = λ where
      {p = ω} ok → ⊥-elim (¬ω _ ok)
      {p = 𝟙} _  → inj₁ refl
      {p = 𝟘} ok → inj₂ (refl , 𝟘→𝟘ᵐ _ ok , refl)
  }

-- Type and usage restrictions that satisfy the full reduction
-- assumptions are "suitable".

full-reduction-assumptions-suitable :
  Full-reduction-assumptions rs us → Suitable-for-full-reduction rs
full-reduction-assumptions-suitable as =
    (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
      (inj₁ ())
      (inj₂ (_ , 𝟘ᵐ-ok , _)) → 𝟘ᵐ-ok)
  , λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
      (inj₁ ())
      (inj₂ (() , _))
  where
  open Full-reduction-assumptions as
