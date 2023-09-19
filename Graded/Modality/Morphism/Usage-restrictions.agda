------------------------------------------------------------------------
-- Preserving/reflecting usage restrictions
------------------------------------------------------------------------

module Graded.Modality.Morphism.Usage-restrictions where

open import Tools.Function
open import Tools.Level

open import Graded.Usage.Restrictions

private variable
  R R₁ R₂ R₃          : Usage-restrictions _
  M M₁ M₂             : Set _
  tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q r               : M

------------------------------------------------------------------------
-- Are-preserving-usage-restrictions and
-- Are-reflecting-usage-restrictions

-- The property of preserving Usage-restrictions.

record Are-preserving-usage-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (R₁ : Usage-restrictions M₁) (R₂ : Usage-restrictions M₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂

  field
    -- The functions tr and tr-Σ preserve the Prodrec-allowed property
    -- in a certain way.
    Prodrec-preserved :
      R₁.Prodrec-allowed r p q →
      R₂.Prodrec-allowed (tr r) (tr-Σ p) (tr q)

-- The property of reflecting Usage-restrictions.

record Are-reflecting-usage-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (R₁ : Usage-restrictions M₁) (R₂ : Usage-restrictions M₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂

  field
    -- The functions tr and tr-Σ reflect the Prodrec-allowed property
    -- in a certain way.
    Prodrec-reflected :
      R₂.Prodrec-allowed (tr r) (tr-Σ p) (tr q) →
      R₁.Prodrec-allowed r p q

------------------------------------------------------------------------
-- Identity

-- For every value R of type Usage-restrictions the identity function
-- preserves Usage-restrictions for R and R.

Are-preserving-usage-restrictions-id :
  Are-preserving-usage-restrictions R R idᶠ idᶠ
Are-preserving-usage-restrictions-id {R = R} = λ where
    .Prodrec-preserved → idᶠ
  where
  open Are-preserving-usage-restrictions
  open Usage-restrictions R

-- For every value R of type Usage-restrictions the identity function
-- reflects Usage-restrictions for R and R.

Are-reflecting-usage-restrictions-id :
  Are-reflecting-usage-restrictions R R idᶠ idᶠ
Are-reflecting-usage-restrictions-id {R = R} = λ where
    .Prodrec-reflected → idᶠ
  where
  open Are-reflecting-usage-restrictions
  open Usage-restrictions R

------------------------------------------------------------------------
-- Composition

-- Composition preserves Are-preserving-usage-restrictions.

Are-preserving-usage-restrictions-∘ :
  Are-preserving-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
  Are-preserving-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
  Are-preserving-usage-restrictions
    R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Are-preserving-usage-restrictions-∘ m₁ m₂ = λ where
    .Prodrec-preserved →
      M₁.Prodrec-preserved ∘→ M₂.Prodrec-preserved
  where
  open Are-preserving-usage-restrictions
  module M₁ = Are-preserving-usage-restrictions m₁
  module M₂ = Are-preserving-usage-restrictions m₂

-- Composition preserves Are-reflecting-usage-restrictions.

Are-reflecting-usage-restrictions-∘ :
  Are-reflecting-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
  Are-reflecting-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
  Are-reflecting-usage-restrictions R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Are-reflecting-usage-restrictions-∘ m₁ m₂ = λ where
    .Prodrec-reflected →
      M₂.Prodrec-reflected ∘→ M₁.Prodrec-reflected
  where
  open Are-reflecting-usage-restrictions
  module M₁ = Are-reflecting-usage-restrictions m₁
  module M₂ = Are-reflecting-usage-restrictions m₂
