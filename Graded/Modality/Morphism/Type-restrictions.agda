------------------------------------------------------------------------
-- Preserving/reflecting type restrictions
------------------------------------------------------------------------

module Graded.Modality.Morphism.Type-restrictions where

open import Tools.Function
open import Tools.Level

open import Definition.Typed.Restrictions

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  R R₁ R₂ R₃          : Type-restrictions _
  b                   : BinderMode
  M M₁ M₂             : Set _
  tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q                 : M

------------------------------------------------------------------------
-- Are-preserving-type-restrictions and
-- Are-reflecting-type-restrictions

-- The property of preserving Type-restrictions.

record Are-preserving-type-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (R₁ : Type-restrictions M₁) (R₂ : Type-restrictions M₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Type-restrictions R₁
    module R₂ = Type-restrictions R₂

  field
    -- If R₁.Unit-allowed holds, then R₂.Unit-allowed holds.
    Unit-preserved :
      R₁.Unit-allowed → R₂.Unit-allowed

    -- The functions tr and tr-Σ preserve the ΠΣ-allowed property in a
    -- certain way.
    ΠΣ-preserved :
      R₁.ΠΣ-allowed b p q →
      R₂.ΠΣ-allowed b (tr-BinderMode tr tr-Σ b p) (tr q)

-- The property of reflecting Type-restrictions.

record Are-reflecting-type-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (R₁ : Type-restrictions M₁) (R₂ : Type-restrictions M₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Type-restrictions R₁
    module R₂ = Type-restrictions R₂

  field
    -- If R₂.Unit-allowed holds, then R₁.Unit-allowed holds.
    Unit-reflected :
      R₂.Unit-allowed → R₁.Unit-allowed

    -- The functions tr and tr-Σ reflect the ΠΣ-allowed property in a
    -- certain way.
    ΠΣ-reflected :
      R₂.ΠΣ-allowed b (tr-BinderMode tr tr-Σ b p) (tr q) →
      R₁.ΠΣ-allowed b p q

------------------------------------------------------------------------
-- Identity

-- For every value R of type Type-restrictions the identity function
-- preserves Type-restrictions for R and R.

Are-preserving-type-restrictions-id :
  Are-preserving-type-restrictions R R idᶠ idᶠ
Are-preserving-type-restrictions-id {R = R} = λ where
    .Unit-preserved           → idᶠ
    .ΠΣ-preserved {b = BMΠ}   → idᶠ
    .ΠΣ-preserved {b = BMΣ _} → idᶠ
  where
  open Are-preserving-type-restrictions
  open Type-restrictions R

-- For every value R of type Type-restrictions the identity function
-- reflects Type-restrictions for R and R.

Are-reflecting-type-restrictions-id :
  Are-reflecting-type-restrictions R R idᶠ idᶠ
Are-reflecting-type-restrictions-id {R = R} = λ where
    .Unit-reflected           → idᶠ
    .ΠΣ-reflected {b = BMΠ}   → idᶠ
    .ΠΣ-reflected {b = BMΣ _} → idᶠ
  where
  open Are-reflecting-type-restrictions
  open Type-restrictions R

------------------------------------------------------------------------
-- Composition

-- Composition preserves Are-preserving-type-restrictions.

Are-preserving-type-restrictions-∘ :
  Are-preserving-type-restrictions R₂ R₃ tr₁ tr-Σ₁ →
  Are-preserving-type-restrictions R₁ R₂ tr₂ tr-Σ₂ →
  Are-preserving-type-restrictions
    R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Are-preserving-type-restrictions-∘ m₁ m₂ = λ where
    .Unit-preserved →
      M₁.Unit-preserved ∘→ M₂.Unit-preserved
    .ΠΣ-preserved {b = BMΠ} →
      M₁.ΠΣ-preserved ∘→ M₂.ΠΣ-preserved
    .ΠΣ-preserved {b = BMΣ _} →
      M₁.ΠΣ-preserved ∘→ M₂.ΠΣ-preserved
  where
  open Are-preserving-type-restrictions
  module M₁ = Are-preserving-type-restrictions m₁
  module M₂ = Are-preserving-type-restrictions m₂

-- Composition preserves Are-reflecting-type-restrictions.

Are-reflecting-type-restrictions-∘ :
  Are-reflecting-type-restrictions R₂ R₃ tr₁ tr-Σ₁ →
  Are-reflecting-type-restrictions R₁ R₂ tr₂ tr-Σ₂ →
  Are-reflecting-type-restrictions R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Are-reflecting-type-restrictions-∘ m₁ m₂ = λ where
    .Unit-reflected →
      M₂.Unit-reflected ∘→ M₁.Unit-reflected
    .ΠΣ-reflected {b = BMΠ} →
      M₂.ΠΣ-reflected ∘→ M₁.ΠΣ-reflected
    .ΠΣ-reflected {b = BMΣ _} →
      M₂.ΠΣ-reflected ∘→ M₁.ΠΣ-reflected
  where
  open Are-reflecting-type-restrictions
  module M₁ = Are-reflecting-type-restrictions m₁
  module M₂ = Are-reflecting-type-restrictions m₂
