------------------------------------------------------------------------
-- Preserving/reflecting type restrictions
------------------------------------------------------------------------

module Graded.Modality.Morphism.Type-restrictions where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

open import Definition.Typed.Restrictions

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

open import Graded.Modality

private variable
  R R₁ R₂ R₃          : Type-restrictions _
  b                   : BinderMode
  M M₁ M₂             : Set _
  tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q                 : M
  s                   : Strength

------------------------------------------------------------------------
-- Are-preserving-type-restrictions and
-- Are-reflecting-type-restrictions

-- The property of preserving Type-restrictions.

record Are-preserving-type-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
         (R₁ : Type-restrictions 𝕄₁) (R₂ : Type-restrictions 𝕄₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module R₁ = Type-restrictions R₁
    module R₂ = Type-restrictions R₂

  field
    -- R₁.Unitʷ-η implies R₂.Unitʷ-η.
    Unitʷ-η-preserved :
      R₁.Unitʷ-η → R₂.Unitʷ-η

    -- If R₁.Unit-allowed s holds, then R₂.Unit-allowed s holds.
    Unit-preserved :
      R₁.Unit-allowed s → R₂.Unit-allowed s

    -- The functions tr and tr-Σ preserve the ΠΣ-allowed property in a
    -- certain way.
    ΠΣ-preserved :
      R₁.ΠΣ-allowed b p q →
      R₂.ΠΣ-allowed b (tr-BinderMode tr tr-Σ b p) (tr q)

    -- If R₁.K-allowed holds, then R₂.K-allowed holds.
    K-preserved :
      R₁.K-allowed → R₂.K-allowed

    -- If R₁.[]-cong-allowed holds, then R₂.[]-cong-allowed holds.
    []-cong-preserved :
      R₁.[]-cong-allowed s → R₂.[]-cong-allowed s

-- The property of reflecting Type-restrictions.

record Are-reflecting-type-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
         (R₁ : Type-restrictions 𝕄₁) (R₂ : Type-restrictions 𝕄₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module R₁ = Type-restrictions R₁
    module R₂ = Type-restrictions R₂

  field
    -- R₂.Unitʷ-η implies R₁.Unitʷ-η.
    Unitʷ-η-reflected :
      R₂.Unitʷ-η → R₁.Unitʷ-η

    -- If R₂.Unit-allowed s holds, then R₁.Unit-allowed s holds.
    Unit-reflected :
      R₂.Unit-allowed s → R₁.Unit-allowed s

    -- The functions tr and tr-Σ reflect the ΠΣ-allowed property in a
    -- certain way.
    ΠΣ-reflected :
      R₂.ΠΣ-allowed b (tr-BinderMode tr tr-Σ b p) (tr q) →
      R₁.ΠΣ-allowed b p q

    -- If R₂.K-allowed holds, then R₁.K-allowed holds.
    K-reflected :
      R₂.K-allowed → R₁.K-allowed

    -- If R₂.[]-cong-allowed s holds or 𝕄₂ is trivial, then
    -- R₁.[]-cong-allowed s holds or 𝕄₁ is trivial.
    []-cong-reflected :
      R₂.[]-cong-allowed s ⊎ M₂.Trivial →
      R₁.[]-cong-allowed s ⊎ M₁.Trivial

------------------------------------------------------------------------
-- Identity

-- For every value R of type Type-restrictions 𝕄 the identity function
-- preserves Type-restrictions for R and R.

Are-preserving-type-restrictions-id :
  Are-preserving-type-restrictions R R idᶠ idᶠ
Are-preserving-type-restrictions-id {R = R} = λ where
    .Unitʷ-η-preserved        → idᶠ
    .Unit-preserved           → idᶠ
    .ΠΣ-preserved {b = BMΠ}   → idᶠ
    .ΠΣ-preserved {b = BMΣ _} → idᶠ
    .K-preserved              → idᶠ
    .[]-cong-preserved        → idᶠ
  where
  open Are-preserving-type-restrictions
  open Type-restrictions R

-- For every value R of type Type-restrictions 𝕄 the identity function
-- reflects Type-restrictions for R and R.

Are-reflecting-type-restrictions-id :
  Are-reflecting-type-restrictions R R idᶠ idᶠ
Are-reflecting-type-restrictions-id {R = R} = λ where
    .Unitʷ-η-reflected        → idᶠ
    .Unit-reflected           → idᶠ
    .ΠΣ-reflected {b = BMΠ}   → idᶠ
    .ΠΣ-reflected {b = BMΣ _} → idᶠ
    .K-reflected              → idᶠ
    .[]-cong-reflected        → idᶠ
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
    .Unitʷ-η-preserved →
      M₁.Unitʷ-η-preserved ∘→ M₂.Unitʷ-η-preserved
    .Unit-preserved →
      M₁.Unit-preserved ∘→ M₂.Unit-preserved
    .ΠΣ-preserved {b = BMΠ} →
      M₁.ΠΣ-preserved ∘→ M₂.ΠΣ-preserved
    .ΠΣ-preserved {b = BMΣ _} →
      M₁.ΠΣ-preserved ∘→ M₂.ΠΣ-preserved
    .K-preserved →
      M₁.K-preserved ∘→ M₂.K-preserved
    .[]-cong-preserved →
      M₁.[]-cong-preserved ∘→ M₂.[]-cong-preserved
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
    .Unitʷ-η-reflected →
      M₂.Unitʷ-η-reflected ∘→ M₁.Unitʷ-η-reflected
    .Unit-reflected →
      M₂.Unit-reflected ∘→ M₁.Unit-reflected
    .ΠΣ-reflected {b = BMΠ} →
      M₂.ΠΣ-reflected ∘→ M₁.ΠΣ-reflected
    .ΠΣ-reflected {b = BMΣ _} →
      M₂.ΠΣ-reflected ∘→ M₁.ΠΣ-reflected
    .K-reflected →
      M₂.K-reflected ∘→ M₁.K-reflected
    .[]-cong-reflected →
      M₂.[]-cong-reflected ∘→ M₁.[]-cong-reflected
  where
  open Are-reflecting-type-restrictions
  module M₁ = Are-reflecting-type-restrictions m₁
  module M₂ = Are-reflecting-type-restrictions m₂
