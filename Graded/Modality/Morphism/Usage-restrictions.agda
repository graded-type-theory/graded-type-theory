------------------------------------------------------------------------
-- Preserving/reflecting usage restrictions
------------------------------------------------------------------------

module Graded.Modality.Morphism.Usage-restrictions where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.PropositionalEquality

open import Graded.Usage.Restrictions

private variable
  R R₁ R₂ R₃          : Usage-restrictions _
  M M₁ M₂             : Set _
  tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q r               : M

------------------------------------------------------------------------
-- Are-preserving-usage-restrictions

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

    -- The function tr preserves the Unitrec-allowed property
    Unitrec-preserved :
      R₁.Unitrec-allowed p q →
      R₂.Unitrec-allowed (tr p) (tr q)

    -- The property that the strong unit acts as a sink is preserved.
    starˢ-sink-preserved :
      R₁.starˢ-sink ≡ R₂.starˢ-sink

    -- R₁.Id-erased holds if and only if R₂.Id-erased holds.
    Id-erased-preserved : R₁.Id-erased ⇔ R₂.Id-erased

    -- If R₁.Erased-matches-for-J holds, then R₂.Erased-matches-for-J
    -- holds.
    Erased-matches-for-J-preserved :
      R₁.Erased-matches-for-J → R₂.Erased-matches-for-J

    -- If R₁.Erased-matches-for-K holds, then R₂.Erased-matches-for-K
    -- holds.
    Erased-matches-for-K-preserved :
      R₁.Erased-matches-for-K → R₂.Erased-matches-for-K

opaque

  -- For every value R of type Usage-restrictions the identity
  -- function preserves Usage-restrictions for R and R.

  Are-preserving-usage-restrictions-id :
    Are-preserving-usage-restrictions R R idᶠ idᶠ
  Are-preserving-usage-restrictions-id {R = R} = λ where
      .Prodrec-preserved              → idᶠ
      .Unitrec-preserved              → idᶠ
      .starˢ-sink-preserved           → refl
      .Id-erased-preserved            → id⇔
      .Erased-matches-for-J-preserved → idᶠ
      .Erased-matches-for-K-preserved → idᶠ
    where
    open Are-preserving-usage-restrictions

opaque

  -- Composition preserves Are-preserving-usage-restrictions.

  Are-preserving-usage-restrictions-∘ :
    Are-preserving-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
    Are-preserving-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
    Are-preserving-usage-restrictions
      R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
  Are-preserving-usage-restrictions-∘ m₁ m₂ = λ where
      .Prodrec-preserved →
        M₁.Prodrec-preserved ∘→ M₂.Prodrec-preserved
      .Unitrec-preserved →
        M₁.Unitrec-preserved ∘→ M₂.Unitrec-preserved
      .starˢ-sink-preserved →
        trans M₂.starˢ-sink-preserved M₁.starˢ-sink-preserved
      .Id-erased-preserved →
        M₁.Id-erased-preserved ∘⇔ M₂.Id-erased-preserved
      .Erased-matches-for-J-preserved →
        M₁.Erased-matches-for-J-preserved ∘→
        M₂.Erased-matches-for-J-preserved
      .Erased-matches-for-K-preserved →
        M₁.Erased-matches-for-K-preserved ∘→
        M₂.Erased-matches-for-K-preserved
    where
    open Are-preserving-usage-restrictions
    module M₁ = Are-preserving-usage-restrictions m₁
    module M₂ = Are-preserving-usage-restrictions m₂

------------------------------------------------------------------------
-- Are-reflecting-usage-restrictions

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

    -- The function tr reflects the Unitrec-allowed property.
    Unitrec-reflected :
      R₂.Unitrec-allowed (tr p) (tr q) →
      R₁.Unitrec-allowed p q

    -- The property that the strong unit acts as a sink is reflected.
    starˢ-sink-reflected :
      R₂.starˢ-sink ≡ R₁.starˢ-sink

    -- R₂.Id-erased holds if and only if R₁.Id-erased holds.
    Id-erased-reflected : R₂.Id-erased ⇔ R₁.Id-erased

    -- If R₂.Erased-matches-for-J holds, then R₁.Erased-matches-for-J
    -- holds.
    Erased-matches-for-J-reflected :
      R₂.Erased-matches-for-J → R₁.Erased-matches-for-J

    -- If R₂.Erased-matches-for-K holds, then R₁.Erased-matches-for-K
    -- holds.
    Erased-matches-for-K-reflected :
      R₂.Erased-matches-for-K → R₁.Erased-matches-for-K

opaque

  -- For every value R of type Usage-restrictions the identity
  -- function reflects Usage-restrictions for R and R.

  Are-reflecting-usage-restrictions-id :
    Are-reflecting-usage-restrictions R R idᶠ idᶠ
  Are-reflecting-usage-restrictions-id {R = R} = λ where
      .Prodrec-reflected              → idᶠ
      .Unitrec-reflected              → idᶠ
      .starˢ-sink-reflected           → refl
      .Id-erased-reflected            → id⇔
      .Erased-matches-for-J-reflected → idᶠ
      .Erased-matches-for-K-reflected → idᶠ
    where
    open Are-reflecting-usage-restrictions
    open Usage-restrictions R

opaque

  -- Composition preserves Are-reflecting-usage-restrictions.

  Are-reflecting-usage-restrictions-∘ :
    Are-reflecting-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
    Are-reflecting-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
    Are-reflecting-usage-restrictions
      R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
  Are-reflecting-usage-restrictions-∘ m₁ m₂ = λ where
      .Prodrec-reflected →
        M₂.Prodrec-reflected ∘→ M₁.Prodrec-reflected
      .Unitrec-reflected →
        M₂.Unitrec-reflected ∘→ M₁.Unitrec-reflected
      .starˢ-sink-reflected →
        trans M₁.starˢ-sink-reflected M₂.starˢ-sink-reflected
      .Id-erased-reflected →
        M₂.Id-erased-reflected ∘⇔ M₁.Id-erased-reflected
      .Erased-matches-for-J-reflected →
        M₂.Erased-matches-for-J-reflected ∘→
        M₁.Erased-matches-for-J-reflected
      .Erased-matches-for-K-reflected →
        M₂.Erased-matches-for-K-reflected ∘→
        M₁.Erased-matches-for-K-reflected
    where
    open Are-reflecting-usage-restrictions
    module M₁ = Are-reflecting-usage-restrictions m₁
    module M₂ = Are-reflecting-usage-restrictions m₂
