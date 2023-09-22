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

-- The property that some of the usage restrictions are "the same".

record Same-usage-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (R₁ : Usage-restrictions M₁) (R₂ : Usage-restrictions M₂) :
         Set (a₁ ⊔ a₂) where
  private
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂

  field
    -- R₁.Id-erased holds if and only if R₂.Id-erased holds.
    Id-erased-preserved : R₁.Id-erased ⇔ R₂.Id-erased

    -- If R₁.Erased-matches-for-J holds if and only if
    -- R₂.Erased-matches-for-J holds.
    Erased-matches-for-J-preserved :
      R₁.Erased-matches-for-J ⇔ R₂.Erased-matches-for-J

    -- If R₁.Erased-matches-for-K holds if and only if
    -- R₂.Erased-matches-for-K holds.
    Erased-matches-for-K-preserved :
      R₁.Erased-matches-for-K ⇔ R₂.Erased-matches-for-K

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

    -- The other usage restrictions are "the same".
    --
    -- These restrictions are required to be "the same" because they
    -- are used both "positively" and "negatively". For instance,
    -- Id-erased is used both in a positive way (Id-erased in the type
    -- of Id₀ₘ) and in a negative way (¬ Id-erased in the type of
    -- Idₘ).
    same-usage-restrictions : Same-usage-restrictions R₁ R₂

  open Same-usage-restrictions same-usage-restrictions public

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

    -- The other usage restrictions are "the same".
    same-usage-restrictions : Same-usage-restrictions R₁ R₂

  open Same-usage-restrictions same-usage-restrictions public

------------------------------------------------------------------------
-- Identity

opaque

  -- Same-usage-restrictions is reflexive.

  Same-usage-restrictions-reflexive :
    Same-usage-restrictions R R
  Same-usage-restrictions-reflexive = λ where
      .Id-erased-preserved            → id⇔
      .Erased-matches-for-J-preserved → id⇔
      .Erased-matches-for-K-preserved → id⇔
    where
    open Same-usage-restrictions

-- For every value R of type Usage-restrictions the identity function
-- preserves Usage-restrictions for R and R.

Are-preserving-usage-restrictions-id :
  Are-preserving-usage-restrictions R R idᶠ idᶠ
Are-preserving-usage-restrictions-id {R = R} = λ where
    .Prodrec-preserved       → idᶠ
    .same-usage-restrictions → Same-usage-restrictions-reflexive
  where
  open Are-preserving-usage-restrictions
  open Usage-restrictions R

-- For every value R of type Usage-restrictions the identity function
-- reflects Usage-restrictions for R and R.

Are-reflecting-usage-restrictions-id :
  Are-reflecting-usage-restrictions R R idᶠ idᶠ
Are-reflecting-usage-restrictions-id {R = R} = λ where
    .Prodrec-reflected       → idᶠ
    .same-usage-restrictions → Same-usage-restrictions-reflexive
  where
  open Are-reflecting-usage-restrictions
  open Usage-restrictions R

------------------------------------------------------------------------
-- Composition

opaque

  -- Same-usage-restrictions is transitive.

  Same-usage-restrictions-transitive :
    Same-usage-restrictions R₂ R₃ →
    Same-usage-restrictions R₁ R₂ →
    Same-usage-restrictions R₁ R₃
  Same-usage-restrictions-transitive s₁ s₂ = λ where
      .Id-erased-preserved →
        S₁.Id-erased-preserved ∘⇔ S₂.Id-erased-preserved
      .Erased-matches-for-J-preserved →
        S₁.Erased-matches-for-J-preserved ∘⇔
        S₂.Erased-matches-for-J-preserved
      .Erased-matches-for-K-preserved →
        S₁.Erased-matches-for-K-preserved ∘⇔
        S₂.Erased-matches-for-K-preserved
    where
    open Same-usage-restrictions
    module S₁ = Same-usage-restrictions s₁
    module S₂ = Same-usage-restrictions s₂

-- Composition preserves Are-preserving-usage-restrictions.

Are-preserving-usage-restrictions-∘ :
  Are-preserving-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
  Are-preserving-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
  Are-preserving-usage-restrictions
    R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Are-preserving-usage-restrictions-∘ m₁ m₂ = λ where
    .Prodrec-preserved →
      M₁.Prodrec-preserved ∘→ M₂.Prodrec-preserved
    .same-usage-restrictions →
      Same-usage-restrictions-transitive M₁.same-usage-restrictions
        M₂.same-usage-restrictions
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
    .same-usage-restrictions →
      Same-usage-restrictions-transitive M₁.same-usage-restrictions
        M₂.same-usage-restrictions
  where
  open Are-reflecting-usage-restrictions
  module M₁ = Are-reflecting-usage-restrictions m₁
  module M₂ = Are-reflecting-usage-restrictions m₂
