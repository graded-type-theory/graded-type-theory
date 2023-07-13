------------------------------------------------------------------------
-- "Backward" instances related to morphisms
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Modality.Morphism

module Graded.Modality.Morphism.Backward-instances
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  {tr : M₁ → M₂}
  (m : Is-morphism 𝕄₁ 𝕄₂ tr)
  where

open Is-morphism m

open import Graded.Modality.Dedicated-star

instance

  -- If the target modality has a dedicated natrec-star operator, then
  -- the source modality also has one.

  star-in-first-if-in-second′ :
    ⦃ has-star : Dedicated-star 𝕄₂ ⦄ → Dedicated-star 𝕄₁
  star-in-first-if-in-second′ = star-in-first-if-in-second

  -- If the target modality does not have a dedicated natrec-star
  -- operator, then neither does the source modality.

  no-star-in-first-if-in-second′ :
    ⦃ no-star : No-dedicated-star 𝕄₂ ⦄ → No-dedicated-star 𝕄₁
  no-star-in-first-if-in-second′ = no-star-in-first-if-in-second
