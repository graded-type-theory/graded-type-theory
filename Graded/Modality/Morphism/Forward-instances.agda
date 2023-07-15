------------------------------------------------------------------------
-- "Forward" instances related to morphisms
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Modality.Morphism

module Graded.Modality.Morphism.Forward-instances
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  {tr : M₁ → M₂}
  (m : Is-morphism 𝕄₁ 𝕄₂ tr)
  where

open Is-morphism m

open import Graded.Modality.Dedicated-star

instance

  -- If the source modality has a dedicated natrec-star operator,
  -- then the target modality also has one.

  star-in-second-if-in-first′ :
    ⦃ has-star : Dedicated-star 𝕄₁ ⦄ → Dedicated-star 𝕄₂
  star-in-second-if-in-first′ = star-in-second-if-in-first

  -- If the source modality does not have a dedicated natrec-star
  -- operator, then neither does the target modality.

  no-star-in-second-if-in-first′ :
    ⦃ no-star : No-dedicated-star 𝕄₁ ⦄ → No-dedicated-star 𝕄₂
  no-star-in-second-if-in-first′ = no-star-in-second-if-in-first
