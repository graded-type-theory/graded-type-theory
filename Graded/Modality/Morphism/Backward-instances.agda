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

open import Graded.Modality.Dedicated-nr

instance

  -- If the target modality has a dedicated nr function, then the
  -- source modality also has one.

  nr-in-first-if-in-second′ :
    ⦃ has-nr : Dedicated-nr 𝕄₂ ⦄ → Dedicated-nr 𝕄₁
  nr-in-first-if-in-second′ = nr-in-first-if-in-second

  -- If the target modality does not have a dedicated nr function,
  -- then neither does the source modality.

  no-nr-in-first-if-in-second′ :
    ⦃ no-nr : No-dedicated-nr 𝕄₂ ⦄ → No-dedicated-nr 𝕄₁
  no-nr-in-first-if-in-second′ = no-nr-in-first-if-in-second
