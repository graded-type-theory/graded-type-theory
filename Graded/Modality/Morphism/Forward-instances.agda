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

open import Graded.Modality.Dedicated-nr

instance

  -- If the source modality has a dedicated nr function, then the
  -- target modality also has one.

  nr-in-second-if-in-first′ :
    ⦃ has-nr : Dedicated-nr 𝕄₁ ⦄ → Dedicated-nr 𝕄₂
  nr-in-second-if-in-first′ = nr-in-second-if-in-first

  -- If the source modality does not have a dedicated nr function,
  -- then neither does the target modality.

  no-nr-in-second-if-in-first′ :
    ⦃ no-nr : No-dedicated-nr 𝕄₁ ⦄ → No-dedicated-nr 𝕄₂
  no-nr-in-second-if-in-first′ = no-nr-in-second-if-in-first
