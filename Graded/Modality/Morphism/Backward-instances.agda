------------------------------------------------------------------------
-- "Backward" instances related to morphisms
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Modality.Morphism.Usage-restrictions

module Graded.Modality.Morphism.Backward-instances
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  {R₁ : Usage-restrictions 𝕄₁}
  {R₂ : Usage-restrictions 𝕄₂}
  (cp : Common-properties R₁ R₂)
  where

open Common-properties cp

module R₁ = Usage-restrictions R₁
module R₂ = Usage-restrictions R₂

instance

  -- If the source modality uses the usage rule for natrec with
  -- an nr function then so does the target one.

  nr-in-first-if-in-second′ :
    ⦃ has-nr : R₂.Nr-available ⦄ → R₁.Nr-available
  nr-in-first-if-in-second′ = nr-in-first-if-in-second

  -- If the source modality uses the usage rule for natrec with
  -- inequalities then so does the target one.

  no-nr-in-first-if-in-second′ :
    ⦃ no-nr : R₂.Nr-not-available ⦄ → R₁.Nr-not-available
  no-nr-in-first-if-in-second′ = no-nr-in-first-if-in-second

  -- If the source modality uses the usage rule for natrec with
  -- the greatest lower bound of an nrᵢ sequence then so does the
  -- target one.

  no-nr-glb-in-first-if-in-second′ :
    ⦃ no-nr : R₂.Nr-not-available-GLB ⦄ → R₁.Nr-not-available-GLB
  no-nr-glb-in-first-if-in-second′ = no-nr-glb-in-first-if-in-second
