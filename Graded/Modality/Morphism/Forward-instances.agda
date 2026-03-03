------------------------------------------------------------------------
-- "Forward" instances related to morphisms
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Graded.Modality.Morphism.Usage-restrictions

module Graded.Modality.Morphism.Forward-instances
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  {v₁ : Mode-variant 𝕄₁} {v₂ : Mode-variant 𝕄₂}
  {R₁ : Usage-restrictions 𝕄₁ (Zero-one-isMode v₁)}
  {R₂ : Usage-restrictions 𝕄₂ (Zero-one-isMode v₂)}
  (cp : Common-properties R₁ R₂)
  where

open Common-properties cp

module R₁ = Usage-restrictions R₁
module R₂ = Usage-restrictions R₂

instance

  -- If the source modality uses the usage rule for natrec with
  -- an nr function then so does the target one.

  nr-in-second-if-in-first′ :
    ⦃ has-nr : R₁.Nr-available ⦄ → R₂.Nr-available
  nr-in-second-if-in-first′ = nr-in-second-if-in-first

  -- If the source modality uses the usage rule for natrec with
  -- inequalities then so does the target one.

  no-nr-in-second-if-in-first′ :
    ⦃ no-nr : R₁.Nr-not-available ⦄ → R₂.Nr-not-available
  no-nr-in-second-if-in-first′ = no-nr-in-second-if-in-first

  -- If the source modality uses the usage rule for natrec with
  -- the greatest lower bound of an nrᵢ sequence then so does the
  -- target one.

  no-nr-glb-in-second-if-in-first′ :
    ⦃ no-nr : R₁.Nr-not-available-GLB ⦄ → R₂.Nr-not-available-GLB
  no-nr-glb-in-second-if-in-first′ = no-nr-glb-in-second-if-in-first
