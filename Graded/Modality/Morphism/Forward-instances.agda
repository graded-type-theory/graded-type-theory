------------------------------------------------------------------------
-- "Forward" instances related to morphisms
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Graded.Modality.Morphism.Configuration
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Mode.Instances.Zero-one

module Graded.Modality.Morphism.Forward-instances
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  {v₁ : Mode-variant 𝕄₁} {v₂ : Mode-variant 𝕄₂}
  {C₁ : Configuration (Zero-one-isMode v₁)}
  {C₂ : Configuration (Zero-one-isMode v₂)}
  (cp : Common-properties C₁ C₂)
  where

open import Tools.Product

open Common-properties cp

module C₁ = Configuration C₁
module C₂ = Configuration C₂

instance

  -- If the source modality uses the usage rule for natrec with
  -- an nr function then so does the target one.

  nr-in-second-if-in-first′ :
    ⦃ has-nr : C₁.Nr-available ⦄ → C₂.Nr-available
  nr-in-second-if-in-first′ = nr-in-second-if-in-first

  -- If the source modality uses the usage rule for natrec with
  -- inequalities then so does the target one.

  no-nr-in-second-if-in-first′ :
    ⦃ no-nr : C₁.Nr-not-available ⦄ → C₂.Nr-not-available
  no-nr-in-second-if-in-first′ = no-nr-in-second-if-in-first

  -- If the source modality uses the usage rule for natrec with
  -- the greatest lower bound of an nrᵢ sequence then so does the
  -- target one.

  no-nr-glb-in-second-if-in-first′ :
    ⦃ no-nr : C₁.Nr-not-available-GLB ⦄ → C₂.Nr-not-available-GLB
  no-nr-glb-in-second-if-in-first′ = no-nr-glb-in-second-if-in-first

  -- If the source modality allows grade ω for usage rules then so does
  -- the target one.

  Usage-allows-omega-in-second-if-in-first :
    ⦃ ok : C₁.Usage-allows-omega ⦄ → C₂.Usage-allows-omega
  Usage-allows-omega-in-second-if-in-first ⦃ ok ⦄ =
    Usage-allows-omega-preserved .proj₁ ok
