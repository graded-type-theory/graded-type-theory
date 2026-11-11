------------------------------------------------------------------------
-- "Backward" instances related to morphisms
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Mode.Instances.Zero-one
open import Graded.Modality.Morphism.Configuration

module Graded.Modality.Morphism.Backward-instances
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

  nr-in-first-if-in-second′ :
    ⦃ has-nr : C₂.Nr-available ⦄ → C₁.Nr-available
  nr-in-first-if-in-second′ = nr-in-first-if-in-second

  -- If the source modality uses the usage rule for natrec with
  -- inequalities then so does the target one.

  no-nr-in-first-if-in-second′ :
    ⦃ no-nr : C₂.Nr-not-available ⦄ → C₁.Nr-not-available
  no-nr-in-first-if-in-second′ = no-nr-in-first-if-in-second

  -- If the source modality uses the usage rule for natrec with
  -- the greatest lower bound of an nrᵢ sequence then so does the
  -- target one.

  no-nr-glb-in-first-if-in-second′ :
    ⦃ no-nr : C₂.Nr-not-available-GLB ⦄ → C₁.Nr-not-available-GLB
  no-nr-glb-in-first-if-in-second′ = no-nr-glb-in-first-if-in-second

  -- If the target modality allows grade ω for J and K then so does
  -- the source one.

  Usage-allows-omega-in-first-if-in-second :
    ⦃ ok : C₂.Usage-allows-omega ⦄ → C₁.Usage-allows-omega
  Usage-allows-omega-in-first-if-in-second ⦃ ok ⦄ =
    Usage-allows-omega-preserved .proj₂ ok
