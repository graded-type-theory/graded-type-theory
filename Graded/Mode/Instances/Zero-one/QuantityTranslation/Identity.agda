------------------------------------------------------------------------
-- If Graded.Mode.Instances.Zero-one.QuantityTranslation is
-- instantiated with a single modality and a single modality variant,
-- then tr-Mode is pointwise equal to an identity function
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Modality.Morphism as M
  using (Is-morphism; Is-Σ-morphism)
  hiding (module Is-morphism)
open import Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive
  hiding (module Is-morphism)
open import Graded.Mode.Instances.Zero-one.Variant
open import Tools.Bool

module Graded.Mode.Instances.Zero-one.QuantityTranslation.Identity
  {a} {M : Set a} {𝕄 : Modality M}
  (v : Mode-variant 𝕄)
  (transparent : Bool)
  (tr tr-Σ : M → M)
  (tr-morphism : Is-morphism 𝕄 𝕄 tr)
  (tr-Σ-morphism : Is-Σ-morphism 𝕄 𝕄 tr tr-Σ)
  (mode-respecting : Are-mode-respecting-morphisms v v tr tr-Σ)
  where

open import Graded.Mode.Instances.Zero-one v
import Graded.Mode.Instances.Zero-one.QuantityTranslation

open import Tools.PropositionalEquality

open Graded.Mode.Instances.Zero-one.QuantityTranslation.Is-morphism
       _ _ _ _ transparent _ _ tr-morphism tr-Σ-morphism mode-respecting

private variable
  m : Mode

-- The function tr-Mode is an identity function.

tr-Mode-id : tr-Mode m ≡ m
tr-Mode-id {m = 𝟘ᵐ} = 𝟘ᵐ-cong
tr-Mode-id {m = 𝟙ᵐ} = refl
