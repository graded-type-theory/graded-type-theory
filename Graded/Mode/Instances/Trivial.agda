------------------------------------------------------------------------
-- A trivial mode structure
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Mode.Instances.Trivial
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open import Graded.Mode
open import Graded.Mode.Instances.Zero-one.Variant 𝕄
open import Graded.Mode.Instances.Zero-one 𝟘ᵐ-Not-Allowed

-- A trivial mode structure.

trivial : IsMode Mode 𝕄
trivial = Zero-one-isMode
