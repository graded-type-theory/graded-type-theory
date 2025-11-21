------------------------------------------------------------------------
-- A definition related to the mode instance Zero-one.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Mode.Instances.Zero-one.Variant
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Tools.Bool

------------------------------------------------------------------------
-- The mode variant, either a single mode or two modes.

record Mode-variant : Set a where
  no-eta-equality
  field
    -- Does the mode 𝟘ᵐ exist?
    𝟘ᵐ-allowed : Bool
    -- If mode 𝟘ᵐ exists the modality is assumed to have a well-behaved
    -- zero.
    𝟘-well-behaved :
      T 𝟘ᵐ-allowed → Has-well-behaved-zero semiring-with-meet

------------------------------------------------------------------------
-- Mode variant instances


-- A mode variant for which 𝟘ᵐ is allowed if the boolean is true.

𝟘ᵐ-allowed-if : (b : Bool) → (T b → Has-well-behaved-zero semiring-with-meet) → Mode-variant
𝟘ᵐ-allowed-if b ok = record
  { 𝟘ᵐ-allowed = b ; 𝟘-well-behaved = ok }

-- A mode variant for which 𝟘ᵐ is allowed.

𝟘ᵐ-Allowed : ⦃ ok : Has-well-behaved-zero semiring-with-meet ⦄ → Mode-variant
𝟘ᵐ-Allowed ⦃ ok ⦄ = 𝟘ᵐ-allowed-if true λ _ → ok

-- A mode variant for which 𝟘ᵐ is not allowed.

𝟘ᵐ-Not-Allowed : Mode-variant
𝟘ᵐ-Not-Allowed = 𝟘ᵐ-allowed-if false (λ ())
