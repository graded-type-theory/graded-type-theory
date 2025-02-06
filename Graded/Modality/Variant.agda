------------------------------------------------------------------------
-- Modality variants
------------------------------------------------------------------------

open import Tools.Level

module Graded.Modality.Variant (a : Level) where

open import Tools.Bool

-- Modality variants:
-- * Modalities can come with one mode (𝟙ᵐ) or two (𝟙ᵐ and 𝟘ᵐ).

record Modality-variant : Set (lsuc a) where
  no-eta-equality
  pattern

  field
    -- Is the mode 𝟘ᵐ allowed?
    𝟘ᵐ-allowed : Bool

-- A variant for which 𝟘ᵐ is allowed if the boolean is true.

𝟘ᵐ-allowed-if : Bool → Modality-variant
𝟘ᵐ-allowed-if ok = record
  { 𝟘ᵐ-allowed   = ok
  }
