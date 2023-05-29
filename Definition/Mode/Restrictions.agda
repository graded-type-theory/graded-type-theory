------------------------------------------------------------------------
-- Restrictions on modes
------------------------------------------------------------------------

module Definition.Mode.Restrictions where

open import Tools.Bool

-- Restrictions on modes.

record Mode-restrictions : Set where
  constructor 𝟘ᵐ-allowed-if
  field
    -- Is the mode 𝟘ᵐ allowed?
    𝟘ᵐ-allowed : Bool
