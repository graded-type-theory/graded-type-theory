------------------------------------------------------------------------
-- Modality variants
------------------------------------------------------------------------

open import Tools.Level

module Graded.Modality.Variant (a : Level) where

open import Tools.Bool
open import Tools.Empty
open import Tools.Level
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

-- Modality variants:
-- * Modalities can come with one mode (𝟙ᵐ) or two (𝟙ᵐ and 𝟘ᵐ).
-- * They can also come with, or not come with, a dedicated nr
--   function. Even if they don't come with a *dedicated* nr function
--   such functions can perhaps still be defined.

record Modality-variant : Set (lsuc a) where
  field
    -- Is the mode 𝟘ᵐ allowed?
    𝟘ᵐ-allowed : Bool

    -- Is a dedicated nr function available?
    Nr-available : Set a

    -- The type nr-available is a proposition.
    Nr-available-propositional : (p q : Nr-available) → p ≡ q

    -- The type nr-available is decided.
    Nr-available-decided : Dec Nr-available

-- A variant for which a dedicated nr function must be available, and
-- 𝟘ᵐ is allowed if the boolean is true.

nr-available-and-𝟘ᵐ-allowed-if : Bool → Modality-variant
nr-available-and-𝟘ᵐ-allowed-if ok = record
  { 𝟘ᵐ-allowed                 = ok
  ; Nr-available               = Lift _ ⊤
  ; Nr-available-propositional = λ _ _ → refl
  ; Nr-available-decided       = yes _
  }

-- A variant for which a dedicated nr function is not available, and
-- 𝟘ᵐ is allowed if the boolean is true.

nr-not-available-and-𝟘ᵐ-allowed-if : Bool → Modality-variant
nr-not-available-and-𝟘ᵐ-allowed-if ok = record
  { 𝟘ᵐ-allowed                 = ok
  ; Nr-available               = Lift _ ⊥
  ; Nr-available-propositional = λ ()
  ; Nr-available-decided       = no (λ ())
  }
