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
-- * They can also come with, or not come with, a dedicated
--   natrec-star operator _⊛_▷_. Even if they don't come with a
--   *dedicated* natrec-star operator one or more such operators can
--   perhaps still be defined.

record Modality-variant : Set (lsuc a) where
  field
    -- Is the mode 𝟘ᵐ allowed?
    𝟘ᵐ-allowed : Bool

    -- Is a dedicated natrec-star operator available?
    ⊛-available : Set a

    -- The type ⊛-available is a proposition.
    ⊛-available-propositional : (p q : ⊛-available) → p ≡ q

    -- The type ⊛-available is decided.
    ⊛-available-decided : Dec ⊛-available

-- A variant for which a dedicated natrec-star operator must be
-- available, and 𝟘ᵐ is allowed if the boolean is true.

⊛-available-and-𝟘ᵐ-allowed-if : Bool → Modality-variant
⊛-available-and-𝟘ᵐ-allowed-if ok = record
  { 𝟘ᵐ-allowed                = ok
  ; ⊛-available               = Lift _ ⊤
  ; ⊛-available-propositional = λ _ _ → refl
  ; ⊛-available-decided       = yes _
  }

-- A variant for which a dedicated natrec-star operator is not
-- available, and 𝟘ᵐ is allowed if the boolean is true.

⊛-not-available-and-𝟘ᵐ-allowed-if : Bool → Modality-variant
⊛-not-available-and-𝟘ᵐ-allowed-if ok = record
  { 𝟘ᵐ-allowed                = ok
  ; ⊛-available               = Lift _ ⊥
  ; ⊛-available-propositional = λ ()
  ; ⊛-available-decided       = no (λ ())
  }
