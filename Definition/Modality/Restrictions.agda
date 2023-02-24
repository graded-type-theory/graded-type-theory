------------------------------------------------------------------------
-- "Extra" restrictions
------------------------------------------------------------------------

open import Tools.Relation

module Definition.Modality.Restrictions {a} (M : Set a) where

open import Tools.Bool
open import Tools.Level
open import Tools.Unit

-- "Extra" restrictions related to usage.

record Restrictions : Set (lsuc a) where
  field
    -- The prodrec constructor's quantities have to satisfy this
    -- predicate.
    Prodrec : (p q : M) → Set a

    -- Is the mode 𝟘ᵐ allowed?
    𝟘ᵐ-allowed : Bool

-- No restrictions.

no-restrictions : Restrictions
no-restrictions = record
  { Prodrec    = λ _ _ → Lift _ ⊤
  ; 𝟘ᵐ-allowed = true
  }
