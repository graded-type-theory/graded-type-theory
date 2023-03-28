------------------------------------------------------------------------
-- "Extra" restrictions
------------------------------------------------------------------------

module Definition.Modality.Restrictions {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Bool
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit

-- "Extra" restrictions related to usage.

record Restrictions : Set (lsuc a) where
  field
    -- The prodrec constructor's quantities have to satisfy this
    -- predicate.
    Prodrec : (r p q : M) → Set a

    -- The quantities of binders have to satisfy this predicate.
    Binder : BinderMode → M → M → Set a

    -- Is the mode 𝟘ᵐ allowed?
    𝟘ᵐ-allowed : Bool

-- No restrictions.

no-restrictions : Restrictions
no-restrictions = record
  { Prodrec    = λ _ _ _ → Lift _ ⊤
  ; Binder     = λ _ _ _ → Lift _ ⊤
  ; 𝟘ᵐ-allowed = true
  }

-- Adds the restriction that the two quantities on a Π- or Σ-type have
-- to be equal.

equal-binder-quantities : Restrictions → Restrictions
equal-binder-quantities r = record r
  { Binder = λ b p q → Binder b p q × p ≡ q
  }
  where
  open Restrictions r
