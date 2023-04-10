------------------------------------------------------------------------
-- "Extra" restrictions
------------------------------------------------------------------------

module Definition.Modality.Restrictions {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Bool
open import Tools.Level

-- "Extra" restrictions related to usage for some type/term
-- constructors.

record Term-restrictions : Set (lsuc a) where
  field
    -- The prodrec constructor's quantities have to satisfy this
    -- predicate.
    Prodrec : (r p q : M) → Set a

    -- The quantities of binders have to satisfy this predicate.
    Binder : BinderMode → M → M → Set a

-- "Extra" restrictions related to usage.

record Restrictions : Set (lsuc a) where
  field
    -- Type/term restrictions.
    term-restrictions : Term-restrictions

    -- Is the mode 𝟘ᵐ allowed?
    𝟘ᵐ-allowed : Bool

  open Term-restrictions term-restrictions public
