------------------------------------------------------------------------
-- Variants of the type system
------------------------------------------------------------------------

module Definition.Typed.Variant where

open import Tools.Bool
open import Tools.Relation

-- This type makes it possible to choose between different variants of
-- the type system.
--
-- See also Definition.Typed.Restrictions.Type-restrictions.

record Type-variant : Set where
  no-eta-equality
  field
    -- Should η-equality be enabled for weak unit types?
    η-for-Unitʷ : Bool

  -- Unitʷ-η holds exactly when η-for-Unitʷ is true.

  Unitʷ-η : Set
  Unitʷ-η = T η-for-Unitʷ

  opaque

    -- Unitʷ-η is decided.

    Unitʷ-η? : Dec Unitʷ-η
    Unitʷ-η? = T? _
