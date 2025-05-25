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

data UnfoldingMode : Set where
  -- Unfold only explicitly specified definitions.
  explicit   : UnfoldingMode
  
  -- Unfold all transitive dependencies of definitions.
  transitive : UnfoldingMode

record Type-variant : Set where
  no-eta-equality
  field

    -- How should transitive dependencies of definitions be unfolded?
    
    unfolding-mode : UnfoldingMode

    -- Should η-equality be enabled for weak unit types?
    --
    -- This variant of the type system is used to state some soundness
    -- theorems for extraction, see
    -- Graded.Erasure.Consequences.Soundness.Erased-matches.
  
    η-for-Unitʷ : Bool

  -- Unitʷ-η holds exactly when η-for-Unitʷ is true.

  Unitʷ-η : Set
  Unitʷ-η = T η-for-Unitʷ

  opaque

    -- Unitʷ-η is decided.

    Unitʷ-η? : Dec Unitʷ-η
    Unitʷ-η? = T? _
