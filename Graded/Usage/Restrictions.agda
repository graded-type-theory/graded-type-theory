------------------------------------------------------------------------
-- Restrictions on usage derivations
------------------------------------------------------------------------

module Graded.Usage.Restrictions
  {a} (M : Set a)
  where

open import Tools.Level

-- Restrictions on usage derivations.

record Usage-restrictions : Set (lsuc a) where
  no-eta-equality
  field
    -- The prodrec constructor's quantities have to satisfy this
    -- predicate.
    Prodrec-restriction : (r p q : M) → Set a
