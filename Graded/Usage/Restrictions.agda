------------------------------------------------------------------------
-- Restrictions on usage derivations
------------------------------------------------------------------------

module Graded.Usage.Restrictions
  {a} (M : Set a)
  where

open import Tools.Bool
open import Tools.Level
open import Tools.Relation

-- Restrictions on/choices for usage derivations.

record Usage-restrictions : Set (lsuc a) where
  no-eta-equality
  field
    -- The prodrec constructor's quantities have to satisfy this
    -- predicate.
    Prodrec-allowed : (r p q : M) → Set a

    -- Are most things erased in the usage rule for Id?
    Id-erased : Set a

    -- Id-erased is decided.
    Id-erased? : Dec Id-erased

    -- Are erased matches allowed for the J rule? In that case all
    -- arguments but one are erased, and the non-erased argument is
    -- treated as "linear".
    Erased-matches-for-J : Set a

    -- Erased-matches-for-J is decided.
    Erased-matches-for-J? : Dec Erased-matches-for-J

    -- Are erased matches allowed for the K rule? In that case all
    -- arguments but one are erased, and the non-erased argument is
    -- treated as "linear".
    Erased-matches-for-K : Set a

    -- Erased-matches-for-K is decided.
    Erased-matches-for-K? : Dec Erased-matches-for-K
