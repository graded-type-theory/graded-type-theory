------------------------------------------------------------------------
-- Restrictions on usage derivations
------------------------------------------------------------------------

module Graded.Usage.Restrictions
  {a} (M : Set a)
  where

open import Tools.Bool
open import Tools.Level
open import Tools.Relation
open import Tools.Sum
open import Tools.Empty

-- Restrictions on/choices for usage derivations.

record Usage-restrictions : Set (lsuc a) where
  no-eta-equality
  field
    -- The prodrec constructor's quantities have to satisfy this
    -- predicate.
    Prodrec-allowed : (r p q : M) → Set a

    -- The unitrec constructor's quantities have to satisfy this
    -- predicate.
    Unitrec-allowed : (p q : M) → Set a

    -- Should the strong unit type act as a "sink"?
    starˢ-sink : Bool

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

  -- Does the strong unit type act as a "sink"?

  Starˢ-sink : Set
  Starˢ-sink = T starˢ-sink

  -- Does the strong unit type not act as a "sink"?
  --
  -- This type is used instead of ¬ Starˢ-sink because "¬ A" does not
  -- work well as the type of an instance argument.

  ¬Starˢ-sink : Set
  ¬Starˢ-sink = T (not starˢ-sink)

  -- The strong unit type is not allowed to both act and not act as a
  -- sink.

  not-sink-and-no-sink : Starˢ-sink → ¬Starˢ-sink → ⊥
  not-sink-and-no-sink sink ¬sink with starˢ-sink
  … | false = sink
  … | true = ¬sink

  -- The strong unit type either acts or does not act as a sink.

  sink-or-no-sink : Starˢ-sink ⊎ ¬Starˢ-sink
  sink-or-no-sink with starˢ-sink
  … | false = inj₂ _
  … | true = inj₁ _
