------------------------------------------------------------------------
-- Some assumptions used to define the logical relation for erasure
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Assumptions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.EqualityRelation R
open import Definition.Untyped M

open import Graded.Erasure.Target using (Strictness)

open import Tools.Level
open import Tools.Nat

record Assumptions : Set (lsuc a) where
  field
    -- An "EqRelSet".
    ⦃ eqRelSet ⦄ : EqRelSet

    -- The size of the context below.
    {k} : Nat

    -- A context.
    {Δ} : Con Term k

    -- The context is well-formed.
    ⊢Δ : ⊢ Δ

    -- Should applications be extracted to strict or non-strict
    -- applications?
    str : Strictness

  open EqRelSet eqRelSet public
