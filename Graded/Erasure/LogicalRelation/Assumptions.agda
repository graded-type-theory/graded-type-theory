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

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.EqualityRelation R
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Graded.Erasure.Target using (Strictness)

open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product

record Assumptions : Set (lsuc a) where
  field
    -- An "EqRelSet".
    ⦃ eqRelSet ⦄ : EqRelSet

  open EqRelSet eqRelSet public

  field
    -- The size of the context below.
    {k} : Nat

    -- A context.
    {Δ} : Con Term k

    -- The context is well-formed.
    ⊢Δ : ⊢ Δ

    -- Neutrals-included holds or Δ is empty.
    ⦃ inc ⦄ : Neutrals-included or-empty Δ

    -- Should applications be extracted to strict or non-strict
    -- applications?
    str : Strictness

  instance

    -- Equality reflection is not allowed or Δ is empty.

    no-equality-reflection-or-empty :
      No-equality-reflection or-empty Δ
    no-equality-reflection-or-empty =
      or-empty-map
        (No-equality-reflection⇔ .proj₂ ∘→
         flip Equality-reflection-allowed→¬Neutrals-included)
        inc
