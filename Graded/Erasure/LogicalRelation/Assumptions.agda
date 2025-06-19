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

open import Graded.Erasure.Target as T using (Strictness)

open import Tools.Function
open import Tools.Level
open import Tools.List
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

record Assumptions : Set (lsuc a) where
  field
    -- An "EqRelSet".
    ⦃ eqRelSet ⦄ : EqRelSet

  open EqRelSet eqRelSet public

  field
    -- The size of the definition context below.
    {kᵈ} : Nat

    -- The size of the context below.
    {k} : Nat

    -- A definition context.
    {ts} : DCon (Term 0) kᵈ

    -- A variable context.
    {Δ} : Con Term k

    -- A definition context for the target language.
    vs : List (T.Term 0)

    -- The source contexts are well-formed.
    ⊢Δ : ts »⊢ Δ

    -- Var-included holds or Δ is empty.
    ⦃ inc ⦄ : Var-included or-empty Δ

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
         flip Equality-reflection-allowed→¬Var-included)
        inc
