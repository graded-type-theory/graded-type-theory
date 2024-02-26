------------------------------------------------------------------------
-- Definitions related to Unit
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality

module Definition.Untyped.Unit
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality

private variable
  n : Nat
  t : Term _
  σ : Subst _ _
  s : Strength
  p : M

opaque

  -- Unit-η s p is an implementation of a propositional η-rule for the
  -- type Unit s.

  Unit-η : Strength → M → Term n → Term n
  Unit-η 𝕤 _ _ = rfl
  Unit-η 𝕨 p t = unitrec 𝟙 p (Id Unitʷ starʷ (var x0)) t rfl

opaque
  unfolding Unit-η

  -- A substitution lemma for Unit-η.

  Unit-η-[] : Unit-η s p t [ σ ] ≡ Unit-η s p (t [ σ ])
  Unit-η-[] {s = 𝕤} = refl
  Unit-η-[] {s = 𝕨} = refl
