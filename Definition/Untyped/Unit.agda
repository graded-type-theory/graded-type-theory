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
  n     : Nat
  A t u : Term _
  σ     : Subst _ _
  s     : Strength
  p q   : M

opaque

  -- An eliminator for Unit.

  unitrec⟨_⟩ : Strength → M → M → Term (1+ n) → Term n → Term n → Term n
  unitrec⟨ 𝕨 ⟩ = unitrec
  unitrec⟨ 𝕤 ⟩ = λ _ _ _ _ u → u

opaque
  unfolding unitrec⟨_⟩

  -- A substitution lemma for unitrec⟨_⟩.

  unitrec⟨⟩-[] :
    unitrec⟨ s ⟩ p q A t u [ σ ] ≡
    unitrec⟨ s ⟩ p q (A [ liftSubst σ ]) (t [ σ ]) (u [ σ ])
  unitrec⟨⟩-[] {s = 𝕤} = refl
  unitrec⟨⟩-[] {s = 𝕨} = refl

opaque

  -- Unit-η s p is an implementation of a propositional η-rule for the
  -- type Unit s.

  Unit-η : Strength → M → Term n → Term n
  Unit-η s p t = unitrec⟨ s ⟩ 𝟙 p (Id (Unit s) (star s) (var x0)) t rfl

opaque
  unfolding Unit-η

  -- A substitution lemma for Unit-η.

  Unit-η-[] : Unit-η s p t [ σ ] ≡ Unit-η s p (t [ σ ])
  Unit-η-[] = unitrec⟨⟩-[]
