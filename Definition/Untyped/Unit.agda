------------------------------------------------------------------------
-- Definitions related to Unit
------------------------------------------------------------------------

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
  l     : Universe-level
  p q   : M

opaque

  -- An eliminator for Unit.

  unitrec⟨_⟩ :
    Strength → Universe-level → M → M → Term (1+ n) → Term n → Term n →
    Term n
  unitrec⟨ 𝕨 ⟩ = unitrec
  unitrec⟨ 𝕤 ⟩ = λ _ _ _ _ _ u → u

opaque
  unfolding unitrec⟨_⟩

  -- A substitution lemma for unitrec⟨_⟩.

  unitrec⟨⟩-[] :
    unitrec⟨ s ⟩ l p q A t u [ σ ] ≡
    unitrec⟨ s ⟩ l p q (A [ liftSubst σ ]) (t [ σ ]) (u [ σ ])
  unitrec⟨⟩-[] {s = 𝕤} = refl
  unitrec⟨⟩-[] {s = 𝕨} = refl

opaque

  -- Unit-η s l p is an implementation of a propositional η-rule for the
  -- type Unit s l.

  Unit-η : Strength → Universe-level → M → Term n → Term n
  Unit-η s l p t =
    unitrec⟨ s ⟩ l 𝟙 p (Id (Unit s l) (star s l) (var x0)) t rfl

opaque
  unfolding Unit-η

  -- A substitution lemma for Unit-η.

  Unit-η-[] : Unit-η s l p t [ σ ] ≡ Unit-η s l p (t [ σ ])
  Unit-η-[] = unitrec⟨⟩-[]
