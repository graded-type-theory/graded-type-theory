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
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n       : Nat
  A l t u : Term _
  σ       : Subst _ _
  s       : Strength
  p q     : M

opaque

  -- An eliminator for Unit.

  unitrec⟨_⟩ :
    Strength → M → M → Term n → Term (1+ n) → Term n → Term n →
    Term n
  unitrec⟨ 𝕨 ⟩ = unitrec
  unitrec⟨ 𝕤 ⟩ = λ _ _ _ _ _ u → u

opaque
  unfolding unitrec⟨_⟩

  -- A substitution lemma for unitrec⟨_⟩.

  unitrec⟨⟩-[] :
    unitrec⟨ s ⟩ p q l A t u [ σ ] ≡
    unitrec⟨ s ⟩ p q (l [ σ ]) (A [ liftSubst σ ]) (t [ σ ]) (u [ σ ])
  unitrec⟨⟩-[] {s = 𝕤} = refl
  unitrec⟨⟩-[] {s = 𝕨} = refl

opaque

  -- Unit-η s l p is an implementation of a propositional η-rule for the
  -- type Unit s l.

  Unit-η : Strength → M → Term n → Term n → Term n
  Unit-η s p l t =
    unitrec⟨ s ⟩ 𝟙 p l (Id (Unit s (wk1 l)) (star s (wk1 l)) (var x0)) t rfl

opaque
  unfolding Unit-η

  -- A substitution lemma for Unit-η.

  Unit-η-[] : Unit-η s p l t [ σ ] ≡ Unit-η s p (l [ σ ]) (t [ σ ])
  Unit-η-[] {s} {p} {l} {t} {σ} =
    Unit-η s p l t [ σ ]
                                    ≡⟨ unitrec⟨⟩-[] ⟩
    unitrec⟨ s ⟩ 𝟙 p (l [ σ ])
      (Id (Unit s (wk1 l [ liftSubst σ ])) (star s (wk1 l [ liftSubst σ ])) (var x0))
      (t [ σ ])
      rfl
                                    ≡⟨ cong (λ x → unitrec⟨ s ⟩ 𝟙 p (l [ σ ]) (Id (Unit s x) (star s x) (var x0)) (t [ σ ]) rfl)
                                      (wk1-liftSubst l) ⟩
    unitrec⟨ s ⟩ 𝟙 p (l [ σ ])
      (Id (Unit s (wk1 (l [ σ ]))) (star s (wk1 (l [ σ ]))) (var x0))
      (t [ σ ])
      rfl
                                    ≡⟨⟩
    Unit-η s p (l [ σ ]) (t [ σ ]) ∎
