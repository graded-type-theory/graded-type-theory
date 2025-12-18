------------------------------------------------------------------------
-- Definitions related to Unit
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Untyped.Unit
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

import Definition.Typed.Decidable.Internal.Term
open import Definition.Typed.Restrictions

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
    Strength → M → M → Term (1+ n) → Term n → Term n →
    Term n
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

  -- Unit-η s l p is an implementation of a propositional η-rule for the
  -- type Unit s l.

  Unit-η : Strength → M → Term n → Term n
  Unit-η s p t =
    unitrec⟨ s ⟩ 𝟙 p (Id (Unit s) (star s) (var x0)) t rfl

opaque
  unfolding Unit-η

  -- A substitution lemma for Unit-η.

  Unit-η-[] : Unit-η s p t [ σ ] ≡ Unit-η s p (t [ σ ])
  Unit-η-[] {s} {p} {t} {σ} =
    Unit-η s p t [ σ ]
                                    ≡⟨ unitrec⟨⟩-[] ⟩
    unitrec⟨ s ⟩ 𝟙 p
      (Id (Unit s) (star s) (var x0))
      (t [ σ ])
      rfl
                                    ≡⟨⟩
    Unit-η s p (t [ σ ]) ∎

------------------------------------------------------------------------
-- A variant of one term former, intended to be used with the internal
-- type-checker

module Internal (R : Type-restrictions 𝕄) where

  private
    module I = Definition.Typed.Decidable.Internal.Term R

  private variable
    c        : I.Constants
    pᵢ qᵢ    : I.Termᵍ _
    Aᵢ tᵢ uᵢ : I.Term _ _
    γ        : I.Contexts _

  -- A variant of unitrec⟨_⟩, intended to be used with the internal
  -- type-checker.

  unitrec⟨_⟩ᵢ :
    Strength →
    (_ _ : I.Termᵍ (c .I.gs)) → I.Term c (1+ n) → (_ _ : I.Term c n) →
    I.Term c n
  unitrec⟨ 𝕨 ⟩ᵢ p q A t u = I.unitrec p q A t u
  unitrec⟨ 𝕤 ⟩ᵢ _ _ _ _ u = u

  opaque
    unfolding unitrec⟨_⟩

    -- A translation lemma for unitrec⟨_⟩ᵢ.

    ⌜unitrec⟨⟩ᵢ⌝ :
      ∀ s →
      I.⌜ unitrec⟨ s ⟩ᵢ pᵢ qᵢ Aᵢ tᵢ uᵢ ⌝ γ ≡
      unitrec⟨ s ⟩ (I.⟦ pᵢ ⟧ᵍ γ) (I.⟦ qᵢ ⟧ᵍ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
        (I.⌜ uᵢ ⌝ γ)
    ⌜unitrec⟨⟩ᵢ⌝ 𝕨 = refl
    ⌜unitrec⟨⟩ᵢ⌝ 𝕤 = refl
