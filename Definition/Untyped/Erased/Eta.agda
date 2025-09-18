------------------------------------------------------------------------
-- Definitions related to the variant of Erased that is defined using
-- strong Σ and unit types
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Untyped.Erased.Eta
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄

open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n : Nat
  t : Term _
  σ : Subst _ _
  ρ : Wk _ _

opaque

  -- The projection erased.

  erased : Term n → Term n
  erased t = fst 𝟘 t

opaque
  unfolding erased

  -- A substitution lemma for erased.

  erased-[] : erased t [ σ ] ≡ erased (t [ σ ])
  erased-[] = refl

opaque

  -- A weakening lemma for erased.

  wk-erased : wk ρ (erased t) ≡ erased (wk ρ t)
  wk-erased {ρ} {t} =
    wk ρ (erased t)           ≡⟨ wk≡subst _ _ ⟩
    erased t [ toSubst ρ ]    ≡⟨ erased-[] ⟩
    erased (t [ toSubst ρ ])  ≡˘⟨ cong erased $ wk≡subst _ _ ⟩
    erased (wk ρ t)           ∎
