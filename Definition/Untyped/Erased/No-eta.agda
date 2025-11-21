------------------------------------------------------------------------
-- Definitions related to the variant of Erased that is defined using
-- weak Σ and unit types
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Untyped.Erased.No-eta
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄

open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n   : Nat
  A t : Term _
  σ   : Subst _ _
  ρ   : Wk _ _

opaque

  -- The "projection" erased.

  erased : Term n → Term n → Term n
  erased = fst⟨ 𝕨 ⟩ 𝟘

opaque
  unfolding erased

  -- A substitution lemma for erased.

  erased-[] : erased A t [ σ ] ≡ erased (A [ σ ]) (t [ σ ])
  erased-[] = fst⟨⟩-[]

opaque

  -- A weakening lemma for erased.

  wk-erased : wk ρ (erased A t) ≡ erased (wk ρ A) (wk ρ t)
  wk-erased {ρ} {A} {t} =
    wk ρ (erased A t)                           ≡⟨ wk≡subst _ _ ⟩
    erased A t [ toSubst ρ ]                    ≡⟨ erased-[] ⟩
    erased (A [ toSubst ρ ]) (t [ toSubst ρ ])  ≡˘⟨ cong₂ erased (wk≡subst _ _) (wk≡subst _ _) ⟩
    erased (wk ρ A) (wk ρ t)                    ∎
