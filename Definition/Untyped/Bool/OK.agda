------------------------------------------------------------------------
-- A term used to define booleans
------------------------------------------------------------------------

-- See Definition.Untyped.Bool for the full encoding of booleans.

import Graded.Modality

module Definition.Untyped.Bool.OK
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  -- The grade used to define OK
  (OKᵍ : M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n : Nat
  t : Term _
  σ : Subst _ _
  ρ : Wk _ _

------------------------------------------------------------------------
-- The term OK

opaque

  -- A definition that is used in the implementation of Bool.

  OK : Term n → Term n
  OK t = natcase OKᵍ 𝟘 U₀ Unitʷ (natcase 𝟘 𝟘 U₀ Unitʷ Empty (var x0)) t

------------------------------------------------------------------------
-- Substitution and weakening lemmas

opaque
  unfolding OK

  -- A substitution lemma for OK.

  OK-[] : OK t [ σ ] ≡ OK (t [ σ ])
  OK-[] =
    trans natcase-[] $
    cong (flip (natcase _ _ _ _) _) natcase-[]

opaque

  -- A weakening lemma for OK.

  wk-OK : wk ρ (OK t) ≡ OK (wk ρ t)
  wk-OK {ρ} {t} =
    wk ρ (OK t)           ≡⟨ wk≡subst _ _ ⟩
    OK t [ toSubst ρ ]    ≡⟨ OK-[] ⟩
    OK (t [ toSubst ρ ])  ≡˘⟨ cong OK $ wk≡subst _ _ ⟩
    OK (wk ρ t)           ∎
