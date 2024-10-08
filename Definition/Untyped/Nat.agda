------------------------------------------------------------------------
-- Definitions related to ℕ
------------------------------------------------------------------------

-- Typing rules for the term former defined in this module can be
-- found in Definition.Typed.Consequences.DerivedRules.Nat, and a
-- usage rule can be found in Graded.Derived.Nat.

open import Graded.Modality

module Definition.Untyped.Nat
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n       : Nat
  A t u v : Term _
  σ       : Subst _ _
  ρ       : Wk _ _
  p q     : M

opaque

  -- A case analysis principle for natural numbers.

  natcase : M → M → Term (1+ n) → Term n → Term (1+ n) → Term n → Term n
  natcase p q A t u v =
    natrec p q 𝟘 A t (wk1 u) v

opaque
  unfolding natcase

  -- A substitution lemma for natcase.

  natcase-[] :
    natcase p q A t u v [ σ ] ≡
    natcase p q (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ⇑ ]) (v [ σ ])
  natcase-[] {p} {q} {A} {t} {u} {v} {σ} =
    natrec p q 𝟘 A t (wk1 u) v [ σ ]                                ≡⟨⟩
    natrec p q 𝟘 (A [ σ ⇑ ]) (t [ σ ]) (wk1 u [ σ ⇑ ⇑ ]) (v [ σ ])  ≡⟨ cong₂ (natrec _ _ _ _ _) (wk1-liftSubst u) refl ⟩
    natrec p q 𝟘 (A [ σ ⇑ ]) (t [ σ ]) (wk1 (u [ σ ⇑ ])) (v [ σ ])  ∎

opaque

  -- A weakening lemma for natcase.

  wk-natcase :
    wk ρ (natcase p q A t u v) ≡
    natcase p q (wk (lift ρ) A) (wk ρ t) (wk (lift ρ) u) (wk ρ v)
  wk-natcase {ρ} {p} {q} {A} {t} {u} {v} =
    wk ρ (natcase p q A t u v)                                     ≡⟨ wk≡subst _ _ ⟩

    natcase p q A t u v [ toSubst ρ ]                              ≡⟨ natcase-[] ⟩

    natcase p q (A [ toSubst ρ ⇑ ]) (t [ toSubst ρ ])
      (u [ toSubst ρ ⇑ ]) (v [ toSubst ρ ])                        ≡˘⟨ cong₄ (natcase _ _) (wk-liftn 1) (wk≡subst _ _)
                                                                         (wk-liftn 1) (wk≡subst _ _) ⟩
    natcase p q (wk (lift ρ) A) (wk ρ t) (wk (lift ρ) u) (wk ρ v)  ∎
