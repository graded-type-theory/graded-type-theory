------------------------------------------------------------------------
-- Definitions related to Π-types
------------------------------------------------------------------------

module Definition.Untyped.Pi {a} (M : Set a) where

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n     : Nat
  t u v : Term _
  σ     : Subst _ _
  ρ     : Wk _ _
  p     : M

opaque

  -- Heterogeneous λ-abstraction.

  lamʰ : M → Term (1+ n) → Term n
  lamʰ p t = lam p (lift (lower₀ t))

opaque
  unfolding lamʰ

  -- A substitution lemma for lamʰ.

  lamʰ-[] : lamʰ p t [ σ ] ≡ lamʰ p (t [ σ ⇑ ])
  lamʰ-[] {p} {t} {σ} =
    lam p (lift (lower₀ t [ σ ⇑ ]))    ≡⟨ cong (lam _ ∘→ lift) lower₀-[⇑] ⟩
    lam p (lift (lower₀ (t [ σ ⇑ ])))  ∎

opaque

  -- A weakening lemma for lamʰ.

  wk-lamʰ : wk ρ (lamʰ p t) ≡ lamʰ p (wk (lift ρ) t)
  wk-lamʰ {ρ} {p} {t} =
    wk ρ (lamʰ p t)                  ≡⟨ wk≡subst _ _ ⟩
    lamʰ p t [ toSubst ρ ]           ≡⟨ lamʰ-[] ⟩
    lamʰ p (t [ toSubst ρ ⇑ ])       ≡˘⟨ cong (lamʰ _) $ substVar-to-subst (toSubst-liftn 1) t ⟩
    lamʰ p (t [ toSubst (lift ρ) ])  ≡˘⟨ cong (lamʰ _) $ wk≡subst _ _ ⟩
    lamʰ p (wk (lift ρ) t)           ∎

opaque

  -- Heterogeneous application.

  ∘ʰ : M → (_ _ _ : Term n) → Term n
  ∘ʰ p _ t u = lower (t ∘⟨ p ⟩ lift u)

opaque
  unfolding ∘ʰ

  -- A substitution lemma for ∘ʰ.

  ∘ʰ-[] : ∘ʰ p t u v [ σ ] ≡ ∘ʰ p (t [ σ ]) (u [ σ ]) (v [ σ ])
  ∘ʰ-[] = refl

opaque

  -- A weakening lemma for ∘ʰ.

  wk-∘ʰ : wk ρ (∘ʰ p t u v) ≡ ∘ʰ p (wk ρ t) (wk ρ u) (wk ρ v)
  wk-∘ʰ {ρ} {p} {t} {u} {v} =
    wk ρ (∘ʰ p t u v)                                           ≡⟨ wk≡subst _ _ ⟩
    ∘ʰ p t u v [ toSubst ρ ]                                    ≡⟨ ∘ʰ-[] ⟩
    ∘ʰ p (t [ toSubst ρ ]) (u [ toSubst ρ ]) (v [ toSubst ρ ])  ≡˘⟨ cong₃ (∘ʰ _) (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _) ⟩
    ∘ʰ p (wk ρ t) (wk ρ u) (wk ρ v)                             ∎
