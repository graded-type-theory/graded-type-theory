------------------------------------------------------------------------
-- Definitions related to Π-types
------------------------------------------------------------------------

-- Typing rules for the terms given in this module can be found in
-- Definition.Typed.Properties.Admissible.Pi.

module Definition.Untyped.Pi {a} (M : Set a) where

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n   : Nat
  t u : Term _
  σ   : Subst _ _
  ρ   : Wk _ _
  p   : M

------------------------------------------------------------------------
-- Iterated Π-types

opaque

  -- Iterated Π-types.

  Πs : M → M → Con Term n → Term n → Term 0
  Πs p q ε       B = B
  Πs p q (Γ ∙ A) B = Πs p q Γ (Π p , q ▷ A ▹ B)

opaque

  -- Iterated lambdas.

  lams : M → Con Term n → Term n → Term 0
  lams p ε       t = t
  lams p (Γ ∙ _) t = lams p Γ (lam p t)

opaque

  -- Iterated applications.

  apps : M → Con Term n → Term 0 → Term n
  apps p ε       t = t
  apps p (Γ ∙ _) t = wk1 (apps p Γ t) ∘⟨ p ⟩ var x0

------------------------------------------------------------------------
-- Some definitions related to heterogeneous Π-types

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

  ∘ʰ : M → (_ _ : Term n) → Term n
  ∘ʰ p t u = lower (t ∘⟨ p ⟩ lift u)

opaque
  unfolding ∘ʰ

  -- A substitution lemma for ∘ʰ.

  ∘ʰ-[] : ∘ʰ p t u [ σ ] ≡ ∘ʰ p (t [ σ ]) (u [ σ ])
  ∘ʰ-[] = refl

opaque

  -- A weakening lemma for ∘ʰ.

  wk-∘ʰ : wk ρ (∘ʰ p t u) ≡ ∘ʰ p (wk ρ t) (wk ρ u)
  wk-∘ʰ {ρ} {p} {t} {u} =
    wk ρ (∘ʰ p t u)                           ≡⟨ wk≡subst _ _ ⟩
    ∘ʰ p t u [ toSubst ρ ]                    ≡⟨ ∘ʰ-[] ⟩
    ∘ʰ p (t [ toSubst ρ ]) (u [ toSubst ρ ])  ≡˘⟨ cong₂ (∘ʰ _) (wk≡subst _ _) (wk≡subst _ _) ⟩
    ∘ʰ p (wk ρ t) (wk ρ u)                    ∎
