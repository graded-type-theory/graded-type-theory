------------------------------------------------------------------------
-- Definitions related to ΠΣ⟨_⟩_,_▷_▹_
------------------------------------------------------------------------

module Definition.Untyped.Pi-Sigma {a} (M : Set a) where

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n     : Nat
  A B   : Term _
  l₁ l₂ : Lvl _
  σ     : Subst _ _
  ρ     : Wk _ _
  s     : Strength
  b     : BinderMode
  p q   : M

opaque

  -- Heterogeneous Π- and Σ-types.

  ΠΣʰ :
    BinderMode → (_ _ : M) (_ _ : Lvl n) → Term n → Term (1+ n) → Term n
  ΠΣʰ b p q l₁ l₂ A B =
    ΠΣ⟨ b ⟩ p , q ▷ Lift l₂ A ▹ Lift (wk1 l₁) (lower₀ B)

-- Heterogeneous Π-types.

Πʰ : (_ _ : M) (_ _ : Lvl n) → Term n → Term (1+ n) → Term n
Πʰ = ΠΣʰ BMΠ

-- Heterogeneous Σ-types.

Σʰ⟨_⟩ :
  Strength → (_ _ : M) (_ _ : Lvl n) → Term n →  Term (1+ n) → Term n
Σʰ⟨ s ⟩ = ΠΣʰ (BMΣ s)

-- Heterogeneous strong Σ-types.

Σʰˢ : (_ _ : M) (_ _ : Lvl n) → Term n → Term (1+ n) → Term n
Σʰˢ = Σʰ⟨ 𝕤 ⟩

-- Heterogeneous weak Σ-types.

Σʰʷ : (_ _ : M) (_ _ : Lvl n) → Term n → Term (1+ n) → Term n
Σʰʷ = Σʰ⟨ 𝕨 ⟩

opaque
  unfolding ΠΣʰ

  -- A substitution lemma for ΠΣʰ.

  ΠΣʰ-[] :
    ΠΣʰ b p q l₁ l₂ A B [ σ ] ≡
    ΠΣʰ b p q (l₁ [ σ ]) (l₂ [ σ ]) (A [ σ ]) (B [ σ ⇑ ])
  ΠΣʰ-[] {b} {p} {q} {l₁} {l₂} {A} {B} {σ} =
    ΠΣ⟨ b ⟩ p , q ▷ Lift (l₂ [ σ ]) (A [ σ ]) ▹
      Lift (wk (step id) l₁ [ σ ⇑ ]) (lower₀ B [ σ ⇑ ])    ≡⟨ cong₂ (ΠΣ⟨ b ⟩ p , q ▷_▹_) refl $
                                                              cong₂ Lift (wk1-liftSubst l₁) lower₀-[⇑] ⟩
    ΠΣ⟨ b ⟩ p , q ▷ Lift (l₂ [ σ ]) (A [ σ ]) ▹
      Lift (wk (step id) (l₁ [ σ ])) (lower₀ (B [ σ ⇑ ]))  ∎

opaque

  -- A weakening lemma for ΠΣʰ.

  wk-ΠΣʰ :
    wk ρ (ΠΣʰ b p q l₁ l₂ A B) ≡
    ΠΣʰ b p q (wk ρ l₁) (wk ρ l₂) (wk ρ A) (wk (lift ρ) B)
  wk-ΠΣʰ {ρ} {b} {p} {q} {l₁} {l₂} {A} {B} =
    wk ρ (ΠΣʰ b p q l₁ l₂ A B)                                         ≡⟨ wk≡subst _ _ ⟩

    ΠΣʰ b p q l₁ l₂ A B [ toSubst ρ ]                                  ≡⟨ ΠΣʰ-[] ⟩

    ΠΣʰ b p q (l₁ [ toSubst ρ ]) (l₂ [ toSubst ρ ]) (A [ toSubst ρ ])
      (B [ toSubst ρ ⇑ ])                                              ≡˘⟨ cong (ΠΣʰ _ _ _ _ _ _) $
                                                                           substVar-to-subst (toSubst-liftn 1) B ⟩
    ΠΣʰ b p q (l₁ [ toSubst ρ ]) (l₂ [ toSubst ρ ]) (A [ toSubst ρ ])
      (B [ toSubst (lift ρ) ])                                         ≡˘⟨ cong₄ (ΠΣʰ _ _ _)
                                                                             (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _) ⟩
    ΠΣʰ b p q (wk ρ l₁) (wk ρ l₂) (wk ρ A) (wk (lift ρ) B)             ∎
