------------------------------------------------------------------------
-- Definitions related to Lift
------------------------------------------------------------------------

module Definition.Untyped.Lift {a} (M : Set a) where

open import Definition.Untyped M
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

opaque

  -- If Γ ∙ A ⊢ t ∷ B, then Γ ∙ Lift l A ⊢ lower₀ t ∷ lower₀ B.

  lower₀ : Term (1+ n) → Term (1+ n)
  lower₀ t = t [ lower (var x0) ]↑

opaque
  unfolding lower₀

  -- A substitution lemma for lower₀.

  lower₀-[⇑] : lower₀ t [ σ ⇑ ] ≡ lower₀ (t [ σ ⇑ ])
  lower₀-[⇑] {t} {σ} =
    t [ lower (var x0) ]↑ [ σ ⇑ ]  ≡⟨ [][]↑-commutes t ⟩
    t [ σ ⇑ ] [ lower (var x0) ]↑  ∎

opaque

  -- A weakening lemma for lower₀.

  wk-lift-lower₀ : wk (lift ρ) (lower₀ t) ≡ lower₀ (wk (lift ρ) t)
  wk-lift-lower₀ {ρ} {t} =
    wk (lift ρ) (lower₀ t)           ≡⟨ wk≡subst _ _ ⟩
    lower₀ t [ toSubst (lift ρ) ]    ≡⟨ substVar-to-subst (toSubst-liftn 1) (lower₀ _) ⟩
    lower₀ t [ toSubst ρ ⇑ ]         ≡⟨ lower₀-[⇑] ⟩
    lower₀ (t [ toSubst ρ ⇑ ])       ≡˘⟨ cong lower₀ $ substVar-to-subst (toSubst-liftn 1) t ⟩
    lower₀ (t [ toSubst (lift ρ) ])  ≡˘⟨ cong lower₀ $ wk≡subst _ _ ⟩
    lower₀ (wk (lift ρ) t)           ∎
