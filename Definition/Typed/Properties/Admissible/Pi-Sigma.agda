------------------------------------------------------------------------
-- Admissible rules related to Π and Σ
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Pi-Sigma
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Pi-Sigma M
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R
open import Definition.Typed.Properties.Admissible.Lift R
import Definition.Typed.Properties.Admissible.Pi-Sigma.Primitive R as PP

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n     : Nat
  Γ     : Con Term n
  A A₁ A₂ B B₁ B₂ C E F G H a f g l l₁ l₁₁ l₁₂ l₂ l₂₁ l₂₂ t u : Term n
  p p′ q : M
  s     : Strength
  b     : BinderMode

------------------------------------------------------------------------
-- Simple variants of typing, equality and reduction rules

opaque

  ΠΣⱼ′ : Γ     ⊢ A ∷ U l
       → Γ ∙ A ⊢ B ∷ U (wk1 l)
       → ΠΣ-allowed b p q
       → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U l
  ΠΣⱼ′ ⊢A ⊢B ok = ΠΣⱼ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢A ⊢B ok

opaque

  ΠΣ-cong′ : Γ     ⊢ F ≡ H ∷ U l
           → Γ ∙ F ⊢ G ≡ E ∷ U (wk1 l)
           → ΠΣ-allowed b p q
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡
                     ΠΣ⟨ b ⟩ p , q ▷ H ▹ E ∷ U l
  ΠΣ-cong′ F≡H G≡E ok = ΠΣ-cong (inversion-U-Level (wf-⊢≡∷ F≡H .proj₁)) F≡H G≡E ok

------------------------------------------------------------------------
-- Some properties related to ΠΣʰ

opaque

  -- An admissible typing rule for ΠΣʰ.

  ΠΣʰⱼ :
    Γ ⊢ l₂ ∷ Level →
    Γ ⊢ A ∷ U l₁ →
    Γ ∙ A ⊢ B ∷ U (wk1 l₂) →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B ∷ U (l₁ supᵘ l₂)
  ΠΣʰⱼ ⊢l₂ ⊢A = PP.ΠΣʰⱼ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢l₂ ⊢A

opaque

  -- An admissible equality rule for ΠΣʰ.

  ΠΣʰ-cong :
    Γ ⊢ l₁₁ ≡ l₁₂ ∷ Level →
    Γ ⊢ l₂₁ ≡ l₂₂ ∷ Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁₁ →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk1 l₂₁) →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣʰ b p q l₁₁ l₂₁ A₁ B₁ ≡ ΠΣʰ b p q l₁₂ l₂₂ A₂ B₂ ∷
      U (l₁₁ supᵘ l₂₁)
  ΠΣʰ-cong l₁₁≡l₁₂ l₂₁≡l₂₂ A₁≡A₂ =
    let _ , ⊢l₁₁ , _ = wf-⊢≡∷ l₁₁≡l₁₂
        _ , ⊢l₂₁ , _ = wf-⊢≡∷ l₂₁≡l₂₂
        _ , ⊢A₁ , _  = wf-⊢≡∷ A₁≡A₂
    in
    PP.ΠΣʰ-cong ⊢l₁₁ ⊢l₂₁ l₁₁≡l₁₂ l₂₁≡l₂₂ (univ ⊢A₁) A₁≡A₂
