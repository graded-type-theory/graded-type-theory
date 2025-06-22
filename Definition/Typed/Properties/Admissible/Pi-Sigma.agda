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

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Well-formed R

open import Tools.Product

private variable
  Γ     : Con Term _
  A B E F G H l : Term _
  p q   : M
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
