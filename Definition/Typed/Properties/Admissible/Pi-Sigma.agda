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
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R
open import Definition.Typed.Properties.Admissible.Lift R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n     : Nat
  Γ     : Con Term n
  A A′ B B′ C E F G H a f g l l₁ l₂ t u : Term n
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
-- Heterogeneous variants of Π and Σ that take types in different universes.
-- See also the bottom of Definition.Typed.Properties.Admissible.{Pi,Sigma}.

ΠΣʰ : (b : BinderMode) (p q : M) (l₁ l₂ A : Term n) (B : Term (1+ n)) → Term n
ΠΣʰ b p q l₁ l₂ A B = ΠΣ⟨ b ⟩ p , q ▷ Lift l₂ A ▹ Lift (wk1 l₁) (lower₀ B)

Σʰ⟨_⟩ : (s : Strength) (p q : M) (l₁ l₂ A : Term n) (B : Term (1+ n)) → Term n
Σʰ⟨ s ⟩ p q l₁ l₂ A B = ΠΣʰ (BMΣ s) p q l₁ l₂ A B

Πʰ Σʰˢ Σʰʷ : (p q : M) (l₁ l₂ A : Term n) (B : Term (1+ n)) → Term n
Πʰ p q l₁ l₂ A B = ΠΣʰ BMΠ p q l₁ l₂ A B
Σʰˢ p q l₁ l₂ A B = ΠΣʰ (BMΣ 𝕤) p q l₁ l₂ A B
Σʰʷ p q l₁ l₂ A B = ΠΣʰ (BMΣ 𝕨) p q l₁ l₂ A B

opaque

  ΠΣʰⱼ : Γ     ⊢ l₂ ∷ Level
       → Γ     ⊢ A ∷ U l₁
       → Γ ∙ A ⊢ B ∷ U (wk1 l₂)
       → ΠΣ-allowed b p q
       → Γ     ⊢ ΠΣʰ b p q l₁ l₂ A B ∷ U (l₁ supᵘ l₂)
  ΠΣʰⱼ ⊢l₂ ⊢A ⊢B ok =
    let ⊢l₁ = inversion-U-Level (wf-⊢∷ ⊢A)
    in ΠΣⱼ′
        (Liftⱼ′ ⊢l₂ ⊢A)
        (Liftⱼ-comm
          (wkTerm₁ (Liftⱼ ⊢l₂ (univ ⊢A)) ⊢l₁)
          (PE.subst (_⊢_∷_ _ _) wk[]′-[]↑ (lower₀Term ⊢l₂ ⊢B)))
        ok

opaque

  ΠΣʰ-cong
    : Γ     ⊢ l₂ ∷ Level
    → Γ     ⊢ A ≡ A′ ∷ U l₁
    → Γ ∙ A ⊢ B ≡ B′ ∷ U (wk1 l₂)
    → ΠΣ-allowed b p q
    → Γ     ⊢ ΠΣʰ b p q l₁ l₂ A B ≡ ΠΣʰ b p q l₁ l₂ A′ B′ ∷ U (l₁ supᵘ l₂)
  ΠΣʰ-cong ⊢l₂ A≡A′ B≡B′ ok =
    let ⊢U , ⊢A , ⊢A′ = wf-⊢≡∷ A≡A′
        ⊢l₁ = inversion-U-Level ⊢U
    in ΠΣ-cong′
        (Lift-cong′ (refl ⊢l₂) A≡A′)
        (Lift-cong-comm
          (refl (wkTerm₁ (Liftⱼ ⊢l₂ (univ ⊢A)) ⊢l₁))
          (PE.subst (_⊢_≡_∷_ _ _ _) wk[]′-[]↑ (lower₀TermEq ⊢l₂ B≡B′)))
        ok
