------------------------------------------------------------------------
-- Derived rules related to both Π- and Σ-types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.DerivedRules.Pi-Sigma
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R

open import Definition.Untyped M hiding (_∷_)

open import Tools.Function
open import Tools.Product

private variable
  Γ               : Con _ _
  A A₁ A₂ B B₁ B₂ : Term _
  p q             : M
  b               : BinderMode

opaque

  -- A variant of the type formation rule ΠΣⱼ.

  ΠΣⱼ′ :
    Γ ∙ A ⊢ B →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ΠΣⱼ′ ⊢B ok =
    case wf ⊢B of λ {
      (_ ∙ ⊢A) →
    ΠΣⱼ ⊢A ⊢B ok }

opaque

  -- A variant of the type equality rule ΠΣ-cong.

  ΠΣ-cong′ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂
  ΠΣ-cong′ A₁≡A₂ =
    ΠΣ-cong (syntacticEq A₁≡A₂ .proj₁) A₁≡A₂

opaque

  -- A variant of the term equality rule ΠΣ-cong.

  ΠΣ-cong-U :
    Γ ⊢ A₁ ≡ A₂ ∷ U →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ ∷ U →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷ U
  ΠΣ-cong-U A₁≡A₂ =
    ΠΣ-cong (univ (syntacticEqTerm A₁≡A₂ .proj₂ .proj₁)) A₁≡A₂
