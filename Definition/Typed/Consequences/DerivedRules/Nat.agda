------------------------------------------------------------------------
-- Derived rules related to the natural number type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Nat
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R

open import Tools.Fin
open import Tools.Nat
open import Tools.Product

private
  variable
    Γ : Con Term _
    A A′ z z′ s s′ n n′ : Term _
    p q r : M

opaque

  -- Congruence of the type of the successor case in natrec.
  sucCong : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
          → Γ ∙ ℕ ∙ F ⊢ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑²
  sucCong F≡G with wfEq F≡G
  sucCong F≡G | ⊢Γ ∙ ⊢ℕ =
    let ⊢F , ⊢G = syntacticEq F≡G
    in subst↑²TypeEq ⊢ℕ ⊢F F≡G (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ ∙ ⊢F) (there here))))

opaque

  sucCong′ : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
          → Γ ∙ ℕ ∙ G ⊢ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑²
  sucCong′ F≡G with wfEq F≡G
  sucCong′ F≡G | ⊢Γ ∙ ⊢ℕ =
    let ⊢F , ⊢G = syntacticEq F≡G
    in subst↑²TypeEq ⊢ℕ ⊢G F≡G (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ ∙ ⊢G) (there here))))

opaque

  -- A variant of natrec-cong.

  natrec-cong′ : Γ ∙ ℕ     ⊢ A ≡ A′
               → Γ         ⊢ z ≡ z′ ∷ A [ zero ]₀
               → Γ ∙ ℕ ∙ A ⊢ s ≡ s′ ∷ A [ suc (var x1) ]↑²
               → Γ         ⊢ n ≡ n′ ∷ ℕ
               → Γ         ⊢ natrec p q r A z s n ≡
                             natrec p q r A′ z′ s′ n′ ∷
                             A [ n ]₀
  natrec-cong′ A≡A′ z≡z′ s≡s′ n≡n′ =
    natrec-cong (syntacticEq A≡A′ .proj₁) A≡A′ z≡z′ s≡s′ n≡n′
