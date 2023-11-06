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
    n : Nat
    Γ : Con Term n

-- Congruence of the type of the successor case in natrec.
sucCong : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
        → Γ ∙ ℕ ∙ F ⊢ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑²
sucCong F≡G with wfEq F≡G
sucCong F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , ⊢G = syntacticEq F≡G
  in subst↑²TypeEq ⊢ℕ ⊢F F≡G (refl (sucⱼ (var₁ ⊢F)))

sucCong′ : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
        → Γ ∙ ℕ ∙ G ⊢ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑²
sucCong′ F≡G with wfEq F≡G
sucCong′ F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , ⊢G = syntacticEq F≡G
  in subst↑²TypeEq ⊢ℕ ⊢G F≡G (refl (sucⱼ (var₁ ⊢G)))
