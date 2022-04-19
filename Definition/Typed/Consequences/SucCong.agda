{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.SucCong (M : Set) where

open import Definition.Untyped M
open import Definition.Typed M
open import Definition.Typed.Weakening M
open import Definition.Typed.Properties M
open import Definition.Typed.Consequences.Syntactic M
open import Definition.Typed.Consequences.Substitution M

open import Tools.Fin
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Congruence of the type of the successor case in natrec.
sucCong : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
        → Γ ∙ ℕ ∙ F ⊢ wk1 (F [ suc (var x0) ]↑) ≡ wk1 (G [ suc (var x0) ]↑)
sucCong F≡G with wfEq F≡G
sucCong F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , ⊢G = syntacticEq F≡G
  in wkEq (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢F)
          (subst↑TypeEq F≡G (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ) here))))

sucCong′ : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
        → Γ ∙ ℕ ∙ G ⊢ wk1 (F [ suc (var x0) ]↑) ≡ wk1 (G [ suc (var x0) ]↑)
sucCong′ F≡G with wfEq F≡G
sucCong′ F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , ⊢G = syntacticEq F≡G
  in wkEq (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢G)
          (subst↑TypeEq F≡G (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ) here))))
