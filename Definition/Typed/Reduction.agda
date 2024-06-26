------------------------------------------------------------------------
-- Weak head expansion of equality
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Reduction
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A A′ B B′ : Term n
    a a′ b b′ : Term n

-- Weak head expansion of type equality
reduction : Γ ⊢ A ↘ A′
          → Γ ⊢ B ↘ B′
          → Γ ⊢ A′ ≡ B′
          → Γ ⊢ A ≡ B
reduction (D , _) (D′ , _) A′≡B′ =
  trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

reduction′ : Γ ⊢ A ↘ A′
           → Γ ⊢ B ↘ B′
           → Γ ⊢ A ≡ B
           → Γ ⊢ A′ ≡ B′
reduction′ (D , _) (D′ , _) A≡B =
  trans (sym (subset* D)) (trans A≡B (subset* D′))

-- Weak head expansion of term equality
reductionₜ : Γ ⊢ A ↘ B
           → Γ ⊢ a ↘ a′ ∷ B
           → Γ ⊢ b ↘ b′ ∷ B
           → Γ ⊢ a′ ≡ b′ ∷ B
           → Γ ⊢ a ≡ b ∷ A
reductionₜ (D , _) (d , _) (d′ , _) a′≡b′ =
  conv (trans (subset*Term d)
              (trans a′≡b′ (sym (subset*Term d′))))
       (sym (subset* D))

reductionₜ′ : Γ ⊢ A ↘ B
            → Γ ⊢ a ↘ a′ ∷ B
            → Γ ⊢ b ↘ b′ ∷ B
            → Γ ⊢ a ≡ b ∷ A
            → Γ ⊢ a′ ≡ b′ ∷ B
reductionₜ′ (D , _) (d , _) (d′ , _) a≡b =
  trans (sym (subset*Term d))
        (trans (conv a≡b (subset* D)) (subset*Term d′))
