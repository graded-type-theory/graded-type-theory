------------------------------------------------------------------------
-- Decidability of reducing to Π and Σ-types.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Tools.PropositionalEquality as PE
open import Tools.Relation

module Definition.Typed.Decidable.Reduction
  {a} {M : Set a}
  (R : Type-restrictions M)
  (_≟_ : Decidable (PE._≡_ {A = M}))
  where

open import Definition.Untyped M hiding (_∷_; U≢B; ℕ≢B; B≢ne)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inequality R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A : Term n

-- Decidability of being (reducing to) a binding type

isB′ : ∀ {l} → Γ ⊩⟨ l ⟩ A → Dec (∃₃ λ F G W → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (⟦ W ⟧ F ▹ G))
isB′ (Uᵣ′ l′ l< ⊢Γ) = no (λ {(F , G , W , ⊢F , ⊢G , U⇒W) → U≢B W (subset* U⇒W)})
isB′ (ℕᵣ x) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → ℕ≢B W (trans (sym (subset* (red x))) (subset* A⇒W))})
isB′ (Emptyᵣ x) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → Empty≢Bⱼ W (trans (sym (subset* (red x))) (subset* A⇒W))})
isB′ (Unitᵣ (Unitₜ x _)) =
  no (λ { (_ , _ , W , _ , _ , A⇒W) →
          Unit≢Bⱼ W (trans (sym (subset* (red x))) (subset* A⇒W)) })
isB′ (ne′ K D neK K≡K) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → B≢ne W neK (trans (sym (subset* A⇒W)) (subset* (red D)))})
isB′ (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
  yes (F , G , W , ⊢F , ⊢G , red D)
isB′ (emb 0<1 [A]) = isB′ [A]

isB : Γ ⊢ A → Dec (∃₃ λ F G W → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (⟦ W ⟧ F ▹ G))
isB ⊢A = isB′ (reducible ⊢A)

-- Decidability of being (reducing to) a Π-type

isΠ : Γ ⊢ A → Dec (∃₄ λ F G p q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Π p , q ▷ F ▹ G))
isΠ ⊢A with isB ⊢A
... | yes (F , G , BΠ p q , ⊢F , ⊢G , A⇒Π) = yes (F , G , p , q , ⊢F , ⊢G , A⇒Π)
... | yes (F , G , BΣ p q x , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , p′ , q′ , ⊢F , ⊢G , A⇒Π) → Π≢Σⱼ (trans (sym (subset* A⇒Π)) (subset* A⇒Σ))})
... | no ¬isB = no (λ {(F′ , G′ , p′ , q′ , ⊢F , ⊢G , A⇒Π) → ¬isB (F′ , G′ , BΠ p′ q′ , ⊢F , ⊢G , A⇒Π)})

-- Decidability of being (reducing to) a Σ-type

isΣ : Γ ⊢ A → Dec (∃₄ λ F G m p → ∃ λ q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σ⟨ m ⟩ p , q ▷ F ▹ G))
isΣ ⊢A with isB ⊢A
... | yes (F , G , BΣ m p q , ⊢F , ⊢G , A⇒Σ) = yes (F , G , m , p , q , ⊢F , ⊢G , A⇒Σ)
... | yes (F , G , BΠ p q , ⊢F , ⊢G , A⇒Π) = no (λ {(F′ , G′ , m′ , p′ , q′ , ⊢F , ⊢G , A⇒Σ) → Π≢Σⱼ (trans (sym (subset* A⇒Π)) (subset* A⇒Σ))})
... | no ¬isB = no (λ {(F′ , G′ , m , p′ , q′ , ⊢F , ⊢G , A⇒Π) → ¬isB (F′ , G′ , BΣ m p′ q′ , ⊢F , ⊢G , A⇒Π)})

isΣₚ : Γ ⊢ A → Dec (∃₄ λ F G p q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σₚ p , q ▷ F ▹ G))
isΣₚ ⊢A with isΣ ⊢A
... | yes (F , G , Σₚ , p , q , ⊢F , ⊢G , A⇒Σ) = yes (F , G , p , q , ⊢F , ⊢G , A⇒Σ)
... | yes (F , G , Σᵣ , p , q , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → Σₚ≢Σᵣⱼ (trans (sym (subset* A⇒Σ′)) (subset* A⇒Σ))})
... | no ¬isΣ = no (λ {(F′ , G′ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → ¬isΣ (F′ , G′ , Σₚ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′)})

isΣᵣ : Γ ⊢ A → Dec (∃₄ λ F G p q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σᵣ p , q ▷ F ▹ G))
isΣᵣ ⊢A with isΣ ⊢A
... | yes (F , G , Σₚ , p , q , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → Σₚ≢Σᵣⱼ (trans (sym (subset* A⇒Σ)) (subset* A⇒Σ′))})
... | yes (F , G , Σᵣ , p , q , ⊢F , ⊢G , A⇒Σ) = yes (F , G , p , q , ⊢F , ⊢G , A⇒Σ)
... | no ¬isΣ = no (λ {(F′ , G′ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → ¬isΣ (F′ , G′ , Σᵣ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′)})
