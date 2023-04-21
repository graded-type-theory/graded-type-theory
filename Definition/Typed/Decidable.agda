open import Tools.PropositionalEquality as PE using (_≈_)
open import Tools.Relation

module Definition.Typed.Decidable
  {a} {M : Set a} (_≟_ : Decidable (_≈_ {A = M})) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typechecking M
open import Definition.Typechecking.Soundness M
open import Definition.Typechecking.Completeness M
open import Definition.Typechecking.Decidable _≟_

open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A t : Term n

-- Re-export decidability of type and term equality
open import Definition.Typed.Decidable.Equality _≟_ public

-- Decidability of well-formed types

dec : ⊢ Γ → Checkable A → Dec (Γ ⊢ A)
dec ⊢Γ A = map (soundness⇇Type ⊢Γ) (completeness⇇Type A) (dec⇇Type ⊢Γ A)

-- Decidability of type checking Checkable terms

decTermᶜ : ⊢ Γ → Γ ⊢ A → Checkable t → Dec (Γ ⊢ t ∷ A)
decTermᶜ ⊢Γ ⊢A t = map (soundness⇇ ⊢Γ) (completeness⇇ t) (dec⇇ ⊢Γ t ⊢A)

-- Decidability of type inference of Inferable terms

decTermᵢ : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ∷ A)
decTermᵢ ⊢Γ t = map (λ { (A , t⇉A) → A , (proj₂ (soundness⇉ ⊢Γ t⇉A))})
                    (λ { (A , ⊢t)  → _ , (proj₁ (proj₂ (completeness⇉ t ⊢t)))})
                    (dec⇉ ⊢Γ t)

-- Decidability of well-formed contexts consisting of checkable types

data CheckableCon : (Γ : Con Term n) → Set a where
  ε : CheckableCon ε
  _∙_ : CheckableCon Γ → Checkable A → CheckableCon (Γ ∙ A)

decWfCon : CheckableCon Γ → Dec (⊢ Γ)
decWfCon ε = yes ε
decWfCon (Γ ∙ A) = case decWfCon Γ of λ where
  (yes ⊢Γ) → case dec ⊢Γ A of λ where
    (yes ⊢A) → yes (⊢Γ ∙ ⊢A)
    (no ⊬A) → no λ where
      (⊢Γ ∙ ⊢A) → ⊬A ⊢A
  (no ⊬Γ) → no λ where
    (⊢Γ ∙ ⊢A) → ⊬Γ ⊢Γ
