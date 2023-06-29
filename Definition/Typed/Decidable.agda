------------------------------------------------------------------------
-- Decidability of typing.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Tools.PropositionalEquality as PE using (_≈_)
open import Tools.Relation

module Definition.Typed.Decidable
  {a} {M : Set a}
  (R : Type-restrictions M)
  (open Type-restrictions R)
  -- Equality is assumed to be decidable for M.
  (_≟_ : Decidable (PE._≡_ {A = M}))
  -- It is decidable whether the Unit type is allowed.
  (Unit-ok? : Dec Unit-allowed)
  -- ΠΣ-allowed is pointwise decidable.
  (ΠΣ-ok? : ∀ b p q → Dec (ΠΣ-allowed b p q))
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typechecking R
open import Definition.Typechecking.Soundness R
open import Definition.Typechecking.Completeness R
open import Definition.Typechecking.Decidable R _≟_ Unit-ok? ΠΣ-ok?

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
open import Definition.Typed.Decidable.Equality R _≟_ public

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

decWfCon : CheckableCon Γ → Dec (⊢ Γ)
decWfCon ε = yes ε
decWfCon (Γ ∙ A) = case decWfCon Γ of λ where
  (yes ⊢Γ) → case dec ⊢Γ A of λ where
    (yes ⊢A) → yes (⊢Γ ∙ ⊢A)
    (no ⊬A) → no λ where
      (⊢Γ ∙ ⊢A) → ⊬A ⊢A
  (no ⊬Γ) → no λ where
    (⊢Γ ∙ ⊢A) → ⊬Γ ⊢Γ
