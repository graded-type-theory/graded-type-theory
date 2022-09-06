open import Tools.PropositionalEquality as PE using (_≈_)
open import Tools.Relation

module Definition.Typed.Decidable
  {a} {M : Set a} (_≟_ : Decidable (_≈_ {A = M})) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Conversion.Decidable _≟_
open import Definition.Conversion.Soundness M
open import Definition.Conversion.Consequences.Completeness M

open import Tools.Level
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
open import Tools.Unit

private
  variable
    n : Nat
    Γ : Con Term n
    A t : Term n

-- Re-export decidability of type and term equality
open import Definition.Typed.Decidable.Equality M″ public

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

-- Decidability of well-formed contexts consisting of normal form types

CheckableCon : (Γ : Con Term n) → Set a
CheckableCon ε = Lift a ⊤
CheckableCon (Γ ∙ A) = Checkable A × CheckableCon Γ

decWfCon : CheckableCon Γ → Dec (⊢ Γ)
decWfCon {Γ = ε} (lift tt) = yes ε
decWfCon {Γ = Γ ∙ A} (NfA , NfΓ) with decWfCon NfΓ
decWfCon {Γ = Γ ∙ A} (NfA , NfΓ) | yes ⊢Γ with dec ⊢Γ NfA
decWfCon {Γ = Γ ∙ A} (NfA , NfΓ) | yes ⊢Γ | yes ⊢A = yes (⊢Γ ∙ ⊢A)
decWfCon {Γ = Γ ∙ A} (NfA , NfΓ) | yes ⊢Γ | no ⊬A = no λ { (_ ∙ ⊢A) → ⊬A ⊢A}
decWfCon {Γ = Γ ∙ A} (NfA , NfΓ) | no ⊬Γ = no (λ { (⊢Γ ∙ _) → ⊬Γ ⊢Γ})
