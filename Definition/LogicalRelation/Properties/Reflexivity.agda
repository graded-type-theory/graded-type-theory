------------------------------------------------------------------------
-- Equality in the logical relation is reflexive
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Reflexivity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Kit R

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    n : Nat
    l′ l : Universe-level
    A B t : Term _
    Γ : Con Term n


-- Reflexivity of reducible terms.
reflEqTerm : ∀ {l A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm _ ⊩t = ⊩t

-- Reflexivity of reducible types.
reflEq : ∀ {l A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]

private

  -- A lemma used below.

  reflEq-⊩< :
    (p : l′ <ᵘ l) (⊩A : Γ ⊩<⟨ p ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / emb p ⊩A
  reflEq-⊩< ≤ᵘ-refl     = reflEq
  reflEq-⊩< (≤ᵘ-step p) = reflEq-⊩< p

reflEq (Uᵣ′ l′ l< ⊢Γ) = ⊢Γ
reflEq (ℕᵣ D) = D
reflEq (Emptyᵣ D) = D
reflEq (Unitᵣ (Unitₜ D _)) = D
reflEq (ne′ inc _ D neK K≡K) = ne₌ inc _ D neK K≡K
reflEq (Bᵣ′ _ _ _ D A≡A [F] [G] _ _) =
   B₌ _ _ D A≡A
      (λ ρ → reflEq ([F] ρ))
      (λ ρ [a] → reflEq ([G] ρ [a]))
reflEq (Idᵣ ⊩A) = record
  { ⇒*Id′             = ⇒*Id
  ; Ty≡Ty′            = reflEq ⊩Ty
  ; lhs≡lhs′          = reflEqTerm ⊩Ty ⊩lhs
  ; rhs≡rhs′          = reflEqTerm ⊩Ty ⊩rhs
  ; lhs≡rhs→lhs′≡rhs′ = idᶠ
  ; lhs′≡rhs′→lhs≡rhs = idᶠ
  }
  where
  open _⊩ₗId_ ⊩A
reflEq (emb p [A]) = reflEq-⊩< p [A]
