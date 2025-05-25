------------------------------------------------------------------------
-- Completeness of the algorithmic equality (in the absence of
-- equality reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Consequences.Completeness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Conversion R

open import Definition.Conversion.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    m n     : Nat
    ∇       : DCon (Term 0) m
    Γ       : Con Term n
    A B t u : Term n

opaque

  -- Algorithmic equality of types is derivable from judgmental
  -- equality.

  completeEq : ∇ » Γ ⊢ A ≡ B → ∇ » Γ ⊢ A [conv↑] B
  completeEq {∇} {Γ} {A} {B} =
    ∇ » Γ ⊢ A ≡ B                 →⟨ reducible-⊩≡ ⟩
    (∃ λ l → ∇ » Γ ⊩⟨ l ⟩ A ≡ B)  →⟨ escape-⊩≡ ∘→ proj₂ ⟩
    ∇ » Γ ⊢ A [conv↑] B           □

opaque

  -- Algorithmic equality of terms is derivable from judgmental
  -- equality.

  completeEqTerm : ∇ » Γ ⊢ t ≡ u ∷ A → ∇ » Γ ⊢ t [conv↑] u ∷ A
  completeEqTerm {∇} {Γ} {t} {u} {A} =
    ∇ » Γ ⊢ t ≡ u ∷ A                 →⟨ reducible-⊩≡∷ ⟩
    (∃ λ l → ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A)  →⟨ escape-⊩≡∷ ∘→ proj₂ ⟩
    ∇ » Γ ⊢ t [conv↑] u ∷ A           □
