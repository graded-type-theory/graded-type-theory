------------------------------------------------------------------------
-- Completeness of the algorithmic equality (in the absence of
-- equality reflection)
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Conversion.Consequences.Completeness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  (open Type-configuration TC)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Typed TC
open import Definition.Conversion TC

open import Definition.Conversion.EqRelInstance TC
open import Definition.LogicalRelation TC
open import Definition.LogicalRelation.Hidden TC
open import Definition.LogicalRelation.Properties TC
open import Definition.LogicalRelation.Fundamental.Reducibility TC

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private variable
  m n     : Nat
  Γ       : Cons m n
  A B t u : Term n
  l₁ l₂   : Lvl _

opaque

  -- Algorithmic equality of types is derivable from judgmental
  -- equality.

  completeEq : Γ ⊢ A ≡ B → Γ ⊢ A [conv↑] B
  completeEq {Γ} {A} {B} =
    Γ ⊢ A ≡ B                 →⟨ reducible-⊩≡ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B)  →⟨ escape-⊩≡ ∘→ proj₂ ⟩
    Γ ⊢ A [conv↑] B           □

opaque

  -- Algorithmic equality of terms is derivable from judgmental
  -- equality.

  completeEqTerm : Γ ⊢ t ≡ u ∷ A → Γ ⊢ t [conv↑] u ∷ A
  completeEqTerm {Γ} {t} {u} {A} =
    Γ ⊢ t ≡ u ∷ A                 →⟨ reducible-⊩≡∷ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ t ≡ u ∷ A)  →⟨ escape-⊩≡∷ ∘→ proj₂ ⟩
    Γ ⊢ t [conv↑] u ∷ A           □

opaque

  -- A completeness lemma for level equality.

  completeEqLevel : Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₁ [conv↑] l₂ ∷Level
  completeEqLevel {Γ} {l₁} {l₂} =
    Γ ⊢ l₁ ≡ l₂ ∷Level        →⟨ reducible-⊩≡∷L ⟩
    Γ ⊩Level l₁ ≡ l₂ ∷Level   →⟨ escapeLevelEq ⟩
    Γ ⊢ l₁ [conv↑] l₂ ∷Level  □
