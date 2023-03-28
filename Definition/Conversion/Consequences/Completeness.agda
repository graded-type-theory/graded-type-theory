module Definition.Conversion.Consequences.Completeness
  {a} (M : Set a) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Conversion M

open import Definition.Conversion.EqRelInstance M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Escape M
open import Definition.LogicalRelation.Fundamental M

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Algorithmic equality is derivable from judgemental equality of types.
completeEq : ∀ {A B} → Γ ⊢ A ≡ B → Γ ⊢ A [conv↑] B
completeEq A≡B =
  let [Γ] , [A] , [B] , [A≡B] = fundamentalEq A≡B
  in  escapeEqᵛ [Γ] [A] [A≡B]

-- Algorithmic equality is derivable from judgemental equality of terms.
completeEqTerm : ∀ {t u A} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ t [conv↑] u ∷ A
completeEqTerm t≡u =
  let [Γ] , modelsTermEq [A] [t] [u] [t≡u] = fundamentalTermEq t≡u
  in  escapeEqTermᵛ [Γ] [A] [t≡u]
