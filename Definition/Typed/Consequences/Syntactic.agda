module Definition.Typed.Consequences.Syntactic
  {a} (M : Set a) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.EqRelInstance M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Escape M
open import Definition.LogicalRelation.Fundamental M
open import Definition.Typed.Consequences.Injectivity M

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    p q : M

-- Syntactic validity of type equality.
syntacticEq : ∀ {A B} → Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
syntacticEq A≡B with fundamentalEq A≡B
syntacticEq A≡B | [Γ] , [A] , [B] , [A≡B] =
  escapeᵛ [Γ] [A] , escapeᵛ [Γ] [B]

-- Syntactic validity of terms.
syntacticTerm : ∀ {t A} → Γ ⊢ t ∷ A → Γ ⊢ A
syntacticTerm t with fundamentalTerm t
syntacticTerm t | [Γ] , [A] , [t] = escapeᵛ [Γ] [A]

-- Syntactic validity of term equality.
syntacticEqTerm : ∀ {t u A} → Γ ⊢ t ≡ u ∷ A → Γ ⊢ A × (Γ ⊢ t ∷ A × Γ ⊢ u ∷ A)
syntacticEqTerm t≡u with fundamentalTermEq t≡u
syntacticEqTerm t≡u | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  escapeᵛ [Γ] [A] , escapeTermᵛ [Γ] [A] [t] , escapeTermᵛ [Γ] [A] [u]

-- Syntactic validity of type reductions.
syntacticRed : ∀ {A B} → Γ ⊢ A ⇒* B → Γ ⊢ A × Γ ⊢ B
syntacticRed D = syntacticEq (subset* D)

-- Syntactic validity of term reductions.
syntacticRedTerm : ∀ {t u A} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A × (Γ ⊢ t ∷ A × Γ ⊢ u ∷ A)
syntacticRedTerm d = syntacticEqTerm (subset*Term d)

-- Syntactic validity of Π-types.
syntacticΠ : ∀ {F G} → Γ ⊢ Π p , q ▷ F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΠ ΠFG with injectivity (refl ΠFG)
syntacticΠ ΠFG | F≡F , G≡G , _ = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)

syntacticΣ : ∀ {m F G} → Γ ⊢ Σ⟨ m ⟩ p , q ▷ F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΣ ΣFG with Σ-injectivity (refl ΣFG)
syntacticΣ ΣFG | F≡F , G≡G , _ = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)
