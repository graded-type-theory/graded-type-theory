------------------------------------------------------------------------
-- Syntactic validity of the typing and reduction relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Syntactic
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M hiding (_∷_; wk)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Weakening R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Fundamental R
open import Definition.Typed.Consequences.Injectivity R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term n
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

opaque

  -- The relation _⊢_⇒*_ is contained in _⊢_:⇒*:_.

  ⇒*→:⇒*: : Γ ⊢ A ⇒* B → Γ ⊢ A :⇒*: B
  ⇒*→:⇒*: A⇒*B =
    case syntacticRed A⇒*B of λ
      (⊢A , ⊢B) →
    [ ⊢A , ⊢B , A⇒*B ]

-- Syntactic validity of term reductions.
syntacticRedTerm : ∀ {t u A} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A × (Γ ⊢ t ∷ A × Γ ⊢ u ∷ A)
syntacticRedTerm d = syntacticEqTerm (subset*Term d)

opaque

  -- The relation _⊢_⇒*_∷_ is contained in _⊢_:⇒*:_∷_.

  ⇒*∷→:⇒*:∷ : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t :⇒*: u ∷ A
  ⇒*∷→:⇒*:∷ t⇒*u =
    case syntacticRedTerm t⇒*u of λ
      (_ , ⊢t , ⊢u) →
    [ ⊢t , ⊢u , t⇒*u ]

-- Syntactic validity of Π-types.
syntacticΠ : ∀ {F G} → Γ ⊢ Π p , q ▷ F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΠ ΠFG with injectivity (refl ΠFG)
syntacticΠ ΠFG | F≡F , G≡G , _ = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)

syntacticΣ : ∀ {m F G} → Γ ⊢ Σ⟨ m ⟩ p , q ▷ F ▹ G → Γ ⊢ F × Γ ∙ F ⊢ G
syntacticΣ ΣFG with Σ-injectivity (refl ΣFG)
syntacticΣ ΣFG | F≡F , G≡G , _ = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)

-- Syntactic validity of context lookup

syntacticVar : ∀ {x A} → x ∷ A ∈ Γ → ⊢ Γ → Γ ⊢ A
syntacticVar here (_ ∙ ⊢A) = wk₁ ⊢A ⊢A
syntacticVar (there x) (⊢Γ ∙ ⊢B) = wk₁ ⊢B (syntacticVar x ⊢Γ)
