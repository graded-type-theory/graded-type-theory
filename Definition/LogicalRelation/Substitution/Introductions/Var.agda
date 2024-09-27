------------------------------------------------------------------------
-- Validity of variables.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Var
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R as H
open import Definition.LogicalRelation.Hidden.Levels R
open import Definition.LogicalRelation.Substitution R

open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE

private
  variable
    x : Fin _
    Γ : Con Term _
    A : Term _
    l : Universe-level

opaque

  -- Reducibility for variables.

  ⊩⟨⟩var :
    x ∷ A ∈ Γ →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ var x ∷ A
  ⊩⟨⟩var x∈Γ ⊩A =
    case var (wf (H.escape-⊩ ⊩A)) x∈Γ of λ
      ⊢var →
    H.neutral-⊩∷ ⊩A (var _) ⊢var (~-var ⊢var)

opaque
  unfolding _⊩_ _⊩_∷_

  -- Reducibility for variables.

  ⊩var :
    x ∷ A ∈ Γ →
    Γ ⊩ A →
    Γ ⊩ var x ∷ A
  ⊩var x∈Γ (_ , ⊩A) = _ , ⊩⟨⟩var x∈Γ ⊩A

opaque

  -- Well-typed variables in valid contexts are valid.

  varᵛ :
    x ∷ A ∈ Γ →
    ⊩ᵛ Γ →
    Γ ⊩ᵛ var x ∷ A
  varᵛ (here {A}) ⊩Γ∙A =
    case wf-⊩ᵛ-∙ ⊩Γ∙A of λ
      ⊩A →
    ⊩ᵛ∷⇔ .proj₂
      ( wk1-⊩ᵛ ⊩A ⊩A
      , λ σ₁≡σ₂ →
          case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
            (_ , σ₁₀≡σ₂₀ , _) →
          PE.subst (_⊩_≡_∷_ _ _ _) (PE.sym $ wk1-tail A) σ₁₀≡σ₂₀
      )
  varᵛ (there x∈Γ) ⊩Γ∙B =
    case wf-⊩ᵛ-∙ ⊩Γ∙B of λ
      ⊩B →
    wk1-⊩ᵛ∷ ⊩B (varᵛ x∈Γ (wf-⊩ᵛ ⊩B))

opaque

  -- A variant of varᵛ.

  varᵛ′ :
    x ∷ A ∈ Γ →
    Γ ⊩ᵛ A →
    Γ ⊩ᵛ var x ∷ A
  varᵛ′ x∈Γ ⊩A =
    varᵛ x∈Γ (wf-⊩ᵛ ⊩A)
