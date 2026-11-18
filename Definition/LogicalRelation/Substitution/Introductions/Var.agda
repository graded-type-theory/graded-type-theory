------------------------------------------------------------------------
-- Validity of variables.
------------------------------------------------------------------------

open import Configuration-types
open import Definition.Typed.EqualityRelation
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Var
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  {{eqrel : EqRelSet TC}}
  where

open EqRelSet eqrel
open Type-configuration TC

open import Definition.Untyped M
open import Definition.Untyped.Neutral.Atomic M TC⁻
open import Definition.Untyped.Properties M
open import Definition.Typed TC
open import Definition.Typed.Properties TC
open import Definition.LogicalRelation TC
open import Definition.LogicalRelation.Hidden TC
import Definition.LogicalRelation.Hidden.Restricted TC as R
open import Definition.LogicalRelation.Substitution TC

open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE

private
  variable
    x : Fin _
    Γ : Cons _ _
    A : Term _
    l : Universe-level

opaque

  -- Reducibility for variables.

  ⊩var :
    ⦃ inc : Var-included ⦄ →
    x ∷ A ∈ Γ .vars →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ var x ∷ A
  ⊩var x∈Γ ⊩A =
    case var (wf (escape-⊩ ⊩A)) x∈Γ of λ
      ⊢var →
    neutral-⊩∷ ⊩A varᵃₗ (~-var ⊢var)

opaque

  -- Well-typed variables in valid contexts are valid.

  varᵛ :
    x ∷ A ∈ Γ .vars →
    ⊩ᵛ Γ →
    ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ var x ∷ A
  varᵛ (here {A}) ⊩Γ∙A =
    case wf-⊩ᵛ-∙ ⊩Γ∙A of λ
      (l , ⊩A) →
    case wk1-⊩ᵛ ⊩A ⊩A of λ
      ⊩wk1-A →
      l
    , ⊩ᵛ∷⇔ .proj₂
        ( ⊩wk1-A
        , λ ξ⊇ σ₁≡σ₂ →
            case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
              ((_ , _ , σ₁₀≡σ₂₀) , _) →
            R.level-⊩≡∷
              (⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ξ⊇ ⊩wk1-A) (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁))
              (PE.subst (R._⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk1-tail A)
                 σ₁₀≡σ₂₀)
        )
  varᵛ (there x∈Γ) ⊩Γ∙B =
    case wf-⊩ᵛ-∙ ⊩Γ∙B .proj₂ of λ
      ⊩B →
    Σ.map idᶠ (wk1-⊩ᵛ∷ ⊩B) (varᵛ x∈Γ (wf-⊩ᵛ ⊩B))

opaque

  -- A variant of varᵛ.

  varᵛ′ :
    x ∷ A ∈ Γ .vars →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ var x ∷ A
  varᵛ′ x∈Γ ⊩A =
    level-⊩ᵛ∷ ⊩A (varᵛ x∈Γ (wf-⊩ᵛ ⊩A) .proj₂)
