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
open import Definition.LogicalRelation.Hidden R
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

  ⊩var :
    x ∷ A ∈ Γ →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ var x ∷ A
  ⊩var x∈Γ ⊩A =
    case var (wf (escape-⊩ ⊩A)) x∈Γ of λ
      ⊢var →
    neutral-⊩∷ ⊩A (var _) ⊢var (~-var ⊢var)

opaque

  -- Well-typed variables in valid contexts are valid.

  varᵛ :
    x ∷ A ∈ Γ →
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
        , λ σ₁≡σ₂ →
            case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
              ((_ , _ , σ₁₀≡σ₂₀) , _) →
            level-⊩≡∷
              (⊩ᵛ→⊩ˢ∷→⊩[] ⊩wk1-A (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁))
              (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk1-tail A)
                 σ₁₀≡σ₂₀)
        )
  varᵛ (there x∈Γ) ⊩Γ∙B =
    case wf-⊩ᵛ-∙ ⊩Γ∙B .proj₂ of λ
      ⊩B →
    Σ.map idᶠ (wk1-⊩ᵛ∷ ⊩B) (varᵛ x∈Γ (wf-⊩ᵛ ⊩B))

opaque

  -- A variant of varᵛ.

  varᵛ′ :
    x ∷ A ∈ Γ →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ var x ∷ A
  varᵛ′ x∈Γ ⊩A =
    level-⊩ᵛ∷ ⊩A (varᵛ x∈Γ (wf-⊩ᵛ ⊩A) .proj₂)
