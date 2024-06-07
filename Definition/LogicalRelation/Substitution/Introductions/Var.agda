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
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Irrelevance R

open import Tools.Fin
open import Tools.Function
open import Tools.Product

private
  variable
    x : Fin _
    Γ : Con Term _
    A : Term _
    l : TypeLevel

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

  -- A variant of varᵛ.

  varᵛ′ :
    x ∷ A ∈ Γ →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ var x ∷ A
  varᵛ′ x∈Γ ⊩A =
    level-⊩ᵛ∷ ⊩A (varᵛ x∈Γ (wf-⊩ᵛ ⊩A) .proj₂)

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- Another variant of varᵛ.

  var-⊩ᵛ∷// :
    x ∷ A ∈ Γ →
    (⊩Γ : ⊩ᵛ Γ)
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ var x ∷ A / ⊩Γ / ⊩A
  var-⊩ᵛ∷// x∈Γ ⊩Γ ⊩A =
    case varᵛ x∈Γ ⊩Γ of λ
      (_ , _ , ⊩A′ , ⊩x) →
    irrelevanceTerm _ _ ⊩A′ ⊩A ⊩x
