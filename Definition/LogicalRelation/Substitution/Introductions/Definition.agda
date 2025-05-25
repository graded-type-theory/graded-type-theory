------------------------------------------------------------------------
-- Validity of definitions.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Definition
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
open import Definition.Typed.Weakening R hiding (wk)
open import Definition.Typed.Weakening.Definition R

open import Definition.LogicalRelation.Hidden.Restricted R
open import Definition.LogicalRelation.Substitution R

open import Tools.Function
open import Tools.Level hiding (_⊔_)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum
open import Tools.Unit

private
  variable
    n α : Nat
    ∇ ∇′ : DCon (Term 0) _
    Γ : Con Term _
    t t′ u A B : Term _
    l l′ : Universe-level
    p : M

------------------------------------------------------------------------
-- Validity of definition contexts

opaque

  -- Valid definition contexts.
  
  »ᵛ_ : DCon (Term 0) n → Set a
  »ᵛ ε              = Lift _ ⊤
  »ᵛ (∇ ∙[ t ∷ A ]) = »ᵛ ∇ × ∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A

opaque
  unfolding »ᵛ_

  -- A characterisation lemma for »ᵛ_.

  »ᵛε⇔ : »ᵛ ε ⇔ ⊤
  »ᵛε⇔ = _

opaque
  unfolding »ᵛ_

  -- A characterisation lemma for »ᵛ_.

  »ᵛ∙⇔ : »ᵛ ∇ ∙[ t ∷ A ] ⇔ (»ᵛ ∇ × ∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A)
  »ᵛ∙⇔ = id⇔

opaque

  -- An introduction lemma for »ᵛ_.

  »ᵛ-∙-intro : »ᵛ ∇ → ∇ » ε ⊩ᵛ⟨ l′ ⟩ t ∷ A → »ᵛ ∇ ∙[ t ∷ A ]
  »ᵛ-∙-intro »∇ ⊩t = »ᵛ∙⇔ .proj₂ (»∇ , _ , ⊩t)

private instance
  
  ε-inc : Var-included or-empty (ε {A = Term})
  ε-inc = ε

opaque

  -- A well-formedness lemma for _↦∷_∈_.

  wf-↦∈ᵛ : α ↦∷ A ∈ ∇ → »ᵛ ∇ → ∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ A
  wf-↦∈ᵛ here »∇ =
    let _ , l , ⊩t = »ᵛ∙⇔ .proj₁ »∇
    in  l , defn-wk-⊩ᵛ (stepᵗ₁ (escape-⊩ᵛ∷ ⊩t)) (wf-⊩ᵛ∷ ⊩t)
  wf-↦∈ᵛ (there α↦t) »∇ =
    let »∇′ , _ , ⊩u = »ᵛ∙⇔ .proj₁ »∇
        l , ⊩A = wf-↦∈ᵛ α↦t »∇′
    in  l , defn-wk-⊩ᵛ (stepᵗ₁ (escape-⊩ᵛ∷ ⊩u)) ⊩A

opaque

  -- A well-formedness lemma for _↦_∷_∈_.

  wf-↦∷∈ᵛ : α ↦ t ∷ A ∈ ∇ → »ᵛ ∇ → ∃ λ l → ∇ » ε ⊩ᵛ⟨ l ⟩ t ∷ A
  wf-↦∷∈ᵛ here »∇ =
    let _ , l , ⊩t = »ᵛ∙⇔ .proj₁ »∇
    in  l , defn-wk-⊩ᵛ∷ (stepᵗ₁ (escape-⊩ᵛ∷ ⊩t)) ⊩t
  wf-↦∷∈ᵛ (there α↦t) »∇ =
    let »∇′ , _ , ⊩u = »ᵛ∙⇔ .proj₁ »∇
        l , ⊩t = wf-↦∷∈ᵛ α↦t »∇′
    in  l , defn-wk-⊩ᵛ∷ (stepᵗ₁ (escape-⊩ᵛ∷ ⊩u)) ⊩t

opaque

  -- An escape lemma for »ᵛ_.

  escape-»ᵛ : »ᵛ ∇ → » ∇
  escape-»ᵛ {∇ = ε}            »∇ = ε
  escape-»ᵛ {∇ = ∇ ∙[ t ∷ A ]} »∇ =
    ∙ escape-⊩ᵛ∷ ⦃ inc = ε ⦄ (»ᵛ∙⇔ .proj₁ »∇ .proj₂ .proj₂)

------------------------------------------------------------------------
-- Validity theorems for definitions

opaque

  -- Validity of δ-reduction.

  δ-redᵛ :
    α ↦ t ∷ A ∈ ∇ →
    »ᵛ ∇ →
    ∇ »⊩ᵛ Γ →
    ∃ λ l → ∇ » Γ ⊩ᵛ⟨ l ⟩ defn α ≡ wk wk₀ t ∷ wk wk₀ A
  δ-redᵛ {α} {t} {A} {∇} {Γ} α↦t »∇ ⊩Γ =
    let l , ⊩t = wf-↦∷∈ᵛ α↦t »∇
        
        α⇒t : ∀ {κ′ ∇′} {ξ : DExt _ κ′ _} (ξ⊇ : ξ » ∇′ ⊇ ∇)
                {m Δ} {σ : Subst m _} ⦃ inc : Var-included or-empty Δ ⦄
              → ∇′ » Δ ⊩ˢ σ ∷ Γ
              → ∇′ » Δ ⊢ defn α [ σ ] ⇒ wk wk₀ t [ σ ] ∷ wk wk₀ A [ σ ]
        α⇒t ξ⊇ ⊩σ = PE.subst₂ (_ » _ ⊢ defn α ⇒_∷_)
                              (PE.sym (wk₀-subst-invariant t))
                              (PE.sym (wk₀-subst-invariant A))
                              (δ-red (escape-⊩ˢ∷ ⊩σ .proj₁)
                                     (there*-↦∷∈ ξ⊇ α↦t)
                                     PE.refl PE.refl)

    in  l , ⊩ᵛ∷-⇐ α⇒t (wk-⊩ᵛ∷ wk₀∷⊇ ⊩Γ ⊩t)

opaque

  -- Validity of definitions.
  
  defnᵛ :
    α ↦∷ A ∈ ∇ →
    »ᵛ ∇ →
    ∇ »⊩ᵛ Γ →
    ∃ λ l → ∇ » Γ ⊩ᵛ⟨ l ⟩ defn α ∷ wk wk₀ A
  defnᵛ α↦∷A »∇ ⊩Γ =
    let l , α≡t = δ-redᵛ (↦∈⇒↦∷∈ α↦∷A .proj₂) »∇ ⊩Γ
    in  l , wf-⊩ᵛ≡∷ α≡t .proj₁
