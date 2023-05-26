------------------------------------------------------------------------
-- The logical relation is closed under weakenings
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Substitution.Weakening
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Substitution R

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Weakening of valid types by one.
wk1ᵛ : ∀ {A F l}
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
    → Γ ∙ F ⊩ᵛ⟨ l ⟩ wk1 A / [Γ] ∙ [F]
wk1ᵛ {A = A} [Γ] [F] [A] = wrap λ ⊢Δ [σ] →
  let [σA] = proj₁ (unwrap [A] ⊢Δ (proj₁ [σ]))
      [σA]′ = irrelevance′ (PE.sym (subst-wk A)) [σA]
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] →
         irrelevanceEq″ (PE.sym (subst-wk A))
                        (PE.sym (subst-wk A))
                        [σA] [σA]′
                        (proj₂ (unwrap [A] ⊢Δ (proj₁ [σ])) (proj₁ [σ′]) (proj₁ [σ≡σ′])))

-- Weakening of valid type equality by one.
wk1Eqᵛ : ∀ {A B F l}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([A≡B] : Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A])
       → Γ ∙ F ⊩ᵛ⟨ l ⟩ wk1 A ≡ wk1 B / [Γ] ∙ [F] / wk1ᵛ {A = A} {F} [Γ] [F] [A]
wk1Eqᵛ {A = A} {B} [Γ] [F] [A] [A≡B] ⊢Δ [σ] =
  let [σA] = proj₁ (unwrap [A] ⊢Δ (proj₁ [σ]))
      [σA]′ = irrelevance′ (PE.sym (subst-wk A)) [σA]
  in  irrelevanceEq″ (PE.sym (subst-wk A))
                     (PE.sym (subst-wk B))
                     [σA] [σA]′
                     ([A≡B] ⊢Δ (proj₁ [σ]))
