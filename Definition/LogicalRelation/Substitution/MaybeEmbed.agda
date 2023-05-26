------------------------------------------------------------------------
-- Embedding of the logical relation into higher type levels
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Substitution.MaybeEmbed
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.Untyped M using (Con ; Term)

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Any level can be embedded into the highest level (validity variant).
maybeEmbᵛ : ∀ {l A}
            ([Γ] : ⊩ᵛ Γ)
          → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
          → Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]
maybeEmbᵛ {l = ⁰} [Γ] [A] = wrap λ ⊢Δ [σ] →
  let [σA]  = proj₁ (unwrap [A] ⊢Δ [σ])
      [σA]′ = maybeEmb (proj₁ (unwrap [A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ (unwrap [A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
maybeEmbᵛ {l = ¹} [Γ] [A] = [A]

-- The lowest level can be embedded in any level (validity variant).
maybeEmbₛ′ : ∀ {l A}
             ([Γ] : ⊩ᵛ Γ)
           → Γ ⊩ᵛ⟨ ⁰ ⟩ A / [Γ]
           → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
maybeEmbₛ′ {l = ⁰} [Γ] [A] = [A]
maybeEmbₛ′ {l = ¹} [Γ] [A] = wrap λ ⊢Δ [σ] →
  let [σA]  = proj₁ (unwrap [A] ⊢Δ [σ])
      [σA]′ = maybeEmb′ (proj₁ (unwrap [A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ (unwrap [A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
