------------------------------------------------------------------------
-- Embedding of the logical relation into higher type levels
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.MaybeEmbed
  {a} (M : Set a) {{eqrel : EqRelSet M}} where

open EqRelSet {{...}}

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Irrelevance M
open import Definition.LogicalRelation.Properties M
open import Definition.LogicalRelation.Substitution M
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
