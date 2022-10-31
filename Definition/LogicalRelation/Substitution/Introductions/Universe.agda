{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation
open import Tools.Level
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Introductions.Universe {a ℓ} (M′ : Setoid a ℓ)
                                                                      {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Properties M′
open import Definition.LogicalRelation.Substitution M′

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Validity of the universe type.
Uᵛ : ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ]
Uᵛ [Γ] = wrap λ ⊢Δ [σ] → Uᵣ′ ⁰ 0<1 ⊢Δ , λ _ x₂ → lift PE.refl

-- Valid terms of type U are valid types.
univᵛ : ∀ {A l l′} ([Γ] : ⊩ᵛ Γ)
        ([U] : Γ ⊩ᵛ⟨ l ⟩ U / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ∷ U / [Γ] / [U]
      → Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]
univᵛ {l′ = l′} [Γ] [U] [A] = wrap λ ⊢Δ [σ] →
  let [A]₁ = maybeEmb′ {l = l′} (univEq (proj₁ (unwrap [U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ [σ′] [σ≡σ′] → univEqEq (proj₁ (unwrap [U] ⊢Δ [σ])) [A]₁
                                       ((proj₂ ([A] ⊢Δ [σ])) [σ′] [σ≡σ′]))

-- Valid term equality of type U is valid type equality.
univEqᵛ : ∀ {A B l l′} ([Γ] : ⊩ᵛ Γ)
          ([U] : Γ ⊩ᵛ⟨ l′ ⟩ U / [Γ])
          ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        → Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B ∷ U / [Γ] / [U]
        → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
univEqᵛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ (unwrap [U] ⊢Δ [σ])) (proj₁ (unwrap [A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
