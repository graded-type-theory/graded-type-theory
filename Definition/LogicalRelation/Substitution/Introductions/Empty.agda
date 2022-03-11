{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Introductions.Empty {a ℓ} (M′ : Setoid a ℓ)
                                                                   {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Properties M′
open import Definition.LogicalRelation.Substitution M′
open import Definition.LogicalRelation.Substitution.Introductions.Universe M′

open import Tools.Nat
open import Tools.Unit
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n


-- Validity of the Empty type.
Emptyᵛ : ∀ {l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Empty / [Γ]
Emptyᵛ [Γ] ⊢Δ [σ] = Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)) , λ _ x₂ → id (Emptyⱼ ⊢Δ)

-- Validity of the Empty type as a term.
Emptyᵗᵛ : ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ Empty ∷ U / [Γ] / Uᵛ [Γ]
Emptyᵗᵛ [Γ] ⊢Δ [σ] = let ⊢Empty  = Emptyⱼ ⊢Δ
                         [Empty] = Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))
                 in  Uₜ Empty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) [Empty]
                 ,   (λ x x₁ → Uₜ₌ Empty Empty (idRedTerm:*: ⊢Empty) (idRedTerm:*: ⊢Empty) Emptyₙ Emptyₙ
                                   (≅ₜ-Emptyrefl ⊢Δ) [Empty] [Empty] (id (Emptyⱼ ⊢Δ)))
