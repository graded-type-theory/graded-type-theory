open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Introductions.Nat {a ℓ} (M′ : Setoid a ℓ)
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
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n


-- Validity of the natural number type.
ℕᵛ : ∀ {l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ]
ℕᵛ [Γ] = wrap λ ⊢Δ [σ] → ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)) , λ _ x₂ → id (ℕⱼ ⊢Δ)

-- Validity of the natural number type as a term.
ℕᵗᵛ : ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ ℕ ∷ U / [Γ] / Uᵛ [Γ]
ℕᵗᵛ [Γ] ⊢Δ [σ] = let ⊢ℕ  = ℕⱼ ⊢Δ
                     [ℕ] = ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))
                 in  Uₜ ℕ (idRedTerm:*: ⊢ℕ) ℕₙ (≅ₜ-ℕrefl ⊢Δ) [ℕ]
                 ,   (λ x x₁ → Uₜ₌ ℕ ℕ (idRedTerm:*: ⊢ℕ) (idRedTerm:*: ⊢ℕ) ℕₙ ℕₙ
                                   (≅ₜ-ℕrefl ⊢Δ) [ℕ] [ℕ] (id (ℕⱼ ⊢Δ)))

-- Validity of zero.
zeroᵛ : ∀ {l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ zero ∷ ℕ / [Γ] / ℕᵛ [Γ]
zeroᵛ [Γ] ⊢Δ [σ] =
  ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) (≅ₜ-zerorefl ⊢Δ) zeroᵣ
    , (λ _ x₁ → ℕₜ₌ zero zero (idRedTerm:*: (zeroⱼ ⊢Δ)) (idRedTerm:*: (zeroⱼ ⊢Δ))
                    (≅ₜ-zerorefl ⊢Δ) zeroᵣ)

-- Validity of successor of valid natural numbers.
sucᵛ : ∀ {n l} ([Γ] : ⊩ᵛ Γ)
         ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
     → Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ / [Γ] / [ℕ]
     → Γ ⊩ᵛ⟨ l ⟩ suc n ∷ ℕ / [Γ] / [ℕ]
sucᵛ ⊢Γ [ℕ] [n] ⊢Δ [σ] =
  sucTerm (proj₁ (unwrap [ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
  , (λ x x₁ → sucEqTerm (proj₁ (unwrap [ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x x₁))
