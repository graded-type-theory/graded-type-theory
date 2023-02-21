open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Conversion
  {a} (M : Set a) {{eqrel : EqRelSet M}} where

open EqRelSet {{...}}

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

-- Conversion from left to right of valid terms.
convᵛ : ∀ {t A B l}
        ([Γ] : ⊩ᵛ Γ)
        ([A]  : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        ([B]  : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ t ∷ B / [Γ] / [B]
convᵛ [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
  let [σA]     = proj₁ (unwrap [A] ⊢Δ [σ])
      [σB]     = proj₁ (unwrap [B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
      [σt]     = proj₁ ([t] ⊢Δ [σ])
      [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ])
  in  convTerm₁ [σA] [σB] [σA≡σB] [σt]
  ,   λ [σ′] [σ≡σ′] → convEqTerm₁ [σA] [σB] [σA≡σB] ([σt≡σ′t] [σ′] [σ≡σ′])

-- Conversion from right to left of valid terms.
conv₂ᵛ : ∀ {t A B l}
         ([Γ] : ⊩ᵛ Γ)
         ([A]  : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([B]  : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
       → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
       → Γ ⊩ᵛ⟨ l ⟩ t ∷ B / [Γ] / [B]
       → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
conv₂ᵛ [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
  let [σA]     = proj₁ (unwrap [A] ⊢Δ [σ])
      [σB]     = proj₁ (unwrap [B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
      [σt]     = proj₁ ([t] ⊢Δ [σ])
      [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ])
  in  convTerm₂ [σA] [σB] [σA≡σB] [σt]
  ,   λ [σ′] [σ≡σ′] → convEqTerm₂ [σA] [σB] [σA≡σB] ([σt≡σ′t] [σ′] [σ≡σ′])

-- Conversion from left to right of valid term equality.
convEqᵛ : ∀ {t u A B l}
        ([Γ] : ⊩ᵛ Γ)
        ([A]  : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        ([B]  : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B / [Γ] / [B]
convEqᵛ [Γ] [A] [B] [A≡B] [t≡u] ⊢Δ [σ] =
  let [σA]     = proj₁ (unwrap [A] ⊢Δ [σ])
      [σB]     = proj₁ (unwrap [B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
  in  convEqTerm₁ [σA] [σB] [σA≡σB] ([t≡u] ⊢Δ [σ])
