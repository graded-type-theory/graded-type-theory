open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Reflexivity {a ℓ} (M′ : Setoid a ℓ)
                                                           {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using () renaming (Carrier to M)

open import Definition.LogicalRelation.Properties M′
open import Definition.LogicalRelation.Substitution M′
open import Definition.Untyped M using (Con ; Term)

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Reflexivity of valid types.
reflᵛ : ∀ {A l}
        ([Γ] : ⊩ᵛ Γ)
        ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ≡ A / [Γ] / [A]
reflᵛ [Γ] [A] ⊢Δ [σ] =
  reflEq (proj₁ (unwrap [A] ⊢Δ [σ]))

-- Reflexivity of valid terms.
reflᵗᵛ : ∀ {A t l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A])
       → Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A / [Γ] / [A]
reflᵗᵛ [Γ] [A] [t] ⊢Δ [σ] =
  reflEqTerm (proj₁ (unwrap [A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))
