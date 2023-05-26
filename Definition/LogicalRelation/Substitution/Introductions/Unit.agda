------------------------------------------------------------------------
-- Validity of the unit type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Unit
  {a} (M : Set a) {{eqrel : EqRelSet M}} where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Properties M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Introductions.Universe M
open import Definition.LogicalRelation.Irrelevance M

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Validity of the Unit type.
Unitᵛ : ∀ {l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ]
Unitᵛ [Γ] = wrap λ ⊢Δ [σ] → Unitᵣ (idRed:*: (Unitⱼ ⊢Δ)) , λ _ x₂ → id (Unitⱼ ⊢Δ)

-- Validity of the Unit type as a term.
Unitᵗᵛ : ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ¹ ⟩ Unit ∷ U / [Γ] / Uᵛ [Γ]
Unitᵗᵛ [Γ] ⊢Δ [σ] = let ⊢Unit  = Unitⱼ ⊢Δ
                        [Unit] = Unitᵣ (idRed:*: (Unitⱼ ⊢Δ))
                    in  Uₜ Unit (idRedTerm:*: ⊢Unit) Unitₙ (≅ₜ-Unitrefl ⊢Δ) [Unit]
                    ,   (λ x x₁ → Uₜ₌ Unit Unit (idRedTerm:*: ⊢Unit) (idRedTerm:*: ⊢Unit) Unitₙ Unitₙ
                                      (≅ₜ-Unitrefl ⊢Δ) [Unit] [Unit] (id (Unitⱼ ⊢Δ)))

-- Validity of star.
starᵛ : ∀ {l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ star ∷ Unit / [Γ] / Unitᵛ [Γ]
starᵛ [Γ] ⊢Δ [σ] =
  Unitₜ star (idRedTerm:*: (starⱼ ⊢Δ)) starₙ
    , (λ _ x₁ → Unitₜ₌ (starⱼ ⊢Δ) (starⱼ ⊢Δ))

-- Validity of η-unit.
η-unitᵛ : ∀ {l e e'} ([Γ] : ⊩ᵛ Γ)
  ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ])
  ([e] : Γ ⊩ᵛ⟨ l ⟩ e ∷ Unit / [Γ] / [Unit])
  ([e'] : Γ ⊩ᵛ⟨ l ⟩ e' ∷ Unit / [Γ] / [Unit])
  → Γ ⊩ᵛ⟨ l ⟩ e ≡ e' ∷ Unit / [Γ] / [Unit]
η-unitᵛ {Γ = Γ} {l} {e} {e'} [Γ] [Unit] [e] [e'] {Δ = Δ} {σ} ⊢Δ [σ] =
  let J = proj₁ (unwrap [Unit] ⊢Δ [σ])
      [σe] = proj₁ ([e] ⊢Δ [σ])
      [σe'] = proj₁ ([e'] ⊢Δ [σ])
      UnitJ : Δ ⊩⟨ l ⟩ Unit
      UnitJ = Unitᵣ (idRed:*: (Unitⱼ ⊢Δ))
      [σe] = irrelevanceTerm J UnitJ [σe]
      [σe'] = irrelevanceTerm J UnitJ [σe']
      ⊢σe = escapeTerm UnitJ [σe]
      ⊢σe' = escapeTerm UnitJ [σe']
  in  irrelevanceEqTerm UnitJ J (Unitₜ₌ ⊢σe ⊢σe')
