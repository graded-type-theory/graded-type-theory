------------------------------------------------------------------------
-- Validity of the unit type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- Validity of the Unit type.
Unitᵛ :
  ∀ {l} ([Γ] : ⊩ᵛ Γ) → Unit-allowed → Γ ⊩ᵛ⟨ l ⟩ Unit / [Γ]
Unitᵛ _ ok =
  wrap λ ⊢Δ _ →
    Unitᵣ (Unitₜ (idRed:*: (Unitⱼ ⊢Δ ok)) ok)
  , λ _ _ → id (Unitⱼ ⊢Δ ok)

-- Validity of the Unit type as a term.
Unitᵗᵛ :
  ([Γ] : ⊩ᵛ Γ) →
  Unit-allowed →
  Γ ⊩ᵛ⟨ ¹ ⟩ Unit ∷ U / [Γ] / Uᵛ [Γ]
Unitᵗᵛ _ ok ⊢Δ _ =
    Uₜ Unit (idRedTerm:*: ⊢Unit) Unitₙ Unit≅Unit [Unit]
  , (λ _ _ →
       Uₜ₌ Unit Unit (idRedTerm:*: ⊢Unit) (idRedTerm:*: ⊢Unit)
         Unitₙ Unitₙ Unit≅Unit [Unit] [Unit] (id ⊢Unit′))
  where
  ⊢Unit     = Unitⱼ ⊢Δ ok
  ⊢Unit′    = univ ⊢Unit
  Unit≅Unit = ≅ₜ-Unitrefl ⊢Δ ok
  [Unit]    = Unitᵣ (Unitₜ (idRed:*: ⊢Unit′) ok)

-- Validity of star.
starᵛ :
  ∀ {l} ([Γ] : ⊩ᵛ Γ) (ok : Unit-allowed) →
  Γ ⊩ᵛ⟨ l ⟩ star ∷ Unit / [Γ] / Unitᵛ [Γ] ok
starᵛ [Γ] ok ⊢Δ _ =
    Unitₜ star (idRedTerm:*: ⊢star) starₙ
  , (λ _ _ → Unitₜ₌ ⊢star ⊢star)
  where
  ⊢star = starⱼ ⊢Δ ok

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
      ok = ⊩ᵛUnit→Unit-allowed [Unit]
      UnitJ : Δ ⊩⟨ l ⟩ Unit
      UnitJ = Unitᵣ (Unitₜ (idRed:*: (Unitⱼ ⊢Δ ok)) ok)
      [σe] = irrelevanceTerm J UnitJ [σe]
      [σe'] = irrelevanceTerm J UnitJ [σe']
      ⊢σe = escapeTerm UnitJ [σe]
      ⊢σe' = escapeTerm UnitJ [σe']
  in  irrelevanceEqTerm UnitJ J (Unitₜ₌ ⊢σe ⊢σe')
