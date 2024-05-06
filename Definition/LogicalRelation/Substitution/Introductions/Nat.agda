------------------------------------------------------------------------
-- Validity of the natural numbers type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Nat
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import
  Definition.LogicalRelation.Substitution.Introductions.DoubleSubst R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
open import Definition.LogicalRelation.Substitution.Weakening R

open import Tools.Fin
open import Tools.Nat using (Nat)
open import Tools.Product

private
  variable
    n   : Nat
    Γ   : Con Term n
    F G : Term n


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

private
  [suc] : ∀ {l}
        → ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
        → Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ suc (var x1) ∷ ℕ / [Γ] ∙ ℕᵛ [Γ] ∙ [F] / ℕᵛ ([Γ] ∙ ℕᵛ [Γ] ∙ [F])
  [suc] {l = l} [Γ] [F] {σ = σ} ⊢Δ [σ] =
    let [ℕ] = ℕᵛ [Γ]
        [ΓℕF] = [Γ] ∙ [ℕ] ∙ [F]
        [ℕ]′ = ℕᵛ {l = l} [ΓℕF]
        [x1] = varᵛ (there here) [ΓℕF] [ℕ]′
    in  sucᵛ {n = var x1} [ΓℕF] [ℕ]′ (λ {_} {_} {σ₁} ⊢Δ₁ [σ]₁ → [x1] {σ = σ₁} ⊢Δ₁ [σ]₁) {σ = σ} ⊢Δ [σ]

opaque
  unfolding wk1ᵛ

  subst↑²S-suc :
    ∀ {Γ : Con Term n} {F l}
    ([Γ] : ⊩ᵛ Γ)
    ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ])) →
    Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ F [ suc (var x1) ]↑² / [Γ] ∙ ℕᵛ [Γ] ∙ [F]
  subst↑²S-suc {n} {Γ} {F} {l} [Γ] [F] =
    let [ℕ] = ℕᵛ [Γ]
    in  subst↑²S {t = suc (var x1)} [Γ] [ℕ] [F] [ℕ] [F] (λ {_} {_} {σ} → [suc] [Γ] [F] {σ = σ})

opaque
  unfolding wk1ᵛ

  subst↑²S-suc′ :
    ∀ {Γ : Con Term n} {F G l}
    ([Γ] : ⊩ᵛ Γ)
    ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ])) →
    ([G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ])) →
    Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ G [ suc (var x1) ]↑² / [Γ] ∙ ℕᵛ [Γ] ∙ [F]
  subst↑²S-suc′ {n} {Γ} {F} {l} [Γ] [F] [G] =
    let [ℕ] = ℕᵛ [Γ]
    in  subst↑²S {t = suc (var x1)} [Γ] [ℕ] [F] [ℕ] [G] (λ {_} {_} {σ} → [suc] [Γ] [F] {σ = σ})

opaque
  unfolding subst↑²S-suc

  subst↑²SEq-suc : ∀ {Γ : Con Term n} {F l}
    ([Γ] : ⊩ᵛ Γ)
    ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
    ([G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
    ([F≡G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) / [F]) →
    Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑² / [Γ] ∙ ℕᵛ [Γ] ∙ [F] / subst↑²S-suc [Γ] [F]
  subst↑²SEq-suc {l = l} [Γ] [F] [G] [F≡G] =
    let [ℕ] = ℕᵛ [Γ]
    in  subst↑²SEq [Γ] [ℕ] [F] [ℕ] [F] [G] [F≡G] (λ {_} {_} {σ} → [suc] [Γ] [F] {σ = σ})

opaque
  unfolding subst↑²S-suc′

  subst↑²SEq-suc′ : ∀ {Γ : Con Term n} {F l}
    ([Γ] : ⊩ᵛ Γ)
    ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
    ([G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
    ([F≡G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) / [F]) →
    Γ ∙ ℕ ∙ G ⊩ᵛ⟨ l ⟩ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑² / [Γ] ∙ ℕᵛ [Γ] ∙ [G] / subst↑²S-suc′ [Γ] [G] [F]
  subst↑²SEq-suc′ {l = l} [Γ] [F] [G] [F≡G] =
    let [ℕ] = ℕᵛ [Γ]
    in  subst↑²SEq [Γ] [ℕ] [G] [ℕ] [F] [G] [F≡G] (λ {_} {_} {σ} → [suc] [Γ] [G] {σ = σ})
