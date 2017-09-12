{-# OPTIONS --without-K #-}

module Definition.Typed.SubstitutionTest where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T

open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE


mutual
  substitutionVar : ∀ {Γ Δ n A σ} → ⊢ Γ → n ∷ A ∈ Γ → Δ ⊢ₛ σ ∷ Γ → ⊢ Δ → Δ ⊢ substVar σ n ∷ subst σ A
  substitutionVar x here (σ₁ , x₁) ⊢Δ = PE.subst (\x → _ ⊢ _ ∷ x) {!!} x₁
  substitutionVar x (there x₁) (σ₁ , x₂) ⊢Δ =
    PE.subst (\x → _ ⊢ _ ∷ x) {!!} (substitutionVar {!!} x₁ σ₁ ⊢Δ)

  substitution : ∀ {A Γ Δ σ} → Γ ⊢ A → Δ ⊢ₛ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A
  substitution (ℕ x) σ₁ ⊢Δ = ℕ ⊢Δ
  substitution (U x) σ₁ ⊢Δ = U ⊢Δ
  substitution (Π A ▹ A₁) σ₁ ⊢Δ = Π (substitution A σ₁ ⊢Δ) ▹ substitution A₁ (liftSubst' {!!} ⊢Δ A σ₁) (⊢Δ ∙ (substitution A σ₁ ⊢Δ))
  substitution (univ x) σ₁ ⊢Δ = univ (substitutionTerm x σ₁ ⊢Δ)

  substitutionEq : ∀ {A B Γ Δ σ}
                 → Γ ⊢ A ≡ B → Δ ⊢ₛ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A ≡ subst σ B
  substitutionEq (univ x) σ₁ ⊢Δ = {!!}
  substitutionEq (refl x) σ₁ ⊢Δ = {!!}
  substitutionEq (sym x) σ₁ ⊢Δ = {!!}
  substitutionEq (trans x x₁) σ₁ ⊢Δ = {!!}
  substitutionEq (Π-cong x x₁ x₂) σ₁ ⊢Δ = {!!}

  substitutionTerm : ∀ {t A Γ Δ σ}
                 → Γ ⊢ t ∷ A → Δ ⊢ₛ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ t ∷ subst σ A
  substitutionTerm (ℕ x) σ₁ ⊢Δ = ℕ ⊢Δ
  substitutionTerm (Π x ▹ x₁) σ₁ ⊢Δ = {!!}
  substitutionTerm (var x₁ x₂) σ₁ ⊢Δ = substitutionVar x₁ x₂ σ₁ ⊢Δ
  substitutionTerm (lam x x₁) σ₁ ⊢Δ = lam (substitution x σ₁ ⊢Δ) (substitutionTerm x₁ (liftSubst' {!!} ⊢Δ x σ₁) (⊢Δ ∙ (substitution x σ₁ ⊢Δ)))
  substitutionTerm (x ∘ x₁) σ₁ ⊢Δ = PE.subst (\x → _ ⊢ _ ∷ x) {!!} ((substitutionTerm x σ₁ ⊢Δ) ∘ (substitutionTerm x₁ σ₁ ⊢Δ))
  substitutionTerm (zero x) σ₁ ⊢Δ = zero ⊢Δ
  substitutionTerm (suc x) σ₁ ⊢Δ = suc (substitutionTerm x σ₁ ⊢Δ)
  substitutionTerm (natrec x x₁ x₂ x₃) σ₁ ⊢Δ =
    PE.subst (\x → _ ⊢ _ ∷ x) {!!}
      (natrec {!!} (substitutionTerm x₁ σ₁ ⊢Δ)
              {!!} (substitutionTerm x₃ σ₁ ⊢Δ))
  substitutionTerm (conv x x₁) σ₁ ⊢Δ = conv {!!} {!!}

  substitutionEqTerm : ∀ {t u A Γ Δ σ}
                     → Γ ⊢ t ≡ u ∷ A → Δ ⊢ₛ σ ∷ Γ → ⊢ Δ
                     → Δ ⊢ subst σ t ≡ subst σ u ∷ subst σ A
  substitutionEqTerm (refl x) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (sym x) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (trans x x₁) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (conv x x₁) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (Π-cong x x₁ x₂) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (app-cong x x₁) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (β-red x x₁ x₂) σ₁ ⊢Δ =
    PE.subst₂ (\x y → _ ⊢ _ ≡ y ∷ x) {!!} {!!}
      (β-red (substitution x σ₁ ⊢Δ)
             (substitutionTerm x₁ (liftSubst' {!!} ⊢Δ x σ₁) (⊢Δ ∙ (substitution x σ₁ ⊢Δ)))
             (substitutionTerm x₂ σ₁ ⊢Δ))
  substitutionEqTerm (fun-ext x x₁ x₂ x₃) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (suc-cong x) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (natrec-cong x x₁ x₂ x₃) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (natrec-zero x x₁ x₂) σ₁ ⊢Δ = {!!}
  substitutionEqTerm (natrec-suc x x₁ x₂ x₃) σ₁ ⊢Δ = {!!}

  wkSubst' : ∀ {ρ σ Γ Δ Δ'} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ' : ⊢ Δ')
             ([ρ] : ρ ∷ Δ' ⊆ Δ)
             ([σ] : Δ ⊢ₛ σ ∷ Γ)
           → Δ' ⊢ₛ ρ •ₛ σ ∷ Γ
  wkSubst' ε ⊢Δ ⊢Δ' ρ id = id
  wkSubst' (_∙_ {Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ' ρ (tailσ , headσ) =
    wkSubst' ⊢Γ ⊢Δ ⊢Δ' ρ tailσ
    , PE.subst (λ x → _ ⊢ _ ∷ x) (wk-subst A) (wkTerm ρ ⊢Δ' headσ)

  wk1Subst' : ∀ {F σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
              (⊢F : Δ ⊢ F)
              ([σ] : Δ ⊢ₛ σ ∷ Γ)
            → (Δ ∙ F) ⊢ₛ wk1Subst σ ∷ Γ
  wk1Subst' {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
    wkSubst' ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (T.step T.id) [σ]

  liftSubst' : ∀ {F σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
               (⊢F  : Γ ⊢ F)
               ([σ] : Δ ⊢ₛ σ ∷ Γ)
             → (Δ ∙ subst σ F) ⊢ₛ liftSubst σ ∷ Γ ∙ F
  liftSubst' {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
    let ⊢Δ∙F = ⊢Δ ∙ substitution ⊢F [σ] ⊢Δ
    in  wkSubst' ⊢Γ ⊢Δ ⊢Δ∙F (T.step T.id) [σ]
    ,   var ⊢Δ∙F (PE.subst (λ x → 0 ∷ x ∈ (Δ ∙ subst σ F))
                           (wk-subst F) here)

  substComp' : ∀ {σ σ' Γ Δ Δ'} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ' : ⊢ Δ')
               ([σ] : Δ' ⊢ₛ σ ∷ Δ)
               ([σ'] : Δ ⊢ₛ σ' ∷ Γ)
             → Δ' ⊢ₛ σ ₛ•ₛ σ' ∷ Γ
  substComp' ε ⊢Δ ⊢Δ' [σ] id = id
  substComp' (_∙_ {Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ' [σ] ([tailσ'] , [headσ']) =
    substComp' ⊢Γ ⊢Δ ⊢Δ' [σ] [tailσ']
    , PE.subst (λ x → _ ⊢ _ ∷ x) (substCompEq A)
               (substitutionTerm [headσ'] [σ] ⊢Δ')
