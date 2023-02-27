open import Definition.Modality

module Definition.Modality.Usage.Weakening
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Mode 𝕄
open import Definition.Untyped M hiding (_∙_ ; subst)

open import Tools.Fin
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.Product
open import Tools.PropositionalEquality as PE

private
  variable
    ℓ n m : Nat
    ρ : Wk m n
    p r : M
    γ δ : Conₘ n
    t : Term n
    m′ : Mode

-- Weakenings of modality contexts

wkConₘ : Wk m n → Conₘ n → Conₘ m
wkConₘ id γ = γ
wkConₘ (step ρ) γ = (wkConₘ ρ γ) ∙ 𝟘
wkConₘ (lift ρ) (γ ∙ p) = wkConₘ ρ γ ∙ p

-- Weakening the zero context is the zero context
-- wkConₘ ρ 𝟘ᶜ ≡ 𝟘ᶜ

wk-𝟘ᶜ : (ρ : Wk m n) → wkConₘ ρ 𝟘ᶜ ≡ 𝟘ᶜ
wk-𝟘ᶜ id = PE.refl
wk-𝟘ᶜ (step ρ) = cong (λ γ → γ ∙ 𝟘) (wk-𝟘ᶜ ρ)
wk-𝟘ᶜ (lift ρ) = cong (λ γ → γ ∙ 𝟘) (wk-𝟘ᶜ ρ)

-- Weakening of modality contexts distribute over addition
-- wkConₘ ρ (γ +ᶜ δ) ≈ᶜ wkConₘ ρ γ +ᶜ wkConₘ ρ δ

wk-+ᶜ : (ρ : Wk m n) → wkConₘ ρ (γ +ᶜ δ) ≈ᶜ wkConₘ ρ γ +ᶜ wkConₘ ρ δ
wk-+ᶜ id = ≈ᶜ-refl
wk-+ᶜ (step ρ) = (wk-+ᶜ ρ) ∙ (≈-sym (+-identityˡ 𝟘))
wk-+ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = (wk-+ᶜ ρ) ∙ ≈-refl

-- Weakening of modality contexts distribute over multiplication
-- wkConₘ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ ρ γ

wk-·ᶜ : (ρ : Wk m n) → wkConₘ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ ρ γ
wk-·ᶜ id = ≈ᶜ-refl
wk-·ᶜ (step ρ) = (wk-·ᶜ ρ) ∙ (≈-sym (·-zeroʳ _))
wk-·ᶜ {γ = γ ∙ p} (lift ρ) = (wk-·ᶜ ρ) ∙ ≈-refl

-- Weakening of modality contexts distribute over meet
-- wkConₘ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ ρ γ ∧ᶜ wkConₘ ρ δ

wk-∧ᶜ : (ρ : Wk m n) → wkConₘ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ ρ γ ∧ᶜ wkConₘ ρ δ
wk-∧ᶜ id = ≈ᶜ-refl
wk-∧ᶜ (step ρ) = (wk-∧ᶜ ρ) ∙ (≈-sym (∧-idem 𝟘))
wk-∧ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = (wk-∧ᶜ ρ) ∙ ≈-refl

-- Weakening of modality contexts distribute over the reccurence operator
-- wkConₘ ρ (γ ⊛ᵣ δ) ≈ᶜ (wkConₘ ρ γ) ⊛ᵣ (wkConₘ ρ δ)

wk-⊛ᶜ : (ρ : Wk m n) → wkConₘ ρ (γ ⊛ᶜ δ ▷ r) ≈ᶜ (wkConₘ ρ γ) ⊛ᶜ (wkConₘ ρ δ) ▷ r
wk-⊛ᶜ id = ≈ᶜ-refl
wk-⊛ᶜ (step ρ) = wk-⊛ᶜ ρ ∙ ≈-sym (⊛-idem-𝟘 _)
wk-⊛ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = wk-⊛ᶜ ρ ∙ ≈-refl

-- Weakening of modality contexts is monotone
-- If γ ≤ᶜ δ then wkConₘ ρ γ ≤ᶜ wkConₘ ρ δ

wk-≤ᶜ : (ρ : Wk m n) → γ ≤ᶜ δ → wkConₘ ρ γ ≤ᶜ wkConₘ ρ δ
wk-≤ᶜ id γ≤δ = γ≤δ
wk-≤ᶜ (step ρ) γ≤δ = (wk-≤ᶜ ρ γ≤δ) ∙ ≤-refl
wk-≤ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) (γ≤δ ∙ p≤q) = wk-≤ᶜ ρ γ≤δ ∙ p≤q

-- Lemma for usage of weakened variables

wkUsageVar : (ρ : Wk m n) → (x : Fin n)
           → wkConₘ ρ (𝟘ᶜ , x ≔ p) ≡ 𝟘ᶜ , wkVar ρ x ≔ p
wkUsageVar id x = PE.refl
wkUsageVar (step ρ) x = cong (λ γ → γ ∙ 𝟘) (wkUsageVar ρ x)
wkUsageVar (lift ρ) x0 = cong (λ γ → γ ∙ _) (wk-𝟘ᶜ ρ)
wkUsageVar (lift ρ) (x +1) = cong (λ γ → γ ∙ 𝟘) (wkUsageVar ρ x)

-- Usage of weakened terms: if γ ▸[ m ] t then
-- wkConₘ ρ γ ▸[ m ] wk ρ t.

wkUsage :
  {γ : Conₘ n} → (ρ : Wk m n) → γ ▸[ m′ ] t → wkConₘ ρ γ ▸[ m′ ] wk ρ t
wkUsage ρ Uₘ = PE.subst (λ γ → γ ▸[ _ ] U) (PE.sym (wk-𝟘ᶜ ρ)) Uₘ
wkUsage ρ ℕₘ = PE.subst (λ γ → γ ▸[ _ ] ℕ) (PE.sym (wk-𝟘ᶜ ρ)) ℕₘ
wkUsage ρ Emptyₘ =
  PE.subst (λ γ → γ ▸[ _ ] Empty) (PE.sym (wk-𝟘ᶜ ρ)) Emptyₘ
wkUsage ρ Unitₘ =
  PE.subst (λ γ → γ ▸[ _ ] Unit) (PE.sym (wk-𝟘ᶜ ρ)) Unitₘ
wkUsage ρ (ΠΣₘ γ▸F δ▸G ok) =
  sub (ΠΣₘ (wkUsage ρ γ▸F) (wkUsage (lift ρ) δ▸G) ok)
      (≤ᶜ-reflexive (wk-+ᶜ ρ))
wkUsage ρ var =
  PE.subst (λ γ → γ ▸[ _ ] wk ρ (var _)) (PE.sym (wkUsageVar ρ _)) var
wkUsage ρ (lamₘ γ▸t) = lamₘ (wkUsage (lift ρ) γ▸t)
wkUsage ρ (γ▸t ∘ₘ δ▸u) =
  sub ((wkUsage ρ γ▸t) ∘ₘ (wkUsage ρ δ▸u))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congˡ (wk-·ᶜ ρ))))
wkUsage ρ (prodᵣₘ γ▸t δ▸u refl) =
  sub (prodᵣₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸u) PE.refl)
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ))))
wkUsage ρ (prodₚₘ γ▸t γ▸u) = sub
  (prodₚₘ (wkUsage ρ γ▸t) (wkUsage ρ γ▸u))
  (≤ᶜ-reflexive (≈ᶜ-trans (wk-∧ᶜ ρ) (∧ᶜ-congʳ (wk-·ᶜ ρ))))
wkUsage ρ (fstₘ m γ▸t PE.refl ok) = fstₘ m (wkUsage ρ γ▸t) PE.refl ok
wkUsage ρ (sndₘ γ▸t) = sndₘ (wkUsage ρ γ▸t)
wkUsage ρ (prodrecₘ γ▸t δ▸u P) =
  sub (prodrecₘ (wkUsage ρ γ▸t) (wkUsage (liftn ρ 2) δ▸u ) P)
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ))))
wkUsage ρ zeroₘ =
  PE.subst (λ γ → γ ▸[ _ ] zero) (PE.sym (wk-𝟘ᶜ ρ)) zeroₘ
wkUsage ρ (sucₘ γ▸t) = sucₘ (wkUsage ρ γ▸t)
wkUsage ρ (natrecₘ γ▸z δ▸s η▸n) =
  sub (natrecₘ (wkUsage ρ γ▸z) (wkUsage (liftn ρ 2) δ▸s) (wkUsage ρ η▸n))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-⊛ᶜ ρ)
                              (⊛ᵣᶜ-cong (wk-∧ᶜ ρ)
                                       (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congˡ (wk-·ᶜ ρ))))))
wkUsage ρ (Emptyrecₘ γ▸t) =
  sub (Emptyrecₘ (wkUsage ρ γ▸t)) (≤ᶜ-reflexive (wk-·ᶜ ρ))
wkUsage ρ starₘ = subst (λ γ → γ ▸[ _ ] star) (PE.sym (wk-𝟘ᶜ ρ)) starₘ
wkUsage ρ (sub γ▸t x) = sub (wkUsage ρ γ▸t) (wk-≤ᶜ ρ x)
