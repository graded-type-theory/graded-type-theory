{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage.Weakening {a ℓ′}
  {M′ : Setoid a ℓ′} (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
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

wkConₘ : Wk m n → Conₘ n → Conₘ m
wkConₘ id γ = γ
wkConₘ (step ρ) γ = (wkConₘ ρ γ) ∙ 𝟘
wkConₘ (lift ρ) (γ ∙ p) = wkConₘ ρ γ ∙ p

wk-𝟘ᶜ : (ρ : Wk m n) → wkConₘ ρ 𝟘ᶜ ≡ 𝟘ᶜ
wk-𝟘ᶜ id = PE.refl
wk-𝟘ᶜ (step ρ) = cong (λ γ → γ ∙ 𝟘) (wk-𝟘ᶜ ρ)
wk-𝟘ᶜ (lift ρ) = cong (λ γ → γ ∙ 𝟘) (wk-𝟘ᶜ ρ)

wk-+ᶜ : (ρ : Wk m n) → wkConₘ ρ (γ +ᶜ δ) ≈ᶜ wkConₘ ρ γ +ᶜ wkConₘ ρ δ
wk-+ᶜ id = ≈ᶜ-refl
wk-+ᶜ (step ρ) = (wk-+ᶜ ρ) ∙ (≈-sym (proj₁ +-identity 𝟘))
wk-+ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = (wk-+ᶜ ρ) ∙ ≈-refl

wk-·ᶜ : (ρ : Wk m n) → wkConₘ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ ρ γ
wk-·ᶜ id = ≈ᶜ-refl
wk-·ᶜ (step ρ) = (wk-·ᶜ ρ) ∙ (≈-sym (proj₂ ·-zero _))
wk-·ᶜ {γ = γ ∙ p} (lift ρ) = (wk-·ᶜ ρ) ∙ ≈-refl

wk-∧ᶜ : (ρ : Wk m n)
      → wkConₘ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ ρ γ ∧ᶜ wkConₘ ρ δ
wk-∧ᶜ id = ≈ᶜ-refl
wk-∧ᶜ (step ρ) = (wk-∧ᶜ ρ) ∙ (≈-sym (∧-idem 𝟘))
wk-∧ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = (wk-∧ᶜ ρ) ∙ ≈-refl

wk-nrᶜ : (ρ : Wk m n)
       → wkConₘ ρ (nrᶜ γ δ r) ≈ᶜ nrᶜ (wkConₘ ρ γ) (wkConₘ ρ δ) r
wk-nrᶜ id = ≈ᶜ-refl
wk-nrᶜ (step ρ) = (wk-nrᶜ ρ) ∙ (≈-sym (nr-idem-𝟘 _))
wk-nrᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = (wk-nrᶜ ρ) ∙ ≈-refl

wk-≤ᶜ : (ρ : Wk m n) → γ ≤ᶜ δ → wkConₘ ρ γ ≤ᶜ wkConₘ ρ δ
wk-≤ᶜ id γ≤δ = γ≤δ
wk-≤ᶜ (step ρ) γ≤δ = (wk-≤ᶜ ρ γ≤δ) ∙ ≤-refl
wk-≤ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) (γ≤δ ∙ p≤q) = (wk-≤ᶜ ρ γ≤δ) ∙ p≤q

wkUsageVar : (ρ : Wk m n) → (x : Fin n)
           → wkConₘ ρ (𝟘ᶜ , x ≔ 𝟙) ≡ 𝟘ᶜ , wkVar ρ x ≔ 𝟙
wkUsageVar id x = PE.refl
wkUsageVar (step ρ) x = cong (λ γ → γ ∙ 𝟘) (wkUsageVar ρ x)
wkUsageVar (lift ρ) x0 = cong (λ γ → γ ∙ 𝟙) (wk-𝟘ᶜ ρ)
wkUsageVar (lift ρ) (x +1) = cong (λ γ → γ ∙ 𝟘) (wkUsageVar ρ x)

wkUsage : {γ : Conₘ n} → (ρ : Wk m n) → γ ▸ t → wkConₘ ρ γ ▸ wk ρ t
wkUsage ρ Uₘ = PE.subst (λ γ → γ ▸ U) (PE.sym (wk-𝟘ᶜ ρ)) Uₘ
wkUsage ρ ℕₘ = PE.subst (λ γ → γ ▸ ℕ) (PE.sym (wk-𝟘ᶜ ρ)) ℕₘ
wkUsage ρ Emptyₘ = PE.subst (λ γ → γ ▸ Empty) (PE.sym (wk-𝟘ᶜ ρ)) Emptyₘ
wkUsage ρ Unitₘ = PE.subst (λ γ → γ ▸ Unit) (PE.sym (wk-𝟘ᶜ ρ)) Unitₘ
wkUsage ρ (Πₘ γ▸F δ▸G) =
  sub (Πₘ (wkUsage ρ γ▸F) (wkUsage (lift ρ) δ▸G))
      (≤ᶜ-reflexive (wk-+ᶜ ρ))
wkUsage ρ (Σₘ γ▸F δ▸G) =
  sub (Σₘ (wkUsage ρ γ▸F) (wkUsage (lift ρ) δ▸G))
      (≤ᶜ-reflexive (wk-+ᶜ ρ))
wkUsage ρ var =
  PE.subst (λ γ → γ ▸ wk ρ (var _)) (PE.sym (wkUsageVar ρ _)) var
wkUsage ρ (lamₘ γ▸t) = lamₘ (wkUsage (lift ρ) γ▸t)
wkUsage ρ (γ▸t ∘ₘ δ▸u) =
  sub ((wkUsage ρ γ▸t) ∘ₘ (wkUsage ρ δ▸u))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-cong ≈ᶜ-refl (wk-·ᶜ ρ))))
wkUsage ρ (prodₘ γ▸t δ▸u refl) =
  sub (prodₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸u) PE.refl)
      (≤ᶜ-reflexive (wk-+ᶜ ρ))
wkUsage ρ (fstₘ 𝟘▸t) =
  subst (λ γ → γ ▸ fst _) (PE.sym (wk-𝟘ᶜ ρ))
        (fstₘ (subst (λ γ → γ ▸ _) (wk-𝟘ᶜ ρ) (wkUsage ρ 𝟘▸t)))
wkUsage ρ (sndₘ 𝟘▸t) =
  subst (λ γ → γ ▸ snd _) (PE.sym (wk-𝟘ᶜ ρ))
        (sndₘ (subst (λ γ → γ ▸ _) (wk-𝟘ᶜ ρ) (wkUsage ρ 𝟘▸t)))
wkUsage ρ (prodrecₘ γ▸t δ▸u) =
  sub (prodrecₘ (wkUsage ρ γ▸t) (wkUsage (liftn ρ 2) δ▸u))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-cong (wk-·ᶜ ρ) ≈ᶜ-refl)))
wkUsage ρ zeroₘ = PE.subst (λ γ → γ ▸ zero) (PE.sym (wk-𝟘ᶜ ρ)) zeroₘ
wkUsage ρ (sucₘ γ▸t) = sucₘ (wkUsage ρ γ▸t)
wkUsage ρ (natrecₘ γ▸z δ▸s η▸n) =
  sub (natrecₘ (wkUsage ρ γ▸z) (wkUsage (liftn ρ 2) δ▸s) (wkUsage ρ  η▸n))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-nrᶜ ρ)
                              (nrᶜ-cong (wk-∧ᶜ ρ)
                                        (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-cong ≈ᶜ-refl (wk-·ᶜ ρ)))
                                        ≈-refl)))
wkUsage ρ (Emptyrecₘ γ▸t) =
  sub (Emptyrecₘ (wkUsage ρ γ▸t)) (≤ᶜ-reflexive (wk-·ᶜ ρ))
wkUsage ρ starₘ = subst (λ γ → γ ▸ star) (PE.sym (wk-𝟘ᶜ ρ)) starₘ
wkUsage ρ (sub γ▸t x) = sub (wkUsage ρ γ▸t) (wk-≤ᶜ ρ x)

-- Usage of lifted wk1 terms
-- If γ ▸ t, then insertAt ℓ γ 𝟘 ▸ wk (liftn (step id) ℓ) t

liftn-usage : (ℓ : Nat) {γ : Conₘ (ℓ +ⁿ n)} {t : Term (ℓ +ⁿ n)}
            → γ ▸ t → insertAt ℓ γ 𝟘 ▸ wk (liftn (step id) ℓ) t
liftn-usage ℓ γ▸t =
  subst (λ γ → γ ▸ _) (lem ℓ) (wkUsage (liftn (step id) ℓ) γ▸t)
  where
  lem : ∀ {m} (ℓ : Nat) {γ : Conₘ (ℓ +ⁿ m)}
      → wkConₘ (liftn (step id) ℓ) γ ≡ insertAt ℓ γ 𝟘
  lem 0 = PE.refl
  lem (1+ ℓ) {γ ∙ p} = cong (_∙ p) (lem ℓ)

-- Usage of single lift
-- If γ ▸ t, then insertAt 1 γ 𝟘 ▸ wk (lift (step id)) t

lift-usage : {γ : Conₘ (1+ n)} {t : Term (1+ n)}
           → γ ▸ t → insertAt 1 γ 𝟘 ▸ wk (lift (step id)) t
lift-usage = liftn-usage 1


-- Usage of wk1
-- If γ ▸ t, then γ ∙ 𝟘 ▸ wk1 t

wk1-usage : {γ : Conₘ n} {t : Term n} → γ ▸ t →  γ ∙ 𝟘 ▸ wk1 t
wk1-usage = liftn-usage 0
