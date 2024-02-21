------------------------------------------------------------------------
-- The usage relation is closed under weakening.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality using (Modality)
open import Graded.Usage.Restrictions

module Graded.Usage.Weakening
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Graded.Modality M hiding (Modality)
open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Mode 𝕄
open import Definition.Untyped M
open import Definition.Untyped.Inversion M

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat) renaming (_+_ to _+ⁿ_)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum

private
  variable
    ℓ n m : Nat
    x : Fin n
    ρ : Wk m n
    p r : M
    γ γ′ δ η θ χ : Conₘ n
    t t′ : Term n
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
wk-+ᶜ (step ρ) = wk-+ᶜ ρ ∙ PE.sym (+-identityˡ 𝟘)
wk-+ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = wk-+ᶜ ρ ∙ refl

-- Weakening of modality contexts distribute over multiplication
-- wkConₘ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ ρ γ

wk-·ᶜ : (ρ : Wk m n) → wkConₘ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ ρ γ
wk-·ᶜ id = ≈ᶜ-refl
wk-·ᶜ (step ρ) = wk-·ᶜ ρ ∙ PE.sym (·-zeroʳ _)
wk-·ᶜ {γ = γ ∙ p} (lift ρ) = wk-·ᶜ ρ ∙ refl

-- Weakening of modality contexts distribute over meet
-- wkConₘ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ ρ γ ∧ᶜ wkConₘ ρ δ

wk-∧ᶜ : (ρ : Wk m n) → wkConₘ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ ρ γ ∧ᶜ wkConₘ ρ δ
wk-∧ᶜ id = ≈ᶜ-refl
wk-∧ᶜ (step ρ) = wk-∧ᶜ ρ ∙ PE.sym (∧-idem 𝟘)
wk-∧ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = wk-∧ᶜ ρ ∙ refl

-- Weakening of modality contexts distribute over the reccurence operator
-- wkConₘ ρ (γ ⊛ᵣ δ) ≈ᶜ (wkConₘ ρ γ) ⊛ᵣ (wkConₘ ρ δ)

wk-⊛ᶜ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  (ρ : Wk m n) → wkConₘ ρ (γ ⊛ᶜ δ ▷ r) ≈ᶜ (wkConₘ ρ γ) ⊛ᶜ (wkConₘ ρ δ) ▷ r
wk-⊛ᶜ id = ≈ᶜ-refl
wk-⊛ᶜ (step ρ) = wk-⊛ᶜ ρ ∙ PE.sym (⊛-idem-𝟘 _)
wk-⊛ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) = wk-⊛ᶜ ρ ∙ refl

-- The function wkConₘ ρ commutes with nrᶜ p r.

wk-nrᶜ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (ρ : Wk m n) →
  wkConₘ ρ (nrᶜ p r γ δ η) ≈ᶜ
  nrᶜ p r (wkConₘ ρ γ) (wkConₘ ρ δ) (wkConₘ ρ η)
wk-nrᶜ id =
  ≈ᶜ-refl
wk-nrᶜ (step ρ) =
  wk-nrᶜ ρ ∙ PE.sym nr-𝟘
wk-nrᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) =
  wk-nrᶜ ρ ∙ refl

-- Congruence of modality context weakening

wk-≈ᶜ : (ρ : Wk m n) → γ ≈ᶜ δ → wkConₘ ρ γ ≈ᶜ wkConₘ ρ δ
wk-≈ᶜ id γ≈δ = γ≈δ
wk-≈ᶜ (step ρ) γ≈δ = wk-≈ᶜ ρ γ≈δ ∙ refl
wk-≈ᶜ (lift ρ) (γ≈δ ∙ p≈q) = wk-≈ᶜ ρ γ≈δ ∙ p≈q

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
  PE.subst (λ γ → γ ▸[ _ ] Unit!) (PE.sym (wk-𝟘ᶜ ρ)) Unitₘ
wkUsage ρ (ΠΣₘ γ▸F δ▸G) =
  sub (ΠΣₘ (wkUsage ρ γ▸F) (wkUsage (lift ρ) δ▸G))
      (≤ᶜ-reflexive (wk-+ᶜ ρ))
wkUsage ρ var =
  PE.subst (λ γ → γ ▸[ _ ] wk ρ (var _)) (PE.sym (wkUsageVar ρ _)) var
wkUsage ρ (lamₘ γ▸t) = lamₘ (wkUsage (lift ρ) γ▸t)
wkUsage ρ (γ▸t ∘ₘ δ▸u) =
  sub ((wkUsage ρ γ▸t) ∘ₘ (wkUsage ρ δ▸u))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congˡ (wk-·ᶜ ρ))))
wkUsage ρ (prodʷₘ γ▸t δ▸u) =
  sub (prodʷₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸u))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ))))
wkUsage ρ (prodˢₘ γ▸t γ▸u) = sub
  (prodˢₘ (wkUsage ρ γ▸t) (wkUsage ρ γ▸u))
  (≤ᶜ-reflexive (≈ᶜ-trans (wk-∧ᶜ ρ) (∧ᶜ-congʳ (wk-·ᶜ ρ))))
wkUsage ρ (fstₘ m γ▸t PE.refl ok) = fstₘ m (wkUsage ρ γ▸t) PE.refl ok
wkUsage ρ (sndₘ γ▸t) = sndₘ (wkUsage ρ γ▸t)
wkUsage ρ (prodrecₘ γ▸t δ▸u η▸A ok) =
  sub (prodrecₘ (wkUsage ρ γ▸t) (wkUsage (liftn ρ 2) δ▸u)
         (wkUsage (lift ρ) η▸A) ok)
    (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ))))
wkUsage ρ zeroₘ =
  PE.subst (λ γ → γ ▸[ _ ] zero) (PE.sym (wk-𝟘ᶜ ρ)) zeroₘ
wkUsage ρ (sucₘ γ▸t) = sucₘ (wkUsage ρ γ▸t)
wkUsage ρ (natrecₘ γ▸z δ▸s η▸n θ▸A) =
  sub (natrecₘ (wkUsage ρ γ▸z) (wkUsage (liftn ρ 2) δ▸s) (wkUsage ρ η▸n) (wkUsage (lift ρ) θ▸A))
    (≤ᶜ-reflexive (wk-nrᶜ ρ))
  where
  open import Graded.Modality.Dedicated-nr.Instance
wkUsage
  ρ
  (natrec-no-nrₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
     ▸z ▸s ▸n ▸A χ≤γ χ≤δ χ≤η fix) =
  natrec-no-nrₘ
    (wkUsage ρ ▸z)
    (wkUsage (liftn ρ 2) ▸s)
    (wkUsage ρ ▸n)
    (wkUsage (lift ρ) ▸A)
    (wk-≤ᶜ ρ χ≤γ)
    (wk-≤ᶜ ρ ∘→ χ≤δ)
    (wk-≤ᶜ ρ χ≤η)
    (begin
       wkConₘ ρ χ                                        ≤⟨ wk-≤ᶜ _ fix ⟩

       wkConₘ ρ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)                  ≈⟨ ≈ᶜ-trans (wk-+ᶜ ρ) $
                                                            +ᶜ-congˡ $
                                                            ≈ᶜ-trans (wk-+ᶜ ρ) $
                                                            +ᶜ-cong (wk-·ᶜ ρ) (wk-·ᶜ ρ) ⟩
       wkConₘ ρ δ +ᶜ p ·ᶜ wkConₘ ρ η +ᶜ r ·ᶜ wkConₘ ρ χ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage ρ (emptyrecₘ γ▸t δ▸A) =
  sub (emptyrecₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸A)) (≤ᶜ-reflexive (wk-·ᶜ ρ))
wkUsage ρ starʷₘ = subst (λ γ → γ ▸[ _ ] starʷ) (PE.sym (wk-𝟘ᶜ ρ)) starʷₘ
wkUsage ρ (starˢₘ prop) =
  sub (starˢₘ (λ ns → subst (λ γ → γ ≈ᶜ wkConₘ ρ _) (wk-𝟘ᶜ ρ) (wk-≈ᶜ ρ (prop ns))))
      (≤ᶜ-reflexive (wk-·ᶜ ρ))
wkUsage ρ (unitrecₘ γ▸t δ▸u η▸A ok) =
  sub (unitrecₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸u) (wkUsage (lift ρ) η▸A) ok)
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ))))
wkUsage ρ (Idₘ {δ = δ} {η = η} ok ▸A ▸t ▸u) = sub
  (Idₘ ok (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸u))
  (begin
     wkConₘ ρ (δ +ᶜ η)         ≈⟨ wk-+ᶜ ρ ⟩
     wkConₘ ρ δ +ᶜ wkConₘ ρ η  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage ρ (Id₀ₘ ok ▸A ▸t ▸u) =
  subst (_▸[ _ ] _)
    (𝟘ᶜ           ≡˘⟨ wk-𝟘ᶜ ρ ⟩
     wkConₘ ρ 𝟘ᶜ  ∎)
    (Id₀ₘ ok (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸u))
  where
  open Tools.Reasoning.PropositionalEquality
wkUsage ρ rflₘ =
  subst (_▸[ _ ] _)
    (𝟘ᶜ           ≡˘⟨ wk-𝟘ᶜ ρ ⟩
     wkConₘ ρ 𝟘ᶜ  ∎)
    rflₘ
  where
  open Tools.Reasoning.PropositionalEquality
wkUsage ρ
  (Jₘ {γ₂ = γ₂} {γ₃ = γ₃} {γ₄ = γ₄} {γ₅ = γ₅} {γ₆ = γ₆}
     ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ ▸v) = sub
  (Jₘ ok₁ ok₂ (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B)
     (wkUsage _ ▸u) (wkUsage _ ▸t′) (wkUsage _ ▸v))
  (begin
     wkConₘ ρ (ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆))                  ≈⟨ ≈ᶜ-trans (wk-·ᶜ ρ) $ ·ᶜ-congˡ $
                                                                      ≈ᶜ-trans (wk-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                      ≈ᶜ-trans (wk-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                      ≈ᶜ-trans (wk-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                      wk-∧ᶜ ρ ⟩
     ω ·ᶜ
     (wkConₘ ρ γ₂ ∧ᶜ wkConₘ ρ γ₃ ∧ᶜ wkConₘ ρ γ₄ ∧ᶜ wkConₘ ρ γ₅ ∧ᶜ
      wkConₘ ρ γ₆)                                                 ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage ρ (J₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ ▸v) = sub
  (J₀ₘ₁ ok p≡𝟘 q≡𝟘 (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B)
     (wkUsage _ ▸u) (wkUsage _ ▸t′) (wkUsage _ ▸v))
  (begin
     wkConₘ ρ (ω ·ᶜ (γ₃ ∧ᶜ γ₄))         ≈⟨ ≈ᶜ-trans (wk-·ᶜ ρ) $ ·ᶜ-congˡ $ wk-∧ᶜ ρ ⟩
     ω ·ᶜ (wkConₘ ρ γ₃ ∧ᶜ wkConₘ ρ γ₄)  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage _ (J₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸t′ ▸v) =
  J₀ₘ₂ ok (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B) (wkUsage _ ▸u)
    (wkUsage _ ▸t′) (wkUsage _ ▸v)
wkUsage ρ
  (Kₘ {γ₂ = γ₂} {γ₃ = γ₃} {γ₄ = γ₄} {γ₅ = γ₅}
     ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v) = sub
  (Kₘ ok₁ ok₂ (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B)
     (wkUsage _ ▸u) (wkUsage _ ▸v))
  (begin
     wkConₘ ρ (ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅))                           ≈⟨ ≈ᶜ-trans (wk-·ᶜ ρ) $ ·ᶜ-congˡ $
                                                                         ≈ᶜ-trans (wk-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                         ≈ᶜ-trans (wk-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                         wk-∧ᶜ ρ ⟩
     ω ·ᶜ (wkConₘ ρ γ₂ ∧ᶜ wkConₘ ρ γ₃ ∧ᶜ wkConₘ ρ γ₄ ∧ᶜ wkConₘ ρ γ₅)  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage ρ (K₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v) = sub
  (K₀ₘ₁ ok p≡𝟘 (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B)
     (wkUsage _ ▸u) (wkUsage _ ▸v))
  (begin
     wkConₘ ρ (ω ·ᶜ (γ₃ ∧ᶜ γ₄))         ≈⟨ ≈ᶜ-trans (wk-·ᶜ ρ) $ ·ᶜ-congˡ $ wk-∧ᶜ ρ ⟩
     ω ·ᶜ (wkConₘ ρ γ₃ ∧ᶜ wkConₘ ρ γ₄)  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage _ (K₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v) =
  K₀ₘ₂ ok (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B) (wkUsage _ ▸u)
    (wkUsage _ ▸v)
wkUsage ρ ([]-congₘ ▸A ▸t ▸u ▸v) =
  subst (_▸[ _ ] _)
    (𝟘ᶜ           ≡˘⟨ wk-𝟘ᶜ ρ ⟩
     wkConₘ ρ 𝟘ᶜ  ∎)
    ([]-congₘ (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸u)
       (wkUsage _ ▸v))
  where
  open Tools.Reasoning.PropositionalEquality
wkUsage ρ (sub γ▸t x) = sub (wkUsage ρ γ▸t) (wk-≤ᶜ ρ x)

------------------------------------------------------------------------
-- The function wkConₘ⁻¹

-- A left inverse of wkConₘ ρ.

wkConₘ⁻¹ : Wk m n → Conₘ m → Conₘ n
wkConₘ⁻¹ id       γ       = γ
wkConₘ⁻¹ (step ρ) (γ ∙ _) = wkConₘ⁻¹ ρ γ
wkConₘ⁻¹ (lift ρ) (γ ∙ p) = wkConₘ⁻¹ ρ γ ∙ p

-- The function wkConₘ⁻¹ ρ is a left inverse of wkConₘ ρ.

wkConₘ⁻¹-wkConₘ : (ρ : Wk m n) → wkConₘ⁻¹ ρ (wkConₘ ρ γ) ≡ γ
wkConₘ⁻¹-wkConₘ             id       = refl
wkConₘ⁻¹-wkConₘ             (step ρ) = wkConₘ⁻¹-wkConₘ ρ
wkConₘ⁻¹-wkConₘ {γ = _ ∙ _} (lift ρ) = cong (_∙ _) (wkConₘ⁻¹-wkConₘ ρ)

-- Congruence of the function wkConₘ⁻¹ ρ.

wkConₘ⁻¹-≈ᶜ : (ρ : Wk m n) → γ ≈ᶜ δ → wkConₘ⁻¹ ρ γ ≈ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-≈ᶜ id γ≈δ = γ≈δ
wkConₘ⁻¹-≈ᶜ (step ρ) (γ≈δ ∙ _) = wkConₘ⁻¹-≈ᶜ ρ γ≈δ
wkConₘ⁻¹-≈ᶜ (lift ρ) (γ≈δ ∙ p≈q) = wkConₘ⁻¹-≈ᶜ ρ γ≈δ ∙ p≈q

-- The function wkConₘ⁻¹ ρ is monotone.

wkConₘ⁻¹-monotone : (ρ : Wk m n) → γ ≤ᶜ δ → wkConₘ⁻¹ ρ γ ≤ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-monotone id leq =
  leq
wkConₘ⁻¹-monotone {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) (leq ∙ _) =
  wkConₘ⁻¹-monotone ρ leq
wkConₘ⁻¹-monotone {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
  wkConₘ⁻¹-monotone ρ leq₁ ∙ leq₂

-- The function wkConₘ⁻¹ ρ maps 𝟘ᶜ to 𝟘ᶜ.

wkConₘ⁻¹-𝟘ᶜ : (ρ : Wk m n) → wkConₘ⁻¹ ρ 𝟘ᶜ ≈ᶜ 𝟘ᶜ
wkConₘ⁻¹-𝟘ᶜ id       = ≈ᶜ-refl
wkConₘ⁻¹-𝟘ᶜ (step ρ) = wkConₘ⁻¹-𝟘ᶜ ρ
wkConₘ⁻¹-𝟘ᶜ (lift ρ) = wkConₘ⁻¹-𝟘ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with _+ᶜ_.

wkConₘ⁻¹-+ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ +ᶜ δ) ≈ᶜ wkConₘ⁻¹ ρ γ +ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-+ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-+ᶜ ρ
wkConₘ⁻¹-+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-+ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with _∧ᶜ_.

wkConₘ⁻¹-∧ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ⁻¹ ρ γ ∧ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-∧ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-∧ᶜ ρ
wkConₘ⁻¹-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-∧ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with p ·ᶜ_.

wkConₘ⁻¹-·ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ⁻¹ ρ γ
wkConₘ⁻¹-·ᶜ             id       = ≈ᶜ-refl
wkConₘ⁻¹-·ᶜ {γ = _ ∙ _} (step ρ) = wkConₘ⁻¹-·ᶜ ρ
wkConₘ⁻¹-·ᶜ {γ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-·ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with _⊛ᶜ_▷ r.

wkConₘ⁻¹-⊛ᶜ :
  ⦃ has-star : Has-star semiring-with-meet ⦄
  (ρ : Wk m n) →
  wkConₘ⁻¹ ρ (γ ⊛ᶜ δ ▷ r) ≈ᶜ wkConₘ⁻¹ ρ γ ⊛ᶜ wkConₘ⁻¹ ρ δ ▷ r
wkConₘ⁻¹-⊛ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-⊛ᶜ ρ
wkConₘ⁻¹-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-⊛ᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ commutes with nrᶜ p r.

wkConₘ⁻¹-nrᶜ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄
  (ρ : Wk m n) →
  wkConₘ⁻¹ ρ (nrᶜ p r γ δ η) ≈ᶜ
  nrᶜ p r (wkConₘ⁻¹ ρ γ) (wkConₘ⁻¹ ρ δ) (wkConₘ⁻¹ ρ η)
wkConₘ⁻¹-nrᶜ id =
  ≈ᶜ-refl
wkConₘ⁻¹-nrᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (step ρ) =
  wkConₘ⁻¹-nrᶜ ρ
wkConₘ⁻¹-nrᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) =
  wkConₘ⁻¹-nrᶜ ρ ∙ refl

-- The function wkConₘ⁻¹ ρ "commutes" in a certain sense with _,_≔_.

wkConₘ⁻¹-,≔ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ , wkVar ρ x ≔ p) ≈ᶜ wkConₘ⁻¹ ρ γ , x ≔ p
wkConₘ⁻¹-,≔                        id       = ≈ᶜ-refl
wkConₘ⁻¹-,≔ {γ = _ ∙ _}            (step ρ) = wkConₘ⁻¹-,≔ ρ
wkConₘ⁻¹-,≔ {γ = _ ∙ _} {x = x0}   (lift ρ) = ≈ᶜ-refl
wkConₘ⁻¹-,≔ {γ = _ ∙ _} {x = _ +1} (lift ρ) = wkConₘ⁻¹-,≔ ρ ∙ refl

------------------------------------------------------------------------
-- Inversion lemmas

-- A kind of inversion lemma for the usage relation and weakening.

wkUsage⁻¹ : γ ▸[ m′ ] wk ρ t → wkConₘ⁻¹ ρ γ ▸[ m′ ] t
wkUsage⁻¹ ▸t = wkUsage⁻¹′ ▸t refl
  where
  open module R {n} =
    Tools.Reasoning.PartialOrder (≤ᶜ-poset {n = n})

  wkUsage⁻¹′ :
    γ ▸[ m′ ] t′ → wk ρ t ≡ t′ → wkConₘ⁻¹ ρ γ ▸[ m′ ] t
  wkUsage⁻¹′ {ρ = ρ} = λ where
      Uₘ eq →
        case wk-U eq of λ {
          refl →
        sub Uₘ (≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ)) }
      ℕₘ eq →
        case wk-ℕ eq of λ {
          refl →
        sub ℕₘ (≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ)) }
      Emptyₘ eq →
        case wk-Empty eq of λ {
          refl →
        sub Emptyₘ (≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ)) }
      Unitₘ eq →
        case wk-Unit eq of λ {
          refl →
        sub Unitₘ (≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ)) }
      (ΠΣₘ ▸A ▸B) eq →
        case wk-ΠΣ eq of λ {
          (_ , _ , refl , refl , refl) →
        case wkUsage⁻¹ ▸A of λ {
          ▸A →
        case wkUsage⁻¹ ▸B of λ {
          ▸B →
        sub (ΠΣₘ ▸A ▸B) (≤ᶜ-reflexive (wkConₘ⁻¹-+ᶜ ρ)) }}}
      (var {m = m}) eq →
        case wk-var eq of λ {
          (x , refl , refl) →
        sub var (begin
          wkConₘ⁻¹ ρ (𝟘ᶜ , wkVar ρ x ≔ ⌜ m ⌝)  ≈⟨ wkConₘ⁻¹-,≔ ρ ⟩
          wkConₘ⁻¹ ρ 𝟘ᶜ , x ≔ ⌜ m ⌝            ≈⟨ update-congˡ (wkConₘ⁻¹-𝟘ᶜ ρ) ⟩
          𝟘ᶜ , x ≔ ⌜ m ⌝                       ∎) }
      (lamₘ ▸t) eq →
        case wk-lam eq of λ {
          (_ , refl , refl) →
        lamₘ (wkUsage⁻¹ ▸t) }
      (_∘ₘ_ {γ = γ} {δ = δ} {p = p} ▸t ▸u) eq →
        case wk-∘ eq of λ {
          (_ , _ , refl , refl , refl) →
        sub (wkUsage⁻¹ ▸t ∘ₘ wkUsage⁻¹ ▸u) (begin
          wkConₘ⁻¹ ρ (γ +ᶜ p ·ᶜ δ)             ≈⟨ wkConₘ⁻¹-+ᶜ ρ ⟩
          wkConₘ⁻¹ ρ γ +ᶜ wkConₘ⁻¹ ρ (p ·ᶜ δ)  ≈⟨ +ᶜ-congˡ (wkConₘ⁻¹-·ᶜ ρ) ⟩
          wkConₘ⁻¹ ρ γ +ᶜ p ·ᶜ wkConₘ⁻¹ ρ δ    ∎) }
      (prodʷₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u) eq →
        case wk-prod eq of λ {
          (_ , _ , refl , refl , refl) →
        sub (prodʷₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)) (begin
          wkConₘ⁻¹ ρ (p ·ᶜ γ +ᶜ δ)             ≈⟨ wkConₘ⁻¹-+ᶜ ρ ⟩
          wkConₘ⁻¹ ρ (p ·ᶜ γ) +ᶜ wkConₘ⁻¹ ρ δ  ≈⟨ +ᶜ-congʳ (wkConₘ⁻¹-·ᶜ ρ) ⟩
          p ·ᶜ wkConₘ⁻¹ ρ γ +ᶜ wkConₘ⁻¹ ρ δ    ∎) }
      (prodˢₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u) eq →
        case wk-prod eq of λ {
          (_ , _ , refl , refl , refl) →
        sub (prodˢₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)) (begin
          wkConₘ⁻¹ ρ (p ·ᶜ γ ∧ᶜ δ)             ≈⟨ wkConₘ⁻¹-∧ᶜ ρ ⟩
          wkConₘ⁻¹ ρ (p ·ᶜ γ) ∧ᶜ wkConₘ⁻¹ ρ δ  ≈⟨ ∧ᶜ-congʳ (wkConₘ⁻¹-·ᶜ ρ) ⟩
          p ·ᶜ wkConₘ⁻¹ ρ γ ∧ᶜ wkConₘ⁻¹ ρ δ    ∎) }
      (fstₘ m ▸t refl ok) eq →
        case wk-fst eq of λ {
          (_ , refl , refl) →
        fstₘ m (wkUsage⁻¹ ▸t) refl ok }
      (sndₘ ▸t) eq →
        case wk-snd eq of λ {
          (_ , refl , refl) →
        sndₘ (wkUsage⁻¹ ▸t) }
      (prodrecₘ {γ = γ} {r = r} {δ = δ} ▸t ▸u ▸A ok) eq →
        case wk-prodrec eq of λ {
          (_ , _ , _ , refl , refl , refl , refl) →
        sub
          (prodrecₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)
             (wkUsage⁻¹ ▸A) ok)
          (begin
             wkConₘ⁻¹ ρ (r ·ᶜ γ +ᶜ δ)             ≈⟨ wkConₘ⁻¹-+ᶜ ρ ⟩
             wkConₘ⁻¹ ρ (r ·ᶜ γ) +ᶜ wkConₘ⁻¹ ρ δ  ≈⟨ +ᶜ-congʳ (wkConₘ⁻¹-·ᶜ ρ) ⟩
             r ·ᶜ wkConₘ⁻¹ ρ γ +ᶜ wkConₘ⁻¹ ρ δ    ∎) }
      zeroₘ eq →
        case wk-zero eq of λ {
          refl →
        sub zeroₘ (≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ)) }
      (sucₘ ▸t) eq →
        case wk-suc eq of λ {
          (_ , refl , refl) →
        sucₘ (wkUsage⁻¹ ▸t) }
      (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} ▸t ▸u ▸v ▸A) eq →
        case wk-natrec eq of λ {
          (_ , _ , _ , _ , refl , refl , refl , refl , refl) →
        sub
          (natrecₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)
             (wkUsage⁻¹ ▸v) (wkUsage⁻¹ ▸A))
          (≤ᶜ-reflexive (wkConₘ⁻¹-nrᶜ ρ)) }
      (natrec-no-nrₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
         ▸t ▸u ▸v ▸A χ≤γ χ≤δ χ≤η fix)
        eq →
        case wk-natrec eq of λ {
          (_ , _ , _ , _ , refl , refl , refl , refl , refl) →
        natrec-no-nrₘ
          (wkUsage⁻¹ ▸t)
          (wkUsage⁻¹ ▸u)
          (wkUsage⁻¹ ▸v)
          (wkUsage⁻¹ ▸A)
          (wkConₘ⁻¹-monotone ρ χ≤γ)
          (wkConₘ⁻¹-monotone ρ ∘→ χ≤δ)
          (wkConₘ⁻¹-monotone ρ χ≤η)
          (begin
             wkConₘ⁻¹ ρ χ                                            ≤⟨ wkConₘ⁻¹-monotone ρ fix ⟩

             wkConₘ⁻¹ ρ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)                      ≈⟨ ≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) $
                                                                        +ᶜ-congˡ $
                                                                        ≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) $
                                                                        +ᶜ-cong (wkConₘ⁻¹-·ᶜ ρ) (wkConₘ⁻¹-·ᶜ ρ) ⟩
             wkConₘ⁻¹ ρ δ +ᶜ p ·ᶜ wkConₘ⁻¹ ρ η +ᶜ r ·ᶜ wkConₘ⁻¹ ρ χ  ∎) }
      (emptyrecₘ ▸t ▸A) eq →
        case wk-emptyrec eq of λ {
          (_ , _ , refl , refl , refl) →
        sub (emptyrecₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸A))
          (≤ᶜ-reflexive (wkConₘ⁻¹-·ᶜ ρ)) }
      starʷₘ eq →
        case wk-star eq of λ {
          refl →
        sub starₘ (≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ)) }
      (starˢₘ prop) eq →
        case wk-star eq of λ {
          refl →
        sub (starˢₘ (λ ns → ≈ᶜ-trans (≈ᶜ-sym (wkConₘ⁻¹-𝟘ᶜ ρ))
                                    (wkConₘ⁻¹-≈ᶜ ρ (prop ns))))
            (≤ᶜ-reflexive (wkConₘ⁻¹-·ᶜ ρ))  }
      (unitrecₘ ▸t ▸u ▸A ok) eq →
        case wk-unitrec eq of λ {
          (_ , _ , _ , refl , refl , refl , refl) →
        sub (unitrecₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸A) ok)
            (≤ᶜ-reflexive (≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) (+ᶜ-congʳ (wkConₘ⁻¹-·ᶜ ρ)))) }
      (Idₘ ok ▸A ▸t ▸u) eq →
        case wk-Id eq of λ {
          (_ , _ , _ , refl , refl , refl , refl) →
        sub (Idₘ ok (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)) $
        ≤ᶜ-reflexive (wkConₘ⁻¹-+ᶜ ρ) }
      (Id₀ₘ ok ▸A ▸t ▸u) eq →
        case wk-Id eq of λ {
          (_ , _ , _ , refl , refl , refl , refl) →
        sub (Id₀ₘ ok (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)) $
        ≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ) }
      rflₘ eq →
        case wk-rfl eq of λ {
          refl →
        sub rflₘ (≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ)) }
      (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ ▸v)
        eq →
        case wk-J eq of λ {
          (_ , _ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl , refl) →
        sub
          (Jₘ ok₁ ok₂ (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
             (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸t′) (wkUsage⁻¹ ▸v)) $ begin
        wkConₘ⁻¹ ρ (ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆))         ≈⟨ wkConₘ⁻¹-·ᶜ ρ ⟩

        ω ·ᶜ wkConₘ⁻¹ ρ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅ ∧ᶜ γ₆)           ≈⟨ ·ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                  wkConₘ⁻¹-∧ᶜ ρ ⟩
        ω ·ᶜ
          (wkConₘ⁻¹ ρ γ₂ ∧ᶜ wkConₘ⁻¹ ρ γ₃ ∧ᶜ wkConₘ⁻¹ ρ γ₄ ∧ᶜ
           wkConₘ⁻¹ ρ γ₅ ∧ᶜ wkConₘ⁻¹ ρ γ₆)                     ∎ }
      (J₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ ▸v) eq →
        case wk-J eq of λ {
          (_ , _ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl , refl) →
        sub
          (J₀ₘ₁ ok p≡𝟘 q≡𝟘 (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
             (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸t′) (wkUsage⁻¹ ▸v)) $ begin
        wkConₘ⁻¹ ρ (ω ·ᶜ (γ₃ ∧ᶜ γ₄))           ≈⟨ wkConₘ⁻¹-·ᶜ ρ ⟩
        ω ·ᶜ wkConₘ⁻¹ ρ (γ₃ ∧ᶜ γ₄)             ≈⟨ ·ᶜ-congˡ $ wkConₘ⁻¹-∧ᶜ ρ ⟩
        ω ·ᶜ (wkConₘ⁻¹ ρ γ₃ ∧ᶜ wkConₘ⁻¹ ρ γ₄)  ∎ }
      (J₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸t′ ▸v) eq →
        case wk-J eq of λ {
          (_ , _ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl , refl) →
        J₀ₘ₂ ok (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
          (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸t′) (wkUsage⁻¹ ▸v) }
      (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v)
        eq →
        case wk-K eq of λ {
          (_ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl) →
        sub
          (Kₘ ok₁ ok₂ (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
             (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸v)) $ begin
        wkConₘ⁻¹ ρ (ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅))               ≈⟨ wkConₘ⁻¹-·ᶜ ρ ⟩

        ω ·ᶜ wkConₘ⁻¹ ρ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)                 ≈⟨ ·ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-∧ᶜ ρ) $ ∧ᶜ-congˡ $
                                                                  wkConₘ⁻¹-∧ᶜ ρ ⟩
        ω ·ᶜ
          (wkConₘ⁻¹ ρ γ₂ ∧ᶜ wkConₘ⁻¹ ρ γ₃ ∧ᶜ wkConₘ⁻¹ ρ γ₄ ∧ᶜ
           wkConₘ⁻¹ ρ γ₅)                                      ∎ }
      (K₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v) eq →
        case wk-K eq of λ {
          (_ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl) →
        sub
          (K₀ₘ₁ ok p≡𝟘 (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
             (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸v)) $ begin
        wkConₘ⁻¹ ρ (ω ·ᶜ (γ₃ ∧ᶜ γ₄))           ≈⟨ wkConₘ⁻¹-·ᶜ ρ ⟩
        ω ·ᶜ wkConₘ⁻¹ ρ (γ₃ ∧ᶜ γ₄)             ≈⟨ ·ᶜ-congˡ $ wkConₘ⁻¹-∧ᶜ ρ ⟩
        ω ·ᶜ (wkConₘ⁻¹ ρ γ₃ ∧ᶜ wkConₘ⁻¹ ρ γ₄)  ∎ }
      (K₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v) eq →
        case wk-K eq of λ {
          (_ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl) →
        K₀ₘ₂ ok (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
          (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸v) }
      ([]-congₘ ▸A ▸t ▸u ▸v) eq →
        case wk-[]-cong eq of λ {
          (_ , _ , _ , _ , refl , refl , refl , refl , refl) →
        sub
          ([]-congₘ (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)
             (wkUsage⁻¹ ▸v)) $
        ≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ) }
      (sub ▸t leq) refl →
        sub (wkUsage⁻¹ ▸t) (wkConₘ⁻¹-monotone ρ leq)
    where
    open import Graded.Modality.Dedicated-nr.Instance

-- An inversion lemma for the usage relation and weakening.

wkUsage⁻¹′ : wkConₘ ρ γ ▸[ m′ ] wk ρ t → γ ▸[ m′ ] t
wkUsage⁻¹′ {ρ = ρ} {γ = γ} {m′ = m′} {t = t} =
  wkConₘ ρ γ ▸[ m′ ] wk ρ t          →⟨ wkUsage⁻¹ ⟩
  wkConₘ⁻¹ ρ (wkConₘ ρ γ) ▸[ m′ ] t  →⟨ subst (_▸[ _ ] _) (wkConₘ⁻¹-wkConₘ ρ) ⟩
  γ ▸[ m′ ] t                        □

-- An inversion lemma for wkConₘ and 𝟘ᶜ.

wkConₘ-𝟘 : wkConₘ ρ γ ≤ᶜ 𝟘ᶜ → γ ≤ᶜ 𝟘ᶜ
wkConₘ-𝟘 {ρ = ρ} {γ = γ} =
  wkConₘ ρ γ ≤ᶜ 𝟘ᶜ                          →⟨ wkConₘ⁻¹-monotone ρ ⟩
  wkConₘ⁻¹ ρ (wkConₘ ρ γ) ≤ᶜ wkConₘ⁻¹ ρ 𝟘ᶜ  →⟨ subst₂ _≤ᶜ_ (wkConₘ⁻¹-wkConₘ ρ) (≈ᶜ→≡ (wkConₘ⁻¹-𝟘ᶜ ρ)) ⟩
  γ ≤ᶜ 𝟘ᶜ                                   □

-- An inversion lemma for wkConₘ, wkVar and _,_≔_.

wkConₘ-,-wkVar-≔ :
  (x : Fin n) →
  wkConₘ ρ γ ≤ᶜ δ , wkVar ρ x ≔ p →
  ∃₂ λ δ′ p′ → γ ≤ᶜ δ′ , x ≔ p′ × wkConₘ ρ δ′ ≤ᶜ δ × p′ ≤ p
wkConₘ-,-wkVar-≔ {ρ = id} _ leq =
  _ , _ , leq , ≤ᶜ-refl , ≤-refl
wkConₘ-,-wkVar-≔ {ρ = step _} {δ = _ ∙ _} _ (leq₁ ∙ leq₂) =
  case wkConₘ-,-wkVar-≔ _ leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ , _ , leq₁ , leq₃ ∙ leq₂ , leq₄ }
wkConₘ-,-wkVar-≔ {ρ = lift _} {γ = _ ∙ _} {δ = _ ∙ _} x0 (leq₁ ∙ leq₂) =
  _ ∙ _ , _ , ≤ᶜ-refl , leq₁ ∙ ≤-refl , leq₂
wkConₘ-,-wkVar-≔
  {ρ = lift ρ} {γ = _ ∙ _} {δ = _ ∙ _} (x +1) (leq₁ ∙ leq₂) =
  case wkConₘ-,-wkVar-≔ x leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ ∙ _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ }

-- The lemmas in the following anonymous module are defined under the
-- assumption that the zero is well-behaved.

module _
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄
  where

  -- An inversion lemma for wkConₘ and _+ᶜ_.

  wkConₘ-+ᶜ :
    ∀ ρ → wkConₘ ρ γ ≤ᶜ δ +ᶜ η →
    ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ +ᶜ η′ × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
  wkConₘ-+ᶜ id leq =
    _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-+ᶜ {δ = _ ∙ _} {η = _ ∙ _} (step _) (leq₁ ∙ leq₂) =
    case wkConₘ-+ᶜ _ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ,
    leq₃ ∙ ≤-reflexive (PE.sym (+-positiveˡ (𝟘≮ leq₂))) ,
    leq₄ ∙ ≤-reflexive (PE.sym (+-positiveʳ (𝟘≮ leq₂))) }
  wkConₘ-+ᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-+ᶜ ρ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

  -- An inversion lemma for wkConₘ and _∧ᶜ_.

  wkConₘ-∧ᶜ :
    ∀ ρ → wkConₘ ρ γ ≤ᶜ δ ∧ᶜ η →
    ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ ∧ᶜ η′ × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
  wkConₘ-∧ᶜ id leq =
    _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-∧ᶜ {δ = _ ∙ _} {η = _ ∙ _} (step _) (leq₁ ∙ leq₂) =
    case wkConₘ-∧ᶜ _ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ,
    leq₃ ∙ ≤-reflexive (PE.sym (∧-positiveˡ (𝟘≮ leq₂))) ,
    leq₄ ∙ ≤-reflexive (PE.sym (∧-positiveʳ (𝟘≮ leq₂))) }
  wkConₘ-∧ᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-∧ᶜ ρ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

  -- An inversion lemma for wkConₘ and _·ᶜ_.

  wkConₘ-·ᶜ :
    ∀ ρ → wkConₘ ρ γ ≤ᶜ p ·ᶜ δ →
    p ≡ 𝟘 × γ ≤ᶜ 𝟘ᶜ ⊎
    ∃ λ δ′ → γ ≤ᶜ p ·ᶜ δ′ × wkConₘ ρ δ′ ≤ᶜ δ
  wkConₘ-·ᶜ id leq =
    inj₂ (_ , leq , ≤ᶜ-refl)
  wkConₘ-·ᶜ {γ = γ} {δ = _ ∙ q} (step ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-·ᶜ ρ leq₁ of λ where
      (inj₁ (refl , leq₁))      → inj₁ (refl , leq₁)
      (inj₂ (δ′ , leq₁ , leq₃)) →
        case zero-product (𝟘≮ leq₂) of λ where
          (inj₂ refl) → inj₂ (_ , leq₁ , leq₃ ∙ ≤-refl)
          (inj₁ refl) → inj₁
            ( refl
            , (begin
                 γ        ≤⟨ leq₁ ⟩
                 𝟘 ·ᶜ δ′  ≈⟨ ·ᶜ-zeroˡ _ ⟩
                 𝟘ᶜ       ∎)
            )
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
  wkConₘ-·ᶜ {γ = γ ∙ q} {δ = _ ∙ r} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-·ᶜ ρ leq₁ of λ where
      (inj₂ (_ , leq₁ , leq₃)) →
        inj₂ (_ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl)
      (inj₁ (refl , leq₁)) → inj₁
        ( refl
        , (begin
             γ ∙ q       ≤⟨ leq₁ ∙ leq₂ ⟩
             𝟘ᶜ ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ          ∎)
        )
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

  -- An inversion lemma for wkConₘ and _⊛ᶜ_▷_.

  wkConₘ-⊛ᶜ :
    ⦃ has-star : Has-star semiring-with-meet ⦄ →
    ∀ ρ → wkConₘ ρ γ ≤ᶜ δ ⊛ᶜ η ▷ r →
    ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ ⊛ᶜ η′ ▷ r × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
  wkConₘ-⊛ᶜ id leq =
    _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-⊛ᶜ {δ = _ ∙ _} {η = _ ∙ _} (step _) (leq₁ ∙ leq₂) =
    case wkConₘ-⊛ᶜ _ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ,
    leq₃ ∙ ≤-reflexive (PE.sym (⊛≡𝟘ˡ (𝟘≮ leq₂))) ,
    leq₄ ∙ ≤-reflexive (PE.sym (⊛≡𝟘ʳ (𝟘≮ leq₂))) }
  wkConₘ-⊛ᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-⊛ᶜ ρ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

  -- An inversion lemma for wkConₘ and nrᶜ.

  wkConₘ-nrᶜ :
    ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
    ∀ ρ → wkConₘ ρ γ ≤ᶜ nrᶜ p r δ η θ →
    ∃₃ λ δ′ η′ θ′ →
      γ ≤ᶜ nrᶜ p r δ′ η′ θ′ ×
      wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η × wkConₘ ρ θ′ ≤ᶜ θ
  wkConₘ-nrᶜ id leq =
    _ , _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-nrᶜ {δ = _ ∙ _} {η = η ∙ _} {θ = _ ∙ _}
    (step ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-nrᶜ ρ leq₁ of λ where
      (_ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅) →
        _ , _ , _ , leq₁ ,
        leq₃
          ∙
        ≤-reflexive (PE.sym $ nr-positive (𝟘≮ leq₂) .proj₁) ,
        leq₄
          ∙
        ≤-reflexive (PE.sym $ nr-positive (𝟘≮ leq₂) .proj₂ .proj₁) ,
        leq₅
          ∙
        ≤-reflexive (PE.sym $ nr-positive (𝟘≮ leq₂) .proj₂ .proj₂)
  wkConₘ-nrᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} {θ = _ ∙ _}
    (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-nrᶜ ρ leq₁ of λ where
      (_ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅) →
        _ , _ , _ ,
        leq₁ ∙ leq₂ ,
        leq₃ ∙ ≤-refl ,
        leq₄ ∙ ≤-refl ,
        leq₅ ∙ ≤-refl
