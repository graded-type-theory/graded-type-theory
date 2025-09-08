------------------------------------------------------------------------
-- The usage relation is closed under weakening.
------------------------------------------------------------------------

open import Graded.Modality using (Modality)
open import Graded.Usage.Restrictions

module Graded.Usage.Weakening
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Restrictions.Instance R
open import Graded.Mode 𝕄
open import Definition.Untyped M
open import Definition.Untyped.Inversion M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    n m : Nat
    ρ : Wk m n
    p : M
    γ : Conₘ n
    t t′ : Term n
    m′ : Mode


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
wkUsage ρ Uₘ = PE.subst (λ γ → γ ▸[ _ ] _) (PE.sym (wk-𝟘ᶜ ρ)) Uₘ
wkUsage ρ ℕₘ = PE.subst (λ γ → γ ▸[ _ ] ℕ) (PE.sym (wk-𝟘ᶜ ρ)) ℕₘ
wkUsage ρ Emptyₘ =
  PE.subst (λ γ → γ ▸[ _ ] Empty) (PE.sym (wk-𝟘ᶜ ρ)) Emptyₘ
wkUsage ρ Unitₘ =
  PE.subst (λ γ → γ ▸[ _ ] Unit!) (PE.sym (wk-𝟘ᶜ ρ)) Unitₘ
wkUsage ρ (ΠΣₘ γ▸F δ▸G) =
  sub-≈ᶜ (ΠΣₘ (wkUsage ρ γ▸F) (wkUsage (lift ρ) δ▸G))
    (wk-+ᶜ ρ)
wkUsage ρ var =
  PE.subst (λ γ → γ ▸[ _ ] wk ρ (var _)) (PE.sym (wkUsageVar ρ _)) var
wkUsage ρ (lamₘ γ▸t) = lamₘ (wkUsage (lift ρ) γ▸t)
wkUsage ρ (γ▸t ∘ₘ δ▸u) =
  sub-≈ᶜ ((wkUsage ρ γ▸t) ∘ₘ (wkUsage ρ δ▸u))
    (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congˡ (wk-·ᶜ ρ)))
wkUsage ρ (prodʷₘ γ▸t δ▸u) =
  sub-≈ᶜ (prodʷₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸u))
    (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ)))
wkUsage ρ (prodˢₘ γ▸t γ▸u) =
  sub-≈ᶜ (prodˢₘ (wkUsage ρ γ▸t) (wkUsage ρ γ▸u))
    (≈ᶜ-trans (wk-∧ᶜ ρ) (∧ᶜ-congʳ (wk-·ᶜ ρ)))
wkUsage ρ (fstₘ m γ▸t PE.refl ok) = fstₘ m (wkUsage ρ γ▸t) PE.refl ok
wkUsage ρ (sndₘ γ▸t) = sndₘ (wkUsage ρ γ▸t)
wkUsage ρ (prodrecₘ γ▸t δ▸u η▸A ok) =
  sub-≈ᶜ (prodrecₘ (wkUsage ρ γ▸t) (wkUsage (liftn ρ 2) δ▸u)
           (wkUsage (lift ρ) η▸A) ok)
    (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ)))
wkUsage ρ zeroₘ =
  PE.subst (λ γ → γ ▸[ _ ] zero) (PE.sym (wk-𝟘ᶜ ρ)) zeroₘ
wkUsage ρ (sucₘ γ▸t) = sucₘ (wkUsage ρ γ▸t)
wkUsage ρ (natrecₘ γ▸z δ▸s η▸n θ▸A) =
  sub-≈ᶜ
    (natrecₘ (wkUsage ρ γ▸z) (wkUsage (liftn ρ 2) δ▸s)
      (wkUsage ρ η▸n) (wkUsage (lift ρ) θ▸A))
    (wk-nrᶜ ρ)
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
wkUsage ρ (natrec-no-nr-glbₘ {η} {χ} {x} ▸z ▸s ▸n ▸A x≤ χ≤) =
  sub (natrec-no-nr-glbₘ (wkUsage ρ ▸z) (wkUsage (liftn ρ 2) ▸s)
        (wkUsage ρ ▸n) (wkUsage (lift ρ) ▸A) x≤
        (GLBᶜ-congˡ (λ i → wk-nrᵢᶜ i ρ) (wk-GLBᶜ ρ χ≤)))
    (begin
      wkConₘ ρ (x ·ᶜ η +ᶜ χ)          ≈⟨ wk-+ᶜ ρ ⟩
      wkConₘ ρ (x ·ᶜ η) +ᶜ wkConₘ ρ χ ≈⟨ +ᶜ-congʳ (wk-·ᶜ ρ) ⟩
      x ·ᶜ wkConₘ ρ η +ᶜ wkConₘ ρ χ   ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage ρ (emptyrecₘ γ▸t δ▸A ok) =
  sub-≈ᶜ (emptyrecₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸A) ok)
    (wk-·ᶜ ρ)
wkUsage ρ starʷₘ = subst (_▸[ _ ] _) (PE.sym (wk-𝟘ᶜ ρ)) starʷₘ
wkUsage ρ (starˢₘ prop) =
  sub-≈ᶜ (starˢₘ (λ ns → subst (λ γ → γ ≈ᶜ wkConₘ ρ _) (wk-𝟘ᶜ ρ) (wk-≈ᶜ ρ (prop ns))))
      (wk-·ᶜ ρ)
wkUsage ρ (unitrecₘ γ▸t δ▸u η▸A ok) =
  sub-≈ᶜ (unitrecₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸u) (wkUsage (lift ρ) η▸A) ok)
      (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ)))
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
     wkConₘ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆))                  ≈⟨ ≈ᶜ-trans (wk-·ᶜ ρ) $ ·ᶜ-congˡ $
                                                                      ≈ᶜ-trans (wk-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                      ≈ᶜ-trans (wk-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                      ≈ᶜ-trans (wk-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                      wk-+ᶜ ρ ⟩
     ω ·ᶜ
     (wkConₘ ρ γ₂ +ᶜ wkConₘ ρ γ₃ +ᶜ wkConₘ ρ γ₄ +ᶜ wkConₘ ρ γ₅ +ᶜ
      wkConₘ ρ γ₆)                                                 ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage ρ (J₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ ▸v) = sub
  (J₀ₘ₁ ok p≡𝟘 q≡𝟘 (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B)
     (wkUsage _ ▸u) (wkUsage _ ▸t′) (wkUsage _ ▸v))
  (begin
     wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄))         ≈⟨ ≈ᶜ-trans (wk-·ᶜ ρ) $ ·ᶜ-congˡ $ wk-+ᶜ ρ ⟩
     ω ·ᶜ (wkConₘ ρ γ₃ +ᶜ wkConₘ ρ γ₄)  ∎)
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
     wkConₘ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅))                           ≈⟨ ≈ᶜ-trans (wk-·ᶜ ρ) $ ·ᶜ-congˡ $
                                                                         ≈ᶜ-trans (wk-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                         ≈ᶜ-trans (wk-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                         wk-+ᶜ ρ ⟩
     ω ·ᶜ (wkConₘ ρ γ₂ +ᶜ wkConₘ ρ γ₃ +ᶜ wkConₘ ρ γ₄ +ᶜ wkConₘ ρ γ₅)  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage ρ (K₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v) = sub
  (K₀ₘ₁ ok p≡𝟘 (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B)
     (wkUsage _ ▸u) (wkUsage _ ▸v))
  (begin
     wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄))         ≈⟨ ≈ᶜ-trans (wk-·ᶜ ρ) $ ·ᶜ-congˡ $ wk-+ᶜ ρ ⟩
     ω ·ᶜ (wkConₘ ρ γ₃ +ᶜ wkConₘ ρ γ₄)  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkUsage _ (K₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v) =
  K₀ₘ₂ ok (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸B) (wkUsage _ ▸u)
    (wkUsage _ ▸v)
wkUsage ρ ([]-congₘ ▸A ▸t ▸u ▸v ok) =
  subst (_▸[ _ ] _)
    (𝟘ᶜ           ≡˘⟨ wk-𝟘ᶜ ρ ⟩
     wkConₘ ρ 𝟘ᶜ  ∎)
    ([]-congₘ (wkUsage _ ▸A) (wkUsage _ ▸t) (wkUsage _ ▸u)
       (wkUsage _ ▸v) ok)
  where
  open Tools.Reasoning.PropositionalEquality
wkUsage ρ (sub γ▸t x) = sub (wkUsage ρ γ▸t) (wk-≤ᶜ ρ x)

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
        sub-≈ᶜ Uₘ (wkConₘ⁻¹-𝟘ᶜ ρ) }
      ℕₘ eq →
        case wk-ℕ eq of λ {
          refl →
        sub-≈ᶜ ℕₘ (wkConₘ⁻¹-𝟘ᶜ ρ) }
      Emptyₘ eq →
        case wk-Empty eq of λ {
          refl →
        sub-≈ᶜ Emptyₘ (wkConₘ⁻¹-𝟘ᶜ ρ) }
      Unitₘ eq →
        case wk-Unit eq of λ {
          refl →
        sub-≈ᶜ Unitₘ (wkConₘ⁻¹-𝟘ᶜ ρ) }
      (ΠΣₘ ▸A ▸B) eq →
        case wk-ΠΣ eq of λ {
          (_ , _ , refl , refl , refl) →
        case wkUsage⁻¹ ▸A of λ {
          ▸A →
        case wkUsage⁻¹ ▸B of λ {
          ▸B →
        sub-≈ᶜ (ΠΣₘ ▸A ▸B) (wkConₘ⁻¹-+ᶜ ρ) }}}
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
        sub-≈ᶜ zeroₘ (wkConₘ⁻¹-𝟘ᶜ ρ) }
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
      (natrec-no-nr-glbₘ {η} {χ} {x} ▸z ▸s ▸n ▸A x≤ χ≤) eq →
        case wk-natrec eq of λ {
          (_ , _ , _ , _ , refl , refl , refl , refl , refl) →
        sub (natrec-no-nr-glbₘ (wkUsage⁻¹ ▸z) (wkUsage⁻¹ ▸s) (wkUsage⁻¹ ▸n) (wkUsage⁻¹ ▸A)
              x≤
              (GLBᶜ-congˡ (λ i → wkConₘ⁻¹-nrᵢᶜ i ρ) (wkConₘ⁻¹-GLBᶜ ρ χ≤)))
          (begin
            wkConₘ⁻¹ ρ (x ·ᶜ η +ᶜ χ)            ≈⟨ wkConₘ⁻¹-+ᶜ ρ ⟩
            wkConₘ⁻¹ ρ (x ·ᶜ η) +ᶜ wkConₘ⁻¹ ρ χ ≈⟨ +ᶜ-congʳ (wkConₘ⁻¹-·ᶜ ρ) ⟩
            x ·ᶜ wkConₘ⁻¹ ρ η +ᶜ wkConₘ⁻¹ ρ χ   ∎) }

      (emptyrecₘ ▸t ▸A ok) eq →
        case wk-emptyrec eq of λ {
          (_ , _ , refl , refl , refl) →
        sub-≈ᶜ (emptyrecₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸A) ok)
          (wkConₘ⁻¹-·ᶜ ρ) }
      starʷₘ eq →
        case wk-star eq of λ {
          refl →
        sub-≈ᶜ starₘ (wkConₘ⁻¹-𝟘ᶜ ρ) }
      (starˢₘ prop) eq →
        case wk-star eq of λ {
          refl →
        sub-≈ᶜ (starˢₘ (λ ns → ≈ᶜ-trans (≈ᶜ-sym (wkConₘ⁻¹-𝟘ᶜ ρ))
                                    (wkConₘ⁻¹-≈ᶜ ρ (prop ns))))
            (wkConₘ⁻¹-·ᶜ ρ)  }
      (unitrecₘ ▸t ▸u ▸A ok) eq →
        case wk-unitrec eq of λ {
          (_ , _ , _ , refl , refl , refl , refl) →
        sub-≈ᶜ (unitrecₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸A) ok)
            (≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) (+ᶜ-congʳ (wkConₘ⁻¹-·ᶜ ρ))) }
      (Idₘ ok ▸A ▸t ▸u) eq →
        case wk-Id eq of λ {
          (_ , _ , _ , refl , refl , refl , refl) →
        sub-≈ᶜ (Idₘ ok (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)) $
        wkConₘ⁻¹-+ᶜ ρ }
      (Id₀ₘ ok ▸A ▸t ▸u) eq →
        case wk-Id eq of λ {
          (_ , _ , _ , refl , refl , refl , refl) →
        sub-≈ᶜ (Id₀ₘ ok (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)) $
        wkConₘ⁻¹-𝟘ᶜ ρ }
      rflₘ eq →
        case wk-rfl eq of λ {
          refl →
        sub-≈ᶜ rflₘ (wkConₘ⁻¹-𝟘ᶜ ρ) }
      (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ ▸v)
        eq →
        case wk-J eq of λ {
          (_ , _ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl , refl) →
        sub
          (Jₘ ok₁ ok₂ (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
             (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸t′) (wkUsage⁻¹ ▸v)) $ begin
        wkConₘ⁻¹ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆))         ≈⟨ wkConₘ⁻¹-·ᶜ ρ ⟩

        ω ·ᶜ wkConₘ⁻¹ ρ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)           ≈⟨ ·ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                  wkConₘ⁻¹-+ᶜ ρ ⟩
        ω ·ᶜ
          (wkConₘ⁻¹ ρ γ₂ +ᶜ wkConₘ⁻¹ ρ γ₃ +ᶜ wkConₘ⁻¹ ρ γ₄ +ᶜ
           wkConₘ⁻¹ ρ γ₅ +ᶜ wkConₘ⁻¹ ρ γ₆)                     ∎ }
      (J₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ ▸v) eq →
        case wk-J eq of λ {
          (_ , _ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl , refl) →
        sub
          (J₀ₘ₁ ok p≡𝟘 q≡𝟘 (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
             (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸t′) (wkUsage⁻¹ ▸v)) $ begin
        wkConₘ⁻¹ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄))           ≈⟨ wkConₘ⁻¹-·ᶜ ρ ⟩
        ω ·ᶜ wkConₘ⁻¹ ρ (γ₃ +ᶜ γ₄)             ≈⟨ ·ᶜ-congˡ $ wkConₘ⁻¹-+ᶜ ρ ⟩
        ω ·ᶜ (wkConₘ⁻¹ ρ γ₃ +ᶜ wkConₘ⁻¹ ρ γ₄)  ∎ }
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
        wkConₘ⁻¹ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅))               ≈⟨ wkConₘ⁻¹-·ᶜ ρ ⟩

        ω ·ᶜ wkConₘ⁻¹ ρ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)                 ≈⟨ ·ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                  ≈ᶜ-trans (wkConₘ⁻¹-+ᶜ ρ) $ +ᶜ-congˡ $
                                                                  wkConₘ⁻¹-+ᶜ ρ ⟩
        ω ·ᶜ
          (wkConₘ⁻¹ ρ γ₂ +ᶜ wkConₘ⁻¹ ρ γ₃ +ᶜ wkConₘ⁻¹ ρ γ₄ +ᶜ
           wkConₘ⁻¹ ρ γ₅)                                      ∎ }
      (K₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v) eq →
        case wk-K eq of λ {
          (_ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl) →
        sub
          (K₀ₘ₁ ok p≡𝟘 (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
             (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸v)) $ begin
        wkConₘ⁻¹ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄))           ≈⟨ wkConₘ⁻¹-·ᶜ ρ ⟩
        ω ·ᶜ wkConₘ⁻¹ ρ (γ₃ +ᶜ γ₄)             ≈⟨ ·ᶜ-congˡ $ wkConₘ⁻¹-+ᶜ ρ ⟩
        ω ·ᶜ (wkConₘ⁻¹ ρ γ₃ +ᶜ wkConₘ⁻¹ ρ γ₄)  ∎ }
      (K₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v) eq →
        case wk-K eq of λ {
          (_ , _ , _ , _ , _ ,
           refl , refl , refl , refl , refl , refl) →
        K₀ₘ₂ ok (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸B)
          (wkUsage⁻¹ ▸u) (wkUsage⁻¹ ▸v) }
      ([]-congₘ ▸A ▸t ▸u ▸v ok) eq →
        case wk-[]-cong eq of λ {
          (_ , _ , _ , _ , refl , refl , refl , refl , refl) →
        sub
          ([]-congₘ (wkUsage⁻¹ ▸A) (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)
             (wkUsage⁻¹ ▸v) ok) $
        ≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ) }
      (sub ▸t leq) refl →
        sub (wkUsage⁻¹ ▸t) (wkConₘ⁻¹-monotone ρ leq)

-- An inversion lemma for the usage relation and weakening.

wkUsage⁻¹′ : wkConₘ ρ γ ▸[ m′ ] wk ρ t → γ ▸[ m′ ] t
wkUsage⁻¹′ {ρ = ρ} {γ = γ} {m′ = m′} {t = t} =
  wkConₘ ρ γ ▸[ m′ ] wk ρ t          →⟨ wkUsage⁻¹ ⟩
  wkConₘ⁻¹ ρ (wkConₘ ρ γ) ▸[ m′ ] t  →⟨ subst (_▸[ _ ] _) (wkConₘ⁻¹-wkConₘ ρ) ⟩
  γ ▸[ m′ ] t                        □
