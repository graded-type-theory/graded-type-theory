------------------------------------------------------------------------
-- The usage relation is closed under weakening.
------------------------------------------------------------------------

open import Definition.Modality using (Modality)
open import Definition.Modality.Usage.Restrictions

module Definition.Modality.Usage.Weakening
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions M)
  where

open Modality 𝕄

open import Definition.Modality M hiding (Modality)
open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
import Definition.Modality.Properties.Has-well-behaved-zero as WB𝟘
open import Definition.Modality.Properties.PartialOrder
  semiring-with-meet
open import Definition.Modality.Properties.Star
  semiring-with-meet-and-star
open import Definition.Modality.Usage 𝕄 R
open import Definition.Modality.Usage.Properties 𝕄 R
open import Definition.Mode 𝕄
open import Definition.Untyped M hiding (_∙_ ; subst)
open import Definition.Untyped.Inversion M

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat renaming (_+_ to _+ⁿ_)
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
    γ γ′ δ η θ : Conₘ n
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
wkUsage ρ (ΠΣₘ γ▸F δ▸G) =
  sub (ΠΣₘ (wkUsage ρ γ▸F) (wkUsage (lift ρ) δ▸G))
      (≤ᶜ-reflexive (wk-+ᶜ ρ))
wkUsage ρ var =
  PE.subst (λ γ → γ ▸[ _ ] wk ρ (var _)) (PE.sym (wkUsageVar ρ _)) var
wkUsage ρ (lamₘ γ▸t) = lamₘ (wkUsage (lift ρ) γ▸t)
wkUsage ρ (γ▸t ∘ₘ δ▸u) =
  sub ((wkUsage ρ γ▸t) ∘ₘ (wkUsage ρ δ▸u))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congˡ (wk-·ᶜ ρ))))
wkUsage ρ (prodᵣₘ γ▸t δ▸u) =
  sub (prodᵣₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸u))
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congʳ (wk-·ᶜ ρ))))
wkUsage ρ (prodₚₘ γ▸t γ▸u) = sub
  (prodₚₘ (wkUsage ρ γ▸t) (wkUsage ρ γ▸u))
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
      (≤ᶜ-reflexive (≈ᶜ-trans (wk-⊛ᶜ ρ)
                              (⊛ᵣᶜ-cong (wk-∧ᶜ ρ)
                                       (≈ᶜ-trans (wk-+ᶜ ρ) (+ᶜ-congˡ (wk-·ᶜ ρ))))))
wkUsage ρ (Emptyrecₘ γ▸t δ▸A) =
  sub (Emptyrecₘ (wkUsage ρ γ▸t) (wkUsage ρ δ▸A)) (≤ᶜ-reflexive (wk-·ᶜ ρ))
wkUsage ρ starₘ = subst (λ γ → γ ▸[ _ ] star) (PE.sym (wk-𝟘ᶜ ρ)) starₘ
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
wkConₘ⁻¹-𝟘ᶜ (lift ρ) = wkConₘ⁻¹-𝟘ᶜ ρ ∙ ≈-refl

-- The function wkConₘ⁻¹ ρ commutes with _+ᶜ_.

wkConₘ⁻¹-+ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ +ᶜ δ) ≈ᶜ wkConₘ⁻¹ ρ γ +ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-+ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-+ᶜ ρ
wkConₘ⁻¹-+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-+ᶜ ρ ∙ ≈-refl

-- The function wkConₘ⁻¹ ρ commutes with _∧ᶜ_.

wkConₘ⁻¹-∧ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ ∧ᶜ δ) ≈ᶜ wkConₘ⁻¹ ρ γ ∧ᶜ wkConₘ⁻¹ ρ δ
wkConₘ⁻¹-∧ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-∧ᶜ ρ
wkConₘ⁻¹-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-∧ᶜ ρ ∙ ≈-refl

-- The function wkConₘ⁻¹ ρ commutes with p ·ᶜ_.

wkConₘ⁻¹-·ᶜ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (p ·ᶜ γ) ≈ᶜ p ·ᶜ wkConₘ⁻¹ ρ γ
wkConₘ⁻¹-·ᶜ             id       = ≈ᶜ-refl
wkConₘ⁻¹-·ᶜ {γ = _ ∙ _} (step ρ) = wkConₘ⁻¹-·ᶜ ρ
wkConₘ⁻¹-·ᶜ {γ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-·ᶜ ρ ∙ ≈-refl

-- The function wkConₘ⁻¹ ρ commutes with _⊛ᶜ_▷ r.

wkConₘ⁻¹-⊛ᶜ :
  (ρ : Wk m n) →
  wkConₘ⁻¹ ρ (γ ⊛ᶜ δ ▷ r) ≈ᶜ wkConₘ⁻¹ ρ γ ⊛ᶜ wkConₘ⁻¹ ρ δ ▷ r
wkConₘ⁻¹-⊛ᶜ                         id       = ≈ᶜ-refl
wkConₘ⁻¹-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (step ρ) = wkConₘ⁻¹-⊛ᶜ ρ
wkConₘ⁻¹-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (lift ρ) = wkConₘ⁻¹-⊛ᶜ ρ ∙ ≈-refl

-- The function wkConₘ⁻¹ ρ "commutes" in a certain sense with _,_≔_.

wkConₘ⁻¹-,≔ :
  (ρ : Wk m n) → wkConₘ⁻¹ ρ (γ , wkVar ρ x ≔ p) ≈ᶜ wkConₘ⁻¹ ρ γ , x ≔ p
wkConₘ⁻¹-,≔                        id       = ≈ᶜ-refl
wkConₘ⁻¹-,≔ {γ = _ ∙ _}            (step ρ) = wkConₘ⁻¹-,≔ ρ
wkConₘ⁻¹-,≔ {γ = _ ∙ _} {x = x0}   (lift ρ) = ≈ᶜ-refl
wkConₘ⁻¹-,≔ {γ = _ ∙ _} {x = _ +1} (lift ρ) = wkConₘ⁻¹-,≔ ρ ∙ ≈-refl

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
      (prodᵣₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u) eq →
        case wk-prod eq of λ {
          (_ , _ , refl , refl , refl) →
        sub (prodᵣₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)) (begin
          wkConₘ⁻¹ ρ (p ·ᶜ γ +ᶜ δ)             ≈⟨ wkConₘ⁻¹-+ᶜ ρ ⟩
          wkConₘ⁻¹ ρ (p ·ᶜ γ) +ᶜ wkConₘ⁻¹ ρ δ  ≈⟨ +ᶜ-congʳ (wkConₘ⁻¹-·ᶜ ρ) ⟩
          p ·ᶜ wkConₘ⁻¹ ρ γ +ᶜ wkConₘ⁻¹ ρ δ    ∎) }
      (prodₚₘ {γ = γ} {p = p} {δ = δ} ▸t ▸u) eq →
        case wk-prod eq of λ {
          (_ , _ , refl , refl , refl) →
        sub (prodₚₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸u)) (begin
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
          (begin
             wkConₘ⁻¹ ρ ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r)             ≈⟨ wkConₘ⁻¹-⊛ᶜ ρ ⟩

             wkConₘ⁻¹ ρ (γ ∧ᶜ η) ⊛ᶜ wkConₘ⁻¹ ρ (δ +ᶜ p ·ᶜ η) ▷ r  ≈⟨ ⊛ᵣᶜ-cong (wkConₘ⁻¹-∧ᶜ ρ) (wkConₘ⁻¹-+ᶜ ρ) ⟩

             (wkConₘ⁻¹ ρ γ ∧ᶜ wkConₘ⁻¹ ρ η) ⊛ᶜ
               wkConₘ⁻¹ ρ δ +ᶜ wkConₘ⁻¹ ρ (p ·ᶜ η) ▷ r            ≈⟨ ⊛ᵣᶜ-congˡ (+ᶜ-congˡ (wkConₘ⁻¹-·ᶜ ρ)) ⟩

             (wkConₘ⁻¹ ρ γ ∧ᶜ wkConₘ⁻¹ ρ η) ⊛ᶜ
               wkConₘ⁻¹ ρ δ +ᶜ p ·ᶜ wkConₘ⁻¹ ρ η ▷ r              ∎) }
      (Emptyrecₘ ▸t ▸A) eq →
        case wk-Emptyrec eq of λ {
          (_ , _ , refl , refl , refl) →
        sub (Emptyrecₘ (wkUsage⁻¹ ▸t) (wkUsage⁻¹ ▸A))
          (≤ᶜ-reflexive (wkConₘ⁻¹-·ᶜ ρ)) }
      starₘ eq →
        case wk-star eq of λ {
          refl →
        sub starₘ (≤ᶜ-reflexive (wkConₘ⁻¹-𝟘ᶜ ρ)) }
      (sub ▸t leq) refl →
        sub (wkUsage⁻¹ ▸t) (wkConₘ⁻¹-monotone ρ leq)

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
  (𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet)
  where

  open WB𝟘 semiring-with-meet-and-star 𝟘-well-behaved

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
    ∀ ρ → wkConₘ ρ γ ≤ᶜ δ ⊛ᶜ η ▷ r →
    ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ ⊛ᶜ η′ ▷ r × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
  wkConₘ-⊛ᶜ id leq =
    _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
  wkConₘ-⊛ᶜ {δ = _ ∙ _} {η = _ ∙ _} (step _) (leq₁ ∙ leq₂) =
    case wkConₘ-⊛ᶜ _ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ,
    leq₃ ∙ ≤-reflexive (PE.sym (⊛≈𝟘ˡ (𝟘≮ leq₂))) ,
    leq₄ ∙ ≤-reflexive (PE.sym (⊛≈𝟘ʳ (𝟘≮ leq₂))) }
  wkConₘ-⊛ᶜ
    {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-⊛ᶜ ρ leq₁ of λ {
      (_ , _ , leq₁ , leq₃ , leq₄) →
    _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

  -- An inversion lemma for wkConₘ and the operation from the conclusion
  -- of the usage rule for natrec.

  wkConₘ-⊛ᶜ′ :
    ∀ ρ → wkConₘ ρ γ ≤ᶜ (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r →
    p ≡ 𝟘 ×
    (∃₃ λ δ′ η′ θ′ →
       γ ≤ᶜ (δ′ ∧ᶜ θ′) ⊛ᶜ η′ ▷ r ×
       wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η × wkConₘ ρ θ′ ≤ᶜ θ)
      ⊎
    (∃₃ λ δ′ η′ θ′ →
       γ ≤ᶜ (δ′ ∧ᶜ θ′) ⊛ᶜ η′ +ᶜ p ·ᶜ θ′ ▷ r ×
       wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η × wkConₘ ρ θ′ ≤ᶜ θ)
  wkConₘ-⊛ᶜ′ id leq =
    inj₂ (_ , _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl , ≤ᶜ-refl)
  wkConₘ-⊛ᶜ′ {δ = _ ∙ _} {θ = _ ∙ _} {η = η ∙ _}
    (step ρ) (leq₁ ∙ leq₂) =
    case zero-product (+-positiveʳ (⊛≈𝟘ʳ (𝟘≮ leq₂))) of λ where
      (inj₂ refl) →
        case wkConₘ-⊛ᶜ′ ρ leq₁ of λ where
          (inj₂ (_ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₂
            (_ , _ , _ , leq₁ ,
             leq₃
               ∙
             ≤-reflexive (PE.sym (∧-positiveˡ (⊛≈𝟘ˡ (𝟘≮ leq₂)))) ,
             leq₄
               ∙
             ≤-reflexive (PE.sym (+-positiveˡ (⊛≈𝟘ʳ (𝟘≮ leq₂)))) ,
             leq₅ ∙ ≤-refl)
          (inj₁ (refl , _ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₁
            (refl , _ , _ , _ , leq₁ ,
             leq₃
               ∙
             ≤-reflexive (PE.sym (∧-positiveˡ (⊛≈𝟘ˡ (𝟘≮ leq₂)))) ,
             leq₄
               ∙
             ≤-reflexive (PE.sym (+-positiveˡ (⊛≈𝟘ʳ (𝟘≮ leq₂)))) ,
             leq₅ ∙ ≤-refl)
      (inj₁ refl) →
        case wkConₘ-⊛ᶜ′ ρ leq₁ of λ where
          (inj₂ (_ , η′ , θ′ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₁
            (refl , _ , _ , _ , leq₁ ,
             leq₃
               ∙
             ≤-reflexive (PE.sym (∧-positiveˡ (⊛≈𝟘ˡ (𝟘≮ leq₂)))) ,
             (begin
                wkConₘ ρ (η′ +ᶜ 𝟘 ·ᶜ θ′)  ≡⟨ cong (wkConₘ ρ) (≈ᶜ→≡ (+ᶜ-congˡ (·ᶜ-zeroˡ _))) ⟩
                wkConₘ ρ (η′ +ᶜ 𝟘ᶜ)       ≡⟨ cong (wkConₘ ρ) (≈ᶜ→≡ (+ᶜ-identityʳ _)) ⟩
                wkConₘ ρ η′               ≤⟨ leq₄ ⟩
                η                         ∎)
               ∙
             ≤-reflexive (PE.sym (+-positiveˡ (⊛≈𝟘ʳ (𝟘≮ leq₂)))) ,
             leq₅
               ∙
             ≤-reflexive (PE.sym (∧-positiveʳ (⊛≈𝟘ˡ (𝟘≮ leq₂)))))
          (inj₁ (_ , _ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₁
            (refl , _ , _ , _ , leq₁ ,
             leq₃
               ∙
             ≤-reflexive (PE.sym (∧-positiveˡ (⊛≈𝟘ˡ (𝟘≮ leq₂)))) ,
             leq₄
               ∙
             ≤-reflexive (PE.sym (+-positiveˡ (⊛≈𝟘ʳ (𝟘≮ leq₂)))) ,
             leq₅
               ∙
             ≤-reflexive (PE.sym (∧-positiveʳ (⊛≈𝟘ˡ (𝟘≮ leq₂)))))
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
  wkConₘ-⊛ᶜ′
    {γ = _ ∙ p₁} {δ = _ ∙ p₂} {θ = _ ∙ p₃} {η = _ ∙ p₄} {r = r}
    (lift ρ) (leq₁ ∙ leq₂) =
    case wkConₘ-⊛ᶜ′ ρ leq₁ of λ where
          (inj₂ (_ , η′ , θ′ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₂
            (_ , _ , _ ,
             leq₁ ∙ leq₂ ,
             leq₃ ∙ ≤-refl ,
             leq₄ ∙ ≤-refl ,
             leq₅ ∙ ≤-refl)
          (inj₁ (refl , _ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₁
            (refl , _ , _ , _ ,
             leq₁
               ∙
             (begin
                p₁                           ≤⟨ leq₂ ⟩
                (p₂ ∧ p₃) ⊛ p₄ + 𝟘 · p₃ ▷ r  ≡⟨ ⊛ᵣ-congˡ (+-congˡ (·-zeroˡ _)) ⟩
                (p₂ ∧ p₃) ⊛ p₄ + 𝟘 ▷ r       ≡⟨ ⊛ᵣ-congˡ (+-identityʳ _) ⟩
                (p₂ ∧ p₃) ⊛ p₄ ▷ r           ∎) ,
             leq₃ ∙ ≤-refl ,
             leq₄ ∙ ≤-refl ,
             leq₅ ∙ ≤-refl)
    where
    open Tools.Reasoning.PartialOrder ≤-poset
