------------------------------------------------------------------------
-- The usage relation is closed under weakening.
------------------------------------------------------------------------

open import Definition.Modality

module Definition.Modality.Usage.Weakening
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Properties 𝕄
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
wkUsage ρ (ΠΣₘ γ▸F δ▸G ok) =
  sub (ΠΣₘ (wkUsage ρ γ▸F) (wkUsage (lift ρ) δ▸G) ok)
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
wkUsage ρ (prodrecₘ γ▸t δ▸u η▸A P) =
  sub (prodrecₘ (wkUsage ρ γ▸t) (wkUsage (liftn ρ 2) δ▸u) (wkUsage (lift ρ) η▸A) P)
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
-- Inversion lemmas

-- An inversion lemma for wkConₘ and 𝟘ᶜ.

wkConₘ-𝟘 : wkConₘ ρ γ ≤ᶜ 𝟘ᶜ → γ ≤ᶜ 𝟘ᶜ
wkConₘ-𝟘 {ρ = id} leq =
  leq
wkConₘ-𝟘 {ρ = step _} (leq ∙ _) =
  wkConₘ-𝟘 leq
wkConₘ-𝟘 {ρ = lift _} {γ = _ ∙ _} (leq₁ ∙ leq₂) =
  wkConₘ-𝟘 leq₁ ∙ leq₂

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

-- An inversion lemma for wkConₘ and _+ᶜ_.

wkConₘ-+ᶜ :
  T 𝟘ᵐ-allowed →
  ∀ ρ → wkConₘ ρ γ ≤ᶜ δ +ᶜ η →
  ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ +ᶜ η′ × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
wkConₘ-+ᶜ _ id leq =
  _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
wkConₘ-+ᶜ {δ = _ ∙ _} {η = _ ∙ _} ok (step _) (leq₁ ∙ leq₂) =
  case wkConₘ-+ᶜ ok _ leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ , _ , leq₁ ,
  leq₃ ∙ ≤-reflexive (PE.sym (+-positiveˡ ok (𝟘≮ ok leq₂))) ,
  leq₄ ∙ ≤-reflexive (PE.sym (+-positiveʳ ok (𝟘≮ ok leq₂))) }
wkConₘ-+ᶜ
  {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} ok (lift ρ) (leq₁ ∙ leq₂) =
  case wkConₘ-+ᶜ ok ρ leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

-- An inversion lemma for wkConₘ and _∧ᶜ_.

wkConₘ-∧ᶜ :
  T 𝟘ᵐ-allowed →
  ∀ ρ → wkConₘ ρ γ ≤ᶜ δ ∧ᶜ η →
  ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ ∧ᶜ η′ × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
wkConₘ-∧ᶜ _ id leq =
  _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
wkConₘ-∧ᶜ {δ = _ ∙ _} {η = _ ∙ _} ok (step _) (leq₁ ∙ leq₂) =
  case wkConₘ-∧ᶜ ok _ leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ , _ , leq₁ ,
  leq₃ ∙ ≤-reflexive (PE.sym (∧-positiveˡ ok (𝟘≮ ok leq₂))) ,
  leq₄ ∙ ≤-reflexive (PE.sym (∧-positiveʳ ok (𝟘≮ ok leq₂))) }
wkConₘ-∧ᶜ
  {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} ok (lift ρ) (leq₁ ∙ leq₂) =
  case wkConₘ-∧ᶜ ok ρ leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

-- An inversion lemma for wkConₘ and _·ᶜ_.

wkConₘ-·ᶜ :
  T 𝟘ᵐ-allowed →
  ∀ ρ → wkConₘ ρ γ ≤ᶜ p ·ᶜ δ →
  p ≡ 𝟘 × γ ≤ᶜ 𝟘ᶜ ⊎
  ∃ λ δ′ → γ ≤ᶜ p ·ᶜ δ′ × wkConₘ ρ δ′ ≤ᶜ δ
wkConₘ-·ᶜ _ id leq =
  inj₂ (_ , leq , ≤ᶜ-refl)
wkConₘ-·ᶜ {γ = γ} {δ = _ ∙ q} ok (step ρ) (leq₁ ∙ leq₂) =
  case wkConₘ-·ᶜ ok ρ leq₁ of λ where
    (inj₁ (refl , leq₁))      → inj₁ (refl , leq₁)
    (inj₂ (δ′ , leq₁ , leq₃)) →
      case zero-product ok (𝟘≮ ok leq₂) of λ where
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
wkConₘ-·ᶜ {γ = γ ∙ q} {δ = _ ∙ r} ok (lift ρ) (leq₁ ∙ leq₂) =
  case wkConₘ-·ᶜ ok ρ leq₁ of λ where
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
  T 𝟘ᵐ-allowed →
  ∀ ρ → wkConₘ ρ γ ≤ᶜ δ ⊛ᶜ η ▷ r →
  ∃₂ λ δ′ η′ → γ ≤ᶜ δ′ ⊛ᶜ η′ ▷ r × wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η
wkConₘ-⊛ᶜ ok id leq =
  _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl
wkConₘ-⊛ᶜ {δ = _ ∙ _} {η = _ ∙ _} ok (step _) (leq₁ ∙ leq₂) =
  case wkConₘ-⊛ᶜ ok _ leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ , _ , leq₁ ,
  leq₃ ∙ ≤-reflexive (PE.sym (⊛≈𝟘ˡ ok (𝟘≮ ok leq₂))) ,
  leq₄ ∙ ≤-reflexive (PE.sym (⊛≈𝟘ʳ ok (𝟘≮ ok leq₂))) }
wkConₘ-⊛ᶜ
  {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} ok (lift ρ) (leq₁ ∙ leq₂) =
  case wkConₘ-⊛ᶜ ok ρ leq₁ of λ {
    (_ , _ , leq₁ , leq₃ , leq₄) →
  _ , _ , leq₁ ∙ leq₂ , leq₃ ∙ ≤-refl , leq₄ ∙ ≤-refl }

-- An inversion lemma for wkConₘ and the operation from the conclusion
-- of the usage rule for natrec.

wkConₘ-⊛ᶜ′ :
  T 𝟘ᵐ-allowed →
  ∀ ρ → wkConₘ ρ γ ≤ᶜ (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r →
  p ≡ 𝟘 ×
  (∃₃ λ δ′ η′ θ′ →
     γ ≤ᶜ (δ′ ∧ᶜ θ′) ⊛ᶜ η′ ▷ r ×
     wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η × wkConₘ ρ θ′ ≤ᶜ θ)
    ⊎
  (∃₃ λ δ′ η′ θ′ →
     γ ≤ᶜ (δ′ ∧ᶜ θ′) ⊛ᶜ η′ +ᶜ p ·ᶜ θ′ ▷ r ×
     wkConₘ ρ δ′ ≤ᶜ δ × wkConₘ ρ η′ ≤ᶜ η × wkConₘ ρ θ′ ≤ᶜ θ)
wkConₘ-⊛ᶜ′ ok id leq =
  inj₂ (_ , _ , _ , leq , ≤ᶜ-refl , ≤ᶜ-refl , ≤ᶜ-refl)
wkConₘ-⊛ᶜ′ {δ = _ ∙ _} {θ = _ ∙ _} {η = η ∙ _}
  ok (step ρ) (leq₁ ∙ leq₂) =
  case zero-product ok (+-positiveʳ ok (⊛≈𝟘ʳ ok (𝟘≮ ok leq₂))) of λ where
    (inj₂ refl) →
      case wkConₘ-⊛ᶜ′ ok ρ leq₁ of λ where
        (inj₂ (_ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₂
          (_ , _ , _ , leq₁ ,
           leq₃
             ∙
           ≤-reflexive (PE.sym (∧-positiveˡ ok (⊛≈𝟘ˡ ok (𝟘≮ ok leq₂)))) ,
           leq₄
             ∙
           ≤-reflexive (PE.sym (+-positiveˡ ok (⊛≈𝟘ʳ ok (𝟘≮ ok leq₂)))) ,
           leq₅ ∙ ≤-refl)
        (inj₁ (refl , _ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₁
          (refl , _ , _ , _ , leq₁ ,
           leq₃
             ∙
           ≤-reflexive (PE.sym (∧-positiveˡ ok (⊛≈𝟘ˡ ok (𝟘≮ ok leq₂)))) ,
           leq₄
             ∙
           ≤-reflexive (PE.sym (+-positiveˡ ok (⊛≈𝟘ʳ ok (𝟘≮ ok leq₂)))) ,
           leq₅ ∙ ≤-refl)
    (inj₁ refl) →
      case wkConₘ-⊛ᶜ′ ok ρ leq₁ of λ where
        (inj₂ (_ , η′ , θ′ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₁
          (refl , _ , _ , _ , leq₁ ,
           leq₃
             ∙
           ≤-reflexive (PE.sym (∧-positiveˡ ok (⊛≈𝟘ˡ ok (𝟘≮ ok leq₂)))) ,
           (begin
              wkConₘ ρ (η′ +ᶜ 𝟘 ·ᶜ θ′)  ≡⟨ cong (wkConₘ ρ) (≈ᶜ→≡ (+ᶜ-congˡ (·ᶜ-zeroˡ _))) ⟩
              wkConₘ ρ (η′ +ᶜ 𝟘ᶜ)       ≡⟨ cong (wkConₘ ρ) (≈ᶜ→≡ (+ᶜ-identityʳ _)) ⟩
              wkConₘ ρ η′               ≤⟨ leq₄ ⟩
              η                         ∎)
             ∙
           ≤-reflexive (PE.sym (+-positiveˡ ok (⊛≈𝟘ʳ ok (𝟘≮ ok leq₂)))) ,
           leq₅
             ∙
           ≤-reflexive (PE.sym (∧-positiveʳ ok (⊛≈𝟘ˡ ok (𝟘≮ ok leq₂)))))
        (inj₁ (_ , _ , _ , _ , leq₁ , leq₃ , leq₄ , leq₅)) → inj₁
          (refl , _ , _ , _ , leq₁ ,
           leq₃
             ∙
           ≤-reflexive (PE.sym (∧-positiveˡ ok (⊛≈𝟘ˡ ok (𝟘≮ ok leq₂)))) ,
           leq₄
             ∙
           ≤-reflexive (PE.sym (+-positiveˡ ok (⊛≈𝟘ʳ ok (𝟘≮ ok leq₂)))) ,
           leq₅
             ∙
           ≤-reflexive (PE.sym (∧-positiveʳ ok (⊛≈𝟘ˡ ok (𝟘≮ ok leq₂)))))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wkConₘ-⊛ᶜ′
  {γ = _ ∙ p₁} {δ = _ ∙ p₂} {θ = _ ∙ p₃} {η = _ ∙ p₄} {r = r}
  ok (lift ρ) (leq₁ ∙ leq₂) =
  case wkConₘ-⊛ᶜ′ ok ρ leq₁ of λ where
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

-- An inversion lemma for the usage relation and weakening.

wkUsage⁻¹ : T 𝟘ᵐ-allowed → wkConₘ ρ γ ▸[ m′ ] wk ρ t → γ ▸[ m′ ] t
wkUsage⁻¹ 𝟘ᵐ-ok = λ ▸t → wkUsage⁻¹′ ▸t ≤ᶜ-refl
  where mutual

  wkUsage⁻¹′ :
    γ′ ▸[ m′ ] wk ρ t → wkConₘ ρ γ ≤ᶜ γ′ → γ ▸[ m′ ] t
  wkUsage⁻¹′ ▸t leq = wkUsage⁻¹″ ▸t leq refl

  wkUsage⁻¹″ :
    γ′ ▸[ m′ ] t′ → wkConₘ ρ γ ≤ᶜ γ′ → wk ρ t ≡ t′ → γ ▸[ m′ ] t
  wkUsage⁻¹″ {m′ = m′} {ρ = ρ} {γ = γ} = λ where
      Uₘ leq eq →
        case wk-U eq of λ {
          refl →
        sub Uₘ (wkConₘ-𝟘 leq) }
      ℕₘ leq eq →
        case wk-ℕ eq of λ {
          refl →
        sub ℕₘ (wkConₘ-𝟘 leq) }
      Emptyₘ leq eq →
        case wk-Empty eq of λ {
          refl →
        sub Emptyₘ (wkConₘ-𝟘 leq) }
      Unitₘ leq eq →
        case wk-Unit eq of λ {
          refl →
        sub Unitₘ (wkConₘ-𝟘 leq) }
      (ΠΣₘ ▸A ▸B ok) leq eq →
        case wk-ΠΣ eq of λ {
          (_ , _ , refl , refl , refl) →
        case wkConₘ-+ᶜ 𝟘ᵐ-ok ρ leq of λ {
          (_ , _ , leq₁ , leq₂ , leq₃) →
        case wkUsage⁻¹′ ▸A leq₂ of λ {
          ▸A →
        case wkUsage⁻¹′ ▸B (leq₃ ∙ ≤-refl) of λ {
          ▸B →
        sub (ΠΣₘ ▸A ▸B ok) leq₁ }}}}
      var leq eq →
        case wk-var eq of λ {
          (x , refl , refl) →
        case wkConₘ-,-wkVar-≔ x leq of λ {
          (δ , p , leq₁ , leq₂ , leq₃) →
        sub var $ begin
          γ                ≤⟨ leq₁ ⟩
          δ , x ≔ p        ≤⟨ update-monotoneʳ _ leq₃ ⟩
          δ , x ≔ ⌜ m′ ⌝   ≤⟨ update-monotoneˡ _ (wkConₘ-𝟘 leq₂) ⟩
          𝟘ᶜ , x ≔ ⌜ m′ ⌝  ∎ }}
      (lamₘ ▸t) leq eq →
        case wk-lam eq of λ {
          (_ , refl , refl) →
        lamₘ (wkUsage⁻¹′ ▸t (leq ∙ ≤-refl)) }
      (_∘ₘ_ {p = p} ▸t ▸u) leq eq →
        case wk-∘ eq of λ {
          (_ , _ , refl , refl , refl) →
        case wkConₘ-+ᶜ 𝟘ᵐ-ok ρ leq of λ {
          (δ , η , leq₁ , leq₂ , leq₃) →
        case wkConₘ-·ᶜ 𝟘ᵐ-ok ρ leq₃ of λ where
          (inj₂ (θ , leq₃ , leq₄)) → sub
            (wkUsage⁻¹′ ▸t leq₂ ∘ₘ wkUsage⁻¹′ ▸u leq₄)
            (begin
               γ            ≤⟨ leq₁ ⟩
               δ +ᶜ η       ≤⟨ +ᶜ-monotoneʳ leq₃ ⟩
               δ +ᶜ p ·ᶜ θ  ∎)
          (inj₁ (refl , leq₃)) → sub
            (wkUsage⁻¹′ ▸t leq₂ ∘ₘ wkUsage⁻¹-ᵐ·𝟘 m′ ▸u)
            (begin
               γ             ≤⟨ leq₁ ⟩
               δ +ᶜ η        ≤⟨ +ᶜ-monotoneʳ leq₃ ⟩
               δ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
               δ +ᶜ 𝟘 ·ᶜ 𝟘ᶜ  ∎) }}
      (prodᵣₘ {p = p} ▸t ▸u) leq eq →
        case wk-prod eq of λ {
          (_ , _ , refl , refl , refl) →
        case wkConₘ-+ᶜ 𝟘ᵐ-ok ρ leq of λ {
          (δ , η , leq₁ , leq₂ , leq₃) →
        case wkConₘ-·ᶜ 𝟘ᵐ-ok ρ leq₂ of λ where
          (inj₂ (θ , leq₂ , leq₄)) → sub
            (prodᵣₘ (wkUsage⁻¹′ ▸t leq₄) (wkUsage⁻¹′ ▸u leq₃))
            (begin
               γ            ≤⟨ leq₁ ⟩
               δ +ᶜ η       ≤⟨ +ᶜ-monotoneˡ leq₂ ⟩
               p ·ᶜ θ +ᶜ η  ∎)
          (inj₁ (refl , leq₂)) → sub
            (prodᵣₘ (wkUsage⁻¹-ᵐ·𝟘 m′ ▸t) (wkUsage⁻¹′ ▸u leq₃))
            (begin
               γ             ≤⟨ leq₁ ⟩
               δ +ᶜ η        ≤⟨ +ᶜ-monotoneˡ leq₂ ⟩
               𝟘ᶜ +ᶜ η       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
               𝟘 ·ᶜ 𝟘ᶜ +ᶜ η  ∎) }}
      (prodₚₘ {p = p} ▸t ▸u) leq eq →
        case wk-prod eq of λ {
          (_ , _ , refl , refl , refl) →
        case wkConₘ-∧ᶜ 𝟘ᵐ-ok ρ leq of λ {
          (δ , η , leq₁ , leq₂ , leq₃) →
        case wkConₘ-·ᶜ 𝟘ᵐ-ok ρ leq₂ of λ where
          (inj₂ (θ , leq₂ , leq₄)) → sub
            (prodₚₘ (wkUsage⁻¹′ ▸t leq₄) (wkUsage⁻¹′ ▸u leq₃))
            (begin
               γ            ≤⟨ leq₁ ⟩
               δ ∧ᶜ η       ≤⟨ ∧ᶜ-monotoneˡ leq₂ ⟩
               p ·ᶜ θ ∧ᶜ η  ∎)
          (inj₁ (refl , leq₂)) → sub
            (prodₚₘ (wkUsage⁻¹-ᵐ·𝟘 m′ ▸t) (wkUsage⁻¹′ ▸u leq₃))
            (begin
               γ             ≤⟨ leq₁ ⟩
               δ ∧ᶜ η        ≤⟨ ∧ᶜ-monotoneˡ leq₂ ⟩
               𝟘ᶜ ∧ᶜ η       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
               𝟘 ·ᶜ 𝟘ᶜ ∧ᶜ η  ∎) }}
      (fstₘ m ▸t refl ok) leq eq →
        case wk-fst eq of λ {
          (_ , refl , refl) →
        fstₘ m (wkUsage⁻¹′ ▸t leq) refl ok }
      (sndₘ ▸t) leq eq →
        case wk-snd eq of λ {
          (_ , refl , refl) →
        sndₘ (wkUsage⁻¹′ ▸t leq) }
      (prodrecₘ {r = r} ▸t ▸u ▸A ok) leq eq →
        case wk-prodrec eq of λ {
          (_ , _ , _ , refl , refl , refl , refl) →
        case wkConₘ-+ᶜ 𝟘ᵐ-ok ρ leq of λ {
          (δ , η , leq₁ , leq₂ , leq₃) →
        case wkConₘ-·ᶜ 𝟘ᵐ-ok ρ leq₂ of λ where
          (inj₂ (θ , leq₂ , leq₄)) → sub
            (prodrecₘ
               (wkUsage⁻¹′ ▸t leq₄)
               (wkUsage⁻¹′ ▸u (leq₃ ∙ ≤-refl ∙ ≤-refl))
               (wkUsage⁻¹-𝟘ᵐ?-∙ ▸A)
               ok)
            (begin
               γ            ≤⟨ leq₁ ⟩
               δ +ᶜ η       ≤⟨ +ᶜ-monotoneˡ leq₂ ⟩
               r ·ᶜ θ +ᶜ η  ∎)
          (inj₁ (refl , leq₂)) → sub
            (prodrecₘ
               (wkUsage⁻¹-ᵐ·𝟘 m′ ▸t)
               (wkUsage⁻¹′ ▸u (leq₃ ∙ ≤-refl ∙ ≤-refl))
               (wkUsage⁻¹-𝟘ᵐ?-∙ ▸A)
               ok)
            (begin
               γ             ≤⟨ leq₁ ⟩
               δ +ᶜ η        ≤⟨ +ᶜ-monotoneˡ leq₂ ⟩
               𝟘ᶜ +ᶜ η       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
               𝟘 ·ᶜ 𝟘ᶜ +ᶜ η  ∎) }}
      zeroₘ leq eq →
        case wk-zero eq of λ {
          refl →
        sub zeroₘ (wkConₘ-𝟘 leq) }
      (sucₘ ▸t) leq eq →
        case wk-suc eq of λ {
          (_ , refl , refl) →
        sucₘ (wkUsage⁻¹′ ▸t leq) }
      (natrecₘ {p = p} {r = r} ▸t ▸u ▸v ▸A) leq eq →
        case wk-natrec eq of λ {
          (_ , _ , _ , _ , refl , refl , refl , refl , refl) →
        case wkConₘ-⊛ᶜ′ 𝟘ᵐ-ok ρ leq of λ where
          (inj₁ (refl , δ , η , θ , leq₁ , leq₂ , leq₃ , leq₄)) → sub
            (natrecₘ
               (wkUsage⁻¹′ ▸t leq₂)
               (wkUsage⁻¹′ ▸u (leq₃ ∙ ≤-refl ∙ ≤-refl))
               (wkUsage⁻¹′ ▸v leq₄)
               (wkUsage⁻¹-𝟘ᵐ?-∙ ▸A))
            (begin
               γ                            ≤⟨ leq₁ ⟩
               (δ ∧ᶜ θ) ⊛ᶜ η ▷ r            ≈˘⟨ ⊛ᵣᶜ-congˡ (+ᶜ-identityʳ _) ⟩
               (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ 𝟘ᶜ ▷ r      ≈˘⟨ ⊛ᵣᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroˡ _)) ⟩
               (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ 𝟘 ·ᶜ θ ▷ r  ∎)
          (inj₂ (_ , _ , _ , leq₁ , leq₂ , leq₃ , leq₄)) → sub
            (natrecₘ
               (wkUsage⁻¹′ ▸t leq₂)
               (wkUsage⁻¹′ ▸u (leq₃ ∙ ≤-refl ∙ ≤-refl))
               (wkUsage⁻¹′ ▸v leq₄)
               (wkUsage⁻¹-𝟘ᵐ?-∙ ▸A))
            leq₁ }
      (Emptyrecₘ ▸t ▸A) leq eq →
        case wk-Emptyrec eq of λ {
          (_ , _ , refl , refl , refl) →
        case wkConₘ-·ᶜ 𝟘ᵐ-ok ρ leq of λ where
          (inj₂ (_ , leq₁ , leq₂)) → sub
            (Emptyrecₘ (wkUsage⁻¹′ ▸t leq₂) (wkUsage⁻¹-𝟘ᵐ? ▸A))
            leq₁
          (inj₁ (refl , leq)) → sub
            (Emptyrecₘ (wkUsage⁻¹-ᵐ·𝟘 m′ ▸t) (wkUsage⁻¹-𝟘ᵐ? ▸A))
            (begin
               γ        ≤⟨ leq ⟩
               𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
               𝟘 ·ᶜ 𝟘ᶜ  ∎) }
      starₘ leq eq →
        case wk-star eq of λ {
          refl →
        sub starₘ (wkConₘ-𝟘 leq) }
      (sub ▸t leq₁) leq₂ refl →
        wkUsage⁻¹′ ▸t (≤ᶜ-trans leq₂ leq₁)
    where
    open module R {n} = Tools.Reasoning.PartialOrder (≤ᶜ-poset {n = n})

  wkUsage⁻¹-𝟘ᵐ : γ ▸[ m′ ] wk ρ t → 𝟘ᶜ ▸[ 𝟘ᵐ[ 𝟘ᵐ-ok ] ] t
  wkUsage⁻¹-𝟘ᵐ {ρ = ρ} ▸t =
    wkUsage⁻¹′ (▸-𝟘 {ok = 𝟘ᵐ-ok} ▸t) $
    PE.subst (_≤ᶜ _) (PE.sym (wk-𝟘ᶜ ρ)) ≤ᶜ-refl

  wkUsage⁻¹-ᵐ·𝟘 : ∀ m′ → γ ▸[ m′ ᵐ· 𝟘 ] wk ρ t → 𝟘ᶜ ▸[ m′ ᵐ· 𝟘 ] t
  wkUsage⁻¹-ᵐ·𝟘 m′ ▸t = ▸-cong
    (𝟘ᵐ[ _ ]  ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
     𝟘ᵐ?      ≡˘⟨ ᵐ·-zeroʳ m′ ⟩
     m′ ᵐ· 𝟘  ∎)
    (wkUsage⁻¹-𝟘ᵐ ▸t)
    where
    open Tools.Reasoning.PropositionalEquality

  wkUsage⁻¹-𝟘ᵐ? : γ ▸[ 𝟘ᵐ? ] wk ρ t → 𝟘ᶜ ▸[ 𝟘ᵐ? ] t
  wkUsage⁻¹-𝟘ᵐ? ▸t = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) (wkUsage⁻¹-𝟘ᵐ ▸t)

  wkUsage⁻¹-𝟘ᵐ?-∙ :
    γ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] wk (lift ρ) t → 𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] t
  wkUsage⁻¹-𝟘ᵐ?-∙ {p = p} ▸t =
    sub (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) (wkUsage⁻¹-𝟘ᵐ ▸t)) $ begin
      𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ cong (λ m → ⌜ m ⌝ · _) (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok}) ⟩
      𝟘ᶜ ∙ 𝟘 · p        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
      𝟘ᶜ                ∎
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
