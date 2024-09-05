------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States
-- and the reduction relation with resource tracking.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Heap.Usage.Assumptions
open import Heap.Options
open import Definition.Typed.Variant

module Heap.Usage.Reduction
  {a} {M : Set a} {𝕄 : Modality M}
  {UR : Usage-restrictions 𝕄}
  {type-variant : Type-variant}
  (UA : UsageAssumptions type-variant UR)
  (opts : Options)
  (open Options opts)
  ⦃ _ : Track-resources ⦄
  where

open UsageAssumptions UA
open Modality 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit
import Tools.Reasoning.PartialOrder as RPo

open import Definition.Untyped M

open import Heap.Untyped 𝕄 type-variant
open import Heap.Untyped.Properties 𝕄 type-variant
open import Heap.Reduction 𝕄 type-variant opts
open import Heap.Usage 𝕄 type-variant UR
open import Heap.Usage.Properties type-variant UR
open import Heap.Usage.Weakening type-variant UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

private variable
  γ δ η : Conₘ _
  s s′ : State _ _ _

opaque

  ▸-⇒ᵥ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ᵥ s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒ᵥ {δ} (▸H , ▸t , ▸S , γ≤) (lamₕ {p} {E} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (∘ₑ {γ = γ′} ▸u) ▸S) →
    case inv-usage-lam ▸t of λ
      (invUsageLam {δ = δ′} ▸t δ≤) →
    _ , _ , _
      , subₕ ▸H (≤ᶜ-trans γ≤
          (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-congʳ (·-identityʳ _)))
            (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-assoc _ _ _))
              (+ᶜ-assoc _ _ _))))))
      ∙ ▸ᶜᵖ (▸-cong (sym (≢𝟘→⌞·⌟≡ (▸∣S∣≢𝟘 ▸S))) ▸u)
      , ▸t , wk-▸ˢ (step id) ▸S
      , (begin
          ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η ∙ ∣ S ∣ · p                    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ∙ ≤-refl ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ′ +ᶜ η ∙ ∣ S ∣ · p                   ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ (step id) S)) ∙ ·-congʳ (wk-∣S∣ (step id) S) ⟩
          ∣ wk1ˢ S ∣ ·ᶜ wkᶜ E δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · p          ≈˘⟨ ≈ᶜ-refl ∙ ·-congˡ (·-identityˡ p) ⟩
          ∣ wk1ˢ S ∣ ·ᶜ wkᶜ E δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · 𝟙 · p      ≈˘⟨ ≈ᶜ-refl ∙ +-identityʳ _ ⟩
          ∣ wk1ˢ S ∣ ·ᶜ wkᶜ E δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · 𝟙 · p + 𝟘  ∎) }
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (prodˢₕ₁ {p} {E} {S}) =
    case inv-usage-prodˢ ▸t of λ
      (invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤) →
    case ▸S of λ {
      (_∙_ {γ = η} (fstₑ p≤𝟙) ▸S) →
    _ , _ , _
      , ▸H , ▸-cong (≢𝟘→ᵐ·≡ (λ { refl → 𝟘≰𝟙 p≤𝟙})) ▸t , ▸S
      , (begin
          γ ≤⟨ γ≤ ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η +ᶜ 𝟘ᶜ                 ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η         ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (∧ᶜ-decreasingˡ (p ·ᶜ δ₁) δ₂))) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E (p ·ᶜ δ₁) +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ(wk-≤ᶜ E (·ᶜ-monotoneˡ p≤𝟙))) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E (𝟙 ·ᶜ δ₁) +ᶜ η               ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ E (·ᶜ-identityˡ δ₁))) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ₁ +ᶜ η                      ∎) }
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (prodˢₕ₂ {p} {E} {S}) =
    case inv-usage-prodˢ ▸t of λ
      (invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤) →
    case ▸S of λ {
      (_∙_ {γ = η} sndₑ ▸S) →
    _ , _ , _ , ▸H , ▸u , ▸S
      , (begin
          γ ≤⟨ γ≤ ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ 𝟘ᶜ           ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (∧ᶜ-decreasingʳ (p ·ᶜ δ₁) δ₂))) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ₂ +ᶜ η                       ∎) }
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (prodʷₕ {p} {t₁} {E} {r} {E′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (prodrecₑ {γ = γ′} ▸u r≢𝟘) ▸S) →
    case inv-usage-prodʷ ▸t of λ
      (invUsageProdʷ {δ = δ′} {η = η′} ▸t₁ ▸t₂ δ≤) →
    case (begin
          γ                                                                                                      ≤⟨ γ≤ ⟩
          (∣ S ∣ · r) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′                                                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
          (∣ S ∣ · r) ·ᶜ wkᶜ E (p ·ᶜ δ′ +ᶜ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′                                         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
          (∣ S ∣ · r) ·ᶜ (wkᶜ E (p ·ᶜ δ′) +ᶜ wkᶜ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′                                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ E))) ⟩
          (∣ S ∣ · r) ·ᶜ (p ·ᶜ wkᶜ E δ′ +ᶜ wkᶜ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′                                   ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ (∣ S ∣ · r) _ _) ⟩
          ((∣ S ∣ · r) ·ᶜ p ·ᶜ wkᶜ E δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′                    ≈˘⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-assoc (∣ S ∣ · r) p _)) ⟩
          (((∣ S ∣ · r) · p) ·ᶜ wkᶜ E δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′                   ≈⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-congʳ (·-assoc ∣ S ∣ r p))) ⟩
          ((∣ S ∣ · r · p) ·ᶜ wkᶜ E δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′                     ≈⟨ +ᶜ-comm _ _ ⟩
          (η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkᶜ E δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E η′                     ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
          (η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E η′ +ᶜ (∣ S ∣ · r · p) ·ᶜ wkᶜ E δ′                     ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E η′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkᶜ E δ′                   ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ _)) ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E η′) +ᶜ (∣ S ∣ · r · p + 𝟘) ·ᶜ wkᶜ E δ′               ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ _))) ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E η′) +ᶜ (∣ S ∣ · r · p + (∣ S ∣ · r) · 𝟘) ·ᶜ wkᶜ E δ′ ∎) of λ
      γ≤′ →
    case subst₂ (λ x y → δ′ ⨾ x ▸ᶜ[ ⌞ p ⌟ ] (y , t₁ , E))
           (trans lemma (sym (trans (+-congˡ (·-zeroʳ _)) (+-identityʳ _))))
           lemma
           (▸ᶜ ▸t₁ ≤-refl) of λ
      ▸ᶜt₁ →
    _ , _ , _
      , subₕ ▸H γ≤′ ∙ ▸ᶜt₁ ∙ ▸ᶜ¹ ▸t₂ ≤-refl
      , ▸u , wk-▸ˢ (step (step id)) ▸S
      , ≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-comm η _) (+ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ (step (step id)) S)))
          ∙ trans (·-congʳ (wk-∣S∣ (step (step id)) S)) (sym (+-identityʳ _))
          ∙ trans (·-congʳ (wk-∣S∣ (step (step id)) S)) (sym (+-identityʳ _ ))) }
      where
      open RPo ≤ᶜ-poset
      lemma′ : ∀ m → ⌞ p ⌟ ≡ m → ⌜ m ⌝ · (∣ S ∣ · r · p) ≡ ∣ S ∣ · r · p
      lemma′ 𝟘ᵐ p≡m rewrite ⌞⌟≡𝟘ᵐ→≡𝟘 p≡m =
        trans (·-zeroˡ _) (trans (sym (·-zeroʳ _)) (·-assoc _ _ _))
      lemma′ 𝟙ᵐ _ = ·-identityˡ _
      lemma : ⌜ ⌞ p ⌟ ⌝ · (∣ S ∣ · r · p) ≡ ∣ S ∣ · r · p
      lemma = lemma′ ⌞ p ⌟ refl
  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (zeroₕ {E} {p} {r} {E′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (natrecₑ {γ = γ′} {δ = δ′} ▸z ▸s ▸A) ▸S) →
    _ , _ , _ , ▸H , ▸z , ▸S , (begin
      γ                                                                       ≤⟨ γ≤ ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (inv-usage-zero ▸t))) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkᶜ E 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ) ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ E) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)       ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                            ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                                  ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ E′ (nrᶜ-zero ≤ᶜ-refl))) ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ γ′                                                  ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ E′ γ′ +ᶜ η                                                  ∎) }
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (sucₕ {E} {p} {r} {s} {E′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (natrecₑ {γ = γ′} {δ = δ′} ▸z ▸s ▸A) ▸S) →
    case subst₂ (λ x y → _ ∙ x ∙ y ▸ s) (sym (·-identityˡ p)) (sym (·-identityˡ r)) ▸s of λ
      ▸s′ →
    case inv-usage-suc ▸t of λ
      (invUsageSuc {δ = θ} ▸t δ≤θ) →
    case wk-∣S∣ (step (step id)) S of λ
      ∣S∣≡∣↑²S∣ →
    case natrecₘ
           (wkUsage (step id) ▸z)
           (wkUsage (liftn (step id) 2) ▸s′)
           var
           (wkUsage (lift (step id)) ▸A) of λ
      ▸nr →
    let lemma₃ : ∣ S ∣ ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ) ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)
        lemma₃ = begin
           ∣ S ∣ ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                             ≤⟨ ·ᶜ-monotoneʳ (wk-≤ᶜ E′ nrᶜ-suc) ⟩
           ∣ S ∣ ·ᶜ wkᶜ E′ (δ′ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ)      ≈⟨ ·ᶜ-congˡ (wk-≈ᶜ E′ (+ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ p)))) ⟩
           ∣ S ∣ ·ᶜ wkᶜ E′ (δ′ +ᶜ 𝟘ᶜ +ᶜ r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ)           ≈⟨ ·ᶜ-congˡ (wk-≈ᶜ E′ (+ᶜ-congˡ (+ᶜ-identityˡ _))) ⟩
           ∣ S ∣ ·ᶜ wkᶜ E′ (δ′ +ᶜ r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ)                 ≈⟨ ·ᶜ-congˡ (wk-+ᶜ E′) ⟩
           ∣ S ∣ ·ᶜ (wkᶜ E′ δ′ +ᶜ wkᶜ E′ (r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ))        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
           ∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ (r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ) ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ (wk-·ᶜ E′)) ⟩
           ∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ ∣ S ∣ ·ᶜ r ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)  ≈˘⟨ +ᶜ-congˡ (·ᶜ-assoc _ _ _) ⟩
           ∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ) ∎
        lemma₄ : γ ≤ᶜ ((∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 𝟙) ·ᶜ wkᶜ E θ
        lemma₄ = begin
           γ
             ≤⟨ γ≤ ⟩
           (∣ S ∣ · nr₂ p r) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)
             ≤⟨ +ᶜ-monotone (·ᶜ-monotone (wk-≤ᶜ E δ≤θ) (lemma₂ ∣ S ∣ p r)) (+ᶜ-monotoneʳ lemma₃) ⟩
           (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 𝟙) ·ᶜ wkᶜ E θ +ᶜ η +ᶜ (∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ))
             ≈⟨ +ᶜ-comm _ _ ⟩
           (η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 𝟙) ·ᶜ wkᶜ E θ
             ≈˘⟨ +ᶜ-congʳ (+ᶜ-assoc _ _ _) ⟩
           ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 𝟙) ·ᶜ wkᶜ E θ
             ≈⟨ +ᶜ-congʳ (+ᶜ-congʳ (+ᶜ-comm _ _)) ⟩
           ((∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ E′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 𝟙) ·ᶜ wkᶜ E θ ∎
    in  _ , _ , _
          , subₕ ▸H lemma₄
          ∙ ▸ᶜ¹ ▸t (lemma₂ ∣ S ∣ p r)
          ∙ ▸ᶜ¹ ▸nr ≤-refl
          , ▸s , wk-▸ˢ (step (step id)) ▸S
          , ≤ᶜ-reflexive (+ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡∣↑²S∣))
          ∙ ≤-reflexive (trans (·-congʳ ∣S∣≡∣↑²S∣) (sym (+-identityʳ _)))
          ∙ ≤-reflexive (trans (·-congʳ ∣S∣≡∣↑²S∣) (sym (+-identityʳ _)))}
    where
    lemma₁ : ∀ p r → nr₂ p r ≤ p + r · nr p r 𝟘 𝟘 𝟙
    lemma₁ p r = begin
      nr₂ p r                          ≈˘⟨ ·-identityʳ _ ⟩
      nr₂ p r · 𝟙                     ≈˘⟨ +-identityʳ _ ⟩
      nr₂ p r · 𝟙 + 𝟘                 ≈˘⟨ +-congˡ nr-𝟘 ⟩
      nr₂ p r · 𝟙 + nr p r 𝟘 𝟘 𝟘     ≈˘⟨ nr-factoring ⟩ -- Should this be an inequality?
      nr p r 𝟘 𝟘 𝟙                    ≤⟨ nr-suc ⟩
      𝟘 + p · 𝟙 + r · nr p r 𝟘 𝟘 𝟙   ≈˘⟨ +-assoc _ _ _ ⟩
      (𝟘 + p · 𝟙) + r · nr p r 𝟘 𝟘 𝟙 ≈⟨ +-congʳ (+-comm _ _) ⟩
      (p · 𝟙 + 𝟘) + r · nr p r 𝟘 𝟘 𝟙 ≈⟨ +-assoc _ _ _ ⟩
      p · 𝟙 + 𝟘 + r · nr p r 𝟘 𝟘 𝟙   ≈⟨ +-cong (·-identityʳ p) (+-identityˡ _) ⟩
      p + r · nr p r 𝟘 𝟘 𝟙            ∎
      where
      open RPo ≤-poset
    lemma₂ : ∀ q p r → q · nr₂ p r ≤ q · p + (q · r) · nr p r 𝟘 𝟘 𝟙
    lemma₂ q p r = begin
      q · nr₂ p r                     ≤⟨ ·-monotoneʳ (lemma₁ p r) ⟩
      q · (p + r · nr p r 𝟘 𝟘 𝟙)     ≈⟨ ·-distribˡ-+ q p _ ⟩
      q · p + q · r · nr p r 𝟘 𝟘 𝟙   ≈˘⟨ +-congˡ (·-assoc _ _ _) ⟩
      q · p + (q · r) · nr p r 𝟘 𝟘 𝟙 ∎
      where
      open RPo ≤-poset
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸star , ▸S , γ≤) (starʷₕ {E} {p} {E′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (unitrecₑ {γ = δ′} ▸t _) ▸S) →
    case inv-usage-starʷ ▸star of λ
      δ≤𝟘 →
    _ , _ , _ , ▸H , ▸t , ▸S , (begin
      γ                                                 ≤⟨ γ≤ ⟩
      (∣ S ∣ · p) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤𝟘)) ⟩
      (∣ S ∣ · p) ·ᶜ wkᶜ E 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′ ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ E) ⟩
      (∣ S ∣ · p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′       ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′                      ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′                            ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ η                            ∎) }
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ᵥ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (unitrec-ηₕ {p} {E} {S} η-ok) =
    case inv-usage-unitrec ▸t of λ
      (invUsageUnitrec {δ = δ₁} {η = δ₂} ▸t ▸u _ ok δ≤) →
    _ , _ , _ , ▸H , ▸u , ▸S , (begin
      γ                                  ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
      ∣ S ∣ ·ᶜ wkᶜ E (p ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (+ᶜ-monotoneˡ
                                                        (·ᶜ-monotoneˡ (no-erased-unitrec-η η-ok ok))))) ⟩
      ∣ S ∣ ·ᶜ wkᶜ E (𝟘 ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ E (+ᶜ-congʳ (·ᶜ-zeroˡ δ₁)))) ⟩
      ∣ S ∣ ·ᶜ wkᶜ E (𝟘ᶜ +ᶜ δ₂) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ E (+ᶜ-identityˡ δ₂))) ⟩
      ∣ S ∣ ·ᶜ wkᶜ E δ₂ +ᶜ η              ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (rflₕⱼ {E} {E′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (Jₑ {γ = δ′} ▸u) ▸S) →
    _ , _ , _ , ▸H , ▸u , ▸S , (begin
      γ                                                 ≤⟨ γ≤ ⟩
      (∣ S ∣ · ω) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (inv-usage-rfl ▸t))) ⟩
      (∣ S ∣ · ω) ·ᶜ wkᶜ E 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′ ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ E) ⟩
      (∣ S ∣ · ω) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′       ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′                      ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′                            ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ η                            ∎ )}
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (rflₕₖ {E} {E′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (Kₑ {γ = δ′} ▸u) ▸S) →
    _ , _ , _ , ▸H , ▸u , ▸S , (begin
      γ                                                  ≤⟨ γ≤ ⟩
      (∣ S ∣ · ω) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (inv-usage-rfl ▸t))) ⟩
      (∣ S ∣ · ω) ·ᶜ wkᶜ E 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′  ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ E) ⟩
      (∣ S ∣ · ω) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′        ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′                       ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E′ δ′                             ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ E′ δ′ +ᶜ η                             ∎ )}
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ᵥ (▸H , ▸t , ▸S , γ≤) rflₕₑ =
    case ▸S of λ {(() ∙ _)}

opaque

  ▸-⇒ₙ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ₙ s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒ₙ ▸s (varₕ′ d) = ⊥-elim not-tracking-and-no-tracking
  ▸-⇒ₙ {(m)} {γ} {δ} {η} (▸H , ▸x , ▸S , γ≤) (varₕ {E} {x} {S} {E′} d) =
    case ▸-heapLookup d ▸H lemma₂ (▸∣S∣≢𝟘 ▸S) of λ
      (δ′ , ▸t , ▸H′) →
    _ , _ , _
      , ▸H′ , ▸t , ▸S
      , let open RPo ≤ᶜ-poset
            Eδ′ = wkᶜ E′ δ′
        in  begin
          (γ , x′ ≔ η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ Eδ′
            ≤⟨ +ᶜ-monotoneˡ (update-monotoneˡ x′ lemma₁) ⟩
          ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η , x′ ≔ η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ Eδ′
            ≈˘⟨ +ᶜ-congʳ (update-congʳ (+-identityˡ _)) ⟩
          ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η , x′ ≔ 𝟘 + η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ Eδ′
            ≡⟨ cong (_+ᶜ (∣S∣ ·ᶜ Eδ′)) (update-distrib-+ᶜ _ η 𝟘 _ x′) ⟩
          (((𝟘ᶜ , x′ ≔ ∣S∣) , x′ ≔ 𝟘) +ᶜ (η , x′ ≔ η ⟨ x′ ⟩)) +ᶜ ∣S∣ ·ᶜ Eδ′
            ≡⟨ cong₂ (λ x y → (x +ᶜ y) +ᶜ (∣S∣ ·ᶜ Eδ′)) update-twice (update-self η x′) ⟩
          ((𝟘ᶜ , x′ ≔ 𝟘) +ᶜ η) +ᶜ ∣S∣ ·ᶜ Eδ′
            ≡⟨ cong (λ x → (x +ᶜ η) +ᶜ (∣S∣ ·ᶜ Eδ′)) 𝟘ᶜ,≔𝟘 ⟩
          (𝟘ᶜ +ᶜ η) +ᶜ ∣S∣ ·ᶜ Eδ′
            ≈⟨ +ᶜ-congʳ (+ᶜ-identityˡ η) ⟩
          η +ᶜ ∣S∣ ·ᶜ Eδ′
            ≈⟨ +ᶜ-comm η _ ⟩
          ∣S∣ ·ᶜ Eδ′ +ᶜ η ∎
    where
    x′ : Ptr m
    x′ = wkVar E x
    Eδ : Conₘ m
    Eδ = wkᶜ E δ
    ∣S∣ : M
    ∣S∣ = ∣ S ∣
    lemma₁ : γ ≤ᶜ (𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η
    lemma₁ = begin
      γ                                 ≤⟨ γ≤ ⟩
      ∣S∣ ·ᶜ Eδ +ᶜ η                    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (inv-usage-var ▸x))) ⟩
      ∣S∣ ·ᶜ wkᶜ E (𝟘ᶜ , x ≔ 𝟙) +ᶜ η ≡⟨ cong (λ x → ∣S∣ ·ᶜ x +ᶜ η) (wkUsageVar E x) ⟩
      ∣S∣ ·ᶜ (𝟘ᶜ , x′ ≔ 𝟙) +ᶜ η         ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ 𝟘ᶜ ∣S∣ 𝟙 x′) ⟩
      (∣S∣ ·ᶜ 𝟘ᶜ , x′ ≔ ∣S∣ · 𝟙) +ᶜ η   ≈⟨ +ᶜ-congʳ (update-cong (·ᶜ-zeroʳ ∣S∣) (·-identityʳ ∣S∣)) ⟩
      (𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η              ∎
      where
      open RPo ≤ᶜ-poset
    lemma₂ : γ ⟨ x′ ⟩ - ∣S∣ ≤ η ⟨ x′ ⟩
    lemma₂ = begin
      γ ⟨ x′ ⟩                        ≤⟨ lookup-monotone x′ lemma₁ ⟩
      ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η) ⟨ x′ ⟩     ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , x′ ≔ ∣S∣) η x′ ⟩
      (𝟘ᶜ , x′ ≔ ∣S∣) ⟨ x′ ⟩ + η ⟨ x′ ⟩  ≡⟨ cong (_+ η ⟨ x′ ⟩) (update-lookup 𝟘ᶜ x′) ⟩
      ∣S∣ + η ⟨ x′ ⟩                    ≈⟨ +-comm ∣S∣ _ ⟩
      η ⟨ x′ ⟩ + ∣S∣                    ∎
      where
      open RPo ≤-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (appₕ {p} {E} {S}) =
    case inv-usage-app ▸t of λ
      (invUsageApp {δ = δ′} {(η′)} ▸t ▸u δ≤) →
    _ , _ , _
      , ▸H , ▸t
      , ∘ₑ ▸u ∙ ▸S
      , (begin
        γ                                                      ≤⟨ γ≤ ⟩
        ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
        ∣ S ∣ ·ᶜ wkᶜ E (δ′ +ᶜ p ·ᶜ η′) +ᶜ η                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
        ∣ S ∣ ·ᶜ (wkᶜ E δ′ +ᶜ wkᶜ E (p ·ᶜ η′)) +ᶜ η             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (wk-·ᶜ E))) ⟩
        ∣ S ∣ ·ᶜ (wkᶜ E δ′ +ᶜ p ·ᶜ wkᶜ E η′) +ᶜ η               ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
        (∣ S ∣ ·ᶜ wkᶜ E δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ E η′) +ᶜ η      ≈⟨ +ᶜ-assoc _ _ _ ⟩
        ∣ S ∣ ·ᶜ wkᶜ E δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ E η′ +ᶜ η       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-comm _ _) ⟩
        (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ E η′ ∎)
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (fstₕ {E} {S}) =
    case inv-usage-fst ▸t of λ
      (invUsageFst {δ = δ′} m eq ▸t δ≤ mp-cond) →
    _ , _ , _
      , ▸H , ▸t , fstₑ (mp-cond refl) ∙ ▸S
      , (begin
          γ                                           ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ′ +ᶜ η                      ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ 𝟘ᶜ          ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (sndₕ {E} {S}) =
    case inv-usage-snd ▸t of λ
      (invUsageSnd {δ = δ′} ▸t δ≤) →
   _ , _ , _ , ▸H , ▸t , sndₑ ∙ ▸S
     , (begin
         γ                                            ≤⟨ γ≤ ⟩
         ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E δ′ +ᶜ η                       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
         (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ 𝟘ᶜ           ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)
   where
   open RPo ≤ᶜ-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (prodrecₕ {r} {p} {u} {E} {S}) =
    case inv-usage-prodrec ▸t of λ
      (invUsageProdrec {δ = δ′} {η = η′} ▸t ▸u _ ok δ≤) →
    case subst₂ (λ x y → _ ∙ x ∙ y ▸ u)
           (·-identityˡ (r · p))
           (·-identityˡ r) ▸u of λ
      ▸u′ →
    case no-erased-prodrec ok of
      λ r≢𝟘 →
    _ , _ , _
      , ▸H , ▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t
      , prodrecₑ ▸u′ r≢𝟘 ∙ ▸S
      , (begin
         γ                                                   ≤⟨ γ≤ ⟩
         ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (r ·ᶜ δ′ +ᶜ η′) +ᶜ η                  ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
         ∣ S ∣ ·ᶜ (wkᶜ E (r ·ᶜ δ′) +ᶜ wkᶜ E η′) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ ∣ S ∣ _ _) ⟩
         (∣ S ∣ ·ᶜ wkᶜ E (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkᶜ E η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkᶜ E η′ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ E)) (+ᶜ-comm _ η) ⟩
         ∣ S ∣ ·ᶜ r ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E η′     ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc ∣ S ∣ r _) ⟩
         (∣ S ∣ · r) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E η′    ∎)
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (natrecₕ {p} {r} {s} {E} {S}) =
    case inv-usage-natrec ▸t of λ {
      (invUsageNatrec {δ = δ′} {η = η′} {θ} ▸z ▸s ▸n ▸A δ≤nr P) →
    case subst₂ (λ x y → _ ∙ x ∙ y ▸ s) (·-identityˡ p) (·-identityˡ r) ▸s of λ
      ▸s′ →
    case P of λ {
      (invUsageNatrecNoNr _ _ _ _) → ⊥-elim not-nr-and-no-nr ;
      (invUsageNatrecNr ⦃ (d-nr) ⦄) →
    case Dedicated-nr-propositional d-nr dedicatedNr of λ {
      refl →
    _ , _ , _ , ▸H , ▸n , natrecₑ ▸z ▸s′ ▸A ∙ ▸S , (begin
      γ                                                                        ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                                                    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤nr)) ⟩
      ∣ S ∣ ·ᶜ wkᶜ E (nrᶜ p r δ′ η′ θ) +ᶜ η                                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ E nrᶜ-factoring)) ⟩
      ∣ S ∣ ·ᶜ wkᶜ E (nr₂ p r ·ᶜ θ +ᶜ nrᶜ p r δ′ η′ 𝟘ᶜ) +ᶜ η                    ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
      ∣ S ∣ ·ᶜ (wkᶜ E (nr₂ p r ·ᶜ θ) +ᶜ wkᶜ E (nrᶜ p r δ′ η′ 𝟘ᶜ)) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
      (∣ S ∣ ·ᶜ wkᶜ E (nr₂ p r ·ᶜ θ) +ᶜ ∣ S ∣ ·ᶜ wkᶜ E (nrᶜ p r δ′ η′ 𝟘ᶜ)) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ E (nr₂ p r ·ᶜ θ) +ᶜ ∣ S ∣ ·ᶜ wkᶜ E (nrᶜ p r δ′ η′ 𝟘ᶜ) +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ E)) (+ᶜ-comm _ _) ⟩
      ∣ S ∣ ·ᶜ (nr₂ p r ·ᶜ wkᶜ E θ) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E (nrᶜ p r δ′ η′ 𝟘ᶜ)   ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkᶜ E θ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E (nrᶜ p r δ′ η′ 𝟘ᶜ) ∎)}}}
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (unitrecₕ {p} {E} {S} no-η) =
    case inv-usage-unitrec ▸t of λ
      (invUsageUnitrec {δ = δ′} {η = η′} ▸t ▸u _ ok δ≤) →
    case no-erased-unitrec no-η ok of λ
      p≢𝟘 →
    _ , _ , _ , ▸H
      , ▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t
      , unitrecₑ ▸u p≢𝟘 ∙ ▸S
      , (begin
          γ                                                  ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                              ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ E (p ·ᶜ δ′ +ᶜ η′) +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
          ∣ S ∣ ·ᶜ (wkᶜ E (p ·ᶜ δ′) +ᶜ wkᶜ E η′) +ᶜ η        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ E))) ⟩
          ∣ S ∣  ·ᶜ (p ·ᶜ wkᶜ E δ′ +ᶜ wkᶜ E η′) +ᶜ η         ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          (∣ S ∣ ·ᶜ p ·ᶜ wkᶜ E δ′ +ᶜ ∣ S ∣ ·ᶜ wkᶜ E η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
          ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ E δ′ +ᶜ ∣ S ∣ ·ᶜ wkᶜ E η′ +ᶜ η   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
          (∣ S ∣ · p) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E η′  ∎)
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (Jₕ {E} {S}) =
    case inv-usage-J ▸t of λ {
      (invUsageJ₀₁ e _ _ _ _ _ _ _ _ _) → ⊥-elim (no-erased-J-some e) ;
      (invUsageJ₀₂ e _ _ _ _ _ _ _) → ⊥-elim (no-erased-J-all e) ;
      (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ _ _ _ ▸u _ ▸w δ≤) →
        _ , _ , _ , ▸H , ▸w , Jₑ ▸u ∙ ▸S , (begin
         γ                                                         ≤⟨ γ≤ ⟩
         ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (ω ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ E (·ᶜ-distribˡ-+ᶜ ω _ _))) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (ω ·ᶜ γ₄ +ᶜ ω ·ᶜ (γ₅ +ᶜ γ₆)) +ᶜ η           ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E (+ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ))) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (ω ·ᶜ γ₄ +ᶜ ω ·ᶜ γ₆) +ᶜ η                   ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ E)) ⟩
         ∣ S ∣ ·ᶜ (wkᶜ E (ω ·ᶜ γ₄) +ᶜ wkᶜ E (ω ·ᶜ γ₆)) +ᶜ η         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-cong (wk-·ᶜ E) (wk-·ᶜ E))) ⟩
         ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ E γ₄ +ᶜ ω ·ᶜ wkᶜ E γ₆) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneˡ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
         ∣ S ∣ ·ᶜ (𝟙 ·ᶜ wkᶜ E γ₄ +ᶜ ω ·ᶜ wkᶜ E γ₆) +ᶜ η             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _))) ⟩
         ∣ S ∣ ·ᶜ (wkᶜ E γ₄ +ᶜ ω ·ᶜ wkᶜ E γ₆) +ᶜ η                  ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
         (∣ S ∣ ·ᶜ wkᶜ E γ₄ +ᶜ ∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ E γ₆) +ᶜ η         ≈⟨ +ᶜ-congʳ (+ᶜ-comm _ _) ⟩
         (∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ E γ₆ +ᶜ ∣ S ∣ ·ᶜ wkᶜ E γ₄) +ᶜ η         ≈⟨ +ᶜ-assoc _ _ _ ⟩
         ∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ E γ₆ +ᶜ ∣ S ∣ ·ᶜ wkᶜ E γ₄ +ᶜ η           ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
         (∣ S ∣ · ω) ·ᶜ wkᶜ E γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E γ₄          ∎) }
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (Kₕ {E} {S}) =
    case inv-usage-K ▸t of λ {
      (invUsageK₀₁ e _ _ _ _ _ _ _) → ⊥-elim (no-erased-K-some e) ;
      (invUsageK₀₂ e _ _ _ _ _ _) → ⊥-elim (no-erased-K-all e) ;
      (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} _ _ _ _ _ ▸u ▸v δ≤) →
        _ , _ , _ , ▸H , ▸v , Kₑ ▸u ∙ ▸S , (begin
         γ                                                         ≤⟨ γ≤ ⟩
         ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)) +ᶜ η          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅)) +ᶜ η                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ E (ω ·ᶜ (γ₄ +ᶜ γ₅)) +ᶜ η                      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ E)) ⟩
         ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ E (γ₄ +ᶜ γ₅)) +ᶜ η                      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-congˡ (wk-≈ᶜ E (+ᶜ-comm _ _)))) ⟩
         ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ E (γ₅ +ᶜ γ₄)) +ᶜ η                      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-congˡ (wk-+ᶜ E))) ⟩
         ∣ S ∣ ·ᶜ (ω ·ᶜ (wkᶜ E γ₅ +ᶜ wkᶜ E γ₄)) +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
         ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ E γ₅ +ᶜ ω ·ᶜ wkᶜ E γ₄) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
         ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ E γ₅ +ᶜ 𝟙 ·ᶜ wkᶜ E γ₄) +ᶜ η             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-identityˡ _))) ⟩
         ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ E γ₅ +ᶜ wkᶜ E γ₄) +ᶜ η                  ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
         (∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ E γ₅ +ᶜ ∣ S ∣ ·ᶜ wkᶜ E γ₄) +ᶜ η         ≈⟨ +ᶜ-assoc _ _ _ ⟩
         ∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ E γ₅ +ᶜ ∣ S ∣ ·ᶜ wkᶜ E γ₄ +ᶜ η           ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
         (∣ S ∣ · ω) ·ᶜ wkᶜ E γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ E γ₄     ∎) }
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) []-congₕ =
    case inv-usage-[]-cong ▸t of λ
      (invUsage-[]-cong _ _ _ _ ok _) →
    ⊥-elim (no-[]-cong ok)


opaque

  ▸-⇒ₛ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ₛ s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒ₛ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (sucₕ {E} {k} x) =
    case inv-usage-suc ▸t of λ
      (invUsageSuc {δ = δ′} ▸t δ≤) →
    _ , _ , _ , ▸H , ▸t , sucₑ ∙ ▸S , (begin
      γ ≤⟨ γ≤ ⟩
      ∣ sucₛ k ∣ ·ᶜ wkᶜ E δ +ᶜ η                            ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ E δ≤)) ⟩
      ∣ sucₛ k ∣ ·ᶜ wkᶜ E δ′ +ᶜ η                           ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
      (∣ sucₛ k ∣ · 𝟙) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ 𝟘ᶜ               ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      (∣ sucₛ k ∣ · 𝟙) ·ᶜ wkᶜ E δ′ +ᶜ η +ᶜ ∣ sucₛ k ∣ ·ᶜ 𝟘ᶜ ∎)
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₛ {γ} {δ} (▸H , ▸t , _∙_ {γ = η} ▸e ▸S , γ≤) (numₕ {E} {S} x) =
    case ▸e of λ {
      sucₑ →
    _ , _ , _ , ▸H , sucₘ ▸t , ▸S , (begin
      γ                                          ≤⟨ γ≤ ⟩
      (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      (∣ S ∣ · 𝟙) ·ᶜ wkᶜ E δ +ᶜ η +ᶜ 𝟘ᶜ          ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
      ∣ S ∣ ·ᶜ wkᶜ E δ +ᶜ η                      ∎) }
    where
    open RPo ≤ᶜ-poset


opaque

  -- Well-resourced states evaluate to well-resourced states

  ▸-⇒ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒ ▸s (⇒ₙ d) = ▸-⇒ₙ ▸s d
  ▸-⇒ ▸s (⇒ᵥ d) = ▸-⇒ᵥ ▸s d
  ▸-⇒ ▸s (⇒ₛ d) = ▸-⇒ₛ ▸s d

opaque

  ▸-⇒* : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒* s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒* ▸s id =
    _ , _ , _ , ▸s
  ▸-⇒* ▸s (d ⇨ d′) =
    case ▸-⇒ ▸s d of λ
      (_ , _ , _ , ▸s′) →
    ▸-⇒* ▸s′ d′
