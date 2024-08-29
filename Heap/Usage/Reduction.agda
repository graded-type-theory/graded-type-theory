------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States
-- and the reduction relation with resource tracking.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Heap.Options
open import Definition.Typed.Variant
open import Tools.Bool
import Graded.Mode

module Heap.Usage.Reduction
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (erased-heap : Bool)
  (opts : Options)
  (open Type-variant type-variant)
  (open Usage-restrictions UR)
  (open Graded.Mode 𝕄)
  (open Options opts)
  (open Modality 𝕄)
  (Unitʷ-η→ : ∀ {p q} → Unitʷ-η → Unitrec-allowed 𝟙ᵐ p q → p ≤ 𝟘)
  ⦃ _ : Track-resources ⦄
  ⦃ nr-avail : Nr-available ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦃ has-nr nr-avail ⦄ ⦄
  ⦃ _ : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open import Graded.Modality.Dedicated-nr 𝕄

private instance
  _ : Has-nr M semiring-with-meet
  _ = has-nr nr-avail

  d-nr : Dedicated-nr
  d-nr = dedicated-nr nr-avail

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit
import Tools.Reasoning.PartialOrder as RPo

open import Definition.Untyped M

open import Heap.Untyped type-variant UR
open import Heap.Untyped.Properties type-variant UR
open import Heap.Reduction type-variant UR opts
open import Heap.Usage type-variant UR erased-heap
open import Heap.Usage.Properties type-variant UR erased-heap
open import Heap.Usage.Weakening type-variant UR erased-heap

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

private variable
  γ δ η : Conₘ _
  s s′ : State _ _ _
  m : Mode
  A B t u v w : Term _
  p q : M
  ρ : Wk _ _
  H : Heap _ _
  S : Stack _


opaque

  ▸-⇒ᵥ : (▸s : γ ⨾ δ ⨾ η ▸[ m ] s) (d : s ⇒ᵥ s′) → ∃₄ (_⨾_⨾_▸[_] s′)
  ▸-⇒ᵥ {δ} {m} (▸H , ▸t , ▸S , m≤ , γ≤) (lamₕ {p} {ρ} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (∘ₑ {γ = γ′} ▸u , m′≤) ▸S) →
    case inv-usage-lam ▸t of λ
      (invUsageLam {δ = δ′} ▸t δ≤) →
    _ , _ , _ , _
      , subₕ ▸H (≤ᶜ-trans γ≤
           (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-congʳ (·-identityʳ _)))
             (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-assoc _ _ _))
               (+ᶜ-assoc _ _ _))))))
      ∙ ▸ᶜᵐᵖ ▸u m′≤
      , ▸t , wk-▸ˢ (step id) ▸S
      , subst (_ ≤ᵐ_) (trans (·-identityʳ _) (wk-∣S∣ (step id) S)) m≤
      , (begin
          ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η ∙ ∣ S ∣ · p                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ∙ ≤-refl ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η ∙ ∣ S ∣ · p                      ≈˘⟨ ≈ᶜ-refl ∙ ·-congʳ (·-identityʳ _) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η ∙ (∣ S ∣ · 𝟙) · p                ≈˘⟨ ≈ᶜ-refl ∙ ·-congʳ (≤ᵐ-·⌜⌝ m≤) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η ∙ ((∣ S ∣ · 𝟙) · ⌜ m ⌝) · p      ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (·-congʳ (·-identityʳ _)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η ∙ (∣ S ∣ · ⌜ m ⌝) · p            ≈⟨ ≈ᶜ-refl ∙ ·-assoc _ _ _ ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η ∙ ∣ S ∣ · ⌜ m ⌝ · p              ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ (step id) S)) ∙ ·-congʳ (wk-∣S∣ (step id) S) ⟩
          ∣ wk1ˢ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · ⌜ m ⌝ · p     ≈˘⟨ ≈ᶜ-refl ∙ +-identityʳ _ ⟩
          ∣ wk1ˢ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · ⌜ m ⌝ · p + 𝟘 ∎ )}
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} {m} (▸H , ▸t , _∙_ {m = m′} {γ = η} (▸e , m′≤) ▸S , m≤ , γ≤) (prodˢₕ₁ {p} {ρ} {S}) =
    case inv-usage-prodˢ ▸t of λ
      (invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤) →
    case ▸e of λ {
      (fstₑ mp-cond) →
    _ , _ , _ , _ , ▸H , ▸t , ▸S
      , (case singleton m of λ {
          (𝟘ᵐ , refl) →
          subst (_ ≤ᵐ_) (·-identityʳ _) m≤
        , lemma (trans (sym (·-identityʳ _)) (𝟘ᵐ≤ᵐp→p≡𝟘 m≤))
          ;
          (𝟙ᵐ , refl) →
         case singleton m′ of λ {
           (𝟘ᵐ , refl) →
           subst (_ ≤ᵐ_) (sym (𝟘ᵐ≤ᵐp→p≡𝟘 m′≤)) ≤ᵐ𝟘
         , lemma (𝟘ᵐ≤ᵐp→p≡𝟘 m′≤)
           ;
           (𝟙ᵐ , refl) →
           subst (_≤ᵐ _) (sym (≢𝟘→⌞⌟≡𝟙ᵐ λ {refl → 𝟘≰𝟙 (mp-cond refl)})) 𝟙ᵐ≤ᵐ
         , (begin
             γ                                          ≤⟨ γ≤ ⟩
             (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
             ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ 𝟘ᶜ                ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
             ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
             ∣ S ∣ ·ᶜ wkᶜ ρ (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (∧ᶜ-decreasingˡ _ _))) ⟩
             ∣ S ∣ ·ᶜ wkᶜ ρ (p ·ᶜ δ₁) +ᶜ η              ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (·ᶜ-monotoneˡ (mp-cond refl)))) ⟩
             ∣ S ∣ ·ᶜ wkᶜ ρ (𝟙 ·ᶜ δ₁) +ᶜ η              ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-identityˡ _))) ⟩
             ∣ S ∣ ·ᶜ wkConₘ ρ δ₁ +ᶜ η ∎ )}})}
    where
    open RPo ≤ᶜ-poset
    lemma : ∀ {δ′} → ∣ S ∣ ≡ 𝟘 → γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η
    lemma {δ′} ∣S∣≡𝟘 = begin
      γ                                          ≤⟨ γ≤ ⟩
      (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ _  ≡⟨ cong (λ x → (x · 𝟙) ·ᶜ _ +ᶜ _ +ᶜ x ·ᶜ _) ∣S∣≡𝟘 ⟩
      (𝟘 · 𝟙) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ 𝟘 ·ᶜ _         ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (+ᶜ-congˡ (·ᶜ-zeroˡ _)) ⟩
      𝟘 ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ 𝟘ᶜ                   ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-identityʳ _) ⟩
      𝟘ᶜ +ᶜ η                                   ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘 ·ᶜ wkᶜ ρ δ′ +ᶜ η                        ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡𝟘) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η                    ∎

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , m≤ , γ≤) (prodˢₕ₂ {p} {ρ} {S}) =
    case inv-usage-prodˢ ▸t of λ
      (invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤) →
    case ▸S of λ {
      (_∙_ {γ = η} (sndₑ , m′≤) ▸S) →
    _ , _ , _ , _ , ▸H , ▸u , ▸S
      , subst (_ ≤ᵐ_) (·-identityʳ _) m≤
      , (begin
          γ ≤⟨ γ≤ ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ 𝟘ᶜ           ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (∧ᶜ-decreasingʳ (p ·ᶜ δ₁) δ₂))) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ₂ +ᶜ η                       ∎) }
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , m≤ , γ≤) (prodʷₕ {p} {t₁} {ρ} {r} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (prodrecₑ {γ = γ′} ▸u r≢𝟘 , m′≤) ▸S) →
    case inv-usage-prodʷ ▸t of λ
      (invUsageProdʷ {δ = δ′} {η = η′} ▸t₁ ▸t₂ δ≤) →
    let γ≤′ : γ ≤ᶜ ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′) +ᶜ (∣ S ∣ · r · p + (∣ S ∣ · r) · 𝟘) ·ᶜ wkᶜ ρ δ′
        γ≤′ = begin
          γ                                                                                                      ≤⟨ γ≤ ⟩
          (∣ S ∣ · r) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′                                                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          (∣ S ∣ · r) ·ᶜ wkᶜ ρ (p ·ᶜ δ′ +ᶜ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′                                         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
          (∣ S ∣ · r) ·ᶜ (wkᶜ ρ (p ·ᶜ δ′) +ᶜ wkᶜ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′                                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ ρ))) ⟩
          (∣ S ∣ · r) ·ᶜ (p ·ᶜ wkᶜ ρ δ′ +ᶜ wkᶜ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′                                   ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ (∣ S ∣ · r) _ _) ⟩
          ((∣ S ∣ · r) ·ᶜ p ·ᶜ wkᶜ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′                    ≈˘⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-assoc (∣ S ∣ · r) p _)) ⟩
          (((∣ S ∣ · r) · p) ·ᶜ wkᶜ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′                   ≈⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-congʳ (·-assoc ∣ S ∣ r p))) ⟩
          ((∣ S ∣ · r · p) ·ᶜ wkᶜ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′                     ≈⟨ +ᶜ-comm _ _ ⟩
          (η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkᶜ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′                     ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
          (η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′ +ᶜ (∣ S ∣ · r · p) ·ᶜ wkᶜ ρ δ′                     ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkᶜ ρ δ′                   ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ _)) ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′) +ᶜ (∣ S ∣ · r · p + 𝟘) ·ᶜ wkᶜ ρ δ′               ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ _))) ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ η′) +ᶜ (∣ S ∣ · r · p + (∣ S ∣ · r) · 𝟘) ·ᶜ wkᶜ ρ δ′ ∎
        ▸ᶜt₁ = subst₂ (λ x y → (_ ⨾ x ▸ᶜ (y , _)))
                (trans (·-assoc _ _ _) (sym (trans (+-congˡ (·-zeroʳ _)) (+-identityʳ _))))
                (·-assoc _ _ _) (▸ᶜᵐᵖ ▸t₁ m≤)
    in  _ , _ , _ , _
          , subₕ ▸H γ≤′ ∙ ▸ᶜt₁ ∙ ▸ᶜᵐ ▸t₂ m≤
          , ▸u , wk-▸ˢ (step (step id)) ▸S
          , subst (_ ≤ᵐ_) (wk-∣S∣ (step (step id)) S) m′≤
          , ≤ᶜ-reflexive ((≈ᶜ-trans (+ᶜ-comm η _) (+ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ (step (step id)) S))))
              ∙ trans (·-congʳ (sym (≤ᵐ-·⌜⌝ m′≤))) (trans (·-assoc _ _ _)
                 (trans (·-congʳ (wk-∣S∣ (step (step id)) S)) (sym (+-identityʳ _))))
              ∙ trans (·-congʳ (sym (≤ᵐ-·⌜⌝ m′≤))) (trans (·-assoc _ _ _)
                  (trans (·-congʳ (wk-∣S∣ (step (step id)) S)) (sym (+-identityʳ _))))) }
      where
      open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , m≤ , γ≤) (zeroₕ {ρ} {p} {r} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (natrecₑ {γ = γ′} {δ = δ′} ▸z ▸s ▸A , m′≤) ▸S) →
    _ , _ , _ , _ , ▸H , ▸z , ▸S , m′≤ , (begin
      γ                                                                       ≤⟨ γ≤ ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-zero ▸t))) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkᶜ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ) ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)       ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                            ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                                  ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ′ (nrᶜ-zero ≤ᶜ-refl))) ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′                                                  ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ′ γ′ +ᶜ η                                                  ∎) }
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , m≤ , γ≤) (sucₕ {ρ} {p} {r} {s} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (natrecₑ {γ = γ′} {m} {δ = δ′} ▸z ▸s ▸A , m′≤) ▸S) →
    case inv-usage-suc ▸t of λ
      (invUsageSuc {δ = θ} ▸t δ≤θ) →
    case wk-∣S∣ (step (step id)) S of λ
      ∣S∣≡∣↑²S∣ →
    case natrecₘ
           (wkUsage (step id) ▸z)
           (wkUsage (liftn (step id) 2) ▸s)
           (var {x = x0})
           (wkUsage (lift (step id)) ▸A) of λ
      ▸nr →
    let lemma₄ : ∣ S ∣ ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ) ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)
        lemma₄ = begin
           ∣ S ∣ ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                             ≤⟨ ·ᶜ-monotoneʳ (wk-≤ᶜ ρ′ nrᶜ-suc) ⟩
           ∣ S ∣ ·ᶜ wkᶜ ρ′ (δ′ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ)      ≈⟨ ·ᶜ-congˡ (wk-≈ᶜ ρ′ (+ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-zeroʳ p)))) ⟩
           ∣ S ∣ ·ᶜ wkᶜ ρ′ (δ′ +ᶜ 𝟘ᶜ +ᶜ r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ)           ≈⟨ ·ᶜ-congˡ (wk-≈ᶜ ρ′ (+ᶜ-congˡ (+ᶜ-identityˡ _))) ⟩
           ∣ S ∣ ·ᶜ wkᶜ ρ′ (δ′ +ᶜ r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ)                 ≈⟨ ·ᶜ-congˡ (wk-+ᶜ ρ′) ⟩
           ∣ S ∣ ·ᶜ (wkᶜ ρ′ δ′ +ᶜ wkᶜ ρ′ (r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ))        ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
           ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ (r ·ᶜ  nrᶜ p r γ′ δ′ 𝟘ᶜ) ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ (wk-·ᶜ ρ′)) ⟩
           ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ ∣ S ∣ ·ᶜ r ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)  ≈˘⟨ +ᶜ-congˡ (·ᶜ-assoc _ _ _) ⟩
           ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ) ∎
        lemma₅ : γ ≤ᶜ ((∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 ⌜ m ⌝) ·ᶜ wkᶜ ρ θ
        lemma₅ = begin
           γ
             ≤⟨ γ≤ ⟩
           (∣ S ∣ · nr₂ p r) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)
             ≤⟨ +ᶜ-monotone (·ᶜ-monotone (wk-≤ᶜ ρ δ≤θ) (lemma₃ ∣ S ∣ p r m′≤)) (+ᶜ-monotoneʳ lemma₄) ⟩
           (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 ⌜ m ⌝) ·ᶜ wkᶜ ρ θ +ᶜ η +ᶜ (∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ))
             ≈⟨ +ᶜ-comm _ _ ⟩
           (η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 ⌜ m ⌝) ·ᶜ wkᶜ ρ θ
             ≈˘⟨ +ᶜ-congʳ (+ᶜ-assoc _ _ _) ⟩
           ((η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 ⌜ m ⌝) ·ᶜ wkᶜ ρ θ
             ≈⟨ +ᶜ-congʳ (+ᶜ-congʳ (+ᶜ-comm _ _)) ⟩
           ((∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ wkᶜ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · nr p r 𝟘 𝟘 ⌜ m ⌝) ·ᶜ wkᶜ ρ θ ∎
        lemma₆ : ∀ q → ∣ S ∣ · q ≡ ∣ wk2ˢ S ∣ · ⌜ m ⌝ · q + 𝟘
        lemma₆ _ = trans (·-congʳ (sym (≤ᵐ-·⌜⌝ m′≤)))
                     (trans (·-assoc _ _ _) (trans (·-congʳ ∣S∣≡∣↑²S∣)
                       (sym (+-identityʳ _))))
    in  _ , _ , _ , _
          , subₕ ▸H lemma₅
          ∙ subᶜ (▸ᶜᵐ ▸t m≤) (lemma₃ ∣ S ∣ p r m′≤)
          ∙ subst (λ x → nrᶜ p r (γ′ ∙ 𝟘) (δ′ ∙ 𝟘) (𝟘ᶜ ∙ ⌜ m ⌝) ⨾ ∣ S ∣ · r ▸ᶜ
                         (x , natrec p _ r _ _ _ _ , lift ρ′))
              (trans (sym (·-assoc _ _ _)) (·-congʳ (≤ᵐ-⌜⌝· m′≤)))
              (▸ᶜ ▸nr (≤-reflexive (trans (sym (·-assoc _ _ _)) (·-congʳ (≤ᵐ-⌜⌝· m′≤)))))
          , ▸s , wk-▸ˢ (step (step id)) ▸S
          , subst (_ ≤ᵐ_) ∣S∣≡∣↑²S∣ m′≤
          , ≤ᶜ-reflexive (+ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡∣↑²S∣))
          ∙ ≤-reflexive (lemma₆ p)
          ∙ ≤-reflexive (lemma₆ r) }
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
    lemma₃ : ∀ q p r → m ≤ᵐ q → q · nr₂ p r ≤ q · p + (q · r) · nr p r 𝟘 𝟘 ⌜ m ⌝
    lemma₃ q p r 𝟙ᵐ≤ᵐ = lemma₂ q p r
    lemma₃ _ p r 𝟘ᵐ≤ᵐ𝟘 = begin
      𝟘 · nr₂ p r                     ≈⟨ ·-zeroˡ _ ⟩
      𝟘                               ≈˘⟨ +-identityʳ 𝟘 ⟩
      𝟘 + 𝟘                           ≈˘⟨ +-cong (·-zeroˡ p) (·-zeroˡ _) ⟩
      𝟘 · p + 𝟘 · r · nr p r 𝟘 𝟘 𝟘   ≈˘⟨ +-congˡ (·-assoc _ _ _) ⟩
      𝟘 · p + (𝟘 · r) · nr p r 𝟘 𝟘 𝟘 ∎
      where
      open RPo ≤-poset
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸star , ▸S , m≤ , γ≤) (starʷₕ {ρ} {p} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (unitrecₑ {γ = δ′} ▸t _ _ , m′≤) ▸S) →
    case inv-usage-starʷ ▸star of λ
      δ≤𝟘 →
    _ , _ , _ , _ , ▸H , ▸t , ▸S , m′≤ , (begin
      γ                                                 ≤⟨ γ≤ ⟩
      (∣ S ∣ · p) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤𝟘)) ⟩
      (∣ S ∣ · p) ·ᶜ wkᶜ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′       ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′                      ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′                            ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ η                            ∎) }
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (unitrec-ηₕ {p} {ρ} {S} η-ok) =
    case inv-usage-unitrec ▸t of λ
      (invUsageUnitrec {δ = δ₁} {η = δ₂} ▸t ▸u _ ok δ≤) →
    _ , _ , _ , _ , ▸H , ▸u , ▸S , m≤ , lemma _ m≤ δ≤ ok
    where
    open RPo ≤ᶜ-poset
    lemma : ∀ {δ₁ δ₂} m → m ≤ᵐ ∣ S ∣ → δ ≤ᶜ p ·ᶜ δ₁ +ᶜ δ₂
          → Unitrec-allowed m p q
          → γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ₂ +ᶜ η
    lemma {δ₂} 𝟘ᵐ m≤ δ≤ ok = begin
      γ                      ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (𝟘ᵐ≤ᵐp→p≡𝟘 m≤)) ⟩
      𝟘 ·ᶜ wkᶜ ρ δ +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘ᶜ +ᶜ η                ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘 ·ᶜ wkᶜ ρ δ₂ +ᶜ η     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (𝟘ᵐ≤ᵐp→p≡𝟘 m≤)) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ δ₂ +ᶜ η ∎
    lemma {δ₁} {δ₂} 𝟙ᵐ m≤ δ≤ ok = begin
      γ                                  ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ (p ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (+ᶜ-monotoneˡ
                                                        (·ᶜ-monotoneˡ (Unitʷ-η→ η-ok ok))))) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ (𝟘 ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-congʳ (·ᶜ-zeroˡ δ₁)))) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ (𝟘ᶜ +ᶜ δ₂) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-identityˡ δ₂))) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ δ₂ +ᶜ η              ∎

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , m≤ , γ≤) (rflₕⱼ {ρ} {p} {q} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (Jₑ {γ = δ′} ▸u , m′≤) ▸S) →
    _ , _ , _ , _ , ▸H , ▸u , ▸S , m′≤  , (begin
      γ                                                            ≤⟨ γ≤ ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-rfl ▸t))) ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkᶜ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ ≡⟨ cong (λ x → (_ · _) ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′       ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′                                 ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′                                       ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ η                                       ∎ )}
    where
    em : Erased-matches
    em = erased-matches-for-J 𝟙ᵐ
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , m≤ , γ≤) (rflₕₖ {ρ} {p} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (Kₑ {γ = δ′} ▸u , m′≤) ▸S) →
    _ , _ , _ , _ , ▸H , ▸u , ▸S , m′≤ , (begin
      γ                                                           ≤⟨ γ≤ ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-rfl ▸t))) ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkᶜ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′  ≡⟨ cong (λ x → (_ · _) ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′        ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′                                ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′                                      ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ′ δ′ +ᶜ η                                      ∎ )}
    where
    em : Erased-matches
    em = erased-matches-for-K 𝟙ᵐ
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , m≤ , γ≤) (rflₕₑ {ρ} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} ([]-congₑ ok , m′≤) ▸S) →
    _ , _ , _ , _ , ▸H , rflₘ , ▸S , m′≤ , (begin
      γ                                          ≤⟨ γ≤ ⟩
      (∣ S ∣ · 𝟘) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      𝟘 ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ 𝟘ᶜ                    ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-identityʳ _) ⟩
      𝟘ᶜ +ᶜ η                                    ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      ∣ S ∣ ·ᶜ 𝟘ᶜ +ᶜ η                           ≡˘⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ′) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ′ 𝟘ᶜ +ᶜ η ∎) }
    where
    open RPo ≤ᶜ-poset

opaque

  ▸-⇒ₙ : (▸s : γ ⨾ δ ⨾ η ▸[ m ] s) (d : s ⇒ₙ s′) → ∃₄ (_⨾_⨾_▸[_] s′)
  ▸-⇒ₙ ▸s (varₕ′ d) = ⊥-elim not-tracking-and-no-tracking
  ▸-⇒ₙ {(n)} {γ} {δ} {η} {m} (▸H , ▸x , ▸S , m≤ , γ≤) (varₕ {ρ} {x} {S} {ρ′} d) =
    case ▸-heapLookup d ▸H lemma₂ of λ
      (m′ , δ′ , ▸t , ▸H′ , m′≤) →
    _ , _ , _ , _
      , ▸H′ , ▸t , ▸S , m′≤
      , let open RPo ≤ᶜ-poset
            ρδ′ = wkᶜ ρ′ δ′
        in  begin
          (γ , x′ ≔ η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ ρδ′
            ≤⟨ +ᶜ-monotoneˡ (update-monotoneˡ x′ lemma₁) ⟩
          ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η , x′ ≔ η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ ρδ′
            ≈˘⟨ +ᶜ-congʳ (update-congʳ (+-identityˡ _)) ⟩
          ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η , x′ ≔ 𝟘 + η ⟨ x′ ⟩) +ᶜ ∣S∣ ·ᶜ ρδ′
            ≡⟨ cong (_+ᶜ (∣S∣ ·ᶜ ρδ′)) (update-distrib-+ᶜ _ η 𝟘 _ x′) ⟩
          (((𝟘ᶜ , x′ ≔ ∣S∣) , x′ ≔ 𝟘) +ᶜ (η , x′ ≔ η ⟨ x′ ⟩)) +ᶜ ∣S∣ ·ᶜ ρδ′
            ≡⟨ cong₂ (λ x y → (x +ᶜ y) +ᶜ (∣S∣ ·ᶜ ρδ′)) update-twice (update-self η x′) ⟩
          ((𝟘ᶜ , x′ ≔ 𝟘) +ᶜ η) +ᶜ ∣S∣ ·ᶜ ρδ′
            ≡⟨ cong (λ x → (x +ᶜ η) +ᶜ (∣S∣ ·ᶜ ρδ′)) 𝟘ᶜ,≔𝟘 ⟩
          (𝟘ᶜ +ᶜ η) +ᶜ ∣S∣ ·ᶜ ρδ′
            ≈⟨ +ᶜ-congʳ (+ᶜ-identityˡ η) ⟩
          η +ᶜ ∣S∣ ·ᶜ ρδ′
            ≈⟨ +ᶜ-comm η _ ⟩
          ∣S∣ ·ᶜ ρδ′ +ᶜ η ∎
    where
    x′ : Ptr n
    x′ = wkVar ρ x
    ρδ : Conₘ n
    ρδ = wkᶜ ρ δ
    ∣S∣ : M
    ∣S∣ = ∣ S ∣
    lemma₀ : γ ≤ᶜ (𝟘ᶜ , x′ ≔ ∣S∣ · ⌜ m ⌝) +ᶜ η
    lemma₀ = begin
      γ                                   ≤⟨ γ≤ ⟩
      ∣S∣ ·ᶜ ρδ +ᶜ η                      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-var ▸x))) ⟩
      ∣S∣ ·ᶜ wkᶜ ρ (𝟘ᶜ , x ≔ ⌜ m ⌝) +ᶜ η  ≡⟨ cong (λ x → ∣S∣ ·ᶜ x +ᶜ η) (wkUsageVar ρ x)  ⟩
      ∣S∣ ·ᶜ (𝟘ᶜ , x′ ≔ ⌜ m ⌝) +ᶜ η       ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ 𝟘ᶜ ∣S∣ _ x′) ⟩
      (∣S∣ ·ᶜ 𝟘ᶜ , x′ ≔ ∣S∣ · ⌜ m ⌝) +ᶜ η ≈⟨ +ᶜ-congʳ (update-congˡ (·ᶜ-zeroʳ ∣S∣)) ⟩
      (𝟘ᶜ , x′ ≔ ∣S∣ · ⌜ m ⌝) +ᶜ η        ∎
      where
      open RPo ≤ᶜ-poset
    ∣S∣m≡∣S∣ : ∣S∣ · ⌜ m ⌝ ≡ ∣S∣
    ∣S∣m≡∣S∣ = case singleton m of λ where
      (𝟘ᵐ , refl) → trans (·-zeroʳ _) (sym (𝟘ᵐ≤ᵐp→p≡𝟘 m≤))
      (𝟙ᵐ , refl) → ·-identityʳ _
    lemma₁ : γ ≤ᶜ (𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η
    lemma₁ rewrite sym ∣S∣m≡∣S∣ = lemma₀
    lemma₂ : γ ⟨ x′ ⟩ - ∣S∣ ≤ η ⟨ x′ ⟩
    lemma₂ = begin
      γ ⟨ x′ ⟩                        ≤⟨ lookup-monotone x′ lemma₁ ⟩
      ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η) ⟨ x′ ⟩     ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , x′ ≔ ∣S∣) η x′ ⟩
      (𝟘ᶜ , x′ ≔ ∣S∣) ⟨ x′ ⟩ + η ⟨ x′ ⟩  ≡⟨ cong (_+ η ⟨ x′ ⟩) (update-lookup 𝟘ᶜ x′) ⟩
      ∣S∣ + η ⟨ x′ ⟩                    ≈⟨ +-comm ∣S∣ _ ⟩
      η ⟨ x′ ⟩ + ∣S∣                    ∎
      where
      open RPo ≤-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (appₕ {p} {ρ} {S}) =
    case inv-usage-app ▸t of λ
      (invUsageApp {δ = δ′} {(η′)} ▸t ▸u δ≤) →
    _ , _ , _ , _ , ▸H , ▸t , (∘ₑ ▸u , m≤) ∙ ▸S
      , subst (_ ≤ᵐ_) (sym (·-identityʳ _)) m≤
      , (begin
        γ                                                      ≤⟨ γ≤ ⟩
        ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
        ∣ S ∣ ·ᶜ wkᶜ ρ (δ′ +ᶜ p ·ᶜ η′) +ᶜ η                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
        ∣ S ∣ ·ᶜ (wkᶜ ρ δ′ +ᶜ wkᶜ ρ (p ·ᶜ η′)) +ᶜ η             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (wk-·ᶜ ρ))) ⟩
        ∣ S ∣ ·ᶜ (wkᶜ ρ δ′ +ᶜ p ·ᶜ wkᶜ ρ η′) +ᶜ η               ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
        (∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ ρ η′) +ᶜ η      ≈⟨ +ᶜ-assoc _ _ _ ⟩
        ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ ρ η′ +ᶜ η       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-comm _ _) ⟩
        (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ ρ η′ ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (fstₕ {ρ} {S}) =
    case inv-usage-fst ▸t of λ
      (invUsageFst {δ = δ′} m eq ▸t δ≤ mp-cond) →
    _ , _ , _ , _
      , ▸H , ▸t , (fstₑ mp-cond , m≤) ∙ ▸S
      , subst (_ ≤ᵐ_) (sym (·-identityʳ _)) m≤
      , (begin
          γ                                           ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η                      ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ          ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (sndₕ {ρ} {S}) =
    case inv-usage-snd ▸t of λ
      (invUsageSnd {δ = δ′} ▸t δ≤) →
   _ , _ , _ , _ , ▸H , ▸t , (sndₑ , m≤) ∙ ▸S
     , subst (_ ≤ᵐ_) (sym (·-identityʳ _)) m≤
     , (begin
         γ                                            ≤⟨ γ≤ ⟩
         ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η                       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
         (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ           ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)
   where
   open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (prodrecₕ {r} {p} {u} {ρ} {S}) =
    case inv-usage-prodrec ▸t of λ
      (invUsageProdrec {δ = δ′} {η = η′} ▸t ▸u _ ok δ≤) →
    _ , _ , _ , _
      , ▸H , ▸t
      , (prodrecₑ ▸u ok , m≤) ∙ ▸S
      , ≤ᵐ-· m≤
      , (begin
         γ                                                   ≤⟨ γ≤ ⟩
         ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
         ∣ S ∣ ·ᶜ wkᶜ ρ (r ·ᶜ δ′ +ᶜ η′) +ᶜ η                  ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
         ∣ S ∣ ·ᶜ (wkᶜ ρ (r ·ᶜ δ′) +ᶜ wkᶜ ρ η′) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ ∣ S ∣ _ _) ⟩
         (∣ S ∣ ·ᶜ wkᶜ ρ (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
         ∣ S ∣ ·ᶜ wkᶜ ρ (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ η′ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (+ᶜ-comm _ η) ⟩
         ∣ S ∣ ·ᶜ r ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ η′     ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc ∣ S ∣ r _) ⟩
         (∣ S ∣ · r) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ η′    ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (natrecₕ {p} {r} {s} {ρ} {S}) =
    case inv-usage-natrec ▸t of λ {
      (invUsageNatrec {δ = δ′} {η = η′} {θ} ▸z ▸s ▸n ▸A δ≤nr P) →
    case P of λ {
      (invUsageNatrecNoNr _ _ _ _) → ⊥-elim not-nr-and-no-nr ;
      (invUsageNatrecNr ⦃ (d-nr′) ⦄) →
    case Dedicated-nr-propositional d-nr d-nr′ of λ {
      refl →
    _ , _ , _ , _ , ▸H , ▸n , (natrecₑ ▸z ▸s ▸A , m≤) ∙ ▸S
      , subst (_≤ᵐ _) (≢𝟘→ᵐ·≡ nr₂≢𝟘) (≤ᵐ-· m≤) , (begin
      γ                                                                        ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                                                    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤nr)) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ (nrᶜ p r δ′ η′ θ) +ᶜ η                                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ nrᶜ-factoring)) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ (nr₂ p r ·ᶜ θ +ᶜ nrᶜ p r δ′ η′ 𝟘ᶜ) +ᶜ η                    ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
      ∣ S ∣ ·ᶜ (wkᶜ ρ (nr₂ p r ·ᶜ θ) +ᶜ wkᶜ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ)) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
      (∣ S ∣ ·ᶜ wkᶜ ρ (nr₂ p r ·ᶜ θ) +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ)) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ (nr₂ p r ·ᶜ θ) +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ) +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (+ᶜ-comm _ _) ⟩
      ∣ S ∣ ·ᶜ (nr₂ p r ·ᶜ wkᶜ ρ θ) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ)   ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkᶜ ρ θ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ) ∎)}}}
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (unitrecₕ {p} {ρ} {S} no-η) =
    case inv-usage-unitrec ▸t of λ
      (invUsageUnitrec {δ = δ′} {η = η′} ▸t ▸u _ ok δ≤) →
    _ , _ , _ , _ , ▸H
      , ▸t
      , (unitrecₑ ▸u ok no-η , m≤) ∙ ▸S
      , ≤ᵐ-· m≤
      , (begin
          γ                                                  ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                              ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ (p ·ᶜ δ′ +ᶜ η′) +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
          ∣ S ∣ ·ᶜ (wkᶜ ρ (p ·ᶜ δ′) +ᶜ wkᶜ ρ η′) +ᶜ η        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ ρ))) ⟩
          ∣ S ∣  ·ᶜ (p ·ᶜ wkᶜ ρ δ′ +ᶜ wkᶜ ρ η′) +ᶜ η         ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          (∣ S ∣ ·ᶜ p ·ᶜ wkᶜ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
          ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ η′ +ᶜ η   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
          (∣ S ∣ · p) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ η′  ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (emptyrecₕ {p} {ρ} {S}) =
    case inv-usage-emptyrec ▸t of λ {
      (invUsageEmptyrec {δ = δ′} ▸t _ ok δ≤) →
    _ , _ , _ , _ , ▸H , ▸t , (emptyrecₑ ok , m≤) ∙ ▸S
      , ≤ᵐ-· m≤ , (begin
        γ                                              ≤⟨ γ≤ ⟩
        ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
        ∣ S ∣ ·ᶜ wkᶜ ρ (p ·ᶜ δ′) +ᶜ η                  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (≈ᶜ-sym (+ᶜ-identityʳ η)) ⟩
        ∣ S ∣ ·ᶜ p ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ              ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
        (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)}
    where
    open RPo ≤ᶜ-poset


  ▸-⇒ₙ (▸H , ▸t , ▸S , m≤ , γ≤) (Jₕ {H}) = ▸-⇒ₙ-J ▸H ▸S m≤ γ≤ (inv-usage-J ▸t)
    where
    em : Erased-matches
    em = erased-matches-for-J 𝟙ᵐ
    open RPo ≤ᶜ-poset
    ▸-⇒ₙ-J-𝟘ᵐ : ∀ {γ₁ γ₂ ok}
              → γ ▸ʰ H → η ▸ˢ S → ∣ S ∣ ≡ 𝟘 → γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η
              → γ₁ ▸[ 𝟘ᵐ[ ok ] ] u → γ₂ ▸[ 𝟘ᵐ[ ok ] ] w
              → ∃₄ (_⨾_⨾_▸[_] ⟨ H , w , ρ , Jₑ p q A t B u v ρ ∙ S ⟩)
    ▸-⇒ₙ-J-𝟘ᵐ {γ} {η} {S} {ρ} {δ} {p} {q} {γ₁} {γ₂} ▸H ▸S ∣S∣≡𝟘 γ≤ ▸u ▸w =
      _ , _ , _ , _ , ▸H , ▸w
        , (Jₑ ▸u , (subst (_ ≤ᵐ_) (sym ∣S∣≡𝟘) 𝟘ᵐ≤ᵐ𝟘)) ∙ ▸S
        , subst (_ ≤ᵐ_) (sym (trans (·-congʳ ∣S∣≡𝟘) (·-zeroˡ _))) 𝟘ᵐ≤ᵐ𝟘
        , (begin
            γ                                                           ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                    ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡𝟘) ⟩
            𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η                                        ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘ᶜ +ᶜ η                                                     ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityʳ _) ⟩
            (𝟘ᶜ +ᶜ 𝟘ᶜ) +ᶜ η                                             ≈⟨ +ᶜ-assoc _ _ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ η                                               ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
            𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                                               ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroˡ _)) ⟩
            𝟘 ·ᶜ wkᶜ ρ γ₂ +ᶜ η +ᶜ 𝟘 ·ᶜ wkᶜ ρ γ₁                         ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (+ᶜ-congˡ (·ᶜ-congʳ ∣S∣≡𝟘)) ⟩
            (𝟘 · ∣∣ᵉ-J em p q) ·ᶜ wkᶜ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₁     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congʳ ∣S∣≡𝟘)) ⟩
            (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkᶜ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₁ ∎)

    ▸-⇒ₙ-J : γ ▸ʰ H → η ▸ˢ S → m ≤ᵐ ∣ S ∣ → γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η → InvUsageJ δ m p q A t B u v w
           → ∃₄ (_⨾_⨾_▸[_] ⟨ H , w , ρ , Jₑ p q A t B u v ρ ∙ S ⟩)
    ▸-⇒ₙ-J {m = 𝟘ᵐ} ▸H ▸S m≤ γ≤ (invUsageJ {γ₄} {γ₆} e e′ _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₙ-J-𝟘ᵐ ▸H ▸S (𝟘ᵐ≤ᵐp→p≡𝟘 m≤) γ≤ ▸u ▸w
    ▸-⇒ₙ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} ▸H ▸S m≤ γ≤ (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} e e′ _ _ _ ▸u _ ▸w δ≤) rewrite ∣∣ᵉ-J-ω e e′ =
      _ , _ , _ , _ , ▸H , ▸w , (Jₑ ▸u , m≤) ∙ ▸S
        , 𝟙ᵐ≤ᵐ
        , (begin
            γ                                                         ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-distribˡ-+ᶜ ω _ _))) ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ γ₄ +ᶜ ω ·ᶜ (γ₅ +ᶜ γ₆)) +ᶜ η           ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (+ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ))) ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ γ₄ +ᶜ ω ·ᶜ γ₆) +ᶜ η                   ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
            ∣ S ∣ ·ᶜ (wkᶜ ρ (ω ·ᶜ γ₄) +ᶜ wkᶜ ρ (ω ·ᶜ γ₆)) +ᶜ η         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-cong (wk-·ᶜ ρ) (wk-·ᶜ ρ))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ ρ γ₄ +ᶜ ω ·ᶜ wkᶜ ρ γ₆) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneˡ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ (𝟙 ·ᶜ wkᶜ ρ γ₄ +ᶜ ω ·ᶜ wkᶜ ρ γ₆) +ᶜ η             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ (wkᶜ ρ γ₄ +ᶜ ω ·ᶜ wkᶜ ρ γ₆) +ᶜ η                  ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            (∣ S ∣ ·ᶜ wkᶜ ρ γ₄ +ᶜ ∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ ρ γ₆) +ᶜ η         ≈⟨ +ᶜ-congʳ (+ᶜ-comm _ _) ⟩
            (∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ ρ γ₆ +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄) +ᶜ η         ≈⟨ +ᶜ-assoc _ _ _ ⟩
            ∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ ρ γ₆ +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄ +ᶜ η           ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
            (∣ S ∣ · ω) ·ᶜ wkᶜ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄          ∎)
    ▸-⇒ₙ-J {m = 𝟘ᵐ} ▸H ▸S m≤ γ≤ (invUsageJ₀₁ {γ₄} {γ₆} e _ _ _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₙ-J-𝟘ᵐ ▸H ▸S (𝟘ᵐ≤ᵐp→p≡𝟘 m≤) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸w)
    ▸-⇒ₙ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} ▸H ▸S m≤ γ≤ (invUsageJ₀₁ {γ₃} {γ₄} {γ₆} e≡some refl refl _ _ _ ▸u _ ▸w δ≤) rewrite ∣∣ᵉ-J-some₀₀ e≡some =
      _ , _ , _ , _ , ▸H , ▸w , (Jₑ ▸u , m≤) ∙ ▸S
        , subst (𝟘ᵐ? ≤ᵐ_) (sym (·-zeroʳ  _)) 𝟘ᵐ?≤ᵐ𝟘
        , (begin
            γ                                                   ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                            ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄)) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄) +ᶜ η                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (𝟙 ·ᶜ γ₄) +ᶜ η                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η                            ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                            ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄        ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄ ∎)
    ▸-⇒ₙ-J {m = 𝟘ᵐ} ▸H ▸S m≤ γ≤ (invUsageJ₀₂ e≡all _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₙ-J-𝟘ᵐ ▸H ▸S (𝟘ᵐ≤ᵐp→p≡𝟘 m≤) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸w)
    ▸-⇒ₙ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} {q} ▸H ▸S m≤ γ≤ (invUsageJ₀₂ {γ₄} {γ₆} e≡all _ _ _ ▸u _ ▸w δ≤) rewrite ∣∣ᵉ-J-all {p = p} {q = q} e≡all =
      _ , _ , _ , _ , ▸H , ▸w , (Jₑ ▸u , m≤) ∙ ▸S
        , subst (𝟘ᵐ? ≤ᵐ_) (sym (·-zeroʳ  _)) 𝟘ᵐ?≤ᵐ𝟘
        , (begin
            γ                                                    ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η                            ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                            ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄        ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄ ∎)

  ▸-⇒ₙ (▸H , ▸t , ▸S , m≤ , γ≤) (Kₕ {H}) = ▸-⇒ₙ-K ▸H ▸S m≤ γ≤ (inv-usage-K ▸t)
    where
    em : Erased-matches
    em = erased-matches-for-K 𝟙ᵐ
    open RPo ≤ᶜ-poset
    ▸-⇒ₙ-K-𝟘ᵐ : ∀ {γ₁ γ₂ ok}
              → γ ▸ʰ H → η ▸ˢ S → ∣ S ∣ ≡ 𝟘 → γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η
              → γ₁ ▸[ 𝟘ᵐ[ ok ] ] u → γ₂ ▸[ 𝟘ᵐ[ ok ] ] v
              → ∃₄ (_⨾_⨾_▸[_] ⟨ H , v , ρ , Kₑ p A t B u ρ ∙ S ⟩)
    ▸-⇒ₙ-K-𝟘ᵐ {γ} {η} {S} {ρ} {δ} {p} {γ₁} {γ₂} ▸H ▸S ∣S∣≡𝟘 γ≤ ▸u ▸v =
      _ , _ , _ , _ , ▸H , ▸v
        , (Kₑ ▸u , (subst (_ ≤ᵐ_) (sym ∣S∣≡𝟘) 𝟘ᵐ≤ᵐ𝟘)) ∙ ▸S
        , subst (_ ≤ᵐ_) (sym (trans (·-congʳ ∣S∣≡𝟘) (·-zeroˡ _))) 𝟘ᵐ≤ᵐ𝟘
        , (begin
            γ                                                         ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡𝟘) ⟩
            𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η                                      ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘ᶜ +ᶜ η                                                   ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityʳ _) ⟩
            (𝟘ᶜ +ᶜ 𝟘ᶜ) +ᶜ η                                           ≈⟨ +ᶜ-assoc _ _ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ η                                             ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
            𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                                             ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroˡ _)) ⟩
            𝟘 ·ᶜ wkᶜ ρ γ₂ +ᶜ η +ᶜ 𝟘 ·ᶜ wkᶜ ρ γ₁                       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (+ᶜ-congˡ (·ᶜ-congʳ ∣S∣≡𝟘)) ⟩
            (𝟘 · ∣∣ᵉ-K em p) ·ᶜ wkᶜ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₁     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congʳ ∣S∣≡𝟘)) ⟩
            (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkᶜ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₁ ∎)
    ▸-⇒ₙ-K : γ ▸ʰ H → η ▸ˢ S → m ≤ᵐ ∣ S ∣ → γ ≤ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η → InvUsageK δ m p A t B u v
           → ∃₄ (_⨾_⨾_▸[_] ⟨ H , v , ρ , Kₑ p A t B u ρ ∙ S ⟩)
    ▸-⇒ₙ-K {m = 𝟘ᵐ} ▸H ▸S m≤ γ≤ (invUsageK _ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₙ-K-𝟘ᵐ ▸H ▸S (𝟘ᵐ≤ᵐp→p≡𝟘 m≤) γ≤ ▸u ▸v
    ▸-⇒ₙ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≤ γ≤ (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} e e′ _ _ _ ▸u ▸v δ≤) rewrite ∣∣ᵉ-K-ω e e′ =
      _ , _ , _ , _ , ▸H , ▸v , (Kₑ ▸u , m≤) ∙ ▸S , 𝟙ᵐ≤ᵐ
        , (begin
            γ                                                         ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)) +ᶜ η          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅)) +ᶜ η                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ (γ₄ +ᶜ γ₅)) +ᶜ η                      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ ρ (γ₄ +ᶜ γ₅)) +ᶜ η                      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-comm _ _)))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ ρ (γ₅ +ᶜ γ₄)) +ᶜ η                      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-congˡ (wk-+ᶜ ρ))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ (wkᶜ ρ γ₅ +ᶜ wkᶜ ρ γ₄)) +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ ρ γ₅ +ᶜ ω ·ᶜ wkᶜ ρ γ₄) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ ρ γ₅ +ᶜ 𝟙 ·ᶜ wkᶜ ρ γ₄) +ᶜ η             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkᶜ ρ γ₅ +ᶜ wkᶜ ρ γ₄) +ᶜ η                  ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            (∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ ρ γ₅ +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄) +ᶜ η         ≈⟨ +ᶜ-assoc _ _ _ ⟩
            ∣ S ∣ ·ᶜ ω ·ᶜ wkᶜ ρ γ₅ +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄ +ᶜ η           ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
            (∣ S ∣ · ω) ·ᶜ wkᶜ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄          ∎)
    ▸-⇒ₙ-K {m = 𝟘ᵐ} ▸H ▸S m≤ γ≤ (invUsageK₀₁ _ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₙ-K-𝟘ᵐ ▸H ▸S (𝟘ᵐ≤ᵐp→p≡𝟘 m≤) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸-⇒ₙ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≤ γ≤ (invUsageK₀₁ {γ₃} {γ₄} {γ₅} e≡some refl _ _ _ ▸u ▸v δ≤) rewrite ∣∣ᵉ-K-some₀ e≡some =
      _ , _ , _ , _ , ▸H , ▸v , (Kₑ ▸u , m≤) ∙ ▸S
        , subst (𝟘ᵐ? ≤ᵐ_) (sym (·-zeroʳ  _)) 𝟘ᵐ?≤ᵐ𝟘
        , (begin
            γ                                                    ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                                ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ                                ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄))                ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ (ω ·ᶜ γ₄)                        ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ (𝟙 ·ᶜ γ₄)                        ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-identityˡ _))) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄                               ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄                         ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄ ∎)
    ▸-⇒ₙ-K {m = 𝟘ᵐ} ▸H ▸S m≤ γ≤ (invUsageK₀₂ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₙ-K-𝟘ᵐ ▸H ▸S (𝟘ᵐ≤ᵐp→p≡𝟘 m≤) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸-⇒ₙ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≤ γ≤ (invUsageK₀₂ {γ₄} {γ₅} e≡all _ _ _ ▸u ▸v δ≤) rewrite ∣∣ᵉ-K-all {p = p} e≡all =
      _ , _ , _ , _ , ▸H , ▸v , (Kₑ ▸u , m≤) ∙ ▸S
        , subst (𝟘ᵐ? ≤ᵐ_) (sym (·-zeroʳ  _)) 𝟘ᵐ?≤ᵐ𝟘
        , (begin
            γ                                                    ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                                ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ δ                                ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄                               ≈˘⟨ +ᶜ-identityˡ _  ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄                         ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkᶜ ρ γ₄ ∎)

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) ([]-congₕ {ρ} {S}) =
    case inv-usage-[]-cong ▸t of λ
      (invUsage-[]-cong {γ₄} _ _ _ ▸v ok δ≤) →
    _ , _ , _ , _ , ▸H , ▸v , ([]-congₑ ok , m≤) ∙ ▸S
      , subst (𝟘ᵐ? ≤ᵐ_) (sym (·-zeroʳ _)) 𝟘ᵐ?≤ᵐ𝟘
      , (begin
          γ                                           ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkᶜ ρ 𝟘ᶜ +ᶜ η                      ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
          ∣ S ∣ ·ᶜ 𝟘ᶜ +ᶜ η                            ≈⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-sym (+ᶜ-identityʳ _)) ⟩
          𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                               ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          𝟘 ·ᶜ wkᶜ ρ γ₄ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟘) ·ᶜ wkᶜ ρ γ₄ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)
    where
    open RPo ≤ᶜ-poset

opaque

  ▸-⇒ₛ : (▸s : γ ⨾ δ ⨾ η ▸[ m ] s) (d : s ⇒ₛ s′) → ∃₃ (_⨾_⨾_▸[ m ] s′)
  ▸-⇒ₛ {γ} {δ} {η} (▸H , ▸t , ▸S , m≤ , γ≤) (sucₕ {ρ} {k} x) =
    case inv-usage-suc ▸t of λ
      (invUsageSuc {δ = δ′} ▸t δ≤) →
    _ , _ , _ , ▸H , ▸t , (sucₑ , m≤) ∙ ▸S
      , subst (_ ≤ᵐ_) (sym (·-identityʳ _)) m≤ , (begin
      γ ≤⟨ γ≤ ⟩
      ∣ sucₛ k ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                            ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
      ∣ sucₛ k ∣ ·ᶜ wkᶜ ρ δ′ +ᶜ η                           ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
      (∣ sucₛ k ∣ · 𝟙) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ               ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      (∣ sucₛ k ∣ · 𝟙) ·ᶜ wkᶜ ρ δ′ +ᶜ η +ᶜ ∣ sucₛ k ∣ ·ᶜ 𝟘ᶜ ∎)
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₛ {γ} {δ} (▸H , ▸t , _∙_ {γ = η} (▸e , m′≤) ▸S , m≤ , γ≤) (numₕ {ρ} {S} x) =
    case ▸e of λ {
      sucₑ →
    _ , _ , _ , ▸H , sucₘ ▸t , ▸S
      , subst (_ ≤ᵐ_) (·-identityʳ _) m≤ , (begin
      γ                                          ≤⟨ γ≤ ⟩
      (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      (∣ S ∣ · 𝟙) ·ᶜ wkᶜ ρ δ +ᶜ η +ᶜ 𝟘ᶜ          ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
      ∣ S ∣ ·ᶜ wkᶜ ρ δ +ᶜ η                      ∎) }
    where
    open RPo ≤ᶜ-poset


opaque

  -- Well-resourced states evaluate to well-resourced states

  ▸-⇒ : (▸s : γ ⨾ δ ⨾ η ▸[ m ] s) (d : s ⇒ s′) → ∃₄ (_⨾_⨾_▸[_] s′)
  ▸-⇒ ▸s (⇒ₙ d) = ▸-⇒ₙ ▸s d
  ▸-⇒ ▸s (⇒ᵥ d) = ▸-⇒ᵥ ▸s d
  ▸-⇒ ▸s (⇒ₛ d) =
    case ▸-⇒ₛ ▸s d of λ
      (γ , δ , η , ▸s) →
    γ , δ , η , _ , ▸s

opaque

  ▸-⇒* : (▸s : γ ⨾ δ ⨾ η ▸[ m ] s) (d : s ⇒* s′) → ∃₄ (_⨾_⨾_▸[_] s′)
  ▸-⇒* ▸s id =
    _ , _ , _ , _ , ▸s
  ▸-⇒* ▸s (d ⇨ d′) =
    case ▸-⇒ ▸s d of λ
      (_ , _ , _ , _ , ▸s′) →
    ▸-⇒* ▸s′ d′
