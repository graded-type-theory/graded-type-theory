------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States
-- and the reduction relation with resource tracking.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Heap.Options
open import Definition.Typed.Variant
open import Tools.Bool
import Graded.Mode

module Graded.Heap.Usage.Reduction
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
open import Tools.Relation
import Tools.Reasoning.PartialOrder as RPo
import Tools.Reasoning.PropositionalEquality as RPe
import Tools.Reasoning.Equivalence as REq

open import Definition.Untyped M

open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR
open import Graded.Heap.Reduction type-variant UR opts
open import Graded.Heap.Usage type-variant UR erased-heap
open import Graded.Heap.Usage.Properties type-variant UR erased-heap
open import Graded.Heap.Usage.Weakening type-variant UR erased-heap

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

  -- Usage preservation under _⇒ᵥ_

  ▸-⇒ᵥ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ᵥ s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒ᵥ {δ} (▸H , ▸t , ▸S , γ≤) (lamₕ {p} {ρ} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (∘ₑ {γ = γ′} ▸u) ▸S) →
    case inv-usage-lam ▸t of λ
      (invUsageLam {δ = δ′} ▸t δ≤) →
    _ , _ , _
      , subₕ ▸H (≤ᶜ-trans γ≤
           (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-congʳ (·-identityʳ _)))
             (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-assoc _ _ _))
               (+ᶜ-assoc _ _ _))))))
      ∙ ▸ᶜᵖ (▸-cong ⌞⌟ᵐ· ▸u)
      , ▸-cong (⌞⌟-cong (trans (·-identityʳ _) (wk-∣S∣ (step id) S))) ▸t
      , wk-▸ˢ (step id) ▸S
      ,
      (begin
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η ∙ ∣ S ∣ · p                                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ∙ ≤-refl ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ S ∣ · p                                  ≈˘⟨ ≈ᶜ-refl ∙ ·-congʳ ·⌜⌞⌟⌝ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ (∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) · p                ≈⟨ ≈ᶜ-refl ∙ ·-assoc _ _ _ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p                  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ (step id) S)) ∙ ·-congʳ (wk-∣S∣ (step id) S) ⟩
          ∣ wk1ˢ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p         ≈˘⟨ ≈ᶜ-refl ∙ ·-congˡ (·-congʳ (cong (λ x → ⌜ ⌞ x ⌟ ⌝) (·-identityʳ _))) ⟩
          ∣ wk1ˢ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · ⌜ ⌞ ∣ S ∣ · 𝟙 ⌟ ⌝ · p     ≈˘⟨ ≈ᶜ-refl ∙ +-identityʳ _ ⟩
          ∣ wk1ˢ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · ⌜ ⌞ ∣ S ∣ · 𝟙 ⌟ ⌝ · p + 𝟘 ∎ )}
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , _∙_ {γ = η} ▸e ▸S , γ≤) (prodˢₕ₁ {p} {ρ} {S}) =
    case inv-usage-prodˢ ▸t of λ
      (invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤) →
    case ▸e of λ {
      (fstₑ mp-cond) →
    _ , _ , _ , ▸H
      , ▸-cong (lemma′ mp-cond) ▸t
      , ▸S
      , (begin
             γ                                          ≤⟨ γ≤ ⟩
             (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
             ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ                ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
             ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
             ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (∧ᶜ-decreasingˡ _ _))) ⟩
             ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁) +ᶜ η              ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
             ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ δ₁ +ᶜ η                ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
             (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ₁ +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ (lemma mp-cond)) ⟩
             ∣ S ∣ ·ᶜ wkConₘ ρ δ₁ +ᶜ η ∎ )}
    where
    lemma : (⌞ ∣ S ∣ ⌟ ≡ 𝟙ᵐ → p ≤ 𝟙) → ∣ S ∣ · p ≤ ∣ S ∣
    lemma mp-cond =
      case is-𝟘? ∣ S ∣ of λ where
        (yes ∣S∣≡𝟘) → begin
          ∣ S ∣ · p ≈⟨ ·-congʳ ∣S∣≡𝟘 ⟩
          𝟘 · p     ≈⟨ ·-zeroˡ p ⟩
          𝟘         ≈˘⟨ ∣S∣≡𝟘 ⟩
          ∣ S ∣     ∎
        (no ∣S∣≢𝟘) → begin
          ∣ S ∣ · p ≤⟨ ·-monotoneʳ (mp-cond (≢𝟘→⌞⌟≡𝟙ᵐ ∣S∣≢𝟘)) ⟩
          ∣ S ∣ · 𝟙 ≈⟨ ·-identityʳ _ ⟩
          ∣ S ∣     ∎
      where
      open RPo ≤-poset
    lemma′ : (⌞ ∣ S ∣ ⌟ ≡ 𝟙ᵐ → p ≤ 𝟙) → ⌞ ∣ S ∣ · 𝟙 ⌟ ᵐ· p ≡ ⌞ ∣ S ∣ ⌟
    lemma′ mp-cond =
      case is-𝟘? ∣ S ∣ of λ where
        (yes ∣S∣≡𝟘) → begin
          ⌞ ∣ S ∣ · 𝟙 ⌟ ᵐ· p ≡⟨ cong (λ x → ⌞ x · 𝟙 ⌟ ᵐ· p) ∣S∣≡𝟘 ⟩
          ⌞ 𝟘 · 𝟙 ⌟ ᵐ· p    ≡⟨ cong (_ᵐ· p) (⌞⌟-cong (·-zeroˡ 𝟙)) ⟩
          ⌞ 𝟘 ⌟ ᵐ· p        ≡⟨ cong (_ᵐ· p) ⌞𝟘⌟≡𝟘ᵐ? ⟩
          𝟘ᵐ? ᵐ· p          ≡⟨ ᵐ·-zeroˡ ⟩
          𝟘ᵐ?               ≡˘⟨ ⌞𝟘⌟≡𝟘ᵐ? ⟩
          ⌞ 𝟘 ⌟             ≡˘⟨ ⌞⌟-cong ∣S∣≡𝟘 ⟩
          ⌞ ∣ S ∣ ⌟         ∎
        (no ∣S∣≢𝟘) → begin
          ⌞ ∣ S ∣ · 𝟙 ⌟ ᵐ· p ≡⟨ cong (λ x → ⌞ x ⌟ ᵐ· p) (·-identityʳ _) ⟩
          ⌞ ∣ S ∣ ⌟ ᵐ· p ≡⟨ ≢𝟘→ᵐ·≡ (λ {refl → 𝟘≰𝟙 (mp-cond (≢𝟘→⌞⌟≡𝟙ᵐ ∣S∣≢𝟘))}) ⟩
          ⌞ ∣ S ∣ ⌟ ∎
      where
      open RPe
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (prodˢₕ₂ {p} {ρ} {S}) =
    case inv-usage-prodˢ ▸t of λ
      (invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤) →
    case ▸S of λ {
      (_∙_ {γ = η} sndₑ ▸S) →
    _ , _ , _ , ▸H , ▸-cong (⌞⌟-cong (·-identityʳ _)) ▸u , ▸S
      , (begin
          γ ≤⟨ γ≤ ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ           ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (∧ᶜ-decreasingʳ (p ·ᶜ δ₁) δ₂))) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ₂ +ᶜ η                       ∎) }
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (prodʷₕ {p} {t₁} {ρ} {r} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (prodrecₑ {γ = γ′} ▸u r≢𝟘) ▸S) →
    case inv-usage-prodʷ ▸t of λ
      (invUsageProdʷ {δ = δ′} {η = η′} ▸t₁ ▸t₂ δ≤) →
    let γ≤′ : γ ≤ᶜ ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ (∣ S ∣ · r · p + (∣ S ∣ · r) · 𝟘) ·ᶜ wkConₘ ρ δ′
        γ≤′ = begin
          γ                                                                                                               ≤⟨ γ≤ ⟩
          (∣ S ∣ · r) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′                                                          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          (∣ S ∣ · r) ·ᶜ wkConₘ ρ (p ·ᶜ δ′ +ᶜ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′                                            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
          (∣ S ∣ · r) ·ᶜ (wkConₘ ρ (p ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′                                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ ρ))) ⟩
          (∣ S ∣ · r) ·ᶜ (p ·ᶜ wkConₘ ρ δ′ +ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′                                   ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ (∣ S ∣ · r) _ _) ⟩
          ((∣ S ∣ · r) ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′                    ≈˘⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-assoc (∣ S ∣ · r) p _)) ⟩
          (((∣ S ∣ · r) · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′                   ≈⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-congʳ (·-assoc ∣ S ∣ r p))) ⟩
          ((∣ S ∣ · r · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′                     ≈⟨ +ᶜ-comm _ _ ⟩
          (η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′                     ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
          (η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′ +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ ρ δ′                     ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ ρ δ′                   ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ _)) ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ (∣ S ∣ · r · p + 𝟘) ·ᶜ wkConₘ ρ δ′               ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ _))) ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ (∣ S ∣ · r · p + (∣ S ∣ · r) · 𝟘) ·ᶜ wkConₘ ρ δ′ ∎
        ▸ᶜt₁ = subst₂ (λ x y → (_ ⨾ x ▸ᶜ (y , _)))
                (trans (·-assoc _ _ _) (sym (trans (+-congˡ (·-zeroʳ _)) (+-identityʳ _))))
                (·-assoc _ _ _) (▸ᶜᵖ (▸-cong ⌞⌟ᵐ· ▸t₁))
    in  _ , _ , _
          , subₕ ▸H γ≤′ ∙ ▸ᶜt₁ ∙ ▸ᶜᵖ ▸t₂
          , ▸-cong (⌞⌟-cong (wk-∣S∣ (step (step id)) S)) ▸u
          , wk-▸ˢ (step (step id)) ▸S
          , lemma₁ ∙ lemma₂ ∙ lemma₂ }
      where
      lemma₁ : ∀ {n} {γ η : Conₘ n} → η +ᶜ ∣ S ∣ ·ᶜ γ ≤ᶜ ∣ wk2ˢ S ∣ ·ᶜ γ +ᶜ η
      lemma₁ {γ} {η} = begin
        η +ᶜ ∣ S ∣ ·ᶜ γ      ≈⟨ +ᶜ-comm _ _ ⟩
        ∣ S ∣ ·ᶜ γ +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ _ S)) ⟩
        ∣ wk2ˢ S ∣ ·ᶜ γ +ᶜ η ∎
        where
        open RPo ≤ᶜ-poset
      lemma₂ : ∀ {p} → ∣ S ∣ · p ≤ ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p + 𝟘
      lemma₂ {p} = begin
        ∣ S ∣ · p                          ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
        (∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) · p        ≡⟨ ·-assoc _ _ _ ⟩
        ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p          ≡⟨ ·-congʳ (wk-∣S∣ _ S) ⟩
        ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p     ≡˘⟨ +-identityʳ _ ⟩
        ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p + 𝟘 ∎
        where
        open RPo ≤-poset
      open RPo ≤ᶜ-poset


  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (zeroₕ {ρ} {p} {r} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (natrecₑ {γ = γ′} {δ = δ′} ▸z ▸s ▸A) ▸S) →
    _ , _ , _ , ▸H , ▸z , ▸S , (begin
      γ                                                                             ≤⟨ γ≤ ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-zero ▸t))) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ) ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                               ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                                     ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ′ (nrᶜ-zero ≤ᶜ-refl))) ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′                                                     ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′ +ᶜ η                                                     ∎) }
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (sucₕ {t} {ρ} {p} {q} {r} {A} {z} {s} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (natrecₑ {γ = γ′} {δ = δ′} ▸z ▸s ▸A) ▸S) →
    case inv-usage-suc ▸t of λ
      (invUsageSuc {δ = θ} ▸t δ≤θ) →
    case natrecₘ
           (wkUsage (step id) ▸z)
           (wkUsage (liftn (step id) 2) ▸s)
           (var {x = x0})
           (wkUsage (lift (step id)) ▸A) of λ
      ▸nr →
    case ▸ᶜᵖʳ {r = r} {ρ = lift ρ′} ▸nr of λ {
      (χ ∙ x , ▸ᶜnr , rχ≈ ∙ rx≡) →
    case ▸ᶜ ▸t (lemma₂ p r x (sym rx≡)) of λ
      ▸ᶜt →
    _ , _ , _
      , subₕ ▸H (lemma₄ {γ = γ} {δ = wkConₘ ρ δ} {η = η} {wkConₘ ρ θ} {wkConₘ ρ′ χ} {wkConₘ ρ′ γ′} {wkConₘ ρ′ δ′}
               (lemma₅ {ρ = ρ′} γ≤) (wk-≤ᶜ ρ δ≤θ) (lemma₆ rχ≈) (sym rx≡))
               ∙ ▸ᶜt ∙ ▸ᶜnr
      , ▸-cong (⌞⌟-cong (wk-∣S∣ _ S)) ▸s
      , wk-▸ˢ (step (step id)) ▸S
      , ≤ᶜ-reflexive (+ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ _ S))) ∙ ≤-reflexive (lemma₃ p) ∙ ≤-reflexive (lemma₃ r) }}
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
    lemma₂ : ∀ p r q → r · q ≡ r · nr p r 𝟘 𝟘 ⌜ ⌞ ∣ S ∣ ⌟ ⌝
           → ∣ S ∣ · nr₂ p r ≤ ∣ S ∣ · p + (∣ S ∣ · r) · q
    lemma₂ p r q rq≡ =
      case is-𝟘? ∣ S ∣ of λ where
        (yes ∣S∣≡𝟘) → begin
          ∣ S ∣ · nr₂ p r             ≡⟨ ·-congʳ ∣S∣≡𝟘 ⟩
          𝟘 · nr₂ p r                 ≡⟨ ·-zeroˡ _ ⟩
          𝟘                           ≡˘⟨ +-identityʳ _ ⟩
          𝟘 + 𝟘                       ≡˘⟨ +-cong (·-zeroˡ _) (·-zeroˡ _) ⟩
          𝟘 · p + 𝟘 · r · q           ≡˘⟨ +-congˡ (·-congʳ ∣S∣≡𝟘)  ⟩
          𝟘 · p + ∣ S ∣ · r · q       ≡˘⟨ +-cong (·-congʳ ∣S∣≡𝟘) (·-assoc _ _ _)  ⟩
          ∣ S ∣ · p + (∣ S ∣ · r) · q ∎
        (no ∣S∣≢𝟘) → begin
          ∣ S ∣ · nr₂ p r                             ≤⟨ ·-monotoneʳ (lemma₁ p r) ⟩
          ∣ S ∣ · (p + r · nr p r 𝟘 𝟘 𝟙)             ≡˘⟨ ·-congˡ (+-congˡ (·-congˡ (cong (λ x → nr p r 𝟘 𝟘 ⌜ x ⌝) (≢𝟘→⌞⌟≡𝟙ᵐ ∣S∣≢𝟘)))) ⟩
          ∣ S ∣ · (p + r · nr p r 𝟘 𝟘 ⌜ ⌞ ∣ S ∣ ⌟ ⌝) ≡˘⟨ ·-congˡ (+-congˡ rq≡) ⟩
          ∣ S ∣ · (p + r · q)                        ≡⟨ ·-distribˡ-+ _ _ _ ⟩
          ∣ S ∣ · p + ∣ S ∣ · r · q                  ≡˘⟨ +-congˡ (·-assoc _ _ _) ⟩
          ∣ S ∣ · p + (∣ S ∣ · r) · q                ∎
      where
      open RPo ≤-poset
    lemma₃ : ∀ p → ∣ S ∣ · p ≡ ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p + 𝟘
    lemma₃ p = begin
      ∣ S ∣ · p                          ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
      (∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) · p        ≡⟨ ·-assoc _ _ _ ⟩
      ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p          ≡⟨ ·-congʳ (wk-∣S∣ _ S) ⟩
      ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p     ≡˘⟨ +-identityʳ _ ⟩
      ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p + 𝟘 ∎
      where
      open RPe
    lemma₄ : ∀ {n x} {γ δ η θ χ γ′ δ′ : Conₘ n}
           → γ ≤ᶜ (∣ S ∣ · nr₂ p r) ·ᶜ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ nrᶜ p r γ′ δ′ 𝟘ᶜ
           → δ ≤ᶜ θ → r ·ᶜ nrᶜ p r γ′ δ′ 𝟘ᶜ ≈ᶜ r ·ᶜ χ → r · x ≡ r · nr p r 𝟘 𝟘 ⌜ ⌞ ∣ S ∣ ⌟ ⌝
           → γ ≤ᶜ ((∣ S ∣ ·ᶜ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ χ) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · x) ·ᶜ θ
    lemma₄ {x} {γ} {δ} {η} {θ} {χ} {γ′} {δ′} γ≤ δ≤ rχ≈ rx≡ = begin
      γ ≤⟨ γ≤ ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ nrᶜ p r γ′ δ′ 𝟘ᶜ ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ δ≤) (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ nrᶜ-suc)) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ θ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ (δ′ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ nrᶜ p r γ′ δ′ 𝟘ᶜ) ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ p) rχ≈)))) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ θ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ (δ′ +ᶜ 𝟘ᶜ +ᶜ r ·ᶜ χ) ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-congˡ (+ᶜ-identityˡ _)))) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ θ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ (δ′ +ᶜ r ·ᶜ χ) ≈⟨ +ᶜ-comm _ _ ⟩
      (η +ᶜ ∣ S ∣ ·ᶜ (δ′ +ᶜ r ·ᶜ χ)) +ᶜ (∣ S ∣ · nr₂ p r) ·ᶜ θ ≈⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
      (η +ᶜ ∣ S ∣ ·ᶜ δ′ +ᶜ ∣ S ∣ ·ᶜ r ·ᶜ χ) +ᶜ (∣ S ∣ · nr₂ p r) ·ᶜ θ ≈˘⟨ +ᶜ-congʳ (+ᶜ-assoc _ _ _) ⟩
      ((η +ᶜ ∣ S ∣ ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ r ·ᶜ χ) +ᶜ (∣ S ∣ · nr₂ p r) ·ᶜ θ ≈˘⟨ +ᶜ-congʳ (+ᶜ-cong (+ᶜ-comm _ _) (·ᶜ-assoc _ _ _)) ⟩
      ((∣ S ∣ ·ᶜ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ χ) +ᶜ (∣ S ∣ · nr₂ p r) ·ᶜ θ ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneˡ (lemma₂ p r x rx≡)) ⟩
      ((∣ S ∣ ·ᶜ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ χ) +ᶜ (∣ S ∣ · p + (∣ S ∣ · r) · x) ·ᶜ θ  ∎
      where
      open RPo ≤ᶜ-poset
    lemma₅ : ∀ {m n q ρ} {γ δ η : Conₘ n} {γ′ δ′ : Conₘ m}
           → γ ≤ᶜ δ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ (nrᶜ p r γ′ δ′ 𝟘ᶜ)
           → γ ≤ᶜ δ +ᶜ η +ᶜ q ·ᶜ nrᶜ p r (wkConₘ ρ γ′) (wkConₘ ρ δ′) 𝟘ᶜ
    lemma₅ {q} {ρ} {γ} {δ} {η} {γ′} {δ′} γ≤ = begin
      γ ≤⟨ γ≤ ⟩
      δ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ (nrᶜ p r γ′ δ′ 𝟘ᶜ)                       ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ (wk-nrᶜ ρ))) ⟩
      δ +ᶜ η +ᶜ q ·ᶜ nrᶜ p r (wkConₘ ρ γ′) (wkConₘ ρ δ′) (wkConₘ ρ 𝟘ᶜ) ≡⟨ cong (λ x → δ +ᶜ η +ᶜ q ·ᶜ nrᶜ p r (wkConₘ ρ γ′) (wkConₘ ρ δ′) x) (wk-𝟘ᶜ ρ) ⟩
      δ +ᶜ η +ᶜ q ·ᶜ nrᶜ p r (wkConₘ ρ γ′) (wkConₘ ρ δ′) 𝟘ᶜ            ∎
      where
      open RPo ≤ᶜ-poset
    lemma₆ : ∀ {m n} {ρ : Wk m n} {γ δ η}
           → r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ ≈ᶜ r ·ᶜ η
           → r ·ᶜ nrᶜ p r (wkConₘ ρ γ) (wkConₘ ρ δ) 𝟘ᶜ ≈ᶜ r ·ᶜ wkConₘ ρ η
    lemma₆ {ρ} {γ} {δ} {η} ≈rη = begin
      r ·ᶜ nrᶜ p r (wkConₘ ρ γ) (wkConₘ ρ δ) 𝟘ᶜ ≡˘⟨ cong (λ x → r ·ᶜ nrᶜ p r (wkConₘ ρ γ) (wkConₘ ρ δ) x) (wk-𝟘ᶜ ρ) ⟩
      r ·ᶜ nrᶜ p r (wkConₘ ρ γ) (wkConₘ ρ δ) (wkConₘ ρ 𝟘ᶜ) ≈˘⟨ ·ᶜ-congˡ (wk-nrᶜ ρ) ⟩
      r ·ᶜ wkConₘ ρ (nrᶜ p r γ δ 𝟘ᶜ) ≈˘⟨ wk-·ᶜ ρ ⟩
      wkConₘ ρ (r ·ᶜ nrᶜ p r γ δ 𝟘ᶜ) ≈⟨ wk-≈ᶜ ρ ≈rη ⟩
      wkConₘ ρ (r ·ᶜ η) ≈⟨ wk-·ᶜ ρ ⟩
      r ·ᶜ wkConₘ ρ η ∎
      where
      open REq Conₘ-setoid

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸star , ▸S , γ≤) (starʷₕ {ρ} {p} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (unitrecₑ {γ = δ′} ▸t _ _) ▸S) →
    case inv-usage-starʷ ▸star of λ
      δ≤𝟘 →
    _ , _ , _ , ▸H , ▸t , ▸S , (begin
      γ                                                       ≤⟨ γ≤ ⟩
      (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤𝟘)) ⟩
      (∣ S ∣ · p) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                         ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                               ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η                               ∎) }
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (unitrec-ηₕ {p} {ρ} {S} η-ok) =
    case inv-usage-unitrec ▸t of λ
      (invUsageUnitrec {δ = δ₁} {η = δ₂} ▸t ▸u _ ok δ≤) →
    _ , _ , _ , ▸H , ▸u , ▸S , lemma _ refl δ≤ ok
    where
    open RPo ≤ᶜ-poset
    lemma : ∀ {δ₁ δ₂} m → m ≡ ⌞ ∣ S ∣ ⌟ → δ ≤ᶜ p ·ᶜ δ₁ +ᶜ δ₂
          → Unitrec-allowed m p q
          → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ₂ +ᶜ η
    lemma {δ₂} 𝟘ᵐ m≡ δ≤ ok = begin
      γ                         ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡))) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘ᶜ +ᶜ η                   ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ₂ +ᶜ η     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡))) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ₂ +ᶜ η ∎
    lemma {δ₁} {δ₂} 𝟙ᵐ m≡ δ≤ ok = begin
      γ                                      ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (+ᶜ-monotoneˡ
                                                           (·ᶜ-monotoneˡ (Unitʷ-η→ η-ok ok))))) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (𝟘 ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-congʳ (·ᶜ-zeroˡ δ₁)))) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (𝟘ᶜ +ᶜ δ₂) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-identityˡ δ₂))) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ₂ +ᶜ η              ∎

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (rflₕⱼ {ρ} {p} {q} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (Jₑ {γ = δ′} ▸u) ▸S) →
    _ , _ , _ , ▸H , ▸u , ▸S , (begin
      γ                                                                  ≤⟨ γ≤ ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-rfl ▸t))) ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ ≡⟨ cong (λ x → (_ · _) ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                                    ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                                          ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η                                          ∎ )}
    where
    em : Erased-matches
    em = erased-matches-for-J 𝟙ᵐ
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (rflₕₖ {ρ} {p} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} (Kₑ {γ = δ′} ▸u) ▸S) →
    _ , _ , _ , ▸H , ▸u , ▸S , (begin
      γ                                                                 ≤⟨ γ≤ ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-rfl ▸t))) ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′  ≡⟨ cong (λ x → (_ · _) ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′           ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                                   ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                                         ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η                                         ∎ )}
    where
    em : Erased-matches
    em = erased-matches-for-K 𝟙ᵐ
    open RPo ≤ᶜ-poset

  ▸-⇒ᵥ {γ} {δ} (▸H , ▸t , ▸S , γ≤) (rflₕₑ {ρ} {ρ′} {S}) =
    case ▸S of λ {
      (_∙_ {γ = η} ([]-congₑ ok) ▸S) →
    _ , _ , _ , ▸H , rflₘ , ▸S , (begin
      γ                                             ≤⟨ γ≤ ⟩
      (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ                    ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-identityʳ _) ⟩
      𝟘ᶜ +ᶜ η                                       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      ∣ S ∣ ·ᶜ 𝟘ᶜ +ᶜ η                              ≡˘⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ′) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ 𝟘ᶜ +ᶜ η ∎) }
    where
    open RPo ≤ᶜ-poset

opaque

  -- Usage preservation under _⇒ₙ_

  ▸-⇒ₙ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ₙ s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒ₙ ▸s (varₕ′ d) = ⊥-elim not-tracking-and-no-tracking
  ▸-⇒ₙ {(n)} {γ} {δ} {η} (▸H , ▸x , ▸S , γ≤) (varₕ {ρ} {x} {S} {ρ′} d) =
    case ▸-heapLookup d ▸H lemma₂ of λ
      (δ′ , ▸t , ▸H′) →
    _ , _ , _
      , ▸H′ , ▸t , ▸S
      , let open RPo ≤ᶜ-poset
            ρδ′ = wkConₘ ρ′ δ′
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
    ρδ = wkConₘ ρ δ
    ∣S∣ : M
    ∣S∣ = ∣ S ∣
    lemma₁ : γ ≤ᶜ (𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η
    lemma₁ = begin
      γ                                              ≤⟨ γ≤ ⟩
      ∣S∣ ·ᶜ ρδ +ᶜ η                                 ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-var ▸x))) ⟩
      ∣S∣ ·ᶜ wkConₘ ρ (𝟘ᶜ , x ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η  ≡⟨ cong (λ x → ∣S∣ ·ᶜ x +ᶜ η) (wk-,≔ ρ) ⟩
      ∣S∣ ·ᶜ (wkConₘ ρ 𝟘ᶜ , x′ ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η ≡⟨ cong (λ x → ∣S∣ ·ᶜ (x , x′ ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η) (wk-𝟘ᶜ ρ) ⟩
      ∣S∣ ·ᶜ (𝟘ᶜ , x′ ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η          ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ 𝟘ᶜ ∣S∣ _ x′) ⟩
      (∣S∣ ·ᶜ 𝟘ᶜ , x′ ≔ ∣S∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η    ≈⟨ +ᶜ-congʳ (update-cong (·ᶜ-zeroʳ _) ·⌜⌞⌟⌝) ⟩
      (𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η                           ∎
      where
      open RPo ≤ᶜ-poset
    lemma₂ : γ ⟨ x′ ⟩ - ∣S∣ ≤ η ⟨ x′ ⟩
    lemma₂ = begin
      γ ⟨ x′ ⟩                          ≤⟨ lookup-monotone x′ lemma₁ ⟩
      ((𝟘ᶜ , x′ ≔ ∣S∣) +ᶜ η) ⟨ x′ ⟩     ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , x′ ≔ ∣S∣) η x′ ⟩
      (𝟘ᶜ , x′ ≔ ∣S∣) ⟨ x′ ⟩ + η ⟨ x′ ⟩  ≡⟨ cong (_+ η ⟨ x′ ⟩) (update-lookup 𝟘ᶜ x′) ⟩
      ∣S∣ + η ⟨ x′ ⟩                    ≈⟨ +-comm ∣S∣ _ ⟩
      η ⟨ x′ ⟩ + ∣S∣                    ∎
      where
      open RPo ≤-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (appₕ {p} {ρ} {S}) =
    case inv-usage-app ▸t of λ
      (invUsageApp {δ = δ′} {(η′)} ▸t ▸u δ≤) →
    _ , _ , _ , ▸H , ▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t
      , ∘ₑ ▸u ∙ ▸S , (begin
        γ                                                            ≤⟨ γ≤ ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ (δ′ +ᶜ p ·ᶜ η′) +ᶜ η                       ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
        ∣ S ∣ ·ᶜ (wkConₘ ρ δ′ +ᶜ wkConₘ ρ (p ·ᶜ η′)) +ᶜ η            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (wk-·ᶜ ρ))) ⟩
        ∣ S ∣ ·ᶜ (wkConₘ ρ δ′ +ᶜ p ·ᶜ wkConₘ ρ η′) +ᶜ η              ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
        (∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ η′) +ᶜ η     ≈⟨ +ᶜ-assoc _ _ _ ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ η′ +ᶜ η       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-comm _ _) ⟩
        (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ η′ ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (fstₕ {ρ} {S}) =
    case inv-usage-fst ▸t of λ
      (invUsageFst {δ = δ′} m eq ▸t δ≤ mp-cond) →
    _ , _ , _
      , ▸H , ▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t
      , fstₑ mp-cond ∙ ▸S , (begin
          γ                                              ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η                      ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ          ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (sndₕ {ρ} {S}) =
    case inv-usage-snd ▸t of λ
      (invUsageSnd {δ = δ′} ▸t δ≤) →
    _ , _ , _ , ▸H , ▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t , sndₑ ∙ ▸S
      , (begin
          γ                                               ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η                       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ           ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)
   where
   open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (prodrecₕ {r} {p} {u} {ρ} {S}) =
    case inv-usage-prodrec ▸t of λ
      (invUsageProdrec {δ = δ′} {η = η′} ▸t ▸u _ ok δ≤) →
    _ , _ , _
      , ▸H , ▸-cong ⌞⌟ᵐ· ▸t
      , prodrecₑ ▸u ok ∙ ▸S
      , (begin
         γ                                                         ≤⟨ γ≤ ⟩
         ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
         ∣ S ∣ ·ᶜ wkConₘ ρ (r ·ᶜ δ′ +ᶜ η′) +ᶜ η                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
         ∣ S ∣ ·ᶜ (wkConₘ ρ (r ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ ∣ S ∣ _ _) ⟩
         (∣ S ∣ ·ᶜ wkConₘ ρ (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
         ∣ S ∣ ·ᶜ wkConₘ ρ (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (+ᶜ-comm _ η) ⟩
         ∣ S ∣ ·ᶜ r ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′     ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc ∣ S ∣ r _) ⟩
         (∣ S ∣ · r) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′    ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (natrecₕ {p} {r} {s} {ρ} {S}) =
    case inv-usage-natrec ▸t of λ {
      (invUsageNatrec {δ = δ′} {η = η′} {θ} ▸z ▸s ▸n ▸A δ≤nr P) →
    case P of λ {
      (invUsageNatrecNoNr _ _ _ _) → ⊥-elim not-nr-and-no-nr ;
      (invUsageNatrecNr ⦃ (d-nr′) ⦄) →
    case Dedicated-nr-propositional d-nr d-nr′ of λ {
      refl →
    _ , _ , _ , ▸H , ▸-cong (sym (≢𝟘→⌞·⌟≡ʳ nr₂≢𝟘)) ▸n
      , natrecₑ ▸z ▸s ▸A ∙ ▸S , (begin
      γ                                                                              ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                                        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤nr)) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (nrᶜ p r δ′ η′ θ) +ᶜ η                                        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ nrᶜ-factoring)) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (nr₂ p r ·ᶜ θ +ᶜ nrᶜ p r δ′ η′ 𝟘ᶜ) +ᶜ η                       ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
      ∣ S ∣ ·ᶜ (wkConₘ ρ (nr₂ p r ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ)) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
      (∣ S ∣ ·ᶜ wkConₘ ρ (nr₂ p r ·ᶜ θ) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ)) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (nr₂ p r ·ᶜ θ) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ) +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (+ᶜ-comm _ _) ⟩
      ∣ S ∣ ·ᶜ (nr₂ p r ·ᶜ wkConₘ ρ θ) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ)   ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
      (∣ S ∣ · nr₂ p r) ·ᶜ wkConₘ ρ θ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (nrᶜ p r δ′ η′ 𝟘ᶜ)    ∎)}}}
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (unitrecₕ {p} {ρ} {S} no-η) =
    case inv-usage-unitrec ▸t of λ
      (invUsageUnitrec {δ = δ′} {η = η′} ▸t ▸u _ ok δ≤) →
    _ , _ , _ , ▸H
      , ▸-cong ⌞⌟ᵐ· ▸t
      , unitrecₑ ▸u ok no-η ∙ ▸S
      , (begin
          γ                                                        ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                 ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ′ +ᶜ η′) +ᶜ η                   ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
          ∣ S ∣ ·ᶜ (wkConₘ ρ (p ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ ρ))) ⟩
          ∣ S ∣  ·ᶜ (p ·ᶜ wkConₘ ρ δ′ +ᶜ wkConₘ ρ η′) +ᶜ η         ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          (∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
          ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′ +ᶜ η   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
          (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′  ∎)
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (emptyrecₕ {p} {ρ} {S}) =
    case inv-usage-emptyrec ▸t of λ {
      (invUsageEmptyrec {δ = δ′} ▸t _ ok δ≤) →
    _ , _ , _ , ▸H , ▸-cong ⌞⌟ᵐ· ▸t , emptyrecₑ ok ∙ ▸S , (begin
        γ                                                 ≤⟨ γ≤ ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ′) +ᶜ η                  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (≈ᶜ-sym (+ᶜ-identityʳ η)) ⟩
        ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ              ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
        (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ    ∎)}
    where
    open RPo ≤ᶜ-poset

  ▸-⇒ₙ (▸H , ▸t , ▸S , γ≤) (Jₕ {H}) =
    ▸-⇒ₙ-J ▸H ▸S refl γ≤ (inv-usage-J ▸t)
    where
    em : Erased-matches
    em = erased-matches-for-J 𝟙ᵐ
    open RPo ≤ᶜ-poset
    ▸-⇒ₙ-J-𝟘ᵐ : ∀ {γ₁ γ₂ ok}
              → γ ▸ʰ H → η ▸ˢ S → ∣ S ∣ ≡ 𝟘 → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η
              → γ₁ ▸[ 𝟘ᵐ[ ok ] ] u → γ₂ ▸[ 𝟘ᵐ[ ok ] ] w
              → ∃₃ (_⨾_⨾_▸ ⟨ H , w , ρ , Jₑ p q A t B u v ρ ∙ S ⟩)
    ▸-⇒ₙ-J-𝟘ᵐ {γ} {η} {S} {ρ} {δ} {p} {q} {γ₁} {γ₂} ▸H ▸S ∣S∣≡𝟘 γ≤ ▸u ▸w =
      _ , _ , _ , ▸H
        , ▸-cong (trans (sym ⌞𝟘⌟) (⌞⌟-cong (sym (trans (·-congʳ ∣S∣≡𝟘) (·-zeroˡ _))))) ▸w
        , Jₑ (▸-cong (sym (≡𝟘→⌞⌟≡𝟘ᵐ ∣S∣≡𝟘)) ▸u) ∙ ▸S
        , (begin
            γ                                                                 ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                          ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡𝟘) ⟩
            𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η                                              ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘ᶜ +ᶜ η                                                           ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityʳ _) ⟩
            (𝟘ᶜ +ᶜ 𝟘ᶜ) +ᶜ η                                                   ≈⟨ +ᶜ-assoc _ _ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ η                                                     ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
            𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                                                     ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroˡ _)) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ 𝟘 ·ᶜ wkConₘ ρ γ₁                          ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (+ᶜ-congˡ (·ᶜ-congʳ ∣S∣≡𝟘)) ⟩
            (𝟘 · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₁     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congʳ ∣S∣≡𝟘)) ⟩
            (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₁ ∎)

    ▸-⇒ₙ-J : γ ▸ʰ H → η ▸ˢ S → m ≡ ⌞ ∣ S ∣ ⌟ → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η → InvUsageJ δ m p q A t B u v w
           → ∃₃ (_⨾_⨾_▸ ⟨ H , w , ρ , Jₑ p q A t B u v ρ ∙ S ⟩)
    ▸-⇒ₙ-J {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageJ {γ₄} {γ₆} e e′ _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₙ-J-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u ▸w
    ▸-⇒ₙ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} ▸H ▸S m≡ γ≤
           (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} e e′ _ _ _ ▸u _ ▸w δ≤) rewrite ∣∣ᵉ-J-ω e e′ =
      _ , _ , _ , ▸H , ▸-cong (trans m≡ (sym (≢𝟘→⌞·⌟≡ʳ ω≢𝟘))) ▸w
        , Jₑ (▸-cong m≡ ▸u) ∙ ▸S
        , (begin
            γ                                                               ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η                   ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-distribˡ-+ᶜ ω _ _))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄ +ᶜ ω ·ᶜ (γ₅ +ᶜ γ₆)) +ᶜ η              ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (+ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄ +ᶜ ω ·ᶜ γ₆) +ᶜ η                      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
            ∣ S ∣ ·ᶜ (wkConₘ ρ (ω ·ᶜ γ₄) +ᶜ wkConₘ ρ (ω ·ᶜ γ₆)) +ᶜ η         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-cong (wk-·ᶜ ρ) (wk-·ᶜ ρ))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ γ₄ +ᶜ ω ·ᶜ wkConₘ ρ γ₆) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneˡ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ (𝟙 ·ᶜ wkConₘ ρ γ₄ +ᶜ ω ·ᶜ wkConₘ ρ γ₆) +ᶜ η             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ (wkConₘ ρ γ₄ +ᶜ ω ·ᶜ wkConₘ ρ γ₆) +ᶜ η                  ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            (∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ ∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₆) +ᶜ η         ≈⟨ +ᶜ-congʳ (+ᶜ-comm _ _) ⟩
            (∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₆ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄) +ᶜ η         ≈⟨ +ᶜ-assoc _ _ _ ⟩
            ∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₆ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η           ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
            (∣ S ∣ · ω) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄          ∎)
    ▸-⇒ₙ-J {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageJ₀₁ {γ₄} {γ₆} e _ _ _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₙ-J-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸w)
    ▸-⇒ₙ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} ▸H ▸S m≡ γ≤
      (invUsageJ₀₁ {γ₃} {γ₄} {γ₆} e≡some refl refl _ _ _ ▸u _ ▸w δ≤) rewrite ∣∣ᵉ-J-some₀₀ e≡some =
      _ , _ , _ , ▸H , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟≡𝟘ᵐ?)) ▸w
        , Jₑ (▸-cong m≡ ▸u) ∙ ▸S
        , (begin
            γ                                                      ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄)) +ᶜ η                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄) +ᶜ η                        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (𝟙 ·ᶜ γ₄) +ᶜ η                        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η                               ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                               ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                         ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎)
    ▸-⇒ₙ-J {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageJ₀₂ e≡all _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₙ-J-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸w)
    ▸-⇒ₙ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} {q} ▸H ▸S m≡ γ≤
      (invUsageJ₀₂ {γ₄} {γ₆} e≡all _ _ _ ▸u _ ▸w δ≤) rewrite ∣∣ᵉ-J-all {p = p} {q = q} e≡all =
      _ , _ , _ , ▸H , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟≡𝟘ᵐ?)) ▸w
        , Jₑ (▸-cong m≡ ▸u) ∙ ▸S
        , (begin
            γ                                                       ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η                               ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                               ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                         ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎)

  ▸-⇒ₙ (▸H , ▸t , ▸S , γ≤) (Kₕ {H}) = ▸-⇒ₙ-K ▸H ▸S refl γ≤ (inv-usage-K ▸t)
    where
    em : Erased-matches
    em = erased-matches-for-K 𝟙ᵐ
    open RPo ≤ᶜ-poset
    ▸-⇒ₙ-K-𝟘ᵐ : ∀ {γ₁ γ₂ ok}
              → γ ▸ʰ H → η ▸ˢ S → ∣ S ∣ ≡ 𝟘 → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η
              → γ₁ ▸[ 𝟘ᵐ[ ok ] ] u → γ₂ ▸[ 𝟘ᵐ[ ok ] ] v
              → ∃₃ (_⨾_⨾_▸ ⟨ H , v , ρ , Kₑ p A t B u ρ ∙ S ⟩)
    ▸-⇒ₙ-K-𝟘ᵐ {γ} {η} {S} {ρ} {δ} {p} {γ₁} {γ₂} ▸H ▸S ∣S∣≡𝟘 γ≤ ▸u ▸v =
      _ , _ , _ , ▸H
        , ▸-cong (trans (sym ⌞𝟘⌟) (⌞⌟-cong (sym (trans (·-congʳ ∣S∣≡𝟘) (·-zeroˡ _))))) ▸v
        , Kₑ (▸-cong (sym (≡𝟘→⌞⌟≡𝟘ᵐ ∣S∣≡𝟘)) ▸u) ∙ ▸S
        , (begin
            γ                                                               ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                        ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡𝟘) ⟩
            𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η                                            ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘ᶜ +ᶜ η                                                         ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityʳ _) ⟩
            (𝟘ᶜ +ᶜ 𝟘ᶜ) +ᶜ η                                                 ≈⟨ +ᶜ-assoc _ _ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ η                                                   ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
            𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                                                   ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroˡ _)) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ 𝟘 ·ᶜ wkConₘ ρ γ₁                       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (+ᶜ-congˡ (·ᶜ-congʳ ∣S∣≡𝟘)) ⟩
            (𝟘 · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₁     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congʳ ∣S∣≡𝟘)) ⟩
            (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₁ ∎)
    ▸-⇒ₙ-K : γ ▸ʰ H → η ▸ˢ S → m ≡ ⌞ ∣ S ∣ ⌟ → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η → InvUsageK δ m p A t B u v
           → ∃₃ (_⨾_⨾_▸ ⟨ H , v , ρ , Kₑ p A t B u ρ ∙ S ⟩)
    ▸-⇒ₙ-K {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageK _ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₙ-K-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u ▸v
    ▸-⇒ₙ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≡ γ≤
      (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} e e′ _ _ _ ▸u ▸v δ≤) rewrite ∣∣ᵉ-K-ω e e′ =
      _ , _ , _ , ▸H , ▸-cong (trans m≡ (sym (≢𝟘→⌞·⌟≡ʳ ω≢𝟘))) ▸v
        , Kₑ (▸-cong m≡ ▸u) ∙ ▸S
        , (begin
            γ                                                       ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)) +ᶜ η     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅)) +ᶜ η           ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₄ +ᶜ γ₅)) +ᶜ η                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ (γ₄ +ᶜ γ₅)) +ᶜ η                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-comm _ _)))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ (γ₅ +ᶜ γ₄)) +ᶜ η                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-congˡ (wk-+ᶜ ρ))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ (wkConₘ ρ γ₅ +ᶜ wkConₘ ρ γ₄)) +ᶜ η        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ γ₅ +ᶜ ω ·ᶜ wkConₘ ρ γ₄) +ᶜ η     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ γ₅ +ᶜ 𝟙 ·ᶜ wkConₘ ρ γ₄) +ᶜ η     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ γ₅ +ᶜ wkConₘ ρ γ₄) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            (∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₅ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
            ∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₅ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
            (∣ S ∣ · ω) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄  ∎)
    ▸-⇒ₙ-K {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageK₀₁ _ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₙ-K-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸-⇒ₙ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≡ γ≤
      (invUsageK₀₁ {γ₃} {γ₄} {γ₅} e≡some refl _ _ _ ▸u ▸v δ≤) rewrite ∣∣ᵉ-K-some₀ e≡some =
      _ , _ , _ , ▸H , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟≡𝟘ᵐ?)) ▸v
        , Kₑ (▸-cong m≡ ▸u) ∙ ▸S
        , (begin
            γ                                                       ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ                                ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄))                ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄)                        ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (𝟙 ·ᶜ γ₄)                        ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-identityˡ _))) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                               ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                         ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎)
    ▸-⇒ₙ-K {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageK₀₂ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₙ-K-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸-⇒ₙ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≡ γ≤
      (invUsageK₀₂ {γ₄} {γ₅} e≡all _ _ _ ▸u ▸v δ≤) rewrite ∣∣ᵉ-K-all {p = p} e≡all =
      _ , _ , _ , ▸H , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟≡𝟘ᵐ?)) ▸v
        , Kₑ (▸-cong m≡ ▸u) ∙ ▸S
        , (begin
            γ                                                       ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ                                ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                               ≈˘⟨ +ᶜ-identityˡ _  ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                         ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎)

  ▸-⇒ₙ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) ([]-congₕ {ρ} {S}) =
    case inv-usage-[]-cong ▸t of λ
      (invUsage-[]-cong {γ₄} _ _ _ ▸v ok δ≤) →
    _ , _ , _ , ▸H , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟≡𝟘ᵐ?)) ▸v
      , []-congₑ ok ∙ ▸S
      , (begin
          γ                                              ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η                      ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ _) (wk-𝟘ᶜ ρ) ⟩
          ∣ S ∣ ·ᶜ 𝟘ᶜ +ᶜ η                               ≈⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-sym (+ᶜ-identityʳ _)) ⟩
          𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                                  ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          𝟘 ·ᶜ wkConₘ ρ γ₄ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₄ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎)
    where
    open RPo ≤ᶜ-poset

opaque

  -- Usage preservation under _⇒ₛ_

  ▸-⇒ₛ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ₛ s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒ₛ {γ} {δ} {η} (▸H , ▸t , ▸S , γ≤) (sucₕ {ρ} {k} x) =
    case inv-usage-suc ▸t of λ
      (invUsageSuc {δ = δ′} ▸t δ≤) →
    _ , _ , _ , ▸H , ▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t , sucₑ ∙ ▸S , (begin
      γ                                                        ≤⟨ γ≤ ⟩
      ∣ sucₛ k ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                            ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
      ∣ sucₛ k ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η                           ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
      (∣ sucₛ k ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ               ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      (∣ sucₛ k ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ sucₛ k ∣ ·ᶜ 𝟘ᶜ ∎)
    where
    open RPo ≤ᶜ-poset
  ▸-⇒ₛ {γ} {δ} (▸H , ▸t , _∙_ {γ = η} ▸e ▸S , γ≤) (numₕ {ρ} {S} x) =
    case ▸e of λ {
      sucₑ →
    _ , _ , _ , ▸H , sucₘ (▸-cong (⌞⌟-cong (·-identityʳ _)) ▸t) , ▸S , (begin
      γ                                             ≤⟨ γ≤ ⟩
      (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ          ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                      ∎) }
    where
    open RPo ≤ᶜ-poset


opaque

  -- Well-resourced states evaluate to well-resourced states

  ▸-⇒ : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒ s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒ ▸s (⇒ₙ d) = ▸-⇒ₙ ▸s d
  ▸-⇒ ▸s (⇒ᵥ d) = ▸-⇒ᵥ ▸s d
  ▸-⇒ ▸s (⇒ₛ d) = ▸-⇒ₛ ▸s d

opaque

  -- Well-resourced states evaluate to well-resourced states

  ▸-⇒* : (▸s : γ ⨾ δ ⨾ η ▸ s) (d : s ⇒* s′) → ∃₃ (_⨾_⨾_▸ s′)
  ▸-⇒* ▸s id =
    _ , _ , _ , ▸s
  ▸-⇒* ▸s (d ⇨ d′) =
    case ▸-⇒ ▸s d of λ
      (_ , _ , _ , ▸s′) →
    ▸-⇒* ▸s′ d′
