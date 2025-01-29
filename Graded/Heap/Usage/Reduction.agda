------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States
-- and the reduction relation with resource tracking.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Usage.Restrictions.Natrec
open import Definition.Typed.Variant
open import Tools.Relation
import Graded.Mode

module Graded.Heap.Usage.Reduction
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Type-variant type-variant)
  (open Usage-restrictions UR)
  (open Graded.Mode 𝕄)
  (open Modality 𝕄)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (Unitʷ-η→ : ∀ {p q} → Unitʷ-η → Unitrec-allowed 𝟙ᵐ p q → p ≤ 𝟘)
  (¬Nr-not-available : ¬ Nr-not-available)
  ⦃ _ : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum
import Tools.Reasoning.PartialOrder as RPo
import Tools.Reasoning.PropositionalEquality as RPe
import Tools.Reasoning.Equivalence as REq

open import Definition.Untyped M

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr
open import Graded.Heap.Usage.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage.Weakening type-variant UR factoring-nr

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Weakening 𝕄 UR
open import Graded.Restrictions 𝕄

private variable
  γ δ η γ′ δ′ θ : Conₘ _
  s s′ : State _ _ _
  m : Mode
  A B t u v w : Term _
  p p′ q q′ : M
  ρ : Wk _ _
  H : Heap _ _
  S : Stack _

opaque

  -- Usage preservation under _⇒ᵥ_

  ▸-⇒ᵥ : ▸ s → s ⇒ᵥ s′ → ▸ s′
  ▸-⇒ᵥ ▸s (lamₕ {p} {ρ} {ρ′} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , θ≈ = ▸-inv-∘ₑ ▸e
        invUsageLam {δ = δ′} ▸t δ≤ = inv-usage-lam ▸t
        γ≤ = begin
              γ                                                          ≤⟨ γ≤ ⟩
              (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ               ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _))
                                                                                  (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
              ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ′ θ′     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
              ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ′ θ′    ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
              (∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η) +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ′ θ′  ≈˘⟨ +ᶜ-congˡ (·ᶜ-assoc _ _ _) ⟩
              (∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η) +ᶜ (∣ S ∣ · p) ·ᶜ wkConₘ ρ′ θ′ ∎
    in  ▸ₛ (subₕ ▸H γ≤ ∙ ▸ᶜᵖ (▸-cong ⌞⌟ᵐ· ▸u))
           (▸-cong (⌞⌟-cong (trans (·-identityʳ _) (wk-∣S∣ (step id) S))) ▸t)
           (wk-▸ˢ (step id) ▸S) $ begin
             ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ S ∣ · p                                   ≈˘⟨ ≈ᶜ-refl ∙ ·-congʳ ·⌜⌞⌟⌝ ⟩
             ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ (∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) · p                 ≈⟨ ≈ᶜ-refl ∙ ·-assoc _ _ _ ⟩
             ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p                   ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ (step id) S)) ∙ ·-congʳ (wk-∣S∣ (step id) S) ⟩
             ∣ wk1ˢ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p         ≈˘⟨ ≈ᶜ-refl ∙ ·-congˡ (·-congʳ (cong (λ x → ⌜ ⌞ x ⌟ ⌝) (·-identityʳ _))) ⟩
             ∣ wk1ˢ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · ⌜ ⌞ ∣ S ∣ · 𝟙 ⌟ ⌝ · p     ≈˘⟨ ≈ᶜ-refl ∙ +-identityʳ _ ⟩
             ∣ wk1ˢ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η ∙ ∣ wk1ˢ S ∣ · ⌜ ⌞ ∣ S ∣ · 𝟙 ⌟ ⌝ · p + 𝟘 ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (prodˢₕ₁ {p} {ρ} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        mp-cond , θ≈𝟘 = ▸-inv-fstₑ ▸e
        invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤ = inv-usage-prodˢ ▸t
    in  ▸ₛ ▸H (▸-cong (lemma′ mp-cond) ▸t) ▸S $ begin
      γ                                            ≤⟨ γ≤ ⟩
     (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ  ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _))
                                                            (+ᶜ-congˡ (·ᶜ-congˡ θ≈𝟘)) ⟩
     ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ       ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
     ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ                ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
     ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
     ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (∧ᶜ-decreasingˡ _ _))) ⟩
     ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁) +ᶜ η              ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
     ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ δ₁ +ᶜ η                ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
     (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ₁ +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ (lemma mp-cond)) ⟩
     ∣ S ∣ ·ᶜ wkConₘ ρ δ₁ +ᶜ η                     ∎
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
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (prodˢₕ₂ {p} {ρ} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ≈ = ▸-inv-sndₑ ▸e
        invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤ = inv-usage-prodˢ ▸t
    in  ▸ₛ ▸H (▸-cong (⌞⌟-cong (·-identityʳ _)) ▸u) ▸S $ begin
        γ                                            ≤⟨ γ≤ ⟩
        (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ      ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ               ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ η) ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (∧ᶜ-decreasingʳ (p ·ᶜ δ₁) δ₂))) ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ δ₂ +ᶜ η                    ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (prodʷₕ {p} {t₁} {ρ} {r} {ρ′} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , ok , θ≈ = ▸-inv-prodrecₑ ▸e
        invUsageProdʷ {δ = δ′} {η = η′} ▸t₁ ▸t₂ δ≤ = inv-usage-prodʷ ▸t
        γ≤′ : γ ≤ᶜ ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ
                   (∣ S ∣ · r · p + (∣ S ∣ · r) · 𝟘) ·ᶜ wkConₘ ρ δ′
        γ≤′ = begin
          γ                                                                                                                ≤⟨ γ≤ ⟩
          (∣ S ∣ · r) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ                                                                     ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
          (∣ S ∣ · r) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                                                          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          (∣ S ∣ · r) ·ᶜ wkConₘ ρ (p ·ᶜ δ′ +ᶜ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                                            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
          (∣ S ∣ · r) ·ᶜ (wkConₘ ρ (p ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ ρ))) ⟩
          (∣ S ∣ · r) ·ᶜ (p ·ᶜ wkConₘ ρ δ′ +ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                                   ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ (∣ S ∣ · r) _ _) ⟩
          ((∣ S ∣ · r) ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                    ≈˘⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-assoc (∣ S ∣ · r) p _)) ⟩
          (((∣ S ∣ · r) · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                   ≈⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-congʳ (·-assoc ∣ S ∣ r p))) ⟩
          ((∣ S ∣ · r · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                     ≈⟨ +ᶜ-comm _ _ ⟩
          (η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′                     ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
          (η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′ +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ ρ δ′                     ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ (∣ S ∣ · r · p) ·ᶜ wkConₘ ρ δ′                   ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-identityʳ _)) ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ (∣ S ∣ · r · p + 𝟘) ·ᶜ wkConₘ ρ δ′               ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (+-congˡ (·-zeroʳ _))) ⟩
          ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ η′) +ᶜ (∣ S ∣ · r · p + (∣ S ∣ · r) · 𝟘) ·ᶜ wkConₘ ρ δ′ ∎
        ▸ᶜt₁ = subst₂ (λ x y → (δ′ ⨾ x ▸ᶜ (y , _)))
                (trans (·-assoc _ _ _) (sym (trans (+-congˡ (·-zeroʳ _)) (+-identityʳ _))))
                (·-assoc _ _ _) (▸ᶜᵖ (▸-cong ⌞⌟ᵐ· ▸t₁))

    in  ▸ₛ (subₕ ▸H γ≤′ ∙ ▸ᶜt₁ ∙ ▸ᶜᵖ ▸t₂)
           (▸-cong (⌞⌟-cong (wk-∣S∣ (step (step id)) S)) ▸u)
           (wk-▸ˢ (step (step id)) ▸S)
           (lemma₁ ∙ lemma₂ ∙ lemma₂)
    where
    lemma₂ : ∀ {p} → ∣ S ∣ · p ≤ ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p + 𝟘
    lemma₂ {p} = begin
      ∣ S ∣ · p                          ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
      (∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) · p        ≡⟨ ·-assoc _ _ _ ⟩
      ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p          ≡⟨ ·-congʳ (wk-∣S∣ _ S) ⟩
      ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p     ≡˘⟨ +-identityʳ _ ⟩
      ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p + 𝟘 ∎
      where
      open RPo ≤-poset
    open ≤ᶜ-reasoning
    lemma₁ : ∀ {n} {γ η : Conₘ n} → η +ᶜ ∣ S ∣ ·ᶜ γ ≤ᶜ ∣ wk2ˢ S ∣ ·ᶜ γ +ᶜ η
    lemma₁ {γ} {η} = begin
      η +ᶜ ∣ S ∣ ·ᶜ γ      ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ γ +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ _ S)) ⟩
      ∣ wk2ˢ S ∣ ·ᶜ γ +ᶜ η ∎

  ▸-⇒ᵥ ▸s (zeroₕ {ρ} {p} {r} {q′} {ρ′} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        γ′ , δ′ , η′ , ▸z , ▸s , ▸A , extra = ▸-inv-natrecₑ ▸e
    in  ▸ₛ ▸H ▸z ▸S $ begin
      γ                                             ≤⟨ γ≤ ⟩
      (∣ S ∣ · q′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-zero ▸t))) ⟩
      (∣ S ∣ · q′) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · q′) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ                          ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ θ                                ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ θ +ᶜ η                                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (lemma extra)) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ γ′ +ᶜ η                     ∎
    where
    open ≤ᶜ-reasoning
    lemma : InvUsageNatrecₑ p r q′ γ δ ρ′ θ → θ ≤ᶜ wkConₘ ρ′ γ
    lemma (invUsageNatrecNr _) = wk-≤ᶜ ρ′ (nrᶜ-zero ≤ᶜ-refl)
    lemma (invUsageNatrecNoNr _ χ-glb) =
      wk-≤ᶜ ρ′ (≤ᶜ-trans (χ-glb .proj₁ 0) (≤ᶜ-reflexive nrᵢᶜ-zero))

  ▸-⇒ᵥ ▸s (sucₕ {t} {ρ} {p} {q} {r} {q′} {A} {z} {s} {ρ′} {S}) =
    let γ , δ , η , θ′ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        γ′ , δ′ , η′ , ▸z , ▸s , ▸A , extra = ▸-inv-natrecₑ ▸e
        invUsageSuc {δ = θ} ▸t δ≤ = inv-usage-suc ▸t
        χ , χ▸nr , ρ′χ≈θ′ = ▸nr ▸z ▸s ▸A extra
        q′≤ , θ′≤ = InvUsageNatrecₑ-≤ extra
    in case ▸ᶜᵖʳ χ▸nr of λ {
         (χ′ ∙ x , ▸ᶜnr , rχ≈rχ′ ∙ rq′S≡rx) →
       let ∣S∣q′≤ = let open RPo ≤-poset in begin
             ∣ S ∣ · q′                  ≤⟨ ·-monotoneʳ q′≤ ⟩
             ∣ S ∣ · (p + r · q′)        ≡⟨ ·-distribˡ-+ _ _ _ ⟩
             ∣ S ∣ · p + ∣ S ∣ · r · q′  ≡⟨ +-congˡ (lemma₁ rq′S≡rx) ⟩
             ∣ S ∣ · p + ∣ S ∣ · r · x   ≡˘⟨ +-congˡ (·-assoc _ _ _) ⟩
             ∣ S ∣ · p + (∣ S ∣ · r) · x ∎
           γ≤′ = let open ≤ᶜ-reasoning in begin
             γ                                                                                            ≤⟨ γ≤ ⟩
             (∣ S ∣ · q′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ′                                               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
             (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ′                                               ≈⟨ +ᶜ-comm _ _ ⟩
             (η +ᶜ ∣ S ∣ ·ᶜ θ′) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ                                             ≤⟨ +ᶜ-monotoneˡ (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ θ′≤)) ⟩
             (η +ᶜ ∣ S ∣ ·ᶜ (wkConₘ ρ′ δ′ +ᶜ r ·ᶜ θ′)) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ                      ≈⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
             (η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ ∣ S ∣ ·ᶜ r ·ᶜ θ′) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ               ≈˘⟨ +ᶜ-congʳ (+ᶜ-assoc _ _ _) ⟩
             ((η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′) +ᶜ ∣ S ∣ ·ᶜ r ·ᶜ θ′) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ             ≈˘⟨ +ᶜ-congʳ (+ᶜ-cong (+ᶜ-comm _ _)
                                                                                                            (·ᶜ-congˡ (·ᶜ-congˡ ρ′χ≈θ′))) ⟩
             ((∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η) +ᶜ ∣ S ∣ ·ᶜ r ·ᶜ wkConₘ ρ′ χ) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ    ≈˘⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-congˡ (wk-·ᶜ ρ′))) ⟩
             ((∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ (r ·ᶜ χ)) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ  ≈⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-congˡ (wk-≈ᶜ ρ′ rχ≈rχ′))) ⟩
             ((∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ (r ·ᶜ χ′)) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ ≈⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-congˡ (wk-·ᶜ ρ′))) ⟩
             ((∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η) +ᶜ ∣ S ∣ ·ᶜ r ·ᶜ wkConₘ ρ′ χ′) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ   ≈˘⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-assoc _ _ _)) ⟩
             ((∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ′ χ′) +ᶜ (∣ S ∣ · q′) ·ᶜ wkConₘ ρ θ  ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneˡ ∣S∣q′≤) ⟩
             ((∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η) +ᶜ (∣ S ∣ · r) ·ᶜ wkConₘ ρ′ χ′) +ᶜ
                                              (∣ S ∣ · p + (∣ S ∣ · r) · x) ·ᶜ wkConₘ ρ θ                 ∎
       in  ▸ₛ (subₕ ▸H γ≤′ ∙ ▸ᶜ ▸t ∣S∣q′≤ ∙ ▸ᶜnr)
              (▸-cong (⌞⌟-cong (wk-∣S∣ _ S)) ▸s)
              (wk-▸ˢ (step (step id)) ▸S)
              (≤ᶜ-reflexive
                (+ᶜ-congʳ (·ᶜ-congʳ (wk-∣S∣ _ S)) ∙
                 lemma₂ p ∙ lemma₂ r))}
    where
    lemma₁ : ∀ {p q q′ r} → p · q · ⌜ ⌞ r ⌟ ⌝ ≡ p · q′ → r · p · q ≡ r · p · q′
    lemma₁ {p} {q} {q′} {r} eq = case is-𝟘? r of λ where
      (yes refl) → trans (·-zeroˡ _) (sym (·-zeroˡ _))
      (no r≢𝟘) → ·-congˡ $ begin
        p · q             ≡˘⟨ ·-congˡ (·-identityʳ _) ⟩
        p · q · 𝟙         ≡˘⟨ ·-congˡ (·-congˡ (cong ⌜_⌝ (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘))) ⟩
        p · q · ⌜ ⌞ r ⌟ ⌝ ≡⟨ eq ⟩
        p · q′            ∎
        where
        open RPe
    lemma₂ : ∀ p → ∣ S ∣ · p ≡ ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p + 𝟘
    lemma₂ p = begin
      ∣ S ∣ · p                          ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
      (∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) · p        ≡⟨ ·-assoc _ _ _ ⟩
      ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p          ≡⟨ ·-congʳ (wk-∣S∣ _ S) ⟩
      ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p     ≡˘⟨ +-identityʳ _ ⟩
      ∣ wk2ˢ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝ · p + 𝟘 ∎
      where
      open RPe
    ▸nr : γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s →
          η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A → InvUsageNatrecₑ p r q′ γ δ ρ′ θ →
          ∃ λ χ → χ ∙ q′ · ⌜ m ⌝ ▸[ m ] natrec p q r (wk (lift (step id)) A) (wk (step id) z) (wk (liftn (step id) 2) s) (var x0) × wkConₘ ρ′ χ ≈ᶜ θ
    ▸nr ▸z ▸s ▸A (invUsageNatrecNr q′≡nr₂) =
      _ , sub (natrecₘ (wkUsage (step id) ▸z)
                (wkUsage (liftn (step id) 2) ▸s)
                (var {x = x0})
                (wkUsage (lift (step id)) ▸A))
              (≤ᶜ-refl ∙ ≤-reflexive (trans (·-congʳ q′≡nr₂) (sym (trans nr-factoring
                          (trans (+-congˡ nr-𝟘) (+-identityʳ _))))))
        , ≈ᶜ-refl
    ▸nr ▸z ▸s ▸A (invUsageNatrecNoNr x-glb χ-glb) =
      _ , sub (natrec-no-nr-glbₘ (wkUsage (step id) ▸z)
                (wkUsage (liftn (step id) 2) ▸s) var
                (wkUsage (lift (step id)) ▸A) x-glb
                         (GLBᶜ-congˡ (λ i → ≈ᶜ-sym (≈ᶜ-refl ∙ nrᵢ-𝟘 i))
                           (wk-GLBᶜ (step id) χ-glb)))
              (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroʳ _)) (+ᶜ-identityˡ _)) ∙
                (sym (+-identityʳ _))))
        , ≈ᶜ-refl

  ▸-⇒ᵥ ▸s (starʷₕ {ρ} {p} {ρ′} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , _ , _ , θ≈  = ▸-inv-unitrecₑ ▸e
        δ≤𝟘 = inv-usage-starʷ ▸t
    in  ▸ₛ ▸H ▸u ▸S $ begin
      γ                                                       ≤⟨ γ≤ ⟩
      (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ             ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
      (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤𝟘)) ⟩
      (∣ S ∣ · p) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′ ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                         ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                               ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′ +ᶜ η                               ∎

    where
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (unitrec-ηₕ {p} {ρ} {S} η-ok) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageUnitrec {δ = δ₁} {η = δ₂} ▸t ▸u _ ok δ≤ = inv-usage-unitrec ▸t
    in  ▸ₛ ▸H ▸u ▸S (lemma _ refl γ≤ δ≤ ok)
    where
    open ≤ᶜ-reasoning
    lemma : ∀ {δ₁ δ₂} m → m ≡ ⌞ ∣ S ∣ ⌟
          → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η
          → δ ≤ᶜ p ·ᶜ δ₁ +ᶜ δ₂
          → Unitrec-allowed m p q
          → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ₂ +ᶜ η
    lemma {γ} {δ} {η} {δ₂} 𝟘ᵐ m≡ γ≤ δ≤ ok = begin
      γ                         ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡))) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘ᶜ +ᶜ η                   ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ₂ +ᶜ η     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡))) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ₂ +ᶜ η ∎
    lemma {γ} {δ} {η} {δ₁} {δ₂} 𝟙ᵐ m≡ γ≤ δ≤ ok = begin
      γ                                      ≤⟨ γ≤ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (+ᶜ-monotoneˡ
                                                           (·ᶜ-monotoneˡ (Unitʷ-η→ η-ok ok))))) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (𝟘 ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-congʳ (·ᶜ-zeroˡ δ₁)))) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ (𝟘ᶜ +ᶜ δ₂) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-identityˡ δ₂))) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ δ₂ +ᶜ η              ∎

  ▸-⇒ᵥ ▸s (rflₕⱼ {ρ} {p} {q} {ρ′} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , θ≈  = ▸-inv-Jₑ ▸e
        δ≤𝟘 = inv-usage-rfl ▸t
    in  ▸ₛ ▸H ▸u ▸S $ begin
      γ                                                                  ≤⟨ γ≤ ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ             ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-rfl ▸t))) ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′ ≡⟨ cong (λ x → (_ · _) ·ᶜ x +ᶜ η +ᶜ _ ·ᶜ wkConₘ ρ′ θ′) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                                    ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                                          ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′ +ᶜ η                                          ∎
    where
    em : Erased-matches
    em = erased-matches-for-J 𝟙ᵐ
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (rflₕₖ {ρ} {p} {ρ′} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , θ≈  = ▸-inv-Kₑ ▸e
        δ≤𝟘 = inv-usage-rfl ▸t
    in  ▸ₛ ▸H ▸u ▸S $ begin
      γ                                                                 ≤⟨ γ≤ ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ              ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-rfl ▸t))) ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′  ≡⟨ cong (λ x → (_ · _) ·ᶜ x +ᶜ η +ᶜ _ ·ᶜ wkConₘ ρ′ θ′) (wk-𝟘ᶜ ρ) ⟩
      (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′           ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                                   ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′                                         ≈⟨ +ᶜ-comm _ _ ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ θ′ +ᶜ η                                         ∎
    where
    em : Erased-matches
    em = erased-matches-for-K 𝟙ᵐ
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (rflₕₑ {ρ} {ρ′} {S}) =
    let γ , δ , η , θ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        ok , θ≈𝟘  = ▸-inv-[]-congₑ ▸e
    in  ▸ₛ ▸H rflₘ ▸S $ begin
      γ                                             ≤⟨ γ≤ ⟩
      (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ θ  ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈𝟘)) ⟩
      (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ                    ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-identityʳ _) ⟩
      𝟘ᶜ +ᶜ η                                       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      ∣ S ∣ ·ᶜ 𝟘ᶜ +ᶜ η                              ≡˘⟨ cong (λ x → _ ·ᶜ x +ᶜ η) (wk-𝟘ᶜ ρ′) ⟩
      ∣ S ∣ ·ᶜ wkConₘ ρ′ 𝟘ᶜ +ᶜ η                    ∎
    where
    open ≤ᶜ-reasoning

opaque

  -- Usage preservation under _⇒ₑ_

  ▸-⇒ₑ : ▸ s → s ⇒ₑ s′ → ▸ s′
  ▸-⇒ₑ ▸s (appₕ {p} {ρ} {S}) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageApp {(δ′)} {(η′)} ▸t ▸u δ≤ = inv-usage-app ▸t
    in  ▸ₛ ▸H (▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t)
               (∘ₑ ▸u ∙ ▸S) $ begin
               γ                                                            ≤⟨ γ≤ ⟩
               ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
               ∣ S ∣ ·ᶜ wkConₘ ρ (δ′ +ᶜ p ·ᶜ η′) +ᶜ η                       ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
               ∣ S ∣ ·ᶜ (wkConₘ ρ δ′ +ᶜ wkConₘ ρ (p ·ᶜ η′)) +ᶜ η            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (wk-·ᶜ ρ))) ⟩
               ∣ S ∣ ·ᶜ (wkConₘ ρ δ′ +ᶜ p ·ᶜ wkConₘ ρ η′) +ᶜ η              ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
               (∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ η′) +ᶜ η     ≈⟨ +ᶜ-assoc _ _ _ ⟩
               ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ η′ +ᶜ η       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-comm _ _) ⟩
               (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ η′ ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (fstₕ {ρ} {S}) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageFst {(δ′)} m eq ▸t δ≤ mp-cond = inv-usage-fst ▸t
    in  ▸ₛ ▸H (▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t)
               (fstₑ mp-cond ∙ ▸S) $ begin
               γ                                              ≤⟨ γ≤ ⟩
               ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
               ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η                      ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
               (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ          ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
               (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (sndₕ {ρ} {S}) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageSnd {(δ′)} ▸t δ≤ = inv-usage-snd ▸t
    in  ▸ₛ ▸H (▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t)
                (sndₑ ∙ ▸S) $ begin
                γ                                               ≤⟨ γ≤ ⟩
                ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                        ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
                ∣ S ∣ ·ᶜ wkConₘ ρ δ′ +ᶜ η                       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
                (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ           ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
                (∣ S ∣ · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (prodrecₕ {r} {p} {u} {ρ} {S}) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageProdrec {(δ′)} {(η′)} ▸t ▸u _ ok δ≤ = inv-usage-prodrec ▸t
    in  ▸ₛ ▸H (▸-cong ⌞⌟ᵐ· ▸t) (prodrecₑ ▸u ok ∙ ▸S) $ begin
                γ                                                         ≤⟨ γ≤ ⟩
                ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
                ∣ S ∣ ·ᶜ wkConₘ ρ (r ·ᶜ δ′ +ᶜ η′) +ᶜ η                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
                ∣ S ∣ ·ᶜ (wkConₘ ρ (r ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ ∣ S ∣ _ _) ⟩
                (∣ S ∣ ·ᶜ wkConₘ ρ (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
                ∣ S ∣ ·ᶜ wkConₘ ρ (r ·ᶜ δ′) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (+ᶜ-comm _ η) ⟩
                ∣ S ∣ ·ᶜ r ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′     ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc ∣ S ∣ r _) ⟩
                (∣ S ∣ · r) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′    ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (unitrecₕ {p} {ρ} {S} no-η) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageUnitrec {(δ′)} {(η′)} ▸t ▸u _ ok δ≤ = inv-usage-unitrec ▸t
    in  ▸ₛ ▸H (▸-cong ⌞⌟ᵐ· ▸t) (unitrecₑ ▸u ok no-η ∙ ▸S) $ begin
          γ                                                        ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                 ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ′ +ᶜ η′) +ᶜ η                   ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
          ∣ S ∣ ·ᶜ (wkConₘ ρ (p ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ ρ))) ⟩
          ∣ S ∣  ·ᶜ (p ·ᶜ wkConₘ ρ δ′ +ᶜ wkConₘ ρ η′) +ᶜ η         ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          (∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
          ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′ +ᶜ η   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
          (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ η′  ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (emptyrecₕ {p} {ρ} {S}) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageEmptyrec {(δ′)} ▸t _ ok δ≤ = inv-usage-emptyrec ▸t
    in  ▸ₛ ▸H (▸-cong ⌞⌟ᵐ· ▸t) (emptyrecₑ ok ∙ ▸S) $ begin
        γ                                                 ≤⟨ γ≤ ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                          ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
        ∣ S ∣ ·ᶜ wkConₘ ρ (p ·ᶜ δ′) +ᶜ η                  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (≈ᶜ-sym (+ᶜ-identityʳ η)) ⟩
        ∣ S ∣ ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ              ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
        (∣ S ∣ · p) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ    ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s Jₕ =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
    in  ▸-⇒ₑ-J ▸H ▸S refl γ≤ (inv-usage-J ▸t)
    where
    em : Erased-matches
    em = erased-matches-for-J 𝟙ᵐ
    open ≤ᶜ-reasoning
    ▸-⇒ₑ-J-𝟘ᵐ : ∀ {γ₁ γ₂ ok}
              → γ ▸ʰ H → η ▸ˢ S → ∣ S ∣ ≡ 𝟘 → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η
              → γ₁ ▸[ 𝟘ᵐ[ ok ] ] u → γ₂ ▸[ 𝟘ᵐ[ ok ] ] w
              → ▸ ⟨ H , w , ρ , Jₑ p q A t B u v ρ ∙ S ⟩
    ▸-⇒ₑ-J-𝟘ᵐ {γ} {η} {S} {ρ} {δ} {p} {q} {γ₁} {γ₂} ▸H ▸S ∣S∣≡𝟘 γ≤ ▸u ▸w =
      ▸ₛ ▸H
         (▸-cong (trans (sym ⌞𝟘⌟) (⌞⌟-cong (sym (trans (·-congʳ ∣S∣≡𝟘) (·-zeroˡ _))))) ▸w)
         (Jₑ (▸-cong (sym (≡𝟘→⌞⌟≡𝟘ᵐ ∣S∣≡𝟘)) ▸u) ∙ ▸S) $ begin
            γ                                                                 ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                          ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡𝟘) ⟩
            𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η                                              ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘ᶜ +ᶜ η                                                           ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityʳ _) ⟩
            (𝟘ᶜ +ᶜ 𝟘ᶜ) +ᶜ η                                                   ≈⟨ +ᶜ-assoc _ _ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ η                                                     ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
            𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                                                     ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroˡ _)) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ 𝟘 ·ᶜ wkConₘ ρ γ₁                          ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (+ᶜ-congˡ (·ᶜ-congʳ ∣S∣≡𝟘)) ⟩
            (𝟘 · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₁     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congʳ ∣S∣≡𝟘)) ⟩
            (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₁ ∎
    ▸-⇒ₑ-J : γ ▸ʰ H → η ▸ˢ S → m ≡ ⌞ ∣ S ∣ ⌟ → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η → InvUsageJ δ m p q A t B u v w
           → ▸ ⟨ H , w , ρ , Jₑ p q A t B u v ρ ∙ S ⟩
    ▸-⇒ₑ-J {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageJ {γ₄} {γ₆} e e′ _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₑ-J-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u ▸w
    ▸-⇒ₑ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} ▸H ▸S m≡ γ≤
           (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} e e′ _ _ _ ▸u _ ▸w δ≤) =
      ▸ₛ ▸H (▸-cong (trans m≡ (sym (≢𝟘→⌞·⌟≡ʳ (subst (_≢ 𝟘) (sym (∣∣ᵉ-J-ω e e′)) ω≢𝟘)))) ▸w)
        (Jₑ (▸-cong m≡ ▸u) ∙ ▸S) $ begin
            γ                                                                  ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                           ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η         ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆)) +ᶜ η                     ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-distribˡ-+ᶜ ω _ _))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄ +ᶜ ω ·ᶜ (γ₅ +ᶜ γ₆)) +ᶜ η                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (+ᶜ-monotoneʳ ω·ᶜ+ᶜ≤ω·ᶜʳ))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄ +ᶜ ω ·ᶜ γ₆) +ᶜ η                        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
            ∣ S ∣ ·ᶜ (wkConₘ ρ (ω ·ᶜ γ₄) +ᶜ wkConₘ ρ (ω ·ᶜ γ₆)) +ᶜ η           ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-cong (wk-·ᶜ ρ) (wk-·ᶜ ρ))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ γ₄ +ᶜ ω ·ᶜ wkConₘ ρ γ₆) +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneˡ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ (𝟙 ·ᶜ wkConₘ ρ γ₄ +ᶜ ω ·ᶜ wkConₘ ρ γ₆) +ᶜ η               ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ (wkConₘ ρ γ₄ +ᶜ ω ·ᶜ wkConₘ ρ γ₆) +ᶜ η                    ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            (∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ ∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₆) +ᶜ η           ≈⟨ +ᶜ-congʳ (+ᶜ-comm _ _) ⟩
            (∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₆ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄) +ᶜ η           ≈⟨ +ᶜ-assoc _ _ _ ⟩
            ∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₆ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η             ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
            (∣ S ∣ · ω) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄            ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ (∣∣ᵉ-J-ω e e′))) ⟩
            (∣ S ∣ · ∣∣ᵉ-J em _ _) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎
    ▸-⇒ₑ-J {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageJ₀₁ {γ₄} {γ₆} e _ _ _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₑ-J-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸w)
    ▸-⇒ₑ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} ▸H ▸S m≡ γ≤
           (invUsageJ₀₁ {γ₃} {γ₄} {γ₆} e≡some refl refl _ _ _ ▸u _ ▸w δ≤) =
      ▸ₛ ▸H (▸-cong (sym (trans (⌞⌟-cong (trans (·-congˡ (∣∣ᵉ-J-some₀₀ e≡some)) (·-zeroʳ _))) ⌞𝟘⌟≡𝟘ᵐ?)) ▸w)
         (Jₑ (▸-cong m≡ ▸u) ∙ ▸S) $ begin
            γ                                                                  ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                           ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄)) +ᶜ η                           ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄) +ᶜ η                                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (𝟙 ·ᶜ γ₄) +ᶜ η                                   ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η                                          ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                                          ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                                    ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                      ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄            ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ (∣∣ᵉ-J-some₀₀ e≡some))) ⟩
            (∣ S ∣ · ∣∣ᵉ-J em _ _) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎
    ▸-⇒ₑ-J {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageJ₀₂ e≡all _ _ _ ▸u _ ▸w δ≤) =
      ▸-⇒ₑ-J-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸w)
    ▸-⇒ₑ-J {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} {q} ▸H ▸S m≡ γ≤
           (invUsageJ₀₂ {γ₄} {γ₆} e≡all _ _ _ ▸u _ ▸w δ≤) =
      ▸ₛ ▸H (▸-cong (sym (trans (⌞⌟-cong (trans (·-congˡ (∣∣ᵉ-J-all e≡all)) (·-zeroʳ _))) ⌞𝟘⌟≡𝟘ᵐ?)) ▸w)
        (Jₑ (▸-cong m≡ ▸u) ∙ ▸S) $ begin
            γ                                                                  ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                           ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η                                          ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                                          ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                                    ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                      ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄            ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ (∣∣ᵉ-J-all e≡all))) ⟩
            (∣ S ∣ · ∣∣ᵉ-J em p q) ·ᶜ wkConₘ ρ γ₆ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎

  ▸-⇒ₑ ▸s Kₕ =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
    in  ▸-⇒ₑ-K ▸H ▸S refl γ≤ (inv-usage-K ▸t)
    where
    em : Erased-matches
    em = erased-matches-for-K 𝟙ᵐ
    open ≤ᶜ-reasoning
    ▸-⇒ₑ-K-𝟘ᵐ : ∀ {γ₁ γ₂ ok}
              → γ ▸ʰ H → η ▸ˢ S → ∣ S ∣ ≡ 𝟘 → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η
              → γ₁ ▸[ 𝟘ᵐ[ ok ] ] u → γ₂ ▸[ 𝟘ᵐ[ ok ] ] v
              → ▸ ⟨ H , v , ρ , Kₑ p A t B u ρ ∙ S ⟩
    ▸-⇒ₑ-K-𝟘ᵐ {γ} {η} {S} {ρ} {δ} {p} {γ₁} {γ₂} ▸H ▸S ∣S∣≡𝟘 γ≤ ▸u ▸v =
      ▸ₛ ▸H (▸-cong (trans (sym ⌞𝟘⌟) (⌞⌟-cong (sym (trans (·-congʳ ∣S∣≡𝟘) (·-zeroˡ _))))) ▸v)
         (Kₑ (▸-cong (sym (≡𝟘→⌞⌟≡𝟘ᵐ ∣S∣≡𝟘)) ▸u) ∙ ▸S) $ begin
            γ                                                               ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                        ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ ∣S∣≡𝟘) ⟩
            𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η                                            ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘ᶜ +ᶜ η                                                         ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityʳ _) ⟩
            (𝟘ᶜ +ᶜ 𝟘ᶜ) +ᶜ η                                                 ≈⟨ +ᶜ-assoc _ _ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ η                                                   ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
            𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                                                   ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroˡ _)) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ 𝟘 ·ᶜ wkConₘ ρ γ₁                       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (+ᶜ-congˡ (·ᶜ-congʳ ∣S∣≡𝟘)) ⟩
            (𝟘 · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₁     ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congʳ ∣S∣≡𝟘)) ⟩
            (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ γ₂ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₁ ∎
    ▸-⇒ₑ-K : γ ▸ʰ H → η ▸ˢ S → m ≡ ⌞ ∣ S ∣ ⌟ → γ ≤ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η → InvUsageK δ m p A t B u v
           → ▸ ⟨ H , v , ρ , Kₑ p A t B u ρ ∙ S ⟩
    ▸-⇒ₑ-K {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageK _ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₑ-K-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u ▸v
    ▸-⇒ₑ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≡ γ≤
           (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} e e′ _ _ _ ▸u ▸v δ≤) =
      ▸ₛ ▸H (▸-cong (trans m≡ (sym (≢𝟘→⌞·⌟≡ʳ (subst (_≢ 𝟘) (sym (∣∣ᵉ-K-ω e e′)) ω≢𝟘)))) ▸v)
        (Kₑ (▸-cong m≡ ▸u) ∙ ▸S) $ begin
            γ                                                                ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                         ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅)) +ᶜ η                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₄ +ᶜ γ₅)) +ᶜ η                         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ (γ₄ +ᶜ γ₅)) +ᶜ η                         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-comm _ _)))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ (γ₅ +ᶜ γ₄)) +ᶜ η                         ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-congˡ (wk-+ᶜ ρ))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ (wkConₘ ρ γ₅ +ᶜ wkConₘ ρ γ₄)) +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ γ₅ +ᶜ ω ·ᶜ wkConₘ ρ γ₄) +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ γ₅ +ᶜ 𝟙 ·ᶜ wkConₘ ρ γ₄) +ᶜ η             ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-identityˡ _))) ⟩
            ∣ S ∣ ·ᶜ (ω ·ᶜ wkConₘ ρ γ₅ +ᶜ wkConₘ ρ γ₄) +ᶜ η                  ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            (∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₅ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄) +ᶜ η         ≈⟨ +ᶜ-assoc _ _ _ ⟩
            ∣ S ∣ ·ᶜ ω ·ᶜ wkConₘ ρ γ₅ +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ +ᶜ η           ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
            (∣ S ∣ · ω) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄          ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ (∣∣ᵉ-K-ω e e′))) ⟩
            (∣ S ∣ · ∣∣ᵉ-K em _) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎
    ▸-⇒ₑ-K {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageK₀₁ _ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₑ-K-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸-⇒ₑ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≡ γ≤
           (invUsageK₀₁ {γ₃} {γ₄} {γ₅} e≡some refl _ _ _ ▸u ▸v δ≤) =
      ▸ₛ ▸H (▸-cong (sym (trans (⌞⌟-cong (trans (·-congˡ (∣∣ᵉ-K-some₀ e≡some)) (·-zeroʳ _))) ⌞𝟘⌟≡𝟘ᵐ?)) ▸v)
        (Kₑ (▸-cong m≡ ▸u) ∙ ▸S) $ begin
            γ                                                       ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ                                ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ (γ₃ +ᶜ γ₄))                ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ ω·ᶜ+ᶜ≤ω·ᶜʳ)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (ω ·ᶜ γ₄)                        ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (·ᶜ-monotoneˡ ω≤𝟙))) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ (𝟙 ·ᶜ γ₄)                        ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ (wk-≈ᶜ ρ (·ᶜ-identityˡ _))) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                               ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                         ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ (∣∣ᵉ-K-some₀ e≡some))) ⟩
            (∣ S ∣ · ∣∣ᵉ-K em _) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎
    ▸-⇒ₑ-K {m = 𝟘ᵐ} ▸H ▸S m≡ γ≤ (invUsageK₀₂ _ _ _ _ ▸u ▸v _) =
      ▸-⇒ₑ-K-𝟘ᵐ ▸H ▸S (⌞⌟≡𝟘ᵐ→≡𝟘 (sym m≡)) γ≤ ▸u (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸-⇒ₑ-K {γ} {η} {S} {m = 𝟙ᵐ} {ρ} {δ} {p} ▸H ▸S m≡ γ≤
           (invUsageK₀₂ {γ₄} {γ₅} e≡all _ _ _ ▸u ▸v δ≤) =
      ▸ₛ ▸H (▸-cong (sym (trans (⌞⌟-cong (trans (·-congˡ (∣∣ᵉ-K-all e≡all)) (·-zeroʳ _))) ⌞𝟘⌟≡𝟘ᵐ?)) ▸v)
        (Kₑ (▸-cong m≡ ▸u) ∙ ▸S) $ begin
            γ                                                                ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                         ≈⟨ +ᶜ-comm _ _ ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ δ                                         ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
            η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                                        ≈˘⟨ +ᶜ-identityˡ _  ⟩
            𝟘ᶜ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                                  ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
            𝟘 ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄                    ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
            (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄          ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ (∣∣ᵉ-K-all e≡all))) ⟩
            (∣ S ∣ · ∣∣ᵉ-K em p) ·ᶜ wkConₘ ρ γ₅ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ γ₄ ∎

  ▸-⇒ₑ ▸s ([]-congₕ {ρ} {S}) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsage-[]-cong {γ₄} _ _ _ ▸v ok δ≤ = inv-usage-[]-cong ▸t
    in  ▸ₛ ▸H (▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟≡𝟘ᵐ?)) ▸v)
           ([]-congₑ ok ∙ ▸S) $ begin
          γ                                              ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                       ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η                      ≡⟨ cong (λ x → _ ·ᶜ x +ᶜ η) (wk-𝟘ᶜ ρ) ⟩
          ∣ S ∣ ·ᶜ 𝟘ᶜ +ᶜ η                               ≈⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-sym (+ᶜ-identityʳ _)) ⟩
          𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                                  ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          𝟘 ·ᶜ wkConₘ ρ γ₄ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ           ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
          (∣ S ∣ · 𝟘) ·ᶜ wkConₘ ρ γ₄ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ 𝟘ᶜ ∎
    where
    open ≤ᶜ-reasoning

opaque

  ▸-⇾ₑ : ▸ s → s ⇾ₑ s′ → ▸ s′
  ▸-⇾ₑ ▸s (⇒ₑ d) = ▸-⇒ₑ ▸s d
  ▸-⇾ₑ {(n)} ▸s (var {ρ} {x} {S} {ρ′} d) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        γ≤′ = let open ≤ᶜ-reasoning in begin
          γ                                                       ≤⟨ γ≤ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-var ▸t))) ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ (𝟘ᶜ , x ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η         ≡⟨ cong (λ x → ∣ S ∣ ·ᶜ x +ᶜ η) (wk-,≔ ρ) ⟩
          ∣ S ∣ ·ᶜ (wkConₘ ρ 𝟘ᶜ , wkVar ρ x ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η ≡⟨ cong (λ x → ∣ S ∣ ·ᶜ (x , _ ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η) (wk-𝟘ᶜ ρ) ⟩
          ∣ S ∣ ·ᶜ (𝟘ᶜ , wkVar ρ x ≔ ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η          ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ 𝟘ᶜ ∣ S ∣ _ _) ⟩
          (∣ S ∣ ·ᶜ 𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣ · ⌜ ⌞ ∣ S ∣ ⌟ ⌝) +ᶜ η  ≈⟨ +ᶜ-congʳ (update-cong (·ᶜ-zeroʳ _) ·⌜⌞⌟⌝) ⟩
          (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η                           ∎
        γ⟨x⟩≤ = let open RPo ≤-poset in begin
          γ ⟨ wkVar ρ x ⟩                                          ≤⟨ lookup-monotone (wkVar ρ x) γ≤′ ⟩
          ((𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η) ⟨ wkVar ρ x ⟩            ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) η _ ⟩
          (𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) ⟨ wkVar ρ x ⟩ + η ⟨ wkVar ρ x ⟩ ≡⟨ cong (_+ η ⟨ wkVar ρ x ⟩) (update-lookup 𝟘ᶜ (wkVar ρ x)) ⟩
          ∣ S ∣ + η ⟨ wkVar ρ x ⟩                                  ≈⟨ +-comm _ _ ⟩
          η ⟨ wkVar ρ x ⟩ + ∣ S ∣                                  ∎
        δ′ , ▸t , ▸H′ = ▸-heapLookup d ▸H γ⟨x⟩≤
        open ≤ᶜ-reasoning
    in  ▸ₛ ▸H′ ▸t ▸S $ begin
          (γ , wkVar ρ x ≔ η ⟨ wkVar ρ x ⟩) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                                                 ≤⟨ +ᶜ-monotoneˡ (update-monotoneˡ _ γ≤′) ⟩
          ((𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η , wkVar ρ x ≔ η ⟨ wkVar ρ x ⟩) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                     ≈˘⟨ +ᶜ-congʳ (update-congʳ (+-identityˡ _)) ⟩
          ((𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) +ᶜ η , wkVar ρ x ≔ 𝟘 + η ⟨ wkVar ρ x ⟩) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                 ≡⟨ cong (_+ᶜ (∣ S ∣ ·ᶜ wkConₘ ρ′ δ′)) (update-distrib-+ᶜ _ η 𝟘 _ _) ⟩
          (((𝟘ᶜ , wkVar ρ x ≔ ∣ S ∣) , wkVar ρ x ≔ 𝟘) +ᶜ (η , wkVar ρ x ≔ η ⟨ wkVar ρ x ⟩)) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ ≡⟨ cong₂ (λ x y → (x +ᶜ y) +ᶜ (∣ S ∣ ·ᶜ wkConₘ ρ′ δ′)) update-twice (update-self η _) ⟩
          ((𝟘ᶜ , wkVar ρ x ≔ 𝟘) +ᶜ η) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                                                       ≡⟨ cong (λ x → (x +ᶜ η) +ᶜ (∣ S ∣ ·ᶜ wkConₘ ρ′ δ′)) 𝟘ᶜ,≔𝟘 ⟩
          (𝟘ᶜ +ᶜ η) +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                                                                         ≈⟨ +ᶜ-congʳ (+ᶜ-identityˡ η) ⟩
          η +ᶜ ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′                                                                                 ≈⟨ +ᶜ-comm η _ ⟩
          ∣ S ∣ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η                                                                                 ∎
  ▸-⇾ₑ ▸s (natrecₕ {p} {r} {q′} {H} {z} {s} {ρ} {S} ok) =
    let γ , δ , η , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        δ′ , η′ , ▸n , ▸e , δ≤ = lemma (inv-usage-natrec ▸t) ok
    in  ▸ₛ ▸H ▸n (▸e ∙ ▸S) $ begin
            γ                                                ≤⟨ γ≤ ⟩
            ∣ S ∣ ·ᶜ wkConₘ ρ δ +ᶜ η                         ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ δ≤) ⟩
            ∣ S ∣ ·ᶜ (q′ ·ᶜ wkConₘ ρ δ′ +ᶜ η′) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
            (∣ S ∣ ·ᶜ q′ ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
            ∣ S ∣ ·ᶜ q′ ·ᶜ wkConₘ ρ δ′ +ᶜ ∣ S ∣ ·ᶜ η′ +ᶜ η   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
            (∣ S ∣ · q′) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ ∣ S ∣ ·ᶜ η′  ∎
    where
    open ≤ᶜ-reasoning
    lemma : InvUsageNatrec γ ⌞ p′ ⌟ p q r A z s t →
            Ok-natrec-multiplicity p r q′ →
            ∃₂ λ δ η → δ ▸[ ⌞ p′ · q′ ⌟ ] t ×
              (η ▸ᵉ[ ⌞ p′ ⌟ ] natrecₑ p q r q′ A z s ρ ) ×
              wkConₘ ρ γ ≤ᶜ q′ ·ᶜ wkConₘ ρ δ +ᶜ η
    lemma {γ} (invUsageNatrec {δ} {η} {θ} ▸z ▸s ▸n ▸A γ≤ invUsageNatrecNr) ok =
      let q′≡nr₂ = Ok-natrec-multiplicity-nr-inv ok
      in  _ , _ , ▸-cong (sym (trans (⌞⌟-cong (·-congˡ q′≡nr₂)) (≢𝟘→⌞·⌟≡ʳ nr₂≢𝟘))) ▸n
            , natrecₑ ▸z ▸s ▸A q′≡nr₂ , (begin
          wkConₘ ρ γ                                           ≤⟨ wk-≤ᶜ ρ γ≤ ⟩
          wkConₘ ρ (nrᶜ p r δ η θ)                             ≈⟨ wk-≈ᶜ ρ nrᶜ-factoring ⟩
          wkConₘ ρ (nr₂ p r ·ᶜ θ +ᶜ nrᶜ p r δ η 𝟘ᶜ)            ≈⟨ wk-+ᶜ ρ ⟩
          wkConₘ ρ (nr₂ p r ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ) ≈⟨ +ᶜ-congʳ (wk-·ᶜ ρ) ⟩
          nr₂ p r ·ᶜ wkConₘ ρ θ +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)   ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ q′≡nr₂) ⟩
          q′ ·ᶜ wkConₘ ρ θ +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)        ∎)
    lemma {γ} (invUsageNatrec {θ} ▸z ▸s ▸n ▸A γ≤ (invUsageNatrecNoNrGLB {χ} {x = q″} q″-glb χ-glb)) ok =
      let q′-glb = Ok-natrec-multiplicity-no-nr-inv ok
          q″≡q′ = GLB-unique q″-glb q′-glb
      in  _ , _ , ▸-cong (sym (≢𝟘→⌞·⌟≡ʳ λ { refl → 𝟘≰𝟙 (q′-glb .proj₁ 0) })) ▸n
            , natrec-no-nrₑ ▸z ▸s ▸A q′-glb χ-glb , (begin
          wkConₘ ρ γ                       ≤⟨ wk-≤ᶜ ρ γ≤ ⟩
          wkConₘ ρ (q″ ·ᶜ θ +ᶜ χ)          ≈⟨ wk-+ᶜ ρ ⟩
          wkConₘ ρ (q″ ·ᶜ θ) +ᶜ wkConₘ ρ χ ≈⟨ +ᶜ-congʳ (wk-·ᶜ ρ) ⟩
          q″ ·ᶜ wkConₘ ρ θ +ᶜ wkConₘ ρ χ   ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ q″≡q′) ⟩
          q′ ·ᶜ wkConₘ ρ θ +ᶜ wkConₘ ρ χ   ∎)
    lemma (invUsageNatrec ▸z ▸s ▸n ▸A γ≤ (invUsageNatrecNoNr ⦃ (x) ⦄ _ _ _ _)) _ =
      ⊥-elim (¬Nr-not-available x)

opaque

  -- Well-resourced states evaluate to well-resourced states

  ▸-⇾ : ▸ s → s ⇾ s′ → ▸ s′
  ▸-⇾ ▸s (⇾ₑ d) = ▸-⇾ₑ ▸s d
  ▸-⇾ ▸s (⇒ᵥ d) = ▸-⇒ᵥ ▸s d

opaque

  -- Well-resourced states evaluate to well-resourced states

  ▸-⇾* : ▸ s → s ⇾* s′ → ▸ s′
  ▸-⇾* ▸s id = ▸s
  ▸-⇾* ▸s (d ⇨ d′) = ▸-⇾* (▸-⇾ ▸s d) d′

opaque

  -- Well-resourced states evaluate to well-resourced states

  ▸-⇾ₑ* : ▸ s → s ⇾ₑ* s′ → ▸ s′
  ▸-⇾ₑ* ▸s id = ▸s
  ▸-⇾ₑ* ▸s (d ⇨ d′) =
    ▸-⇾ₑ* (▸-⇾ₑ ▸s d) d′

opaque

  -- _⇒ₙ_ does not preserve usage

  ¬▸-⇒ₙ : ▸ s → s ⇒ₙ s′ → ▸ s′ → ⊥
  ¬▸-⇒ₙ ▸s (sucₕ x) ▸s′ =
    let _ , _ , _ , _ , _ , _ , _ , ▸e , _ = ▸ₛ-∙-inv ▸s′
    in  ▸-inv-sucₑ ▸e
  ¬▸-⇒ₙ ▸s (numₕ x) ▸s′ =
    let _ , _ , _ , _ , _ , _ , _ , ▸e , _ = ▸ₛ-∙-inv ▸s
    in  ▸-inv-sucₑ ▸e

opaque

  -- There are three different reasons a well-resourced state can be Final:
  -- 1. It has a variable in head position pointing to a dummy entry
  --    in the heap and the stack multiplicity is 𝟘.
  -- 2. It has a value in head position, the stack is not empty and the
  --    top of the stack does not match the head.
  -- 3. It has a value in head position and the stack is empty.

  ▸Final-reasons :
    Supports-subtraction →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final (⟨_,_,_,_⟩ H t ρ S) →
    (∃ λ x → t ≡ var x × H ⊢ wkVar ρ x ↦● × ∣ S ∣ ≡ 𝟘) ⊎
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε
  ▸Final-reasons {ρ} ok ▸s f =
    case Final-reasons ¬Nr-not-available _ f of λ where
      (inj₂ (inj₂ x)) → inj₂ x
      (inj₂ (inj₁ (_ , _ , _ , _ , _ , _ , _ , refl , ok , no-glb))) →
        let _ , _ , _ , _ , ▸nr , _ = ▸ₛ-inv ▸s
        in  case ▸natrec→Ok-nr ¬Nr-not-available ▸nr of λ where
              (_ , has-nr ⦃ (x) ⦄ _) → ⊥-elim (¬[Nr∧No-nr-glb] _ x ok)
              (_ , no-nr x) → ⊥-elim (no-glb (_ , x))
      (inj₁ (x , refl , ¬d)) →
        case ↦⊎↦● (wkVar ρ x) of λ where
          (inj₁ (_ , _ , d)) →
            case ▸↦→↦[] ok d ▸s of λ
              (_ , d′) →
            ⊥-elim (¬d d′)
          (inj₂ d) →
            inj₁ (_ , refl , d , ▸s● ok d ▸s)

opaque

  -- A variant of the above property with the added assumption that
  -- there are no erased matches if the state is not closed.

  -- Under this assumption there are three different reasons a wel-resourced
  -- state can be Final:
  -- 1. It has a variable in head position pointing to a dummy entry
  --    in the heap, the stack contains an erased emptyrec and erased uses
  --    of emptyrec are allowed.
  -- 2. It has a value in head position, the stack is not empty and the
  --    top of the stack does not match the head.
  -- 3. It has a value in head position and the stack is empty.

  ▸Final-reasons′ :
    ∀ {k} {H : Heap k _} →
    Supports-subtraction →
    (k ≢ 0 → No-erased-matches′ type-variant UR) →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final (⟨_,_,_,_⟩ H t ρ S) →
    (∃ λ x → t ≡ var x × H ⊢ wkVar ρ x ↦● × emptyrec₀∈ S × Emptyrec-allowed 𝟙ᵐ 𝟘) ⊎
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε
  ▸Final-reasons′ {ρ} ok nem ▸s f =
    let _ , _ , _ , _ , _ , ▸S , _ = ▸ₛ-inv ▸s in
    case ▸Final-reasons ok ▸s f of λ where
      (inj₂ x) → inj₂ x
      (inj₁ (x , t≡x , d , ∣S∣≡𝟘)) →
        case ▸∣S∣≢𝟘 (nem (¬erased-heap→¬↦● d)) ▸S of λ where
           (inj₁ ∣S∣≢𝟘) → ⊥-elim (∣S∣≢𝟘 ∣S∣≡𝟘)
           (inj₂ prop) → inj₁ (x , t≡x , d , prop)

opaque

  -- A variant of ▸Final-reasons

  ▸-⇘-reasons :
    Supports-subtraction →
    ▸ s →
    s ⇘ ⟨ H , t , ρ , S ⟩ →
    (∃ λ x → t ≡ var x × H ⊢ wkVar ρ x ↦● × ∣ S ∣ ≡ 𝟘) ⊎
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε
  ▸-⇘-reasons ok ▸s (d , f) =
    ▸Final-reasons ok (▸-⇾* ▸s d) f

opaque

  -- There are two different reasons a closed state can be Final:
  -- 1. It has a value in head position, the stack is not empty and the
  --    top of the stack does not match the head.
  -- 2. It has a value in head position and the stack is empty.

  ▸Final-reasons-closed :
    {H : Heap 0 _} →
    Supports-subtraction →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final (⟨_,_,_,_⟩ H t ρ S) →
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε
  ▸Final-reasons-closed ok ▸s f =
    case ▸Final-reasons ok ▸s f of λ where
      (inj₁ (_ , _ , d , _)) → ⊥-elim (¬erased-heap→¬↦● d refl)
      (inj₂ x) → x
