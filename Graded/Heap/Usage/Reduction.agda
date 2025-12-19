------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States
-- and the reduction relation with resource tracking.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Graded.Usage.Restrictions.Natrec
open import Definition.Typed.Variant
open import Tools.Relation
open import Tools.PropositionalEquality

module Graded.Heap.Usage.Reduction
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄 𝐌)
  (open Type-variant type-variant)
  (open Usage-restrictions UR)
  (open Modality 𝕄)
  (open IsMode 𝐌)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (∣ε∣ : M)
  (Unitʷ-η→ : ∀ {m p q} → Unitʷ-η → Unitrec-allowed m p q → ⌜ m ⌝ ≢ 𝟘 → p ≤ 𝟘)
  (¬Nr-not-available : ¬ Nr-not-available)
  where

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.Sum
import Tools.Reasoning.PartialOrder as RPo
import Tools.Reasoning.PropositionalEquality as RPe
import Tools.Reasoning.Equivalence as REq

open import Definition.Untyped M

open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Reduction type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Usage type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Usage.Properties type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Usage.Weakening type-variant UR factoring-nr ∣ε∣

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Weakening UR
open import Graded.Restrictions 𝕄 𝐌

private variable
  k : Nat
  γ δ η γ′ δ′ θ : Conₘ _
  s s′ : State _ _ _
  m : Mode
  A B t u v w : Term _
  p p′ q q′ r : M
  ρ : Wk _ _
  H : Heap _ _
  S : Stack _

opaque

  -- Usage preservation under _⇒ᵥ_

  ▸-⇒ᵥ : ▸ s → s ⇒ᵥ s′ → ▸ s′
  ▸-⇒ᵥ ▸s (lamₕ {q} {p} {ρ} {ρ′} ∣S∣≡) =
    let q′ , p′ , γ , δ , η , θ
           , ∣S∣≡′ , ∣e∣≡ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , θ≈ = ▸-inv-∘ₑ ▸e
        invUsageLam {δ = δ′} ▸t δ≤ = inv-usage-lam ▸t
        q′≡q = ∣∣-functional ∣S∣≡′ ∣S∣≡
        p′≡𝟙 = ∣∣ᶜ-functional ∣e∣≡ ∘ₑ
        γ≤′ = let open ≤ᶜ-reasoning in begin
          γ ≤⟨ γ≤ ⟩
          (q′ · p′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ θ                 ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
          (q′ · p′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ p ·ᶜ wkConₘ ρ′ θ′ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-cong q′≡q p′≡𝟙)) (+ᶜ-congˡ (·ᶜ-congʳ q′≡q)) ⟩
          (q · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ p ·ᶜ wkConₘ ρ′ θ′    ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-identityʳ _)) ⟩
          q ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ p ·ᶜ wkConₘ ρ′ θ′          ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
          (q ·ᶜ wkConₘ ρ δ +ᶜ η) +ᶜ q ·ᶜ p ·ᶜ wkConₘ ρ′ θ′        ≈˘⟨ +ᶜ-congˡ (·ᶜ-assoc _ _ _) ⟩
          (q ·ᶜ wkConₘ ρ δ +ᶜ η) +ᶜ (q · p) ·ᶜ wkConₘ ρ′ θ′       ∎
        qp≡ = let open RPe in
          q · p                       ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
          (q · ⌜ ⌞ q ⌟ ⌝) · p         ≡˘⟨ ·-congʳ (·-congˡ (cong ⌜_⌝ (⌞⌟-cong q′≡q))) ⟩
          (q · ⌜ ⌞ q′ ⌟ ⌝) · p        ≡˘⟨ ·-congʳ (·-congˡ (cong ⌜_⌝ (⌞⌟-cong (·-identityʳ _)))) ⟩
          (q · ⌜ ⌞ q′ · 𝟙 ⌟ ⌝) · p    ≡˘⟨ ·-congʳ (·-congˡ (cong ⌜_⌝ (⌞⌟-cong (·-congˡ p′≡𝟙)))) ⟩
          (q · ⌜ ⌞ q′ · p′ ⌟ ⌝) · p   ≡⟨ ·-assoc _ _ _ ⟩
          q · ⌜ ⌞ q′ · p′ ⌟ ⌝ · p     ≡˘⟨ +-identityʳ _ ⟩
          q · ⌜ ⌞ q′ · p′ ⌟ ⌝ · p + 𝟘 ∎
    in  ▸ₛ (wk-∣∣ ∣S∣≡)
           (sub ▸H γ≤′ ∙ ▸-cong (trans ⌞⌟ᵐ· (⌞⌟-cong (·-congʳ q′≡q))) ▸u)
           (▸-cong (⌞⌟-cong (trans (·-congˡ p′≡𝟙) (trans (·-identityʳ _) q′≡q))) ▸t)
           (wk-▸ˢ (step id) ▸S)
           (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ∙ ≤-reflexive qp≡)

  ▸-⇒ᵥ ▸s (prodˢₕ₁ {p} {ρ}) =
    let q′ , p′ , γ , δ , η , θ
           , ∣S∣≡ , ∣e∣≡ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        mp-cond , θ≈𝟘 = ▸-inv-fstₑ ▸e
        invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤ = inv-usage-prodˢ ▸t
        p′≡𝟙 = ∣∣ᶜ-functional ∣e∣≡ fstₑ
        mp-cond′ = case is-𝟘? ⌜ ⌞ q′ ⌟ ⌝ of λ where
          (yes q′≡𝟘) → inj₁ q′≡𝟘
          (no q′≢𝟘) → inj₂ (mp-cond q′≢𝟘)
    in  ▸ₛ ∣S∣≡ ▸H (▸-cong (lemma₁ mp-cond′ p′≡𝟙) ▸t) ▸S $ begin
      γ                                        ≤⟨ γ≤ ⟩
      (q′ · p′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ θ  ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-congˡ p′≡𝟙)) (+ᶜ-congˡ (·ᶜ-congˡ θ≈𝟘)) ⟩
      (q′ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      q′ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ              ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
      q′ ·ᶜ wkConₘ ρ δ +ᶜ η                    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
      q′ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (∧ᶜ-decreasingˡ _ _))) ⟩
      q′ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁) +ᶜ η            ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-·ᶜ ρ)) ⟩
      q′ ·ᶜ p ·ᶜ wkConₘ ρ δ₁ +ᶜ η              ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
      (q′ · p) ·ᶜ wkConₘ ρ δ₁ +ᶜ η             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ (lemma₂ mp-cond′)) ⟩
      q′ ·ᶜ wkConₘ ρ δ₁ +ᶜ η                   ∎
    where
    lemma : ⌜ ⌞ q′ ⌟ ⌝ ≡ 𝟘 → q′ ≡ 𝟘
    lemma {q′} q′≡𝟘 =
      let open RPe in begin
        q′              ≡˘⟨ ·⌜⌞⌟⌝ ⟩
        q′ · ⌜ ⌞ q′ ⌟ ⌝ ≡⟨ ·-congˡ q′≡𝟘 ⟩
        q′ · 𝟘          ≡⟨ ·-zeroʳ _ ⟩
        𝟘               ∎
    lemma₁ : (⌜ ⌞ q′ ⌟ ⌝ ≡ 𝟘 ⊎ p ≤ 𝟙) → p′ ≡ 𝟙 → ⌞ q′ · p′ ⌟ ᵐ· p ≡ ⌞ q′ ⌟
    lemma₁ {q′} (inj₁ q′≡𝟘) refl =
      let open RPe in begin
        ⌞ q′ · 𝟙 ⌟ ᵐ· p ≡⟨ ᵐ·-congʳ (⌞⌟-cong (·-identityʳ _)) ⟩
        ⌞ q′ ⌟ ᵐ· p     ≡⟨ ᵐ·-congʳ (⌞⌟-cong (lemma q′≡𝟘)) ⟩
        ⌞ 𝟘 ⌟ ᵐ· p      ≡⟨ ᵐ·-congʳ ⌞𝟘⌟  ⟩
        𝟘ᵐ ᵐ· p         ≡⟨ ᵐ·-zeroˡ ⟩
        𝟘ᵐ              ≡˘⟨ ⌞𝟘⌟ ⟩
        ⌞ 𝟘 ⌟           ≡˘⟨ ⌞⌟-cong (lemma q′≡𝟘) ⟩
        ⌞ q′ ⌟          ∎
    lemma₁ {q′} (inj₂ p≤𝟙) refl =
      let open RPe in begin
        ⌞ q′ · 𝟙 ⌟ ᵐ· p ≡⟨ ᵐ·-identityʳ-≤𝟙 p≤𝟙 ⟩
        ⌞ q′ · 𝟙 ⌟      ≡⟨ ⌞⌟-cong (·-identityʳ _) ⟩
        ⌞ q′ ⌟          ∎
    lemma₂ : (⌜ ⌞ q′ ⌟ ⌝ ≡ 𝟘 ⊎ p ≤ 𝟙) → q′ · p ≤ q′
    lemma₂ {q′} (inj₁ q′≡𝟘) =
      let open ≤-reasoning in begin
        q′ · p ≡⟨ ·-congʳ (lemma q′≡𝟘) ⟩
        𝟘 · p  ≡⟨ ·-zeroˡ _ ⟩
        𝟘      ≡˘⟨ lemma q′≡𝟘 ⟩
        q′     ∎
    lemma₂ {q′} (inj₂ p≤𝟙) =
      let open ≤-reasoning in begin
        q′ · p ≤⟨ ·-monotoneʳ p≤𝟙 ⟩
        q′ · 𝟙 ≡⟨ ·-identityʳ _ ⟩
        q′     ∎
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (prodˢₕ₂ {p} {ρ}) =
    let q′ , p′ , γ , δ , η , θ
           , ∣S∣≡ , ∣e∣≡ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ≈𝟘 = ▸-inv-sndₑ ▸e
        invUsageProdˢ {δ = δ₁} {η = δ₂} ▸t ▸u δ≤ = inv-usage-prodˢ ▸t
        p′≡𝟙 = ∣∣ᶜ-functional ∣e∣≡ sndₑ
    in  ▸ₛ ∣S∣≡ ▸H
           (▸-cong (⌞⌟-cong (trans (·-congˡ p′≡𝟙) (·-identityʳ _))) ▸u)
           ▸S $ begin
      γ                                        ≤⟨ γ≤ ⟩
      (q′ · p′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ θ  ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-congˡ p′≡𝟙)) (+ᶜ-congˡ (·ᶜ-congˡ θ≈𝟘)) ⟩
      (q′ · 𝟙) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      q′ ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ              ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
      q′ ·ᶜ wkConₘ ρ δ +ᶜ η                    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
      q′ ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ ∧ᶜ δ₂) +ᶜ η      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (∧ᶜ-decreasingʳ _ _))) ⟩
      q′ ·ᶜ wkConₘ ρ δ₂ +ᶜ η                   ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (prodʷₕ {q′} {p} {t₁} {ρ} {r} {ρ′} ∣S∣≡′) =
    let q , r′ , γ , δ , η , θ
           , ∣S∣≡ , ∣e∣≡ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , ok , θ≈ = ▸-inv-prodrecₑ ▸e
        invUsageProdʷ {δ = δ′} {η = η′} ▸t₁ ▸t₂ δ≤ = inv-usage-prodʷ ▸t
        r′≡r = ∣∣ᶜ-functional ∣e∣≡ prodrecₑ
        q≡q′ = ∣∣-functional ∣S∣≡ ∣S∣≡′
        q′rp≡ = let open RPe in begin
          q′ · r · p                ≡˘⟨ +-identityʳ _ ⟩
          q′ · r · p + 𝟘            ≡˘⟨ +-congˡ (·-zeroʳ _) ⟩
          q′ · r · p + (q′ · r) · 𝟘 ∎
        q′rp≡′ = let open RPe in begin
          ⌞ q · r′ ⌟ ᵐ· p  ≡⟨ ⌞⌟ᵐ· ⟩
          ⌞ (q · r′) · p ⌟ ≡⟨ ⌞⌟-cong (·-congʳ (·-cong q≡q′ r′≡r)) ⟩
          ⌞ (q′ · r) · p ⌟ ≡⟨ ⌞⌟-cong (·-assoc _ _ _) ⟩
          ⌞ q′ · r · p ⌟   ∎
        open ≤ᶜ-reasoning
        γ≤′ = begin
          γ                                                                                     ≤⟨ γ≤ ⟩
          (q · r′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ θ                                                 ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-cong q≡q′ r′≡r)) (+ᶜ-congˡ (·ᶜ-congʳ q≡q′)) ⟩
          (q′ · r) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ θ                                                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          (q′ · r) ·ᶜ wkConₘ ρ (p ·ᶜ δ′ +ᶜ η′) +ᶜ η +ᶜ q′ ·ᶜ θ                                  ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
          (q′ · r) ·ᶜ (wkConₘ ρ (p ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ q′ ·ᶜ θ                       ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ ρ))) ⟩
          (q′ · r) ·ᶜ (p ·ᶜ wkConₘ ρ δ′ +ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ q′ ·ᶜ θ                         ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          ((q′ · r) ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ (q′ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ q′ ·ᶜ θ             ≈˘⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-assoc _ _ _)) ⟩
          (((q′ · r) · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (q′ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ q′ ·ᶜ θ            ≈⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-congʳ (·-assoc _ _ _))) ⟩
          ((q′ · r · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (q′ · r) ·ᶜ wkConₘ ρ η′) +ᶜ η +ᶜ q′ ·ᶜ θ              ≈⟨ +ᶜ-comm _ _ ⟩
          (η +ᶜ q′ ·ᶜ θ) +ᶜ (q′ · r · p) ·ᶜ wkConₘ ρ δ′ +ᶜ (q′ · r) ·ᶜ wkConₘ ρ η′              ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
          (η +ᶜ q′ ·ᶜ θ) +ᶜ (q′ · r) ·ᶜ wkConₘ ρ η′ +ᶜ (q′ · r · p) ·ᶜ wkConₘ ρ δ′              ≈⟨ +ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
          (η +ᶜ q′ ·ᶜ wkConₘ ρ′ θ′) +ᶜ (q′ · r) ·ᶜ wkConₘ ρ η′ +ᶜ (q′ · r · p) ·ᶜ wkConₘ ρ δ′   ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
          ((η +ᶜ q′ ·ᶜ wkConₘ ρ′ θ′) +ᶜ (q′ · r) ·ᶜ wkConₘ ρ η′) +ᶜ (q′ · r · p) ·ᶜ wkConₘ ρ δ′ ∎
        ▸t₁′ = ▸-cong q′rp≡′ ▸t₁
        ▸t₂′ = ▸-cong (⌞⌟-cong (·-cong q≡q′ r′≡r)) ▸t₂
    in  ▸ₛ (wk-∣∣ ∣S∣≡)
           (sub (sub ▸H γ≤′ ∙ ▸t₁′) (≤ᶜ-refl ∙ ≤-reflexive q′rp≡) ∙ ▸t₂′)
           ▸u (wk-▸ˢ _ ▸S)
           (lemma₁ q≡q′ ∙ lemma₂ q≡q′ ∙ lemma₂ q≡q′)
    where
    lemma₁ : q ≡ q′ → η +ᶜ q′ ·ᶜ γ ≤ᶜ q ·ᶜ γ +ᶜ η
    lemma₁ refl = ≤ᶜ-reflexive (+ᶜ-comm _ _)
    lemma₂ : ∀ {p q q′} → q ≡ q′ → q′ · p ≤ q · ⌜ ⌞ q ⌟ ⌝ · p + 𝟘
    lemma₂ {p} {q} refl = begin
      q · p                 ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
      (q · ⌜ ⌞ q ⌟ ⌝) · p   ≡⟨ ·-assoc _ _ _ ⟩
      q · ⌜ ⌞ q ⌟ ⌝ · p     ≡˘⟨ +-identityʳ _ ⟩
      q · ⌜ ⌞ q ⌟ ⌝ · p + 𝟘 ∎
      where
      open RPo ≤-poset

  ▸-⇒ᵥ ▸s (zeroₕ {ρ} {ρ′}) =
    let q′ , p′ , γ , δ , η , θ
           , ∣S∣≡ , _ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        γ′ , δ′ , η′ , ▸z , ▸s , ▸A , extra = ▸-inv-natrecₑ ▸e
    in  ▸ₛ ∣S∣≡ ▸H ▸z ▸S $ begin
      γ                                        ≤⟨ γ≤ ⟩
      (q′ · p′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ θ  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-zero ▸t))) ⟩
      (q′ · p′) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ q′ ·ᶜ θ ≡⟨ cong (λ x → (q′ · p′) ·ᶜ x +ᶜ η +ᶜ q′ ·ᶜ θ) (wk-𝟘ᶜ ρ) ⟩
      (q′ · p′) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ q′ ·ᶜ θ          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ q′ ·ᶜ θ                       ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ q′ ·ᶜ θ                             ≈⟨ +ᶜ-comm _ _ ⟩
      q′ ·ᶜ θ +ᶜ η                             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (lemma extra)) ⟩
      q′ ·ᶜ wkConₘ ρ′ γ′ +ᶜ η                  ∎
    where
    open ≤ᶜ-reasoning
    lemma : InvUsageNatrecₑ p r γ δ ρ′ θ → θ ≤ᶜ wkConₘ ρ′ γ
    lemma invUsageNatrecNr = wk-≤ᶜ ρ′ (nrᶜ-zero ≤ᶜ-refl)
    lemma (invUsageNatrecNoNr (χ≤ , _)) =
      wk-≤ᶜ ρ′ (≤ᶜ-trans (χ≤ 0) (≤ᶜ-reflexive nrᵢᶜ-zero))

  ▸-⇒ᵥ ▸s (sucₕ {q′} {p} {r} {p′} {ρ} {q} {A} {z} {s} {ρ′} ∣S∣≡′ ∣nr∣≡) =
    let q , p″ , γ , δ , η , θ′
          , ∣S∣≡ , ∣e∣≡ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        γ′ , δ′ , η′ , ▸z , ▸s , ▸A , extra = ▸-inv-natrecₑ ▸e
        invUsageSuc {δ = θ} ▸t δ≤ = inv-usage-suc ▸t
        q≡q′ = ∣∣-functional ∣S∣≡ ∣S∣≡′
        p″≡p′ = ∣∣ᶜ-functional ∣e∣≡ (natrecₑ ∣nr∣≡)
        χ , x , χ▸nr , rρ′χ≈rθ′ , rx≡rp′ = ▸nr′ ▸z ▸s ▸A extra ∣nr∣≡
        ▸t′ = ▸-cong (⌞⌟-cong (·-cong q≡q′ p″≡p′)) ▸t
        χ▸nr′ = ▸-cong (trans ⌞⌟ᵐ· (⌞⌟-cong (·-congʳ q≡q′))) χ▸nr
        γ≤′ = let open ≤ᶜ-reasoning in begin
          γ                                           ≤⟨ γ≤ ⟩
          (q · p″) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ θ′      ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-cong q≡q′ p″≡p′)) (+ᶜ-congˡ (·ᶜ-congʳ q≡q′)) ⟩
          (q′ · p′) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q′ ·ᶜ θ′    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          (q′ · p′) ·ᶜ wkConₘ ρ θ +ᶜ η +ᶜ q′ ·ᶜ θ′    ≈⟨ +ᶜ-comm _ _ ⟩
          (η +ᶜ q′ ·ᶜ θ′) +ᶜ (q′ · p′) ·ᶜ wkConₘ ρ θ  ∎
        η+q′θ′≤ = let open ≤ᶜ-reasoning in begin
          η +ᶜ q′ ·ᶜ θ′                                        ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (InvUsageNatrecₑ-≤ extra)) ⟩
          η +ᶜ q′ ·ᶜ (wkConₘ ρ′ δ′ +ᶜ r ·ᶜ θ′)                 ≈⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          η +ᶜ q′ ·ᶜ wkConₘ ρ′ δ′ +ᶜ q′ ·ᶜ r ·ᶜ θ′             ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
          (η +ᶜ q′ ·ᶜ wkConₘ ρ′ δ′) +ᶜ q′ ·ᶜ r ·ᶜ θ′           ≈˘⟨ +ᶜ-congˡ (·ᶜ-congˡ rρ′χ≈rθ′) ⟩
          (η +ᶜ q′ ·ᶜ wkConₘ ρ′ δ′) +ᶜ q′ ·ᶜ r ·ᶜ wkConₘ ρ′ χ  ≈˘⟨ +ᶜ-cong (+ᶜ-comm _ _) (·ᶜ-assoc _ _ _) ⟩
          (q′ ·ᶜ wkConₘ ρ′ δ′ +ᶜ η) +ᶜ (q′ · r) ·ᶜ wkConₘ ρ′ χ ∎
        q′p′≤ = let open RPo ≤-poset in begin
          q′ · p′                             ≤⟨ ·-monotoneʳ (∣natrec∣≤ ∣nr∣≡) ⟩
          q′ · (p + r · p′)                   ≈⟨ ·-distribˡ-+ _ _ _ ⟩
          q′ · p + q′ · r · p′                ≈⟨ +-congˡ (lemma₁ q′) ⟩
          q′ · p + q′ · (r · p′) · ⌜ ⌞ q′ ⌟ ⌝ ≈˘⟨ +-congˡ (·-congˡ (·-congˡ (cong (λ x → ⌜ ⌞ x ⌟ ⌝) q≡q′))) ⟩
          q′ · p + q′ · (r · p′) · ⌜ ⌞ q ⌟ ⌝  ≈⟨ +-congˡ (·-congˡ (·-assoc _ _ _)) ⟩
          q′ · p + q′ · r · p′ · ⌜ ⌞ q ⌟ ⌝    ≈˘⟨ +-congˡ (·-congˡ rx≡rp′) ⟩
          q′ · p + q′ · r · x                 ≈˘⟨ +-congˡ (·-assoc _ _ _) ⟩
          q′ · p + (q′ · r) · x               ∎

    in  ▸ₛ (wk-∣∣ ∣S∣≡)
           (sub (sub ▸H γ≤′ ∙ ▸t′) (η+q′θ′≤ ∙ q′p′≤) ∙ χ▸nr′)
           ▸s (wk-▸ˢ _ ▸S)
           (≤ᶜ-reflexive (+ᶜ-congʳ (·ᶜ-congʳ (sym q≡q′))) ∙
            ≤-reflexive (lemma₂ p q≡q′) ∙
            ≤-reflexive (lemma₂ r q≡q′))
    where
    lemma₁ : ∀ {q} p → p · q ≡ p · q · ⌜ ⌞ p ⌟ ⌝
    lemma₁ {q} p = begin
      p · q               ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
      (p · ⌜ ⌞ p ⌟ ⌝) · q ≡⟨ ·-assoc _ _ _ ⟩
      p · ⌜ ⌞ p ⌟ ⌝ · q   ≡⟨ ·-congˡ (⌜⌝-·-comm _) ⟩
      p · q · ⌜ ⌞ p ⌟ ⌝   ∎
      where
      open RPe
    lemma₂ : ∀ {q q′} p → q ≡ q′ → q′ · p ≡ q · ⌜ ⌞ q ⌟ ⌝ · p + 𝟘
    lemma₂ {q} p refl = begin
      q · p                 ≡˘⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
      (q · ⌜ ⌞ q ⌟ ⌝) · p   ≡⟨ ·-assoc _ _ _ ⟩
      q · ⌜ ⌞ q ⌟ ⌝ · p     ≡˘⟨ +-identityʳ _ ⟩
      q · ⌜ ⌞ q ⌟ ⌝ · p + 𝟘 ∎
      where
      open RPe

    ▸nr : γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s →
           η ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A → InvUsageNatrecₑ p r γ δ ρ′ θ → ∣natrec p , r ∣≡ p′ →
          ∃ λ χ → χ ∙ p′ · ⌜ m ⌝ ▸[ m ] natrec p q r (wk (lift (step id)) A) (wk (step id) z) (wk (liftn (step id) 2) s) (var x0) ×
          wkConₘ ρ′ χ ≈ᶜ θ
    ▸nr ▸z ▸s ▸A (invUsageNatrecNr ⦃ has-nr ⦄) (no-nrₑ ⦃ no-nr ⦄ x) =
      ⊥-elim (¬[Nr∧No-nr-glb] _ has-nr no-nr)
    ▸nr ▸z ▸s ▸A (invUsageNatrecNr ⦃ has-nr ⦄) (has-nrₑ ⦃ has-nr = has-nr′ ⦄) =
      case Nr-available-propositional _ has-nr has-nr′ of λ {
        refl →
      _ , sub (natrecₘ (wkUsage (step id) ▸z)
                (wkUsage (liftn (step id) 2) ▸s)
                (var {x = x0})
                (wkUsage (lift (step id)) ▸A))
              (≤ᶜ-refl ∙ ≤-reflexive (sym (trans nr-factoring
                           (trans (+-congˡ nr-𝟘) (+-identityʳ _)))))
        , ≈ᶜ-refl }
    ▸nr ▸z ▸s ▸A (invUsageNatrecNoNr ⦃ no-nr ⦄ _) (has-nrₑ ⦃ has-nr ⦄) =
      ⊥-elim (¬[Nr∧No-nr-glb] _ has-nr no-nr)
    ▸nr ▸z ▸s ▸A (invUsageNatrecNoNr ⦃ no-nr ⦄ χ-GLB) (no-nrₑ p′-GLB) =
      _ , sub (natrec-no-nr-glbₘ ⦃ no-nr = no-nr ⦄ (wkUsage (step id) ▸z)
                (wkUsage (liftn (step id) 2) ▸s) var
                (wkUsage (lift (step id)) ▸A) p′-GLB
                (GLBᶜ-congˡ (λ i → ≈ᶜ-sym (≈ᶜ-refl ∙ nrᵢ-𝟘 i))
                  (wk-GLBᶜ (step id) χ-GLB)))
              (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroʳ _)) (+ᶜ-identityˡ _) ∙ +-identityʳ _)))
        , ≈ᶜ-refl

    ▸nr′ : γ ▸[ m ] z → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] s →
           η ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A → InvUsageNatrecₑ p r γ δ ρ′ θ →
           ∣natrec p , r ∣≡ p′ →
           ∃₂ λ χ x →
             χ ∙ x ▸[ m ᵐ· r ] natrec p q r (wk (lift (step id)) A)
                                 (wk (step id) z) (wk (liftn (step id) 2) s) (var x0) ×
             r ·ᶜ wkConₘ ρ′ χ ≈ᶜ r ·ᶜ θ ×
             r · x ≡ r · p′ · ⌜ m ⌝
    ▸nr′ {m} {θ} ▸z ▸s ▸A extra ∣nr∣≡ =
      let χ , ▸nr , ρ′χ≈θ = ▸nr ▸z ▸s ▸A extra ∣nr∣≡
      in _ , _ , ▸-ᵐ· ▸nr
           , (let open ≈ᶜ-reasoning in begin
                r ·ᶜ wkConₘ ρ′ (⌜ ⌞ r ⌟ ⌝ ·ᶜ χ) ≈⟨ ·ᶜ-congˡ (wk-·ᶜ ρ′) ⟩
                r ·ᶜ ⌜ ⌞ r ⌟ ⌝ ·ᶜ wkConₘ ρ′ χ   ≈˘⟨ ·ᶜ-assoc _ _ _ ⟩
                (r · ⌜ ⌞ r ⌟ ⌝) ·ᶜ wkConₘ ρ′ χ  ≈⟨ ·ᶜ-cong ·⌜⌞⌟⌝ ρ′χ≈θ ⟩
                r ·ᶜ θ                          ∎)
           , let open RPe in begin
               r · ⌜ ⌞ r ⌟ ⌝ · p′ · ⌜ m ⌝   ≡˘⟨ ·-assoc _ _ _ ⟩
               (r · ⌜ ⌞ r ⌟ ⌝) · p′ · ⌜ m ⌝ ≡⟨ ·-congʳ ·⌜⌞⌟⌝ ⟩
               r · p′ · ⌜ m ⌝               ∎

  ▸-⇒ᵥ ▸s (starʷₕ {ρ} {ρ′}) =
    let q , p , γ , δ , η , θ
          , ∣S∣≡ , ∣e∣≡ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , _ , _ , θ≈  = ▸-inv-unitrecₑ ▸e
        δ≤𝟘 = inv-usage-starʷ ▸t
    in  ▸ₛ ∣S∣≡ ▸H ▸u ▸S $ begin
      γ                                                ≤⟨ γ≤ ⟩
      (q · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ θ             ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
      (q · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤𝟘)) ⟩
      (q · p) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′ ≡⟨ cong (λ x → (q · p) ·ᶜ x +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′) (wk-𝟘ᶜ ρ) ⟩
      (q · p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′                     ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ q ·ᶜ wkConₘ ρ′ θ′                           ≈⟨ +ᶜ-comm _ _ ⟩
      q ·ᶜ wkConₘ ρ′ θ′ +ᶜ η                           ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (unitrec-ηₕ {p} {ρ} η-ok) =
    let q , γ , δ , η
          , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageUnitrec {δ = δ₁} {η = δ₂} ▸t ▸u _ ok δ≤ = inv-usage-unitrec ▸t
    in  ▸ₛ ∣S∣≡ ▸H ▸u ▸S (lemma γ≤ δ≤ ok (is-𝟘? ⌜ ⌞ q ⌟ ⌝))
    where
    open ≤ᶜ-reasoning
    lemma : ∀ {δ₁ δ₂}
          → γ ≤ᶜ q ·ᶜ wkConₘ ρ δ +ᶜ η
          → δ ≤ᶜ p ·ᶜ δ₁ +ᶜ δ₂
          → Unitrec-allowed ⌞ q ⌟ p r
          → Dec (⌜ ⌞ q ⌟ ⌝ ≡ 𝟘)
          → γ ≤ᶜ q ·ᶜ wkConₘ ρ δ₂ +ᶜ η
    lemma {γ} {q} {δ} {η} {δ₂} γ≤ _ _ (yes q≡𝟘) = begin
      γ                                   ≤⟨ γ≤ ⟩
      q ·ᶜ wkConₘ ρ δ +ᶜ η                ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ ·⌜⌞⌟⌝) ⟩
      (q · ⌜ ⌞ q ⌟ ⌝) ·ᶜ wkConₘ ρ δ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ q≡𝟘)) ⟩
      (q · 𝟘) ·ᶜ wkConₘ ρ δ +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η                ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘ᶜ +ᶜ η                             ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ₂ +ᶜ η               ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
      (q · 𝟘) ·ᶜ wkConₘ ρ δ₂ +ᶜ η         ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ q≡𝟘)) ⟩
      (q · ⌜ ⌞ q ⌟ ⌝) ·ᶜ wkConₘ ρ δ₂ +ᶜ η ≈⟨ +ᶜ-congʳ (·ᶜ-congʳ ·⌜⌞⌟⌝) ⟩
      q ·ᶜ wkConₘ ρ δ₂ +ᶜ η               ∎
    lemma {γ} {q} {δ} {η} {δ₁} {δ₂} γ≤ δ≤ ok (no q≢𝟘) = begin
      γ                                  ≤⟨ γ≤ ⟩
      q ·ᶜ wkConₘ ρ δ +ᶜ η               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
      q ·ᶜ wkConₘ ρ (p ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (+ᶜ-monotoneˡ
                                             (·ᶜ-monotoneˡ (Unitʷ-η→ η-ok ok q≢𝟘))))) ⟩
      q ·ᶜ wkConₘ ρ (𝟘 ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-congʳ (·ᶜ-zeroˡ _)))) ⟩
      q ·ᶜ wkConₘ ρ (𝟘ᶜ +ᶜ δ₂) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-≈ᶜ ρ (+ᶜ-identityˡ _))) ⟩
      q ·ᶜ wkConₘ ρ δ₂ +ᶜ η              ∎

  ▸-⇒ᵥ ▸s (rflₕⱼ {ρ} {ρ′}) =
    let q , p , γ , δ , η , θ
          , ∣S∣≡ , _ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , θ≈  = ▸-inv-Jₑ ▸e
        δ≤𝟘 = inv-usage-rfl ▸t
    in  ▸ₛ ∣S∣≡ ▸H ▸u ▸S $ begin
      γ                                                ≤⟨ γ≤ ⟩
      (q · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ θ             ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
      (q · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-rfl ▸t))) ⟩
      (q · p) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′ ≡⟨ cong (λ x → (q · p) ·ᶜ x +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′) (wk-𝟘ᶜ ρ) ⟩
      (q · p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′                     ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ q ·ᶜ wkConₘ ρ′ θ′                           ≈⟨ +ᶜ-comm _ _ ⟩
      q ·ᶜ wkConₘ ρ′ θ′ +ᶜ η                           ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (rflₕₖ {ρ} {ρ′}) =
    let q , p , γ , δ , η , θ
          , ∣S∣≡ , _ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        θ′ , ▸u , θ≈  = ▸-inv-Kₑ ▸e
        δ≤𝟘 = inv-usage-rfl ▸t
    in  ▸ₛ ∣S∣≡ ▸H ▸u ▸S $ begin
      γ                                                 ≤⟨ γ≤ ⟩
      (q · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ θ              ≈⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-congˡ θ≈)) ⟩
      (q · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-rfl ▸t))) ⟩
      (q · p) ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′  ≡⟨ cong (λ x → (q · p) ·ᶜ x +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′) (wk-𝟘ᶜ ρ) ⟩
      (q · p) ·ᶜ 𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′           ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ′ θ′                      ≈⟨ +ᶜ-identityˡ _ ⟩
      η +ᶜ q ·ᶜ wkConₘ ρ′ θ′                            ≈⟨ +ᶜ-comm _ _ ⟩
      q ·ᶜ wkConₘ ρ′ θ′ +ᶜ η                            ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ᵥ ▸s (rflₕₑ {ρ} {ρ′}) =
    let q , p , γ , δ , η , θ
          , ∣S∣≡ , ∣e∣≡ , ▸H , ▸t , ▸S , ▸e , γ≤ = ▸ₛ-∙-inv ▸s
        ok , θ≈𝟘  = ▸-inv-[]-congₑ ▸e
        p≡𝟘 = ∣∣ᶜ-functional ∣e∣≡ []-congₑ
    in  ▸ₛ ∣S∣≡ ▸H rflₘ ▸S $ begin
      γ                                     ≤⟨ γ≤ ⟩
      (q · p) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ θ  ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-congˡ p≡𝟘)) (+ᶜ-congˡ (·ᶜ-congˡ θ≈𝟘)) ⟩
      (q · 𝟘) ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ q ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-cong (·ᶜ-congʳ (·-zeroʳ _)) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
      𝟘 ·ᶜ wkConₘ ρ δ +ᶜ η +ᶜ 𝟘ᶜ            ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-identityʳ _) ⟩
      𝟘ᶜ +ᶜ η                               ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      q ·ᶜ 𝟘ᶜ +ᶜ η                          ≡˘⟨ cong (λ x → q ·ᶜ x +ᶜ η) (wk-𝟘ᶜ ρ′) ⟩
      q ·ᶜ wkConₘ ρ′ 𝟘ᶜ +ᶜ η                ∎
    where
    open ≤ᶜ-reasoning

opaque

  -- Usage preservation under _⇒ₑ_

  ▸-⇒ₑ : ▸ s → s ⇒ₑ s′ → ▸ s′
  ▸-⇒ₑ ▸s (appₕ {p} {ρ} {S}) =
    let q , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageApp {(δ′)} {(η′)} ▸t ▸u δ≤ = inv-usage-app ▸t
    in  ▸ₛ (∘ₑ ∙ ∣S∣≡) ▸H (▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t)
           (▸ˢ∙ ∣S∣≡ (∘ₑ ▸u) ▸S) $ begin
           γ                                                    ≤⟨ γ≤ ⟩
           q ·ᶜ wkConₘ ρ δ +ᶜ η                                 ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
           q ·ᶜ wkConₘ ρ (δ′ +ᶜ p ·ᶜ η′) +ᶜ η                   ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
           q ·ᶜ (wkConₘ ρ δ′ +ᶜ wkConₘ ρ (p ·ᶜ η′)) +ᶜ η        ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congˡ (wk-·ᶜ ρ))) ⟩
           q ·ᶜ (wkConₘ ρ δ′ +ᶜ p ·ᶜ wkConₘ ρ η′) +ᶜ η          ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
           (q ·ᶜ wkConₘ ρ δ′ +ᶜ q ·ᶜ p ·ᶜ wkConₘ ρ η′) +ᶜ η     ≈⟨ +ᶜ-assoc _ _ _ ⟩
           q ·ᶜ wkConₘ ρ δ′ +ᶜ q ·ᶜ p ·ᶜ wkConₘ ρ η′ +ᶜ η       ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-comm _ _) ⟩
           (q · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ q ·ᶜ p ·ᶜ wkConₘ ρ η′ ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (fstₕ {ρ} {S}) =
    let q , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageFst {(δ′)} m eq ▸t δ≤ mp-cond = inv-usage-fst ▸t
    in  ▸ₛ (fstₑ ∙ ∣S∣≡) ▸H (▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t)
           (▸ˢ∙ ∣S∣≡ (fstₑ mp-cond) ▸S) $ begin
           γ                                      ≤⟨ γ≤ ⟩
           q ·ᶜ wkConₘ ρ δ +ᶜ η                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
           q ·ᶜ wkConₘ ρ δ′ +ᶜ η                  ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
           (q · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ      ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
           (q · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ q ·ᶜ 𝟘ᶜ ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (sndₕ {ρ} {S}) =
    let q , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageSnd {(δ′)} ▸t δ≤ = inv-usage-snd ▸t
    in  ▸ₛ (sndₑ ∙ ∣S∣≡) ▸H (▸-cong (⌞⌟-cong (sym (·-identityʳ _))) ▸t)
           (▸ˢ∙ ∣S∣≡ sndₑ ▸S) $ begin
           γ                                      ≤⟨ γ≤ ⟩
           q ·ᶜ wkConₘ ρ δ +ᶜ η                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
           q ·ᶜ wkConₘ ρ δ′ +ᶜ η                  ≈˘⟨ +ᶜ-cong (·ᶜ-congʳ (·-identityʳ _)) (+ᶜ-identityʳ η) ⟩
           (q · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ      ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
           (q · 𝟙) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ q ·ᶜ 𝟘ᶜ ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (prodrecₕ {r} {p} {u} {ρ} {S}) =
    let q , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageProdrec {(δ′)} {(η′)} ▸t ▸u _ ok δ≤ = inv-usage-prodrec ▸t
    in  ▸ₛ (prodrecₑ ∙ ∣S∣≡) ▸H (▸-cong ⌞⌟ᵐ· ▸t)
           (▸ˢ∙ ∣S∣≡ (prodrecₑ ▸u ok) ▸S) $ begin
           γ                                                  ≤⟨ γ≤ ⟩
           q ·ᶜ wkConₘ ρ δ +ᶜ η                               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
           q ·ᶜ wkConₘ ρ (r ·ᶜ δ′ +ᶜ η′) +ᶜ η                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
           q ·ᶜ (wkConₘ ρ (r ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ q _ _) ⟩
           (q ·ᶜ wkConₘ ρ (r ·ᶜ δ′) +ᶜ q ·ᶜ wkConₘ ρ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
           q ·ᶜ wkConₘ ρ (r ·ᶜ δ′) +ᶜ q ·ᶜ wkConₘ ρ η′ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (+ᶜ-comm _ η) ⟩
           q ·ᶜ r ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ η′     ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc q r _) ⟩
           (q · r) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ η′    ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (natrecₕ {p} {r} {z} {s} {ρ}) =
    let q , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        r′ , δ′ , η′ , ∣nr∣≡ , ▸n , ▸e , δ≤ = lemma (inv-usage-natrec ▸t)
    in  ▸ₛ (natrecₑ ∣nr∣≡ ∙ ∣S∣≡) ▸H ▸n (▸ˢ∙ ∣S∣≡ ▸e ▸S) $ begin
           γ ≤⟨ γ≤ ⟩
           q ·ᶜ wkConₘ ρ δ +ᶜ η                     ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ δ≤) ⟩
           q ·ᶜ (r′ ·ᶜ wkConₘ ρ δ′ +ᶜ η′) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
           (q ·ᶜ r′ ·ᶜ wkConₘ ρ δ′ +ᶜ q ·ᶜ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
           q ·ᶜ r′ ·ᶜ wkConₘ ρ δ′ +ᶜ q ·ᶜ η′ +ᶜ η   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
           (q · r′) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ q ·ᶜ η′  ∎
    where
    open ≤ᶜ-reasoning
    lemma : InvUsageNatrec γ ⌞ q ⌟ p q′ r A z s t →
            ∃₃ λ r′ δ η → ∣natrec p , r ∣≡ r′ × δ ▸[ ⌞ q · r′ ⌟ ] t ×
            η ▸ᶜ[ ⌞ q ⌟ ] natrecₑ p q′ r A z s ρ ×
            wkConₘ ρ γ ≤ᶜ r′ ·ᶜ wkConₘ ρ δ +ᶜ η
    lemma {γ} {q} (invUsageNatrec {δ} {η} {θ} ▸z ▸s ▸n ▸A γ≤ invUsageNatrecNr) =
      _ , _ , _
        , has-nrₑ
        , ▸-≤ᵐ ▸n ⌞·⌟-increasingˡ
        , natrecₑ ▸z ▸s ▸A
        ,  (begin
          wkConₘ ρ γ
            ≤⟨ wk-≤ᶜ ρ γ≤ ⟩
          wkConₘ ρ (nrᶜ p r δ η θ)
            ≈⟨ wk-≈ᶜ ρ nrᶜ-factoring ⟩
          wkConₘ ρ (nr₂ p r ·ᶜ θ +ᶜ nrᶜ p r δ η 𝟘ᶜ)
            ≈⟨ wk-+ᶜ ρ ⟩
          wkConₘ ρ (nr₂ p r ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≈˘⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ ·⌜⌞⌟⌝)) ⟩
          wkConₘ ρ ((nr₂ p r · ⌜ ⌞ nr₂ p r ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≤⟨ +ᶜ-monotoneˡ (wk-≤ᶜ ρ (·ᶜ-monotoneʳ (▸ᵐ ▸n))) ⟩
          wkConₘ ρ ((nr₂ p r · ⌜ ⌞ nr₂ p r ⌟ ⌝) ·ᶜ ⌜ ⌞ q ⌟ ⌝ ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≈˘⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-assoc _ _ _)) ⟩
          wkConₘ ρ (((nr₂ p r · ⌜ ⌞ nr₂ p r ⌟ ⌝) · ⌜ ⌞ q ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≈⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ (·-assoc _ _ _))) ⟩
          wkConₘ ρ ((nr₂ p r · ⌜ ⌞ nr₂ p r ⌟ ⌝ · ⌜ ⌞ q ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≈⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ (·-congˡ (⌜⌝-·-comm _)))) ⟩
          wkConₘ ρ ((nr₂ p r · ⌜ ⌞ q ⌟ ⌝ · ⌜ ⌞ nr₂ p r ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≈˘⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ (·-congˡ (⌜·ᵐ⌝ _)))) ⟩
          wkConₘ ρ ((nr₂ p r · ⌜ ⌞ q ⌟ ·ᵐ ⌞ nr₂ p r ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≈⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ (·-congˡ (⌜⌝-cong ⌞⌟·ᵐ)))) ⟩
          wkConₘ ρ ((nr₂ p r · ⌜ ⌞ q · nr₂ p r ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≈⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-assoc _ _ _)) ⟩
          wkConₘ ρ (nr₂ p r ·ᶜ (⌜ ⌞ q · nr₂ p r ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)
            ≈⟨ +ᶜ-congʳ (wk-·ᶜ ρ) ⟩
          nr₂ p r ·ᶜ wkConₘ ρ (⌜ ⌞ q · nr₂ p r ⌟ ⌝ ·ᶜ θ) +ᶜ wkConₘ ρ (nrᶜ p r δ η 𝟘ᶜ)   ∎)
    lemma {γ} {q} (invUsageNatrec {θ} ▸z ▸s ▸n ▸A γ≤ (invUsageNatrecNoNrGLB {χ} {x} x-glb χ-glb)) =
      _ , _ , _
        , no-nrₑ x-glb
        , ▸-≤ᵐ ▸n ⌞·⌟-increasingˡ
        , natrec-no-nrₑ ▸z ▸s ▸A χ-glb
        ,  (begin
          wkConₘ ρ γ                                                  ≤⟨ wk-≤ᶜ ρ γ≤ ⟩
          wkConₘ ρ (x ·ᶜ θ +ᶜ χ)                                      ≈⟨ wk-+ᶜ ρ ⟩
          wkConₘ ρ (x ·ᶜ θ) +ᶜ wkConₘ ρ χ                             ≈˘⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ ·⌜⌞⌟⌝)) ⟩
          wkConₘ ρ ((x · ⌜ ⌞ x ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ χ               ≤⟨ +ᶜ-monotoneˡ (wk-≤ᶜ ρ (·ᶜ-monotoneʳ (▸ᵐ ▸n))) ⟩
          wkConₘ ρ ((x · ⌜ ⌞ x ⌟ ⌝) ·ᶜ ⌜ ⌞ q ⌟ ⌝ ·ᶜ θ) +ᶜ wkConₘ ρ χ  ≈˘⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-assoc _ _ _)) ⟩
          wkConₘ ρ (((x · ⌜ ⌞ x ⌟ ⌝) · ⌜ ⌞ q ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ χ ≈⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ (·-assoc _ _ _))) ⟩
          wkConₘ ρ ((x · ⌜ ⌞ x ⌟ ⌝ · ⌜ ⌞ q ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ χ   ≈⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ (·-congˡ (⌜⌝-·-comm _)))) ⟩
          wkConₘ ρ ((x ·  ⌜ ⌞ q ⌟ ⌝ · ⌜ ⌞ x ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ χ  ≈˘⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ (·-congˡ (⌜·ᵐ⌝ _)))) ⟩
          wkConₘ ρ ((x · ⌜ ⌞ q ⌟ ·ᵐ ⌞ x ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ χ      ≈⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-congʳ (·-congˡ (⌜⌝-cong ⌞⌟·ᵐ)))) ⟩
          wkConₘ ρ ((x · ⌜ ⌞ q · x ⌟ ⌝) ·ᶜ θ) +ᶜ wkConₘ ρ χ           ≈⟨ +ᶜ-congʳ (wk-≈ᶜ ρ (·ᶜ-assoc _ _ _)) ⟩
          wkConₘ ρ (x ·ᶜ ⌜ ⌞ q · x ⌟ ⌝ ·ᶜ θ) +ᶜ wkConₘ ρ χ            ≈⟨ +ᶜ-congʳ (wk-·ᶜ ρ) ⟩
          x ·ᶜ wkConₘ ρ (⌜ ⌞ q · x ⌟ ⌝ ·ᶜ θ) +ᶜ wkConₘ ρ χ            ∎)
    lemma (invUsageNatrec _ _ _ _ _ (invUsageNatrecNoNr ⦃ (x) ⦄ _ _ _ _)) =
      ⊥-elim (¬Nr-not-available x)

  ▸-⇒ₑ ▸s (unitrecₕ {p} {ρ} no-η) =
    let q , γ , δ , η , ∣S|≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageUnitrec {(δ′)} {(η′)} ▸t ▸u _ ok δ≤ = inv-usage-unitrec ▸t
    in  ▸ₛ (unitrecₑ ∙ ∣S|≡) ▸H
           (▸-cong ⌞⌟ᵐ· ▸t)
           (▸ˢ∙ ∣S|≡ (unitrecₑ ▸u ok no-η) ▸S) $ begin
           γ                                                ≤⟨ γ≤ ⟩
           q ·ᶜ wkConₘ ρ δ +ᶜ η                             ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
           q ·ᶜ wkConₘ ρ (p ·ᶜ δ′ +ᶜ η′) +ᶜ η               ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
           q ·ᶜ (wkConₘ ρ (p ·ᶜ δ′) +ᶜ wkConₘ ρ η′) +ᶜ η    ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-congʳ (wk-·ᶜ ρ))) ⟩
           q  ·ᶜ (p ·ᶜ wkConₘ ρ δ′ +ᶜ wkConₘ ρ η′) +ᶜ η     ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
           (q ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ q ·ᶜ wkConₘ ρ η′) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
           q ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ q ·ᶜ wkConₘ ρ η′ +ᶜ η   ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-comm _ _) ⟩
           (q · p) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ q ·ᶜ wkConₘ ρ η′  ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (emptyrecₕ {p} {ρ}) =
    let q , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsageEmptyrec {(δ′)} ▸t _ ok δ≤ = inv-usage-emptyrec ▸t
    in  ▸ₛ (emptyrecₑ ∙ ∣S∣≡) ▸H (▸-cong ⌞⌟ᵐ· ▸t)
           (▸ˢ∙ ∣S∣≡ (emptyrecₑ ok) ▸S) $ begin
           γ                                      ≤⟨ γ≤ ⟩
           q ·ᶜ wkConₘ ρ δ +ᶜ η                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
           q ·ᶜ wkConₘ ρ (p ·ᶜ δ′) +ᶜ η           ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (≈ᶜ-sym (+ᶜ-identityʳ η)) ⟩
           q ·ᶜ p ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-cong (·ᶜ-assoc _ _ _) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
           (q · p) ·ᶜ wkConₘ ρ δ′ +ᶜ η +ᶜ q ·ᶜ 𝟘ᶜ ∎
    where
    open ≤ᶜ-reasoning

  ▸-⇒ₑ ▸s (Jₕ {ρ}) =
    let r , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        r′ , δ₁ , δ₂ , ▸w , ▸u , ∣K∣≡q′ , δ≤ = lemma (inv-usage-J ▸t)
    in  ▸ₛ (Jₑ ∣K∣≡q′ ∙ ∣S∣≡) ▸H ▸w (▸ˢ∙ ∣S∣≡ (Jₑ ▸u) ▸S) $ begin
           γ                                                   ≤⟨ γ≤ ⟩
           r ·ᶜ wkConₘ ρ δ +ᶜ η                                ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
           r ·ᶜ wkConₘ ρ (r′ ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
           r ·ᶜ (wkConₘ ρ (r′ ·ᶜ δ₁) +ᶜ wkConₘ ρ δ₂) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
           (r ·ᶜ wkConₘ ρ (r′ ·ᶜ δ₁) +ᶜ r ·ᶜ wkConₘ ρ δ₂) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
           r ·ᶜ wkConₘ ρ (r′ ·ᶜ δ₁) +ᶜ r ·ᶜ wkConₘ ρ δ₂ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (+ᶜ-comm _ _) ⟩
           r ·ᶜ r′ ·ᶜ wkConₘ ρ δ₁ +ᶜ η +ᶜ r ·ᶜ wkConₘ ρ δ₂     ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
           (r · r′) ·ᶜ wkConₘ ρ δ₁ +ᶜ η +ᶜ r ·ᶜ wkConₘ ρ δ₂    ∎
    where
    open ≤ᶜ-reasoning
    lemma :
      InvUsageJ γ ⌞ r ⌟ p q A t B u v w →
      ∃₃ λ r′ δ η → δ ▸[ ⌞ r · r′ ⌟ ] w × η ▸[ ⌞ r ⌟ ] u ×
        (∣J erased-matches-for-J ⌞ r ⌟ , p , q ∣≡ r′) ×
        γ ≤ᶜ r′ ·ᶜ δ +ᶜ η
    lemma {γ} (invUsageJ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} x x₁ _ _ _ ▸u _ ▸w γ≤) =
      _ , _ , _ , ▸-cong (trans (sym ᵐ·-identityʳ-ω) ⌞⌟·ᵐ) ▸w
        , ▸u , ∣J∣≡ω x x₁ , (begin
          γ                                 ≤⟨ γ≤ ⟩
          ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
          ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)       ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
          ω ·ᶜ (γ₄ +ᶜ γ₅ +ᶜ γ₆)             ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ω ·ᶜ γ₄ +ᶜ ω ·ᶜ (γ₅ +ᶜ γ₆)        ≤⟨ +ᶜ-monotone ω·ᶜ-decreasing ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
          γ₄ +ᶜ ω ·ᶜ γ₆                     ≈⟨ +ᶜ-comm _ _ ⟩
          ω ·ᶜ γ₆ +ᶜ γ₄                     ∎)
    lemma {γ} (invUsageJ₀₁ {γ₃} {γ₄} {γ₆} x p≡𝟘 q≡𝟘 _ _ _ ▸u _ ▸w γ≤) =
       _ , _ , _ , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟)) ▸w , ▸u
         , (subst (λ em → ∣J em , _ , _ ∣≡ 𝟘) (sym x) (J-some₀ p≡𝟘 q≡𝟘)) , (begin
          γ               ≤⟨ γ≤ ⟩
          ω ·ᶜ (γ₃ +ᶜ γ₄) ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
          ω ·ᶜ γ₄         ≤⟨ ω·ᶜ-decreasing ⟩
          γ₄              ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ γ₄        ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
          𝟘 ·ᶜ γ₆ +ᶜ γ₄   ∎)
    lemma {γ} (invUsageJ₀₂ {γ₄} {γ₆} x _ _ _ ▸u _ ▸w γ≤) =
      _ , _ , _ , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟)) ▸w , ▸u
        , subst (λ em → ∣J em , _ , _ ∣≡ 𝟘) (sym x) J-all , (begin
        γ             ≤⟨ γ≤ ⟩
        γ₄            ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ γ₄      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
        𝟘 ·ᶜ γ₆ +ᶜ γ₄ ∎)

  ▸-⇒ₑ ▸s (Kₕ {ρ}) =
    let r , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        q , δ₁ , δ₂ , ▸v , ▸u , ∣K∣≡q′ , δ≤ = lemma (inv-usage-K ▸t)
    in  ▸ₛ (Kₑ ∣K∣≡q′ ∙ ∣S∣≡) ▸H ▸v
           (▸ˢ∙ ∣S∣≡ (Kₑ ▸u) ▸S) $ begin
           γ                                                  ≤⟨ γ≤ ⟩
           r ·ᶜ wkConₘ ρ δ +ᶜ η                               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
           r ·ᶜ wkConₘ ρ (q ·ᶜ δ₁ +ᶜ δ₂) +ᶜ η                 ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (wk-+ᶜ ρ)) ⟩
           r ·ᶜ (wkConₘ ρ (q ·ᶜ δ₁) +ᶜ wkConₘ ρ δ₂) +ᶜ η      ≈⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
           (r ·ᶜ wkConₘ ρ (q ·ᶜ δ₁) +ᶜ r ·ᶜ wkConₘ ρ δ₂) +ᶜ η ≈⟨ +ᶜ-assoc _ _ _ ⟩
           r ·ᶜ wkConₘ ρ (q ·ᶜ δ₁) +ᶜ r ·ᶜ wkConₘ ρ δ₂ +ᶜ η   ≈⟨ +ᶜ-cong (·ᶜ-congˡ (wk-·ᶜ ρ)) (+ᶜ-comm _ _) ⟩
           r ·ᶜ q ·ᶜ wkConₘ ρ δ₁ +ᶜ η +ᶜ r ·ᶜ wkConₘ ρ δ₂     ≈˘⟨ +ᶜ-congʳ (·ᶜ-assoc _ _ _) ⟩
           (r · q) ·ᶜ wkConₘ ρ δ₁ +ᶜ η +ᶜ r ·ᶜ wkConₘ ρ δ₂    ∎
    where
    open ≤ᶜ-reasoning
    lemma :
      InvUsageK γ ⌞ r ⌟ p A t B u v →
      ∃₃ λ q δ η → δ ▸[ ⌞ r · q ⌟ ] v × η ▸[ ⌞ r ⌟ ] u ×
        (∣K erased-matches-for-K ⌞ r ⌟ , p ∣≡ q) ×
        γ ≤ᶜ q ·ᶜ δ +ᶜ η
    lemma {γ} (invUsageK {γ₂} {γ₃} {γ₄} {γ₅} x x₁ _ _ _ ▸u ▸v γ≤) =
      _ , _ , _ , ▸-cong (trans (sym ᵐ·-identityʳ-ω) ⌞⌟·ᵐ) ▸v
        , ▸u , ∣K∣≡ω x x₁ , (begin
          γ                           ≤⟨ γ≤ ⟩
          ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
          ω ·ᶜ (γ₃ +ᶜ γ₄ +ᶜ γ₅)       ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
          ω ·ᶜ (γ₄ +ᶜ γ₅)             ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
          ω ·ᶜ γ₄ +ᶜ ω ·ᶜ γ₅          ≤⟨ +ᶜ-monotoneˡ ω·ᶜ-decreasing ⟩
          γ₄ +ᶜ ω ·ᶜ γ₅               ≈⟨ +ᶜ-comm _ _ ⟩
          ω ·ᶜ γ₅ +ᶜ γ₄               ∎)
    lemma {γ} (invUsageK₀₁ {γ₃} {γ₄} {γ₅} x p≡𝟘 _ _ _ ▸u ▸v γ≤) =
      _ , _ , _ , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟)) ▸v , ▸u
        , subst (λ em → ∣K em , _ ∣≡ 𝟘) (sym x) (K-some₀ p≡𝟘) , (begin
          γ               ≤⟨ γ≤ ⟩
          ω ·ᶜ (γ₃ +ᶜ γ₄) ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
          ω ·ᶜ γ₄         ≤⟨ ω·ᶜ-decreasing ⟩
          γ₄              ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ γ₄        ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
          𝟘 ·ᶜ γ₅ +ᶜ γ₄   ∎)
    lemma {γ} (invUsageK₀₂ {γ₄} {γ₅} x _ _ _ ▸u ▸v γ≤) =
      _ , _ , _ , ▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟)) ▸v , ▸u
        , subst (λ em → ∣K em , _ ∣≡ 𝟘) (sym x) K-all , (begin
        γ             ≤⟨ γ≤ ⟩
        γ₄            ≈˘⟨ +ᶜ-identityˡ _ ⟩
        𝟘ᶜ +ᶜ γ₄      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
        𝟘 ·ᶜ γ₅ +ᶜ γ₄ ∎)

  ▸-⇒ₑ ▸s ([]-congₕ {ρ}) =
    let q , γ , δ , η , ∣S∣≡ , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        invUsage-[]-cong {γ₄} _ _ _ ▸v ok δ≤ = inv-usage-[]-cong ▸t
    in  ▸ₛ ([]-congₑ ∙ ∣S∣≡) ▸H
           (▸-cong (sym (trans (⌞⌟-cong (·-zeroʳ _)) ⌞𝟘⌟)) ▸v)
           (▸ˢ∙ ∣S∣≡ ([]-congₑ ok) ▸S) $ begin
          γ                                      ≤⟨ γ≤ ⟩
          q ·ᶜ wkConₘ ρ δ +ᶜ η                   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)) ⟩
          q ·ᶜ wkConₘ ρ 𝟘ᶜ +ᶜ η                  ≡⟨ cong (λ x → q ·ᶜ x +ᶜ η) (wk-𝟘ᶜ ρ) ⟩
          q ·ᶜ 𝟘ᶜ +ᶜ η                           ≈⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-sym (+ᶜ-identityʳ _)) ⟩
          𝟘ᶜ +ᶜ η +ᶜ 𝟘ᶜ                          ≈˘⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (+ᶜ-congˡ (·ᶜ-zeroʳ _)) ⟩
          𝟘 ·ᶜ wkConₘ ρ γ₄ +ᶜ η +ᶜ q ·ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
          (q · 𝟘) ·ᶜ wkConₘ ρ γ₄ +ᶜ η +ᶜ q ·ᶜ 𝟘ᶜ ∎
    where
    open ≤ᶜ-reasoning

opaque

  ▸-⇾ₑ : ▸ s → s ⇾ₑ s′ → ▸ s′
  ▸-⇾ₑ ▸s (⇒ₑ d) = ▸-⇒ₑ ▸s d
  ▸-⇾ₑ {(n)} ▸s (var {p} {ρ} {x} {ρ′} ∣S∣≡p d) =
    let q , γ , δ , η , ∣S∣≡q , ▸H , ▸t , ▸S , γ≤ = ▸ₛ-inv ▸s
        γ≤′ = let open ≤ᶜ-reasoning in begin
          γ                                               ≤⟨ γ≤ ⟩
          q ·ᶜ wkConₘ ρ δ +ᶜ η                            ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ (inv-usage-var ▸t))) ⟩
          q ·ᶜ wkConₘ ρ (𝟘ᶜ , x ≔ ⌜ ⌞ q ⌟ ⌝) +ᶜ η         ≡⟨ cong (λ x → q ·ᶜ x +ᶜ η) (wk-,≔ ρ) ⟩
          q ·ᶜ (wkConₘ ρ 𝟘ᶜ , wkVar ρ x ≔ ⌜ ⌞ q ⌟ ⌝) +ᶜ η ≡⟨ cong (λ x → q ·ᶜ (x , _ ≔ ⌜ ⌞ q ⌟ ⌝) +ᶜ η) (wk-𝟘ᶜ ρ) ⟩
          q ·ᶜ (𝟘ᶜ , wkVar ρ x ≔ ⌜ ⌞ q ⌟ ⌝) +ᶜ η          ≡˘⟨ cong (_+ᶜ η) (update-distrib-·ᶜ 𝟘ᶜ q _ _) ⟩
          (q ·ᶜ 𝟘ᶜ , wkVar ρ x ≔ q · ⌜ ⌞ q ⌟ ⌝) +ᶜ η      ≈⟨ +ᶜ-congʳ (update-cong (·ᶜ-zeroʳ _) ·⌜⌞⌟⌝) ⟩
          (𝟘ᶜ , wkVar ρ x ≔ q) +ᶜ η                       ≈⟨ +ᶜ-congʳ (update-congʳ (∣∣-functional ∣S∣≡q ∣S∣≡p)) ⟩
          (𝟘ᶜ , wkVar ρ x ≔ p) +ᶜ η                       ∎
        γ⟨x⟩≤ = let open RPo ≤-poset in begin
          γ ⟨ wkVar ρ x ⟩                                          ≤⟨ lookup-monotone (wkVar ρ x) γ≤′ ⟩
          ((𝟘ᶜ , wkVar ρ x ≔ p) +ᶜ η) ⟨ wkVar ρ x ⟩            ≡⟨ lookup-distrib-+ᶜ (𝟘ᶜ , wkVar ρ x ≔ p) η _ ⟩
          (𝟘ᶜ , wkVar ρ x ≔ p) ⟨ wkVar ρ x ⟩ + η ⟨ wkVar ρ x ⟩ ≡⟨ cong (_+ η ⟨ wkVar ρ x ⟩) (update-lookup 𝟘ᶜ (wkVar ρ x)) ⟩
          p + η ⟨ wkVar ρ x ⟩                                  ≈⟨ +-comm _ _ ⟩
          η ⟨ wkVar ρ x ⟩ + p                                  ∎
        δ′ , ▸t , ▸H′ = ▸-heapLookup d ▸H γ⟨x⟩≤
        open ≤ᶜ-reasoning
    in  ▸ₛ ∣S∣≡p ▸H′ ▸t ▸S $ begin
          (γ , wkVar ρ x ≔ η ⟨ wkVar ρ x ⟩) +ᶜ p ·ᶜ wkConₘ ρ′ δ′                                             ≤⟨ +ᶜ-monotoneˡ (update-monotoneˡ _ γ≤′) ⟩
          ((𝟘ᶜ , wkVar ρ x ≔ p) +ᶜ η , wkVar ρ x ≔ η ⟨ wkVar ρ x ⟩) +ᶜ p ·ᶜ wkConₘ ρ′ δ′                     ≈˘⟨ +ᶜ-congʳ (update-congʳ (+-identityˡ _)) ⟩
          ((𝟘ᶜ , wkVar ρ x ≔ p) +ᶜ η , wkVar ρ x ≔ 𝟘 + η ⟨ wkVar ρ x ⟩) +ᶜ p ·ᶜ wkConₘ ρ′ δ′                 ≡⟨ cong (_+ᶜ (p ·ᶜ wkConₘ ρ′ δ′)) (update-distrib-+ᶜ _ η 𝟘 _ _) ⟩
          (((𝟘ᶜ , wkVar ρ x ≔ p) , wkVar ρ x ≔ 𝟘) +ᶜ (η , wkVar ρ x ≔ η ⟨ wkVar ρ x ⟩)) +ᶜ p ·ᶜ wkConₘ ρ′ δ′ ≡⟨ cong₂ (λ x y → (x +ᶜ y) +ᶜ (p ·ᶜ wkConₘ ρ′ δ′)) update-twice (update-self η _) ⟩
          ((𝟘ᶜ , wkVar ρ x ≔ 𝟘) +ᶜ η) +ᶜ p ·ᶜ wkConₘ ρ′ δ′                                                   ≡⟨ cong (λ x → (x +ᶜ η) +ᶜ (p ·ᶜ wkConₘ ρ′ δ′)) 𝟘ᶜ,≔𝟘 ⟩
          (𝟘ᶜ +ᶜ η) +ᶜ p ·ᶜ wkConₘ ρ′ δ′                                                                     ≈⟨ +ᶜ-congʳ (+ᶜ-identityˡ η) ⟩
          η +ᶜ p ·ᶜ wkConₘ ρ′ δ′                                                                             ≈⟨ +ᶜ-comm η _ ⟩
          p ·ᶜ wkConₘ ρ′ δ′ +ᶜ η                                                                             ∎

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
    let _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ▸e , _ = ▸ₛ-∙-inv ▸s′
    in  ▸-inv-sucₑ ▸e
  ¬▸-⇒ₙ ▸s (numₕ x) ▸s′ =
    let _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ▸e , _ = ▸ₛ-∙-inv ▸s
    in  ▸-inv-sucₑ ▸e

opaque

  -- There are four different reasons why a well-resourced state can
  -- be Final:
  -- 1. It has a variable in head position pointing to a dummy entry
  --    in the heap and the stack multiplicity is 𝟘 if the modality has
  --    a well-behaved zero.
  -- 2. It has a value in head position, the stack is not empty and the
  --    top of the stack does not match the head.
  -- 3. It has a value in head position and the stack is empty.
  -- 4. It has a name in head position.

  ▸Final-reasons :
    Supports-subtraction →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final (⟨_,_,_,_⟩ H t ρ S) →
    (∃ λ x → t ≡ var x × H ⊢ wkVar ρ x ↦● ×
       (Has-well-behaved-zero M semiring-with-meet → ∣ S ∣≡ 𝟘)) ⊎
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × ¬ Matching t S) ⊎
    Value t × S ≡ ε ⊎
    (∃ λ α → t ≡ defn α)
  ▸Final-reasons {ρ} ok ▸s f =
    let _ , _ , _ , _ , ∣S∣≡ , _ = ▸ₛ-inv ▸s
    in  case Final-reasons _ f of λ where
          (inj₂ (inj₂ x)) → inj₂ (inj₂ x)
          (inj₂ (inj₁ (_ , _ , eq , v , prop))) →
            inj₂ (inj₁ (_ , _ , eq , v , λ m → prop (m , _ , ∣S∣≡)))
          (inj₁ (x , refl , ¬d)) →
            case ↦⊎↦● (wkVar ρ x) of λ where
              (inj₁ (_ , _ , d)) →
                case ▸↦→↦[] ok ∣S∣≡ d ▸s of λ
                  (_ , d′) →
                ⊥-elim (¬d ∣S∣≡ d′)
              (inj₂ d) → inj₁ (_ , refl , d , λ x → ▸s● ok ⦃ x ⦄ d ▸s)

-- opaque

--   -- A variant of the above property with the added assumption that
--   -- there are no erased matches and the zero is well-behaved if the
--   -- state is not closed.

--   -- Under this assumption there are four reasons why a well-resourced
--   -- state can be Final:
--   -- 1. It has a variable in head position pointing to a dummy entry
--   --    in the heap, the stack contains an erased emptyrec and erased uses
--   --    of emptyrec are allowed.
--   -- 2. It has a value in head position, the stack is not empty and the
--   --    top of the stack does not match the head.
--   -- 3. It has a value in head position and the stack is empty.
--   -- 4. It has a name in head position.

--   ▸Final-reasons′ :
--     ∀ {k} {H : Heap k _} →
--     Supports-subtraction →
--     (k ≢ 0 → No-erased-matches′ type-variant UR × Has-well-behaved-zero M semiring-with-meet) →
--     ▸ ⟨ H , t , ρ , S ⟩ →
--     Final (⟨_,_,_,_⟩ H t ρ S) →
--     (∃ λ x → t ≡ var x × H ⊢ wkVar ρ x ↦● × emptyrec 𝟘 ∈ S × Emptyrec-allowed 𝟙ᵐ 𝟘) ⊎
--     (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
--     Value t × S ≡ ε ⊎
--     (∃ λ α → t ≡ defn α)
--   ▸Final-reasons′ {ρ} ok prop ▸s f =
--     let _ , _ , _ , _ , _ , _ , _ , ▸S , _ = ▸ₛ-inv ▸s in
--     case ▸Final-reasons ok ▸s f of λ where
--       (inj₂ x) → inj₂ x
--       (inj₁ (x , t≡x , d , ∣S∣≡𝟘)) →
--         let nem , wb-𝟘 = prop (¬erased-heap→¬↦● d)
--         in  inj₁ (x , t≡x , d , {!!})
--         -- case ▸∣∣≢𝟘 nem ⦃ wb-𝟘 ⦄ ▸S of λ where
--         --       (inj₁ ∣S∣≢𝟘) → ⊥-elim (∣S∣≢𝟘 (∣S∣≡𝟘 wb-𝟘))
--         --       (inj₂ prop) → inj₁ (x , t≡x , d , prop)

opaque

  -- A variant of ▸Final-reasons

  ▸-⇘-reasons :
    Supports-subtraction →
    ▸ s →
    s ⇘ ⟨ H , t , ρ , S ⟩ →
    (∃ λ x → t ≡ var x × H ⊢ wkVar ρ x ↦● ×
      (Has-well-behaved-zero M semiring-with-meet → ∣ S ∣≡ 𝟘)) ⊎
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε ⊎
    (∃ λ α → t ≡ defn α)
  ▸-⇘-reasons ok ▸s (d , f) =
    ▸Final-reasons ok (▸-⇾* ▸s d) f

opaque

  -- There are three different reasons why a closed state can be
  -- Final:
  -- 1. It has a value in head position, the stack is not empty and the
  --    top of the stack does not match the head.
  -- 2. It has a value in head position and the stack is empty.
  -- 3. It has a name in head position.

  ▸Final-reasons-closed :
    {H : Heap 0 _} →
    Supports-subtraction →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final (⟨_,_,_,_⟩ H t ρ S) →
    (∃₂ λ e S′ → S ≡ e ∙ S′ × Value t × (Matching t S → ⊥)) ⊎
    Value t × S ≡ ε ⊎
    (∃ λ α → t ≡ defn α)
  ▸Final-reasons-closed ok ▸s f =
    case ▸Final-reasons ok ▸s f of λ where
      (inj₁ (_ , _ , d , _)) → ⊥-elim (¬erased-heap→¬↦● d refl)
      (inj₂ x) → x
