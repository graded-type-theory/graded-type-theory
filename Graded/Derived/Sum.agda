------------------------------------------------------------------------
-- Some properties related to usage and Sum.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Derived.Sum
  {ℓ ℓ′} {M : Set ℓ} {Mode : Set ℓ′}
  (open Graded.Modality M)
  {𝕄 : Modality}
  {𝐌 : IsMode Mode 𝕄}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 𝐌)
  (open Usage-restrictions UR)
  ⦃ no-nr : Nr-not-available-GLB ⦄
  where

open Modality 𝕄
open IsMode 𝐌

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Derived.Bool.Greatest-lower-bound UR
open import Graded.Derived.Sup TR UR
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution.Properties UR
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Weakening UR

open import Definition.Untyped M
open import Definition.Untyped.Sum TR

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality

private variable
  k                          : Nat
  a b A B P t u l r          : Term[ _ ] _
  γ γ₁ γ₂ γ₃ γ₄ γ₅ δ δ₁ δ₂ η : Conₘ _
  p p′ p₁ p₂ p₃ p₄ q r₁ r₂   : M
  m                          : Mode

------------------------------------------------------------------------
-- The type Sum-allowed

-- A collection of usage restrictions that are used to show that the
-- Sum type is well-resourced.

record Sum-allowed (m : Mode) : Set ℓ where
  no-eta-equality
  field
    Prodrec-ok  : Prodrec-allowed m 𝟙 𝟙 𝟘
    Unitrec-ok  : Unitrec-allowed m 𝟙 𝟘
    Emptyrec-ok : Emptyrec-allowed m 𝟘
    Sink-ok     : Starˢ-sink

------------------------------------------------------------------------
-- Usage lemmas

opaque
  unfolding Sum′

  -- A usage lemma for Sum′

  ▸Sum′ :
    γ₁ ▸[ 𝟘ᵐ ] a →
    γ₂ ▸[ 𝟘ᵐ ] b →
    γ₃ ▸[ m ] A →
    γ₄ ▸[ m ] B →
    γ₅ ▸[ m ] t →
    Sum-allowed m →
    γ₅ +ᶜ γ₃ ∧ᶜ γ₄ ▸[ m ] Sum′ a b A B t
  ▸Sum′ ▸a ▸b ▸A ▸B ▸t ok =
    ▸boolrec Prodrec-ok Unitrec-ok Emptyrec-ok Sink-ok
      (sub-≈ᶜ (Uₘ (wkUsage _ (▸supᵘₗ ▸a ▸b .proj₂)))
         (≈ᶜ-refl ∙ ·-zeroʳ _))
      (Liftₘ ▸b ▸A) (Liftₘ ▸a ▸B) ▸t
    where
    open Sum-allowed ok

private opaque

  -- A usage lemma for Sum′ applied to var x0

  ▸Sum′₀ :
    γ₁ ▸[ 𝟘ᵐ ] a →
    γ₂ ▸[ 𝟘ᵐ ] b →
    γ₃ ▸[ m ] A →
    γ₄ ▸[ m ] B →
    Sum-allowed m →
    γ₃ ∧ᶜ γ₄ ∙ ⌜ m ⌝ · 𝟙 ▸[ m ] Sum′ (wk1 a) (wk1 b) (wk1 A) (wk1 B) (lower (var x0))
  ▸Sum′₀ {γ₃} {m} {γ₄} ▸a ▸b ▸A ▸B ok =
    sub-≈ᶜ
      (▸Sum′ (wkUsage (step id) ▸a) (wkUsage (step id) ▸b)
        (wkUsage (step id) ▸A) (wkUsage (step id) ▸B) (lowerₘ var) ok) $ begin
      (γ₃ ∧ᶜ γ₄) ∙ (⌜ m ⌝ · 𝟙)             ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
      (γ₃ ∧ᶜ γ₄) ∙ ⌜ m ⌝                   ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ⟩
      (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ ((γ₃ ∧ᶜ γ₄) ∙ 𝟘)     ≈˘⟨ +ᶜ-congˡ (≈ᶜ-refl ∙ ∧-idem _) ⟩
      (𝟘ᶜ ∙ ⌜ m ⌝) +ᶜ (γ₃ ∙ 𝟘) ∧ᶜ (γ₄ ∙ 𝟘) ∎
    where
    open ≈ᶜ-reasoning

opaque
  unfolding Sum

  -- A usage lemma for Sum

  ▸Sum :
    γ₁ ▸[ 𝟘ᵐ ] a →
    γ₂ ▸[ 𝟘ᵐ ] b →
    γ₃ ▸[ m ] A →
    γ₄ ▸[ m ] B →
    Sum-allowed m →
    γ₃ ∧ᶜ γ₄ ▸[ m ] Sum a b A B
  ▸Sum {γ₃} {γ₄} ▸a ▸b ▸A ▸B ok =
    sub-≈ᶜ
      (ΠΣₘ (Liftₘ (▸supᵘₗ ▸a ▸b .proj₂) ▸Bool)
         (▸Sum′₀ ▸a ▸b ▸A ▸B ok)) $ begin
      γ₃ ∧ᶜ γ₄                ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ γ₃ ∧ᶜ γ₄          ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ γ₃ ∧ᶜ γ₄     ∎
    where
    open ≈ᶜ-reasoning

opaque
  unfolding inl

  -- A usage lemma for inl

  ▸inl :
    γ ▸[ m ] t →
    γ ▸[ m ] inl t
  ▸inl {γ} ▸t =
    sub-≈ᶜ (prodʷₘ (liftₘ ▸true) (liftₘ ▸t)) $ begin
      γ                ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ γ          ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ γ     ∎
    where
    open ≈ᶜ-reasoning

opaque
  unfolding inr

  -- A usage lemma for inr

  ▸inr :
    γ ▸[ m ] t →
    γ ▸[ m ] inr t
  ▸inr {γ} ▸t =
    sub-≈ᶜ (prodʷₘ (liftₘ ▸false) (liftₘ ▸t)) $ begin
      γ                ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ γ          ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ γ     ∎
    where
    open ≈ᶜ-reasoning

opaque
  unfolding Targetˢʳ

  -- A usage lemma for Targetˢʳ.

  ▸Targetˢʳ :
    γ₁ ∙ p ▸[ m ] A →
    γ₂ ▸[ ⌞ p ⌟ ] t →
    γ₃ ▸[ ⌞ p ⌟ ] u →
    wkConₘ (stepn id k) γ₁ +ᶜ p ·ᶜ (γ₂ +ᶜ γ₃) ▸[ m ] Targetˢʳ k A t u
  ▸Targetˢʳ ▸A ▸t ▸u =
    ▸[][]↑ ▸A $ sub-≈ᶜ (▸-·′ $ prodʷₘ (liftₘ (▸-cong (sym ᵐ·-identityʳ) ▸t)) ▸u)
      (·ᶜ-congˡ (+ᶜ-congʳ (≈ᶜ-sym (·ᶜ-identityˡ _))))

opaque
  unfolding sumrec

  -- A usage lemma for sumrec

  ▸sumrec :
    γ₁ ▸[ 𝟘ᵐ ] a →
    γ₂ ▸[ 𝟘ᵐ ] b →
    γ₃ ▸[ 𝟘ᵐ ] A →
    γ₄ ▸[ 𝟘ᵐ ] B →
    γ₅ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] P →
    δ₁ ∙ ⌜ m ⌝ · p₁ ▸[ m ] l →
    δ₂ ∙ ⌜ m ⌝ · p₂ ▸[ m ] r →
    η ▸[ m ᵐ· p ] t →
    p ≤ p₁ →
    p ≤ p₂ →
    ⌜ m ⌝ · p ≤ ⌜ m ⌝ →
    Sum-allowed 𝟘ᵐ →
    Prodrec-allowed m p 𝟙 q →
    Prodrec-allowed m 𝟙 𝟙 (q + p) →
    Unitrec-allowed m 𝟙 (q + p) →
    Emptyrec-allowed m 𝟘 →
    p ·ᶜ η +ᶜ δ₁ ∧ᶜ δ₂ ▸[ m ] sumrec q p a b A B P l r t
  ▸sumrec {γ₃} {γ₄} {γ₅} {q} {δ₁} {m} {δ₂} {p}
    ▸a ▸b ▸A ▸B ▸P ▸l ▸r ▸t p≤p₁ p≤p₂ ≤m Sum-ok Prodrec-ok₁ Prodrec-ok₂ Unitrec-ok Emptyrec-ok =
    let ▸l′ = lamₘ (sub (▸[][]↑ ▸l ▸lower₀) (lemma {δ = δ₁} p≤p₁))
        ▸r′ = lamₘ (sub (▸[][]↑ ▸r ▸lower₀) (lemma {δ = δ₂} p≤p₂))
        ▸a₃ = wkUsage _ ▸a
        ▸b₃ = wkUsage _ ▸b
        ▸A₃ = wkUsage _ (▸-cong (sym ᵐ·-zeroˡ) ▸A)
        ▸B₃ = wkUsage _ (▸-cong (sym ᵐ·-zeroˡ) ▸B)
        Sum-ok′ = subst Sum-allowed (sym ᵐ·-zeroˡ) Sum-ok
        ▸Q′ = sub (▸Targetˢʳ ▸P var var) $ begin
          γ₅ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · q ∙ ⌜ 𝟘ᵐ ⌝ · q                                                                               ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityˡ _ ⟩
          (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) +ᶜ  (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · q ∙ ⌜ 𝟘ᵐ ⌝ · q)                                                            ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityʳ _ ∙ +-identityˡ _) ⟩
          (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) +ᶜ  (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · q ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · q)                                                ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·⌜⌞⌟⌝ ∙ ·-zeroʳ _) (·ᶜ-zeroʳ _ ∙ ·⌜⌞⌟⌝)) ⟩
          (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ ⌝ · q) ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · q ⌟ ⌝ ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ ⌝ · q) ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · q ⌟ ⌝) ≈˘⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) +ᶜ (⌜ 𝟘ᵐ ⌝ · q) ·ᶜ ((𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · q ⌟ ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ⌜ 𝟘ᵐ ⌝ · q ⌟ ⌝))               ∎
        ▸Q = sub (ΠΣₘ (▸Sum′ ▸a₃ ▸b₃ ▸A₃ ▸B₃ var Sum-ok′) ▸Q′) $ begin
          p ·ᶜ (γ₃ ∧ᶜ γ₄) +ᶜ γ₅ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · (q + p)                                                 ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (+-comm _ _) ⟩
          p ·ᶜ (γ₃ ∧ᶜ γ₄) +ᶜ γ₅ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · (p + q)                                                 ≈˘⟨ ≈ᶜ-refl ∙ +-identityˡ _ ∙ +-identityˡ _ ∙ sym (·-distribˡ-+ _ _ _) ⟩
          (p ·ᶜ (γ₃ ∧ᶜ γ₄) ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · p) +ᶜ (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · q)                              ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityˡ _ ∙ +-identityʳ _) ⟩
          ((𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p) +ᶜ (p ·ᶜ (γ₃ ∧ᶜ γ₄) ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)) +ᶜ (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · q)                ≈˘⟨ +ᶜ-congʳ (+ᶜ-cong (·ᶜ-zeroʳ _ ∙ sym (⌜⌝-·-comm _)) (≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _)) ⟩
          (p ·ᶜ (𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝) +ᶜ p ·ᶜ ((γ₃ ∧ᶜ γ₄) ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)) +ᶜ (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · q)               ≈˘⟨ +ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
          p ·ᶜ ((𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝) +ᶜ ((γ₃ ∧ᶜ γ₄) ∙ 𝟘 ∙ 𝟘 ∙ 𝟘)) +ᶜ (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · q)                    ≈˘⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-cong (≈ᶜ-refl ∙ ⌜⌝-cong ᵐ·-zeroˡ) (≈ᶜ-refl ∙ ∧-idem _ ∙ ∧-idem _ ∙ ∧-idem _))) ⟩
          p ·ᶜ ((𝟘ᶜ ∙ ⌜ 𝟘ᵐ ᵐ· p ⌝) +ᶜ ((γ₃ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) ∧ᶜ (γ₄ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘))) +ᶜ (γ₅ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ 𝟘ᵐ ⌝ · q) ∎
        ▸br = ▸boolrec Prodrec-ok₂ Unitrec-ok Emptyrec-ok (Sum-allowed.Sink-ok Sum-ok) ▸Q ▸l′ ▸r′ (lowerₘ var)
        ▸br∘ = sub (▸br ∘ₘ var) $ begin
          δ₁ ∧ᶜ δ₂ ∙ ⌜ m ⌝ · p · 𝟙 ∙ ⌜ m ⌝ · p                                         ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-identityʳ _) ∙ refl ⟩
          δ₁ ∧ᶜ δ₂ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · p                                             ≤⟨ ≤ᶜ-refl ∙ ≤m ∙ ≤-refl ⟩
          δ₁ ∧ᶜ δ₂ ∙ ⌜ m ⌝ ∙ ⌜ m ⌝ · p                                                 ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
          (δ₁ ∧ᶜ δ₂ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ · p)                                   ≈˘⟨ +ᶜ-cong (+ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ +-identityʳ _)
                                                                                              (≈ᶜ-refl ∙ sym (⌜⌝-·-comm _)) ⟩
          ((𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ (δ₁ ∧ᶜ δ₂ ∙ 𝟘 ∙ 𝟘)) +ᶜ (𝟘ᶜ ∙ p · ⌜ m ⌝)                 ≈˘⟨ +ᶜ-cong (+ᶜ-congˡ (≈ᶜ-refl ∙ ∧-idem _ ∙ ∧-idem _))
                                                                                              (·ᶜ-zeroʳ _ ∙ ·⌜ᵐ·⌝ _) ⟩
          ((𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘) +ᶜ (δ₁ ∙ 𝟘 ∙ 𝟘) ∧ᶜ (δ₂ ∙ 𝟘 ∙ 𝟘)) +ᶜ p ·ᶜ (𝟘ᶜ ∙ ⌜ m ᵐ· p ⌝) ∎
    in  prodrecₘ ▸t ▸br∘ ▸P Prodrec-ok₁
    where
    open ≤ᶜ-reasoning
    ▸lower₀ : ∀ {p} → ⌜ ⌞ ⌜ m ⌝ · p ⌟ ⌝ ·ᶜ (𝟘ᶜ {n = k} ∙ 𝟙) ▸[ ⌞ ⌜ m ⌝ · p ⌟ ] lower (var x0)
    ▸lower₀ = sub-≈ᶜ (lowerₘ var) (·ᶜ-zeroʳ _ ∙ ·-identityʳ _)

    lemma : ∀ {p p′} → p ≤ p′ → δ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · p ≤ᶜ wkConₘ (stepn id 3) δ +ᶜ (⌜ m ⌝ · p′) ·ᶜ (𝟘ᶜ ∙ 𝟙)
    lemma {δ} {p} {p′} p≤p′ = begin
      δ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · p                             ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ p≤p′ ⟩
      δ ∙ 𝟘 ∙ 𝟘 ∙ ⌜ m ⌝ · p′                            ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ⟩
      (δ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) +ᶜ (𝟘ᶜ ∙ ⌜ m ⌝ · p′)              ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) ⟩
      (δ ∙ 𝟘 ∙ 𝟘 ∙ 𝟘) +ᶜ (⌜ m ⌝ · p′) ·ᶜ (𝟘ᶜ ∙ 𝟙)       ≡⟨⟩
      wkConₘ (stepn id 3) δ +ᶜ (⌜ m ⌝ · p′) ·ᶜ (𝟘ᶜ ∙ 𝟙) ∎

opaque

  -- An alternative usage lemma for sumrec

  ▸sumrec′ :
      γ₁ ▸[ 𝟘ᵐ ] a →
      γ₂ ▸[ 𝟘ᵐ ] b →
      γ₃ ▸[ 𝟘ᵐ ] A →
      γ₄ ▸[ 𝟘ᵐ ] B →
      γ₅ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] P →
      δ₁ ∙ ⌜ m ⌝ · p₁ ▸[ m ] l →
      δ₂ ∙ ⌜ m ⌝ · p₂ ▸[ m ] r →
      η ▸[ m ] t →
      Sum-allowed 𝟘ᵐ →
      Prodrec-allowed m (p₁ ∧ p₂ ∧ 𝟙) 𝟙 q →
      Prodrec-allowed m 𝟙 𝟙 (q + (p₁ ∧ p₂ ∧ 𝟙)) →
      Unitrec-allowed m 𝟙 (q + (p₁ ∧ p₂ ∧ 𝟙)) →
      Emptyrec-allowed m 𝟘 →
      (p₁ ∧ p₂ ∧ 𝟙) ·ᶜ η +ᶜ δ₁ ∧ᶜ δ₂ ▸[ m ] sumrec q (p₁ ∧ p₂ ∧ 𝟙) a b A B P l r t
  ▸sumrec′ {m} {p₁} {p₂} ▸a ▸b ▸A ▸B ▸P ▸l ▸r ▸t ok₁ ok₂ ok₃ ok₄ ok₅ =
    ▸sumrec ▸a ▸b ▸A ▸B ▸P ▸l ▸r
      (▸-cong (sym (ᵐ·-identityʳ-≤𝟙 lemma)) ▸t)
      (∧-decreasingˡ p₁ (p₂ ∧ 𝟙))
      (≤-trans (∧-decreasingʳ p₁ (p₂ ∧ 𝟙)) (∧-decreasingˡ p₂ 𝟙))
      (begin
        ⌜ m ⌝ · (p₁ ∧ p₂ ∧ 𝟙) ≤⟨ ·-monotoneʳ lemma ⟩
        ⌜ m ⌝ · 𝟙             ≈⟨ ·-identityʳ _ ⟩
        ⌜ m ⌝                 ∎)
      ok₁ ok₂ ok₃ ok₄ ok₅
    where
    open ≤-reasoning
    lemma : p₁ ∧ p₂ ∧ 𝟙 ≤ 𝟙
    lemma = begin
      p₁ ∧ p₂ ∧ 𝟙 ≤⟨ ∧-decreasingʳ p₁ (p₂ ∧ 𝟙) ⟩
      p₂ ∧ 𝟙      ≤⟨ ∧-decreasingʳ p₂ 𝟙 ⟩
      𝟙           ∎


------------------------------------------------------------------------
-- Usage inversion lemmas

opaque
  unfolding Sum′

  -- A usage inversion lemma for Sum′

  inv-usage-Sum′ :
    γ ▸[ m ] Sum′ a b A B t →
    ∃₅ λ γ₁ γ₂ γ₃ γ₄ γ₅ →
    γ₁ ▸[ 𝟘ᵐ ] a × γ₂ ▸[ 𝟘ᵐ ] b ×
    γ₃ ▸[ m ] A × γ₄ ▸[ m ] B × γ₅ ▸[ m ] t ×
    Prodrec-allowed m 𝟙 𝟙 𝟘 × Unitrec-allowed m 𝟙 𝟘 ×
    Emptyrec-allowed m 𝟘 × γ ≤ᶜ γ₅ +ᶜ γ₃ ∧ᶜ γ₄
  inv-usage-Sum′ ▸sum =
    let _ , _ , _ , _ , ▸↑A , ▸↑B , ▸t , ▸U , ok₁ , ok₂ , ok₃ , γ≤ = inv-usage-boolrec ▸sum
        (_ , ▸b) , ▸A = inv-usage-Lift ▸↑A
        (_ , ▸a) , ▸B = inv-usage-Lift ▸↑B
    in  _ , _ , _ , _ , _ , ▸a , ▸b , ▸A , ▸B , ▸t
          , ok₁ , ok₂ , ok₃ , γ≤

opaque
  unfolding Sum

  -- A usage inversion lemma for Sum

  inv-usage-Sum :
    γ ▸[ m ] Sum a b A B →
    ∃₄ λ γ₁ γ₂ γ₃ γ₄ →
    γ₁ ▸[ 𝟘ᵐ ] a × γ₂ ▸[ 𝟘ᵐ ] b ×
    γ₃ ▸[ m ] A × γ₄ ▸[ m ] B ×
    Prodrec-allowed m 𝟙 𝟙 𝟘 × Unitrec-allowed m 𝟙 𝟘 ×
    Emptyrec-allowed m 𝟘 × γ ≤ᶜ γ₃ ∧ᶜ γ₄
  inv-usage-Sum {γ} ▸Sum =
    let invUsageΠΣ {δ} {η} ▸Bool ▸Sum′ γ≤ = inv-usage-ΠΣ ▸Sum
        open ≤ᶜ-reasoning
    in  case inv-usage-Sum′ ▸Sum′ of λ {
          (_ , _ , η₁ ∙ _ , η₂ ∙ _ , η₃ ∙ _ , ▸a , ▸b , ▸A , ▸B , ▸x0 , ok₁ , ok₂ , ok₃ , η≤ ∙ _) →
        _ , _ , _ , _
          , wkUsage⁻¹ ▸a , wkUsage⁻¹ ▸b
          , wkUsage⁻¹ ▸A , wkUsage⁻¹ ▸B
          , ok₁ , ok₂ , ok₃ , (begin
            γ                             ≤⟨ γ≤ ⟩
            𝟙 ·ᶜ δ +ᶜ η                   ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (inv-usage-Bool (inv-usage-Lift ▸Bool .proj₂))) η≤ ⟩
            𝟙 ·ᶜ 𝟘ᶜ +ᶜ η₃ +ᶜ η₁ ∧ᶜ η₂     ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
            𝟘ᶜ +ᶜ η₃ +ᶜ η₁ ∧ᶜ η₂          ≈⟨ +ᶜ-identityˡ _ ⟩
            η₃ +ᶜ η₁ ∧ᶜ η₂                ≤⟨ +ᶜ-monotoneˡ (tailₘ-monotone (inv-usage-var (inv-usage-lower ▸x0))) ⟩
            𝟘ᶜ +ᶜ η₁ ∧ᶜ η₂                ≈⟨ +ᶜ-identityˡ _ ⟩
            η₁ ∧ᶜ η₂                      ∎) }

opaque
  unfolding inl

  -- A usage inversion lemma for inl

  inv-usage-inl : γ ▸[ m ] inl t → γ ▸[ m ] t
  inv-usage-inl {γ} ▸inl =
    let invUsageProdʷ {δ} {η} ▸true ▸t γ≤ = inv-usage-prodʷ ▸inl
        open ≤ᶜ-reasoning
    in  sub (inv-usage-lift ▸t) $ begin
      γ                ≤⟨ γ≤ ⟩
      𝟙 ·ᶜ δ +ᶜ η      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (inv-usage-true (inv-usage-lift ▸true))) ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ η     ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η          ≈⟨ +ᶜ-identityˡ _ ⟩
      η                ∎

opaque
  unfolding inr

  -- A usage inversion lemma for inr

  inv-usage-inr : γ ▸[ m ] inr t → γ ▸[ m ] t
  inv-usage-inr {γ} ▸inr =
    let invUsageProdʷ {δ} {η} ▸false ▸t γ≤ = inv-usage-prodʷ ▸inr
        open ≤ᶜ-reasoning
    in  sub (inv-usage-lift ▸t) $ begin
      γ                ≤⟨ γ≤ ⟩
      𝟙 ·ᶜ δ +ᶜ η      ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (inv-usage-false (inv-usage-lift ▸false))) ⟩
      𝟙 ·ᶜ 𝟘ᶜ +ᶜ η     ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
      𝟘ᶜ +ᶜ η          ≈⟨ +ᶜ-identityˡ _ ⟩
      η                ∎

opaque
  unfolding sumrec

  -- A usage inversion lemma for sumrec.
  -- It might be possible to make this property stronger
  -- (e.g. if a form of inversion for substitution is proven)

  inv-usage-sumrec :
    γ ▸[ m ] sumrec q p a b A B P l r t →
    ∃₈ λ δ₁ δ₂ δ₃ δ₄ γ₁ γ₂ γ₃ γ₄ →
    δ₁ ▸[ 𝟘ᵐ ] a ×
    δ₂ ▸[ 𝟘ᵐ ] b ×
    δ₃ ▸[ 𝟘ᵐ ] A ×
    δ₄ ▸[ 𝟘ᵐ ] B ×
    γ₁ ▸[ m ᵐ· p ] t ×
    γ₂ ∙ ⌜ m ⌝ · p ▸[ m ] l [ 3 ][ lower (var x0) ]↑ ×
    γ₃ ∙ ⌜ m ⌝ · p ▸[ m ] r [ 3 ][ lower (var x0) ]↑ ×
    γ₄ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] P ×
    Prodrec-allowed m p 𝟙 q × Prodrec-allowed m 𝟙 𝟙 (q + p) ×
    Unitrec-allowed m 𝟙 (q + p) × Emptyrec-allowed m 𝟘 ×
    Prodrec-allowed 𝟘ᵐ 𝟙 𝟙 𝟘 × Unitrec-allowed 𝟘ᵐ 𝟙 𝟘 ×
    Emptyrec-allowed 𝟘ᵐ 𝟘 ×
    γ ≤ᶜ p ·ᶜ γ₁ +ᶜ tailₘ (tailₘ γ₂) ∧ᶜ tailₘ (tailₘ γ₃) ×
    ⌜ m ⌝ · p ≤ ⌜ m ⌝ + headₘ (tailₘ γ₂) ∧ headₘ (tailₘ γ₃) ×
    ⌜ m ⌝ · p ≤ ⌜ m ⌝ · p + headₘ γ₂ ∧ headₘ γ₃
  inv-usage-sumrec {γ} {m} {p} ▸sr =
    let invUsageProdrec {δ} {η} ▸t ▸br∘ ▸P ok₁ γ≤ = inv-usage-prodrec ▸sr
    in  case inv-usage-app ▸br∘ of λ {
          (invUsageApp {δ = η₁ ∙ q₁ ∙ q₂} {η = η₂ ∙ q₃ ∙ q₄} ▸br ▸x0 (η≤ ∙ mp≤ ∙ mp≤′)) →
        case inv-usage-boolrec ▸br of λ {
          (δ₁ ∙ r₁ ∙ r₂ , δ₂ ∙ r₃ ∙ r₄ , δ₃ ∙ r₅ ∙ r₆ , θ ∙ _ ∙ _ , ▸l′ , ▸r′ , ▸x1 , ▸Q , ok₂ , ok₃ , ok₄ , (η₁≤ ∙ q₁≤ ∙ q₂≤)) →
        case inv-usage-lam ▸l′ of λ {
          (invUsageLam {δ = δ₁′ ∙ p₁ ∙ p₂} ▸l (δ₁≤ ∙ r₁≤ ∙ r₂≤)) →
        case inv-usage-lam ▸r′ of λ {
          (invUsageLam {δ = δ₂′ ∙ p₃ ∙ p₄} ▸r (δ₂≤ ∙ r₃≤ ∙ r₄≤)) →
        case inv-usage-ΠΣ ▸Q of λ {
          (invUsageΠΣ ▸Sum′ ▸T θ≤) →
        case inv-usage-Sum′ (▸-cong ᵐ·-zeroˡ ▸Sum′) of λ
          (_ , _ , _ , _ , _ , ▸a , ▸b , ▸A , ▸B , _ , ok₅ , ok₆ , ok₇ , _) →
        _ , _ , _ , _ , _ , _ , _ , _
          , wkUsage⁻¹ ▸a , wkUsage⁻¹ ▸b , wkUsage⁻¹ ▸A , wkUsage⁻¹ ▸B , ▸t , ▸l , ▸r , ▸P
          , ok₁ , ok₂ , ok₃ , ok₄ , ok₅ , ok₆ , ok₇
          , (let open ≤ᶜ-reasoning in begin
              γ ≤⟨ γ≤ ⟩
              p ·ᶜ δ +ᶜ η                           ≤⟨ +ᶜ-monotoneʳ η≤ ⟩
              p ·ᶜ δ +ᶜ η₁ +ᶜ p ·ᶜ η₂               ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotone η₁≤ (·ᶜ-monotoneʳ (tailₘ-monotone (tailₘ-monotone (inv-usage-var ▸x0))))) ⟩
              p ·ᶜ δ +ᶜ (δ₃ +ᶜ δ₁ ∧ᶜ δ₂) +ᶜ p ·ᶜ 𝟘ᶜ ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneˡ (+ᶜ-monotoneˡ (tailₘ-monotone (tailₘ-monotone (inv-usage-var (inv-usage-lower ▸x1)))))) ⟩
              p ·ᶜ δ +ᶜ (𝟘ᶜ +ᶜ δ₁ ∧ᶜ δ₂) +ᶜ p ·ᶜ 𝟘ᶜ ≈⟨ +ᶜ-congˡ (+ᶜ-cong (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _)) ⟩
              p ·ᶜ δ +ᶜ (δ₁ ∧ᶜ δ₂) +ᶜ 𝟘ᶜ            ≈⟨ +ᶜ-congˡ (+ᶜ-identityʳ _) ⟩
              p ·ᶜ δ +ᶜ (δ₁ ∧ᶜ δ₂)                  ≤⟨ +ᶜ-monotoneʳ (∧ᶜ-monotone δ₁≤ δ₂≤) ⟩
              p ·ᶜ δ +ᶜ (δ₁′ ∧ᶜ δ₂′)                ∎)
          , (let open ≤-reasoning in begin
              ⌜ m ⌝ · p              ≈˘⟨ ·-congˡ (·-identityʳ _) ⟩
              ⌜ m ⌝ · p · 𝟙          ≤⟨ mp≤ ⟩
              q₁ + p · q₃            ≤⟨ +-monotone q₁≤ (·-monotoneʳ (headₘ-monotone (tailₘ-monotone (inv-usage-var ▸x0)))) ⟩
              (r₅ + r₁ ∧ r₃) + p · 𝟘 ≈⟨ +-congˡ (·-zeroʳ _) ⟩
              (r₅ + r₁ ∧ r₃) + 𝟘     ≈⟨ +-identityʳ _ ⟩
              r₅ + r₁ ∧ r₃           ≤⟨ +-monotone (headₘ-monotone (tailₘ-monotone (inv-usage-var (inv-usage-lower ▸x1)))) (∧-monotone r₁≤ r₃≤) ⟩
              ⌜ m ⌝ + p₁ ∧ p₃        ∎)
          , (let open ≤-reasoning in begin
              ⌜ m ⌝ · p                       ≤⟨ mp≤′ ⟩
              q₂ + p · q₄                     ≤⟨ +-monotone q₂≤ (·-monotoneʳ (headₘ-monotone (inv-usage-var ▸x0))) ⟩
              (r₆ + r₂ ∧ r₄) + p · ⌜ m ᵐ· p ⌝ ≤⟨ +-monotoneˡ (+-monotone (headₘ-monotone (inv-usage-var (inv-usage-lower ▸x1))) (∧-monotone r₂≤ r₄≤)) ⟩
              (𝟘 + p₂ ∧ p₄) + p · ⌜ m ᵐ· p ⌝  ≈⟨ +-cong (+-identityˡ _) (·⌜ᵐ·⌝ _) ⟩
              (p₂ ∧ p₄) + p · ⌜ m ⌝           ≈˘⟨ +-congˡ (⌜⌝-·-comm _) ⟩
              (p₂ ∧ p₄) + ⌜ m ⌝ · p           ≈⟨ +-comm _ _ ⟩
              ⌜ m ⌝ · p + p₂ ∧ p₄             ∎) }}}}}
