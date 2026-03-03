------------------------------------------------------------------------
-- A property related to usage and ℕ
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Nat
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Restrictions.Instance R
open import Graded.Usage.Properties R
open import Graded.Usage.Weakening R

open import Definition.Untyped M
open import Definition.Untyped.Nat 𝕄

open import Tools.Bool using (T)
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

private variable
  n         : Nat
  A t u v   : Term _
  γ δ η θ χ : Conₘ _
  m         : Mode
  p q       : M

private opaque

  ▸ℕ : 𝟘ᶜ {n = n} ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘 ▸[ 𝟘ᵐ ] ℕ
  ▸ℕ = sub-≈ᶜ ℕₘ (≈ᶜ-refl ∙ ·-zeroʳ _)

opaque

  -- A usage rule for double′

  ▸double′₁ :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t →
    Greatest-lower-bound p (nrᵢ 𝟙 𝟙 𝟘) →
    Greatest-lower-boundᶜ δ (nrᵢᶜ 𝟙 γ 𝟘ᶜ) →
    p ·ᶜ γ +ᶜ δ ▸[ m ] double′ t
  ▸double′₁ ▸t p-GLB δ-GLB =
    natrec-no-nr-glbₘ ▸t
      (sub-≈ᶜ (sucₘ var) (≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-identityʳ _))
      ▸t ▸ℕ p-GLB δ-GLB

opaque

  -- A simplified usage rule for double′

  ▸double′₂ :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t →
    γ +ᶜ γ ▸[ m ] double′ t
  ▸double′₂ ▸t =
    sub-≈ᶜ (▸double′₁ ▸t nrᵢ-const-GLB₁ nrᵢᶜ-const-GLBᶜ₁)
      (+ᶜ-congʳ (≈ᶜ-sym (·ᶜ-identityˡ _)))

opaque

  -- A usage rule for plus′

  ▸plus′₁ :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t → δ ▸[ m ] u →
    Greatest-lower-bound p (nrᵢ 𝟙 𝟙 𝟘) →
    Greatest-lower-boundᶜ η (nrᵢᶜ 𝟙 γ 𝟘ᶜ) →
    p ·ᶜ δ +ᶜ η ▸[ m ] plus′ t u
  ▸plus′₁ ▸t ▸u p-glb η-glb =
    natrec-no-nr-glbₘ ▸t
      (sucₘ (sub-≈ᶜ var (≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-identityʳ _)))
      ▸u ▸ℕ p-glb η-glb

opaque

  -- A simplified usage rule for plus′

  ▸plus′₂ :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t → δ ▸[ m ] u →
    γ +ᶜ δ ▸[ m ] plus′ t u
  ▸plus′₂ ▸t ▸u =
    sub-≈ᶜ (▸plus′₁ ▸t ▸u nrᵢ-const-GLB₁ nrᵢᶜ-const-GLBᶜ₁)
      (≈ᶜ-trans (+ᶜ-comm _ _) (+ᶜ-congʳ (≈ᶜ-sym (·ᶜ-identityˡ _))))

opaque

  -- The term plus is well-resourced.

  ▸plus :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    ε ▸[ 𝟙ᵐ ] plus
  ▸plus =
    lamₘ $
    lamₘ $
    sub-≈ᶜ (▸plus′₂ var var)
      (ε ∙ trans (·-identityʳ _) (sym (+-identityˡ _))
         ∙ trans (·-identityʳ _) (sym (+-identityʳ _)))

opaque
  unfolding f′

  -- A usage rule for f′.

  ▸f′₁ :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t →
    δ ▸[ m ] u →
    Greatest-lower-bound p (nrᵢ 𝟘 𝟙 𝟙) →
    Greatest-lower-boundᶜ η (nrᵢᶜ 𝟘 γ γ) →
    p ·ᶜ δ +ᶜ η ▸[ m ] f′ t u
  ▸f′₁ {γ} {m} ▸t ▸u p-GLB η-GLB =
    natrec-no-nr-glbₘ ▸t
      (sub-≈ᶜ (▸plus′₂ (wkUsage (step (step id)) ▸t) var) $ begin
        γ       ∙ ⌜ m ⌝ · 𝟙 ∙ ⌜ m ⌝ · 𝟘 ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ∙ ·-zeroʳ _ ⟩
        γ       ∙ ⌜ m ⌝     ∙ 𝟘         ≈˘⟨ +ᶜ-identityʳ _ ∙ +-identityˡ _ ∙ +-identityʳ _ ⟩
        γ +ᶜ 𝟘ᶜ ∙ 𝟘 + ⌜ m ⌝ ∙ 𝟘 + 𝟘     ∎)
      ▸u ▸ℕ p-GLB η-GLB
    where
    open ≈ᶜ-reasoning

opaque
  unfolding f′

  -- A simplified usage rule for f′.

  ▸f′₂ :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t →
    δ ▸[ m ] u →
    γ +ᶜ δ ▸[ m ] f′ t u
  ▸f′₂ {γ} {m} ▸t ▸u =
    sub-≈ᶜ (▸f′₁ ▸t ▸u nrᵢ-const-GLB₂ nrᵢᶜ-const-GLBᶜ₂)
      (≈ᶜ-trans (+ᶜ-comm _ _) (≈ᶜ-sym (+ᶜ-congʳ (·ᶜ-identityˡ _))))

opaque
  unfolding f

  -- The term f is well-resourced.

  ▸f : ⦃ ok : Nr-not-available-GLB ⦄ → ε ▸[ 𝟙ᵐ ] f
  ▸f = lamₘ $ lamₘ $ sub-≈ᶜ (▸f′₂ var var) $ begin
    ε ∙ ⌜ 𝟙ᵐ ⌝ · 𝟙 ∙ ⌜ 𝟙ᵐ ⌝ · 𝟙 ≈⟨ ε ∙ ·-identityʳ _ ∙ ·-identityʳ _ ⟩
    ε ∙ ⌜ 𝟙ᵐ ⌝     ∙ ⌜ 𝟙ᵐ ⌝     ≈˘⟨ ε ∙ +-identityʳ _ ∙ +-identityˡ _ ⟩
    ε ∙ ⌜ 𝟙ᵐ ⌝ + 𝟘 ∙ 𝟘 + ⌜ 𝟙ᵐ ⌝ ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- A usage rule for pred′

  ▸pred′₁ :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t →
    Greatest-lower-bound p (nrᵢ 𝟘 𝟙 𝟙) →
    Greatest-lower-boundᶜ δ (nrᵢᶜ 𝟘 𝟘ᶜ 𝟘ᶜ) →
    p ·ᶜ γ +ᶜ δ ▸[ m ] pred′ t
  ▸pred′₁ ▸t p-GLB δ-GLB =
    natrec-no-nr-glbₘ zeroₘ (sub-≈ᶜ var (≈ᶜ-refl ∙ ·-identityʳ _ ∙ ·-zeroʳ _))
      ▸t ▸ℕ p-GLB δ-GLB

opaque

  -- A simplified usage rule for pred′

  ▸pred′₂ :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t →
    γ ▸[ m ] pred′ t
  ▸pred′₂ {γ} ▸t =
    sub-≈ᶜ (▸pred′₁ ▸t nrᵢ-const-GLB₂ GLBᶜ-nrᵢᶜ-𝟘ᶜ) $ begin
      γ            ≈˘⟨ +ᶜ-identityʳ _ ⟩
      γ +ᶜ 𝟘ᶜ      ≈˘⟨ +ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
      𝟙 ·ᶜ γ +ᶜ 𝟘ᶜ ∎
      where
      open ≈ᶜ-reasoning

opaque

  -- The term pred is well-resourced.

  ▸pred :
    ⦃ ok : Nr-not-available-GLB ⦄ →
    ε ▸[ 𝟙ᵐ ] pred
  ▸pred = lamₘ $ ▸pred′₂ (sub-≈ᶜ var (ε ∙ ·-identityʳ _))

opaque
  unfolding natcase

  -- A usage lemma for natcase.

  ▸natcase′ :
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A →
    (⦃ has-nr : Nr-available ⦄ →
     χ ≤ᶜ nrᶜ p 𝟘 γ δ η) →
    (⦃ no-nr : Nr-not-available ⦄ →
     χ ≤ᶜ γ ×
     (¬ Trivialᵐ →
      χ ≤ᶜ δ) ×
     ((Trivialᵐ → Has-well-behaved-zero _ semiring-with-meet) →
      χ ≤ᶜ η) ×
     χ ≤ᶜ δ +ᶜ p ·ᶜ η) →
    (⦃ no-nr : Nr-not-available-GLB ⦄ →
      χ ≤ᶜ (𝟙 ∧ p) ·ᶜ η +ᶜ (γ ∧ᶜ δ)) →
    χ ▸[ m ] natcase p q A t u v
  ▸natcase′ {m} {δ} {p} {η} {χ} ▸t ▸u ▸v ▸A hyp₁ hyp₂ hyp₃ =
    natrec-nr-or-no-nrₘ ▸t
      (sub (wkUsage _ ▸u) $ begin
         δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         δ ∙ ⌜ m ⌝ · p ∙ 𝟘          ∎)
      ▸v ▸A hyp₁
      (let le₁ , le₂ , le₃ , le₄ = hyp₂ in
      le₁ , le₂ , le₃ ,
      (begin
         χ                      ≤⟨ le₄ ⟩
         δ +ᶜ p ·ᶜ η            ≈˘⟨ +ᶜ-congˡ $
                                    ≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-zeroˡ _)) $
                                    +ᶜ-identityʳ _ ⟩
         δ +ᶜ p ·ᶜ η +ᶜ 𝟘 ·ᶜ χ  ∎))
      (_ , _ ,
       Greatest-lower-bound-nrᵢ-𝟘 ,
       Greatest-lower-boundᶜ-nrᵢᶜ-𝟘 ,
       hyp₃)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding natcase

  -- A usage lemma for natcase.

  ▸natcase :
    ⦃ has-nr : Nr-available ⦄ →
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A →
    nrᶜ p 𝟘 γ δ η ▸[ m ] natcase p q A t u v
  ▸natcase {m} {δ} {p} ▸t ▸u ▸v ▸A =
    natrecₘ ▸t
      (sub (wkUsage (step id) ▸u) $ begin
         δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         δ ∙ ⌜ m ⌝ · p ∙ 𝟘          ∎)
      ▸v ▸A
    where
    open ≤ᶜ-reasoning

opaque
  unfolding natcase

  -- A usage lemma for natcase.

  ▸natcase-glb :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A →
    (𝟙 ∧ p) ·ᶜ η +ᶜ γ ∧ᶜ δ ▸[ m ] natcase p q A t u v
  ▸natcase-glb ▸t ▸u ▸v ▸A =
    let ▸u′ = sub-≈ᶜ (wkUsage (step id) ▸u) (≈ᶜ-refl ∙ ·-zeroʳ _)
    in  natrec-no-nr-glbₘ ▸t ▸u′ ▸v ▸A nrᵢ-𝟘-GLB nrᵢᶜ-𝟘-GLB

opaque
  unfolding strict-const

  -- A usage lemma for strict-const.

  ▸strict-const :
    ⦃ has-nr : Nr-available ⦄ →
    γ ▸[ 𝟘ᵐ ] A →
    δ ▸[ m ] t →
    η ▸[ m ] u →
    nrᶜ 𝟘 𝟙 δ 𝟘ᶜ η ▸[ m ] strict-const A t u
  ▸strict-const {γ} {m} ▸A ▸t ▸u =
    natrecₘ ▸t
      (sub var $ begin
         𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-identityʳ _ ⟩
         𝟘ᶜ ∙ ⌜ m ⌝                  ∎)
      ▸u
      (sub (wkUsage (step id) ▸A) $ begin
         γ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         γ ∙ 𝟘            ∎)
    where
    open ≤ᶜ-reasoning

opaque
  unfolding strict-const

  -- A usage lemma for strict-const.

  ▸strict-const-glb :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ 𝟘ᵐ ] A →
    δ ▸[ m ] t →
    η ▸[ m ] u →
    η +ᶜ δ ▸[ m ] strict-const A t u
  ▸strict-const-glb ▸A ▸t ▸u =
    let ▸x0 = sub-≈ᶜ var (≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-identityʳ _)
        ▸A₁ = sub-≈ᶜ (wkUsage (step id) ▸A) (≈ᶜ-refl ∙ ·-zeroʳ _)
    in  sub-≈ᶜ (natrec-no-nr-glbₘ ▸t ▸x0 ▸u ▸A₁ nrᵢ-const-GLB₁ nrᵢᶜ-const-GLBᶜ₁)
          (≈ᶜ-sym (+ᶜ-congʳ (·ᶜ-identityˡ _)))
