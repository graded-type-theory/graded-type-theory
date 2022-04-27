{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Context 𝕄

open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.PropositionalEquality as PE

open import Definition.Modality.Context.Properties.Addition 𝕄 public
open import Definition.Modality.Context.Properties.Equivalence 𝕄 public
open import Definition.Modality.Context.Properties.Insertion 𝕄 public
open import Definition.Modality.Context.Properties.Lookup 𝕄 public
open import Definition.Modality.Context.Properties.Meet 𝕄 public
open import Definition.Modality.Context.Properties.Multiplication 𝕄 public
open import Definition.Modality.Context.Properties.PartialOrder 𝕄 public
open import Definition.Modality.Context.Properties.Recurrence 𝕄 public
open import Definition.Modality.Context.Properties.Update 𝕄 public

private
  variable
    n : Nat
    p q r r′ : M
    γ γ′ δ δ′ η : Conₘ n

-- Context extension is monotone w.r.t the tail
-- If γ ≤ᶜ δ then γ ∙ p ≤ᶜ δ ∙ p

∙-monotoneˡ : {γ δ : Conₘ n} {p : M} → γ ≤ᶜ δ → γ ∙ p ≤ᶜ δ ∙ p
∙-monotoneˡ γ≤δ = γ≤δ ∙ ≤-refl

-- Context extension is monotone w.r.t the head
-- If p ≤ q then γ ∙ p ≤ᶜ γ ∙ q

∙-monotoneʳ : {γ : Conₘ n} {p q : M} → p ≤ q → γ ∙ p ≤ᶜ γ ∙ q
∙-monotoneʳ p≤q = ≤ᶜ-refl ∙ p≤q

-- Context extension is monotone
-- If γ ≤ᶜ δ and p ≤ q then γ ∙ p ≤ᶜ δ ∙ q

∙-monotone : {γ δ : Conₘ n} {p q : M} → γ ≤ᶜ δ → p ≤ q → γ ∙ p ≤ᶜ δ ∙ q
∙-monotone γ≤δ p≤q = ≤ᶜ-trans (∙-monotoneˡ γ≤δ) (∙-monotoneʳ p≤q)

----------------------------------
-- Propeties of headₘ and tailₘ --
----------------------------------

-- tailₘ distributes over meet
-- tailₘ (γ ∧ᶜ δ) ≡ tailₘ γ ∧ᶜ tailₘ δ

tailₘ-distrib-∧ᶜ : (γ δ : Conₘ (1+ n)) → tailₘ (γ ∧ᶜ δ) ≡ (tailₘ γ) ∧ᶜ (tailₘ δ)
tailₘ-distrib-∧ᶜ (ε ∙ p) (ε ∙ q) = PE.refl
tailₘ-distrib-∧ᶜ (γ ∙ p′ ∙ p) (δ ∙ q′ ∙ q) = cong₂ _∙_ (tailₘ-distrib-∧ᶜ (γ ∙ p) (δ ∙ q)) PE.refl

-- headₘ distributes over meet
-- headₘ (γ ∧ᶜ δ) ≡ headₘ γ ∧ headₘ δ

head-distrib-∧ : (γ δ : Conₘ (1+ n)) → headₘ (γ ∧ᶜ δ) ≡ (headₘ γ) ∧ (headₘ δ)
head-distrib-∧ (γ ∙ p) (δ ∙ q) = PE.refl

-- The headₘ and tailₘ functions correctly give the head and tail of the context
-- tailₘ γ ∙ headₘ γ ≡ γ

headₘ-tailₘ-correct : (γ : Conₘ (1+ n)) → tailₘ γ ∙ headₘ γ ≡ γ
headₘ-tailₘ-correct (γ ∙ p) = PE.refl

-- Congruence of tailₘ
-- If γ ≈ᶜ δ then tailₘ γ ≈ᶜ tailₘ δ

tailₘ-cong : {γ δ : Conₘ (1+ n)} → γ ≈ᶜ δ → tailₘ γ ≈ᶜ tailₘ δ
tailₘ-cong (γ≈δ ∙ p≈q) = γ≈δ

-- Congruence of headₘ
-- If γ ≈ᶜ δ then headₘ γ ≈ᶜ headₘ δ

headₘ-cong : {γ δ : Conₘ (1+ n)} → γ ≈ᶜ δ → headₘ γ ≈ headₘ δ
headₘ-cong (γ≈δ ∙ p≈q) = p≈q

-- tailₘ is monotone
-- If γ ≤ᶜ δ then tailₘ γ ≤ᶜ tailₘ δ

tailₘ-monotone : {γ δ : Conₘ (1+ n)} → γ ≤ᶜ δ → tailₘ γ ≤ᶜ tailₘ δ
tailₘ-monotone {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) = γ≤δ

-- headₘ is monotone
-- If γ ≤ᶜ δ then headₘ γ ≤ᶜ headₘ δ

headₘ-monotone : {γ δ : Conₘ (1+ n)} → γ ≤ᶜ δ → headₘ γ ≤ headₘ δ
headₘ-monotone {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) = p≤q
