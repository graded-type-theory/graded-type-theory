{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.Recurrence {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties.Equivalence 𝕄
open import Definition.Modality.Context.Properties.PartialOrder 𝕄
open import Definition.Modality.Properties 𝕄

open import Tools.Nat

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

private
  variable
    n : Nat
    r r′ : M
    γ γ′ δ δ′ : Conₘ n

-- Reccurence relation for nrᶜ
-- nrᶜ γ δ r ≈ γ ∧ᶜ (δ +ᶜ r ·ᶜ nrᶜ γ δ r)

nrᶜ-rec : (γ δ : Conₘ n) (r : M) → nrᶜ γ δ r ≈ᶜ γ ∧ᶜ (δ +ᶜ r ·ᶜ nrᶜ γ δ r)
nrᶜ-rec ε ε r             = ≈ᶜ-refl
nrᶜ-rec (γ ∙ p) (δ ∙ q) r = (nrᶜ-rec γ δ r) ∙ (nr-rec p q r)

-- nrᶜ is idempotent on 𝟘ᶜ on the first two arguments
-- nrᶜ 𝟘ᶜ 𝟘ᶜ r ≈ᶜ 𝟘ᶜ

nrᶜ-𝟘ᶜ : (r : M) → nrᶜ 𝟘ᶜ 𝟘ᶜ r ≈ᶜ 𝟘ᶜ {n = n}
nrᶜ-𝟘ᶜ {0}    r = ≈ᶜ-refl
nrᶜ-𝟘ᶜ {1+ n} r = (nrᶜ-𝟘ᶜ r) ∙ (nr-idem-𝟘 r)

-- Context scaling right distributes over the two first arguments of nrᶜ
-- nrᶜ (p ·ᶜ γ) (q ·ᶜ γ) r ≈ᶜ nr p q r ·ᶜ γ

·ᶜ-distribʳ-nrᶜ : (p q r : M) (γ : Conₘ n) → nrᶜ (p ·ᶜ γ) (q ·ᶜ γ) r ≈ᶜ nr p q r ·ᶜ γ
·ᶜ-distribʳ-nrᶜ p q r ε        = ≈ᶜ-refl
·ᶜ-distribʳ-nrᶜ p q r (γ ∙ p′) = (·ᶜ-distribʳ-nrᶜ p q r γ) ∙ (·-distribʳ-nr p′ p q r)

-- Addition sub-distributes over the two first arguents of nrᶜ
-- nrᶜ (γ +ᶜ γ′) (δ +ᶜ δ′) r ≤ᶜ nrᶜ γ δ r +ᶜ nrᶜ γ′ δ′ r

+ᶜ-super-distrib-nrᶜ : (γ γ′ δ δ′ : Conₘ n) (r : M)
               → nrᶜ γ δ r +ᶜ nrᶜ γ′ δ′ r ≤ᶜ nrᶜ (γ +ᶜ γ′) (δ +ᶜ δ′) r
+ᶜ-super-distrib-nrᶜ ε ε ε ε r = ≤ᶜ-refl
+ᶜ-super-distrib-nrᶜ (γ ∙ p) (γ′ ∙ p′) (δ ∙ q) (δ′ ∙ q′) r =
  (+ᶜ-super-distrib-nrᶜ γ γ′ δ δ′ r) ∙ (+-super-distrib-nr p p′ q q′ r)

-- Congruence of nrᶜ
nrᶜ-cong : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → r ≈ r′ → nrᶜ γ δ r ≈ᶜ nrᶜ γ′ δ′ r′
nrᶜ-cong ε ε r≈r′ = ≈ᶜ-refl
nrᶜ-cong (γ≈γ′ ∙ p≈p′) (δ≈δ′ ∙ q≈q′) r≈r′ =
  (nrᶜ-cong γ≈γ′ δ≈δ′ r≈r′) ∙ (nr-cong p≈p′ q≈q′ r≈r′)

-- nrᶜ is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ and r ≤ r′ then nrᶜ γ δ r ≤ᶜ nrᶜ γ′ δ′ r′

nrᶜ-monotone : γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → r ≤ r′ → nrᶜ γ δ r ≤ᶜ nrᶜ γ′ δ′ r′
nrᶜ-monotone {γ = ε} {ε} {ε} {ε} γ≤γ′ δ≤δ′ r≤r′ = ≤ᶜ-refl
nrᶜ-monotone {γ = γ ∙ p} {γ′ ∙ p′} {δ ∙ q} {δ′ ∙ q′} (γ≤γ′ ∙ p≤p′) (δ≤δ′ ∙ q≤q′) r≤r′ =
  (nrᶜ-monotone γ≤γ′ δ≤δ′ r≤r′) ∙ (nr-monotone p≤p′ q≤q′ r≤r′)
