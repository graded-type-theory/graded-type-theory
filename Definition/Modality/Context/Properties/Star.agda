{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.Star {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties.Equivalence 𝕄
open import Definition.Modality.Context.Properties.PartialOrder 𝕄
open import Definition.Modality.Properties 𝕄

open import Tools.Nat
open import Tools.Product

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

private
  variable
    n : Nat
    r r′ : M
    γ γ′ δ δ′ : Conₘ n

-- ⊛ᶜ is a solution to the inequality x ≤ᶜ q +ᶜ r ·ᶜ x
-- γ ⊛ᶜ δ ▷ r ≤ᶜ δ +ᶜ r ·ᶜ γ ⊛ᶜ δ ▷ r
⊛ᶜ-ineq₁ : (γ δ : Conₘ n) (r : M) → γ ⊛ᶜ δ ▷ r ≤ᶜ δ +ᶜ r ·ᶜ γ ⊛ᶜ δ ▷ r
⊛ᶜ-ineq₁ ε ε r = ε
⊛ᶜ-ineq₁ (γ ∙ p) (δ ∙ q) r = ⊛ᶜ-ineq₁ γ δ r ∙ ⊛-ineq₁ p q r

-- ⊛ᶜ is a solution to the inequality x ≤ᶜ γ
-- γ ⊛ᶜ δ ▷ r ≤ᶜ γ
⊛ᶜ-ineq₂ : (γ δ : Conₘ n) (r : M) → γ ⊛ᶜ δ ▷ r ≤ᶜ γ
⊛ᶜ-ineq₂ ε ε r = ε
⊛ᶜ-ineq₂ (γ ∙ p) (δ ∙ q) r = ⊛ᶜ-ineq₂ γ δ r ∙ ⊛-ineq₂ p q r

-- ⊛ᶜ solves the following system of inequalities
-- γ ⊛ᶜ δ ▷ r ≤ᶜ δ +ᶜ r ·ᶜ γ ⊛ᶜ δ ▷ r
-- γ ⊛ᶜ δ ▷ r ≤ᶜ γ

⊛ᶜ-ineq : ((γ δ : Conₘ n) (r : M) → γ ⊛ᶜ δ ▷ r ≤ᶜ δ +ᶜ r ·ᶜ γ ⊛ᶜ δ ▷ r)
        × ((γ δ : Conₘ n) (r : M) → γ ⊛ᶜ δ ▷ r ≤ᶜ γ)
⊛ᶜ-ineq = ⊛ᶜ-ineq₁ , ⊛ᶜ-ineq₂

-- ⊛ᶜ is idempotent on 𝟘ᶜ on the first two arguments
-- 𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r ≈ᶜ 𝟘ᶜ

⊛ᶜ-idem-𝟘ᶜ : (r : M) → 𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r ≈ᶜ 𝟘ᶜ {n = n}
⊛ᶜ-idem-𝟘ᶜ {0} r = ≈ᶜ-refl
⊛ᶜ-idem-𝟘ᶜ {1+ n} r = (⊛ᶜ-idem-𝟘ᶜ r) ∙ (⊛-idem-𝟘 r)

-- Context scaling right sub-distributes over ⊛ w.r.t the first two arguments
-- (p ⊛ q ▷ r) ·ᶜ γ ≤ᶜ (p ·ᶜ γ) ⊛ᶜ (q ·ᶜ γ) ▷ r

·ᶜ-sub-distribʳ-⊛ : (p q r : M) (γ : Conₘ n) → p ⊛ q ▷ r ·ᶜ γ ≤ᶜ (p ·ᶜ γ) ⊛ᶜ q ·ᶜ γ ▷ r
·ᶜ-sub-distribʳ-⊛ p q r ε = ≤ᶜ-refl
·ᶜ-sub-distribʳ-⊛ p q r (γ ∙ p′) = (·ᶜ-sub-distribʳ-⊛ p q r γ) ∙ ·-sub-distribʳ-⊛ r p′ p q

-- Addition is sub-interchangable over ⊛ᶜ w.r.t the first two arguments
-- (γ ⊛ᵣ δ) + (γ′ ⊛ᵣ δ′) ≤ (γ + γ′) ⊛ᵣ (δ + δ′)

+ᶜ-sub-interchangable-⊛ᶜ : (r : M) → (γ δ γ′ δ′ : Conₘ n)
                         → (γ ⊛ᶜ δ ▷ r) +ᶜ (γ′ ⊛ᶜ δ′ ▷ r) ≤ᶜ (γ +ᶜ γ′) ⊛ᶜ (δ +ᶜ δ′) ▷ r
+ᶜ-sub-interchangable-⊛ᶜ r ε ε ε ε = ε
+ᶜ-sub-interchangable-⊛ᶜ  r (γ ∙ p) (δ ∙ q) (γ′ ∙ p′) (δ′ ∙ q′) =
  +ᶜ-sub-interchangable-⊛ᶜ r γ δ γ′ δ′ ∙ +-sub-interchangable-⊛ r p q p′ q′

-- Congruence of ⊛ᶜ
⊛ᶜ-cong : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → r ≈ r′ → γ ⊛ᶜ δ ▷ r ≈ᶜ γ′ ⊛ᶜ δ′ ▷ r′
⊛ᶜ-cong ε ε r≈r′ = ε
⊛ᶜ-cong (γ≈γ′ ∙ p≈p′) (δ≈δ′ ∙ q≈q′) r≈r′ =
  (⊛ᶜ-cong γ≈γ′ δ≈δ′ r≈r′) ∙ (⊛-cong p≈p′ q≈q′ r≈r′)

-- ⊛ᶜ is monotone on its first two arguments
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ ⊛ᶜ δ ▷ r ≤ᶜ γ′ ⊛ᶜ δ′ ▷ r

⊛ᶜ-monotone : γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → γ ⊛ᶜ δ ▷ r ≤ᶜ γ′ ⊛ᶜ δ′ ▷ r
⊛ᶜ-monotone {γ = ε} {ε} {ε} {ε} γ≤γ′ δ≤δ′ = ε
⊛ᶜ-monotone {γ = γ ∙ p} {γ′ ∙ p′} {δ ∙ q} {δ′ ∙ q′} (γ≤γ′ ∙ p≤p′) (δ≤δ′ ∙ q≤q′) =
  ⊛ᶜ-monotone γ≤γ′ δ≤δ′ ∙ ⊛-monotone p≤p′ q≤q′
