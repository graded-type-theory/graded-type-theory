{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.Meet {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties.Equivalence 𝕄
open import Definition.Modality.Context.Properties.PartialOrder 𝕄
open import Definition.Modality.Properties 𝕄

open import Tools.Nat

open Modality 𝕄

private
  variable
    n : Nat
    γ γ′ δ δ′ η : Conₘ n

-- Meet is idempotent
-- γ ∧ᶜ γ ≈ᶜ γ

∧ᶜ-idem : (γ : Conₘ n) → γ ∧ᶜ γ ≈ᶜ γ
∧ᶜ-idem ε = ≈ᶜ-refl
∧ᶜ-idem (γ ∙ p) = (∧ᶜ-idem γ) ∙ (∧-idem p)

-- Meet is commutative
-- γ ∧ᶜ δ ≈ᶜ δ ∧ᶜ γ

∧ᶜ-comm : (γ δ : Conₘ n) → γ ∧ᶜ δ ≈ᶜ δ ∧ᶜ γ
∧ᶜ-comm ε ε = ≈ᶜ-refl
∧ᶜ-comm  (γ ∙ p) (δ ∙ q) = (∧ᶜ-comm γ δ) ∙ (∧-comm p q)

-- Meet is associative
-- (γ ∧ᶜ δ) ∧ᶜ η ≈ᶜ γ ∧ᶜ (δ ∧ᶜ η)

∧ᶜ-assoc : (γ δ η : Conₘ n) → (γ ∧ᶜ δ) ∧ᶜ η ≈ᶜ γ ∧ᶜ (δ ∧ᶜ η)
∧ᶜ-assoc ε ε ε = ≈ᶜ-refl
∧ᶜ-assoc (γ ∙ p) (δ ∙ q) (η ∙ r) = (∧ᶜ-assoc γ δ η) ∙ (∧-assoc p q r)

-- Congruence of ∧ᶜ
-- If γ ≈ᶜ γ′ and δ ≈ᶜ δ′ then γ ∧ᶜ δ ≈ᶜ γ′ ∧ᶜ δ′

∧ᶜ-cong : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → γ ∧ᶜ δ ≈ᶜ γ′ ∧ᶜ δ′
∧ᶜ-cong ε ε = ≈ᶜ-refl
∧ᶜ-cong (γ≈γ′ ∙ p≈p′) (δ≈δ′ ∙ q≈q′) =
  (∧ᶜ-cong γ≈γ′ δ≈δ′) ∙ (∧-cong p≈p′ q≈q′)

-- Congruence of ∧ᶜ on the left
-- If δ ≈ᶜ δ′ then γ ∧ᶜ δ ≈ᶜ γ ∧ᶜ δ′

∧ᶜ-congˡ : δ ≈ᶜ δ′ → γ ∧ᶜ δ ≈ᶜ γ ∧ᶜ δ′
∧ᶜ-congˡ δ≈δ′ = ∧ᶜ-cong ≈ᶜ-refl δ≈δ′

-- Congruence of ∧ᶜ on the right
-- If γ ≈ᶜ γ′ then γ ∧ᶜ δ ≈ᶜ γ′ ∧ᶜ δ

∧ᶜ-congʳ : γ ≈ᶜ γ′ → γ ∧ᶜ δ ≈ᶜ γ′ ∧ᶜ δ
∧ᶜ-congʳ γ≈γ′ = ∧ᶜ-cong γ≈γ′ ≈ᶜ-refl

-- Meet on the left is monotone
-- If γ ≤ᶜ δ then γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η

∧ᶜ-monotoneˡ : γ ≤ᶜ δ → γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η
∧ᶜ-monotoneˡ {γ = ε} {ε} {ε} ε = ≤ᶜ-refl
∧ᶜ-monotoneˡ {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) =
  (∧ᶜ-monotoneˡ γ≤δ) ∙ (∧-monotoneˡ p≤q)

-- Meet on the right is monotone
-- If γ ≤ᶜ δ then γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η

∧ᶜ-monotoneʳ : γ ≤ᶜ δ → η ∧ᶜ γ ≤ᶜ η ∧ᶜ δ
∧ᶜ-monotoneʳ {γ = ε} {ε} {ε} ̋ε = ≤ᶜ-refl
∧ᶜ-monotoneʳ {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) =
  (∧ᶜ-monotoneʳ γ≤δ) ∙ (∧-monotoneʳ p≤q)

-- Meet is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ ∧ᶜ δ ≤ᶜ γ′ ∧ᶜ δ′

∧ᶜ-monotone : γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → (γ ∧ᶜ δ) ≤ᶜ (γ′ ∧ᶜ δ′)
∧ᶜ-monotone γ≤γ′ δ≤δ′ = ≤ᶜ-trans (∧ᶜ-monotoneˡ γ≤γ′) (∧ᶜ-monotoneʳ δ≤δ′)

-- Meet on the left is a decreasing function
-- γ ∧ᶜ δ ≤ᶜ γ

∧ᶜ-decreasingˡ : (γ δ : Conₘ n) → γ ∧ᶜ δ ≤ᶜ γ
∧ᶜ-decreasingˡ ε ε = ≤ᶜ-refl
∧ᶜ-decreasingˡ (γ ∙ p) (δ ∙ q) = (∧ᶜ-decreasingˡ γ δ) ∙ (∧-decreasingˡ p q)

-- Meet on the right is a decreasing function
-- γ ∧ᶜ δ ≤ᶜ δ

∧ᶜ-decreasingʳ : (γ δ : Conₘ n) → γ ∧ᶜ δ ≤ᶜ δ
∧ᶜ-decreasingʳ ε ε = ≤ᶜ-refl
∧ᶜ-decreasingʳ (γ ∙ p) (δ ∙ q) = (∧ᶜ-decreasingʳ γ δ) ∙ (∧-decreasingʳ p q)
