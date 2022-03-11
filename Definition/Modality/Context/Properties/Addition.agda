{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.Addition {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties.Equivalence 𝕄
open import Definition.Modality.Context.Properties.PartialOrder 𝕄
open import Definition.Modality.Properties 𝕄

open import Tools.Nat hiding (_+_)
open import Tools.Product

open Modality 𝕄

private
  variable
    n : Nat
    γ γ′ δ δ′ η : Conₘ n

-- 𝟘ᶜ is left unit for addition
-- 𝟘ᶜ +ᶜ γ ≈ᶜ γ

+ᶜ-identityˡ : (γ : Conₘ n) → 𝟘ᶜ +ᶜ γ ≈ᶜ γ
+ᶜ-identityˡ  ε      = ≈ᶜ-refl
+ᶜ-identityˡ (γ ∙ p) = (+ᶜ-identityˡ γ) ∙ (proj₁ +-identity p)

-- 𝟘ᶜ is right unit for addition
-- γ +ᶜ 𝟘ᶜ ≈ᶜ γ

+ᶜ-identityʳ : (γ : Conₘ n) → γ +ᶜ 𝟘ᶜ ≈ᶜ γ
+ᶜ-identityʳ ε       = ≈ᶜ-refl
+ᶜ-identityʳ (γ ∙ p) = (+ᶜ-identityʳ γ) ∙ (proj₂ +-identity p)

-- Addition is associative
-- (γ +ᶜ δ) +ᶜ η ≈ᶜ γ +ᶜ (δ +ᶜ η)

+ᶜ-assoc : (γ δ η : Conₘ n) → (γ +ᶜ δ) +ᶜ η ≈ᶜ γ +ᶜ (δ +ᶜ η)
+ᶜ-assoc ε ε ε = ε
+ᶜ-assoc (γ ∙ p) (δ ∙ q) (η ∙ r) = (+ᶜ-assoc γ δ η) ∙ (+-assoc p q r)

-- Addition is commutative
-- γ +ᶜ δ ≈ᶜ δ +ᶜ γ

+ᶜ-comm : (γ δ : Conₘ n) → γ +ᶜ δ ≈ᶜ δ +ᶜ γ
+ᶜ-comm ε ε = ≈ᶜ-refl
+ᶜ-comm (γ ∙ p) (δ ∙ q) = (+ᶜ-comm γ δ) ∙ (+-comm p q)

-- The module of modality contexts is positive
-- If 𝟘ᶜ ≤ᶜ γ +ᶜ δ then 𝟘ᶜ ≤ᶜ γ and 𝟘ᶜ ≤ δ

+ᶜ-positive : (γ δ : Conₘ n) → 𝟘ᶜ ≤ᶜ γ +ᶜ δ → 𝟘ᶜ ≤ᶜ γ × 𝟘ᶜ ≤ᶜ δ
+ᶜ-positive ε ε ε = ≈ᶜ-refl , ≈ᶜ-refl
+ᶜ-positive  (γ ∙ p) (δ ∙ q) (0≤γ+δ ∙ 0≤p+q) =
  (proj₁ (+ᶜ-positive γ δ 0≤γ+δ) ∙ proj₁ (+-positive p q 0≤p+q)) ,
  (proj₂ (+ᶜ-positive γ δ 0≤γ+δ) ∙ proj₂ (+-positive p q 0≤p+q))

-- Addition is left distributive over meet
-- γ +ᶜ (δ ∧ᶜ η) ≈ᶜ (γ +ᶜ δ) ∧ᶜ (γ +ᶜ η)

+ᶜ-distribˡ-∧ᶜ : (γ δ η : Conₘ n) → γ +ᶜ (δ ∧ᶜ η) ≈ᶜ (γ +ᶜ δ) ∧ᶜ (γ +ᶜ η)
+ᶜ-distribˡ-∧ᶜ ε        ε       ε      = ≈ᶜ-refl
+ᶜ-distribˡ-∧ᶜ (γ ∙ p) (δ ∙ q) (η ∙ r) = (+ᶜ-distribˡ-∧ᶜ γ δ η) ∙ (proj₁ +-distrib-∧ p q r)

-- Addition is right distributive over meet
-- (δ ∧ᶜ η) +ᶜ γ ≈ᶜ (̋δ +ᶜ γ) ∧ᶜ (η +ᶜ γ)

+ᶜ-distribʳ-∧ᶜ : (γ δ η : Conₘ n) → (δ ∧ᶜ η) +ᶜ γ ≈ᶜ (δ +ᶜ γ) ∧ᶜ (η +ᶜ γ)
+ᶜ-distribʳ-∧ᶜ ε ε ε = ≈ᶜ-refl
+ᶜ-distribʳ-∧ᶜ (γ ∙ p) (δ ∙ q) (η ∙ r) = (+ᶜ-distribʳ-∧ᶜ γ δ η) ∙ (proj₂ +-distrib-∧ p q r)

-- Congruence of +ᶜ
-- If γ ≈ᶜ γ′ and δ ≈ᶜ δ′ then γ +ᶜ δ ≈ᶜ γ′ +ᶜ δ′

+ᶜ-cong : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → γ +ᶜ δ ≈ᶜ γ′ +ᶜ δ′
+ᶜ-cong ε ε = ≈ᶜ-refl
+ᶜ-cong (γ≈γ′ ∙ p≈p′) (δ≈δ′ ∙ q≈q′) =
  (+ᶜ-cong γ≈γ′ δ≈δ′) ∙ (+-cong p≈p′ q≈q′)


-- Addition on the left is monotone
-- If γ ≤ᶜ δ then γ +ᶜ η ≤ᶜ δ +ᶜ η

+ᶜ-monotoneˡ : γ ≤ᶜ δ → γ +ᶜ η ≤ᶜ δ +ᶜ η
+ᶜ-monotoneˡ {γ = ε} {ε} {ε} ε = ≤ᶜ-refl
+ᶜ-monotoneˡ {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) = (+ᶜ-monotoneˡ γ≤δ) ∙ (+-monotoneˡ p≤q)

-- Addition on the right is monotone
-- If γ ≤ᶜ δ then η +ᶜ γ ≤ᶜ η +ᶜ δ

+ᶜ-monotoneʳ : γ ≤ᶜ δ → η +ᶜ γ ≤ᶜ η +ᶜ δ
+ᶜ-monotoneʳ {γ = ε} {ε} {ε} ε = ≤ᶜ-refl
+ᶜ-monotoneʳ {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) = (+ᶜ-monotoneʳ γ≤δ) ∙ (+-monotoneʳ p≤q)

-- Addition is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ + δ ≤ᶜ γ′ +ᶜ δ′

+ᶜ-monotone : γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → γ +ᶜ δ ≤ᶜ γ′ +ᶜ δ′
+ᶜ-monotone γ≤γ′ δ≤δ′ = ≤ᶜ-trans (+ᶜ-monotoneˡ γ≤γ′) (+ᶜ-monotoneʳ δ≤δ′)
