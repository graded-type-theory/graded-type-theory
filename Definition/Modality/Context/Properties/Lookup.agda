{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.Lookup {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open import Definition.Modality.Context 𝕄

open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.PropositionalEquality as PE

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

private
  variable
    n : Nat
    p r : M
    γ δ : Conₘ n

-- Every lookup in a zero-context is zero
-- 𝟘ᶜ ⟨ x ⟩ ≡ 𝟘

𝟘ᶜ-lookup : (x : Fin n) → 𝟘ᶜ ⟨ x ⟩ ≡ 𝟘
𝟘ᶜ-lookup x0     = PE.refl
𝟘ᶜ-lookup (x +1) = 𝟘ᶜ-lookup x

-- Context lookup is a monotone function
-- If γ ≤ᶜ δ then γ⟨x⟩ ≤ δ⟨x⟩

lookup-monotone : (x : Fin n) → γ ≤ᶜ δ → (γ ⟨ x ⟩) ≤ (δ ⟨ x ⟩)
lookup-monotone {γ = γ ∙ p} {δ ∙ q} x0     (γ≤δ ∙ p≤q) = p≤q
lookup-monotone {γ = γ ∙ p} {δ ∙ q} (x +1) (γ≤δ ∙ p≤q) = lookup-monotone x γ≤δ

-- Context lookup distributes over addition
-- (γ +ᶜ δ)⟨x⟩ ≡ γ⟨x⟩ + δ⟨x⟩

lookup-distrib-+ᶜ : (γ δ : Conₘ n) (x : Fin n) → (γ +ᶜ δ) ⟨ x ⟩ ≡ γ ⟨ x ⟩ + δ ⟨ x ⟩
lookup-distrib-+ᶜ (γ ∙ p) (δ ∙ q) x0     = PE.refl
lookup-distrib-+ᶜ (γ ∙ p) (δ ∙ q) (x +1) = lookup-distrib-+ᶜ γ δ x

-- Context lookup distributes over multiplication
-- (p ·ᶜ γ)⟨x⟩ ≡ p · γ⟨x⟩

lookup-distrib-·ᶜ : (γ : Conₘ n) (p : M) (x : Fin n) → (p ·ᶜ γ) ⟨ x ⟩ ≡ p · γ ⟨ x ⟩
lookup-distrib-·ᶜ (γ ∙ q) p x0     = PE.refl
lookup-distrib-·ᶜ (γ ∙ q) p (x +1) = lookup-distrib-·ᶜ γ p x

-- Context lookup distributes over meet
-- (γ ∧ᶜ δ)⟨x⟩ ≡ γ⟨x⟩ ∧ δ⟨x⟩

lookup-distrib-∧ᶜ : (γ δ : Conₘ n) (x : Fin n)
                  → (γ ∧ᶜ δ) ⟨ x ⟩ ≡ (γ ⟨ x ⟩) ∧ (δ ⟨ x ⟩)
lookup-distrib-∧ᶜ (γ ∙ p) (δ ∙ q) x0     = PE.refl
lookup-distrib-∧ᶜ (γ ∙ p) (δ ∙ q) (x +1) = lookup-distrib-∧ᶜ γ δ x

-- Context lookup distributes over ⊛ᶜ
-- (γ ⊛ᶜ δ ▷ r)⟨x⟩ ≡ γ⟨x⟩ ⊛ δ⟨x⟩ ▷ r

lookup-distrib-⊛ᶜ : (γ δ : Conₘ n) (r : M) (x : Fin n)
                   → (γ ⊛ᶜ δ ▷ r) ⟨ x ⟩ ≡ (γ ⟨ x ⟩) ⊛ (δ ⟨ x ⟩) ▷ r
lookup-distrib-⊛ᶜ (γ ∙ p) (δ ∙ q) r x0     = PE.refl
lookup-distrib-⊛ᶜ (γ ∙ p) (δ ∙ q) r (x +1) = lookup-distrib-⊛ᶜ γ δ r x

-- Lookup is consistent with context updates
-- (γ , x ≔ p) ⟨ x ⟩ ≡ p

update-lookup : (x : Fin n) → (γ , x ≔ p) ⟨ x ⟩ ≡ p
update-lookup {γ = γ ∙ p} x0     = PE.refl
update-lookup {γ = γ ∙ p} (x +1) = update-lookup {γ = γ} x
