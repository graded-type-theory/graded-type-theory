open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.Multiplication {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties.Equivalence 𝕄
open import Definition.Modality.Context.Properties.PartialOrder 𝕄
open import Definition.Modality.Properties 𝕄

open import Tools.Nat hiding (_+_)
open import Tools.Product

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

private
  variable
    n : Nat
    p q : M
    γ δ : Conₘ n

-- 𝟙 is a left identity to modality contex scaling
-- 𝟙 ·ᶜ γ ≈ᶜ γ

·ᶜ-identityˡ : (γ : Conₘ n) → 𝟙 ·ᶜ γ ≈ᶜ γ
·ᶜ-identityˡ  ε      = ≈ᶜ-refl
·ᶜ-identityˡ (γ ∙ p) = (·ᶜ-identityˡ γ) ∙ (·-identityˡ p)

-- 𝟘 is a left zero to modality context scaling
-- 𝟘 ·ᶜ γ ≈ᶜ 𝟘ᶜ

·ᶜ-zeroˡ : (γ : Conₘ n) → 𝟘 ·ᶜ γ ≈ᶜ 𝟘ᶜ
·ᶜ-zeroˡ  ε      = ≈ᶜ-refl
·ᶜ-zeroˡ (γ ∙ p) = (·ᶜ-zeroˡ γ) ∙ (·-zeroˡ p)

-- A zero context is a right zero to modality context scaling
-- p ·ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ

·ᶜ-zeroʳ : {n : Nat} (p : M) → p ·ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = n}
·ᶜ-zeroʳ {n = 0}    p = ≈ᶜ-refl
·ᶜ-zeroʳ {n = 1+ n} p = (·ᶜ-zeroʳ p) ∙ (·-zeroʳ p)

-- Modality context scaling is associative
-- (p · q) ·ᶜ γ ≈ᶜ p ·ᶜ (q ·ᶜ γ)

·ᶜ-assoc : (p q : M) → (γ : Conₘ n) → (p · q) ·ᶜ γ ≈ᶜ p ·ᶜ (q ·ᶜ γ)
·ᶜ-assoc p q  ε      = ≈ᶜ-refl
·ᶜ-assoc p q (γ ∙ r) = (·ᶜ-assoc p q γ) ∙ (·-assoc p q r)

-- Modality contex scaling is left distributive over addition
-- p ·ᶜ (γ +ᶜ δ) ≈ᶜ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)

·ᶜ-distribˡ-+ᶜ : (p : M) → (γ δ : Conₘ n) → (p ·ᶜ (γ +ᶜ δ)) ≈ᶜ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)
·ᶜ-distribˡ-+ᶜ p  ε       ε      = ≈ᶜ-refl
·ᶜ-distribˡ-+ᶜ p (γ ∙ q) (δ ∙ r) = (·ᶜ-distribˡ-+ᶜ p γ δ) ∙ (·-distribˡ-+ p q r)

-- Modality context scaling is right distributive over addition
-- (p + q) ·ᶜ γ ≈ᶜ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)

·ᶜ-distribʳ-+ᶜ : (p q : M) → (γ : Conₘ n) → (p + q) ·ᶜ γ ≈ᶜ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-+ᶜ p q  ε      = ≈ᶜ-refl
·ᶜ-distribʳ-+ᶜ p q (γ ∙ r) = (·ᶜ-distribʳ-+ᶜ p q γ) ∙ (·-distribʳ-+ r p q)

-- Modality contex scaling is left distributive over meet
-- p ·ᶜ (γ ∧ᶜ δ) ≈ᶜ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)

·ᶜ-distribˡ-∧ᶜ : (p : M) → (γ δ : Conₘ n) → p ·ᶜ (γ ∧ᶜ δ) ≈ᶜ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)
·ᶜ-distribˡ-∧ᶜ p  ε       ε      = ≈ᶜ-refl
·ᶜ-distribˡ-∧ᶜ p (γ ∙ q) (δ ∙ r) = (·ᶜ-distribˡ-∧ᶜ p γ δ) ∙ (·-distribˡ-∧ p q r)

-- Modality context scaling is right distributive over meet
-- (p ∧ q) ·ᶜ γ ≈ᶜ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)

·ᶜ-distribʳ-∧ᶜ : (p q : M) → (γ : Conₘ n) → (p ∧ q) ·ᶜ γ ≈ᶜ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-∧ᶜ p q  ε      = ≈ᶜ-refl
·ᶜ-distribʳ-∧ᶜ p q (γ ∙ r) = (·ᶜ-distribʳ-∧ᶜ p q γ) ∙ (·-distribʳ-∧ r p q)

-- Congruence of ·ᶜ
-- If p ≈ q and γ ≈ᶜ δ then p ·ᶜ γ ≈ᶜ q ·ᶜ δ

·ᶜ-cong : p ≈ q → γ ≈ᶜ δ → p ·ᶜ γ ≈ᶜ q ·ᶜ δ
·ᶜ-cong p≈q ε = ≈ᶜ-refl
·ᶜ-cong p≈q (γ≈δ ∙ p′≈q′) = (·ᶜ-cong p≈q γ≈δ) ∙ (·-cong p≈q p′≈q′)

-- Congruence of ·ᶜ on the left
-- If γ ≈ᶜ δ then p ·ᶜ γ ≈ᶜ p ·ᶜ δ

·ᶜ-congˡ : γ ≈ᶜ δ → p ·ᶜ γ ≈ᶜ p ·ᶜ δ
·ᶜ-congˡ γ≈δ = ·ᶜ-cong ≈-refl γ≈δ

-- Congruence of ·ᶜ on the right
-- If p ≈ q then p ·ᶜ γ ≈ᶜ q ·ᶜ γ

·ᶜ-congʳ : p ≈ q → p ·ᶜ γ ≈ᶜ q ·ᶜ γ
·ᶜ-congʳ p≈q = ·ᶜ-cong p≈q ≈ᶜ-refl

-- Multiplication on the left is monotone
-- If p ≤ q then p ·ᶜ γ ≤ᶜ q ·ᶜ γ

·ᶜ-monotoneˡ : p ≤ q → p ·ᶜ γ ≤ᶜ q ·ᶜ γ
·ᶜ-monotoneˡ {γ = ε}     p≤q = ≤ᶜ-refl
·ᶜ-monotoneˡ {γ = γ ∙ r} p≤q = (·ᶜ-monotoneˡ p≤q) ∙ (·-monotoneˡ p≤q)

-- Multiplication on the right is monotone
-- If γ ≤ᶜ δ then p ·ᶜ γ ≤ᶜ p ·ᶜ δ

·ᶜ-monotoneʳ : γ ≤ᶜ δ → p ·ᶜ γ ≤ᶜ p ·ᶜ δ
·ᶜ-monotoneʳ {γ = ε} {ε} ε = ≤ᶜ-refl
·ᶜ-monotoneʳ {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) = (·ᶜ-monotoneʳ γ≤δ) ∙ (·-monotoneʳ p≤q)

-- Multiplication is monotone
-- If γ ≤ᶜ δ and p ≤ q then p ·ᶜ γ ≤ᶜ q ·ᶜ δ

·ᶜ-monotone : γ ≤ᶜ δ → p ≤ q → p ·ᶜ γ ≤ᶜ q ·ᶜ δ
·ᶜ-monotone {γ = ε} {ε} ε p≤q = ≤ᶜ-refl
·ᶜ-monotone {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) p′≤q′ = (·ᶜ-monotone γ≤δ p′≤q′) ∙ (·-monotone p′≤q′ p≤q)
