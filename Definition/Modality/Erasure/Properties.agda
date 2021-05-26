{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Erasure.Properties where

open import Definition.Modality.Erasure

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Context.Properties ErasureModality public

open import Definition.Modality.Properties ErasureModality public

open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality

open import Definition.Untyped Erasure

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat hiding (_+_)
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    σ σ′ : Subst m n
    γ : Conₘ n
    t a : Term n
    x : Fin n


-- Addition on the left is a decreasing function
-- γ + δ ≤ᶜ γ

+-decreasingˡ : (p q : Erasure) → (p + q) ≤ p
+-decreasingˡ 𝟘 𝟘 = PE.refl
+-decreasingˡ 𝟘 ω = PE.refl
+-decreasingˡ ω 𝟘 = PE.refl
+-decreasingˡ ω ω = PE.refl

-- Addition on the right is a decreasing function
-- γ + δ ≤ᶜ δ

+-decreasingʳ : (p q : Erasure) → (p + q) ≤ q
+-decreasingʳ 𝟘 𝟘 = PE.refl
+-decreasingʳ 𝟘 ω = PE.refl
+-decreasingʳ ω 𝟘 = PE.refl
+-decreasingʳ ω ω = PE.refl


-- Addition on the left is a decreasing function
-- γ +ᶜ δ ≤ᶜ γ

+ᶜ-decreasingˡ : (γ δ : Conₘ n) → γ +ᶜ δ ≤ᶜ γ
+ᶜ-decreasingˡ ε ε = ≤ᶜ-refl
+ᶜ-decreasingˡ (γ ∙ p) (δ ∙ q) = (+ᶜ-decreasingˡ γ δ) ∙ (+-decreasingˡ p q)

-- Addition on the right is a decreasing function
-- γ +ᶜ δ ≤ᶜ δ

+ᶜ-decreasingʳ : (γ δ : Conₘ n) → γ +ᶜ δ ≤ᶜ δ
+ᶜ-decreasingʳ ε ε = ≤ᶜ-refl
+ᶜ-decreasingʳ (γ ∙ p) (δ ∙ q) = (+ᶜ-decreasingʳ γ δ) ∙ (+-decreasingʳ p q)

-- 𝟘 is the greatest element of the erasure modality
-- p ≤ 𝟘

greatest-elem : (p : Erasure) → p ≤ 𝟘
greatest-elem p = PE.refl

-- ω is the least element of the erasure modality
-- ω ≤ p

least-elem : (p : Erasure) → ω ≤ p
least-elem 𝟘 = PE.refl
least-elem ω = PE.refl


-- 𝟘 is the greatest element of the erasure modality
-- If 𝟘 ≤ p then p ≡ 𝟘

greatest-elem′ : (p : Erasure) → 𝟘 ≤ p → p PE.≡ 𝟘
greatest-elem′ p 𝟘≤p = ≤-antisym (greatest-elem p) 𝟘≤p

-- ω is the least element of the erasure modality
-- If p ≤ ω then p ≡ ω

least-elem′ : (p : Erasure) → p ≤ ω → p PE.≡ ω
least-elem′ p p≤ω = ≤-antisym p≤ω (least-elem p)



-- Variables are always annotated with ω
-- If γ ▸ var x then x ◂ ω ∈ γ

valid-var-usage : γ ▸ var x → x ◂ ω ∈ γ
valid-var-usage γ▸x with inv-usage-var γ▸x
valid-var-usage {x = x0} γ▸x | γ≤γ′ ∙ p≤ω rewrite least-elem′ _ p≤ω = here
valid-var-usage {x = x +1} γ▸x | γ≤γ′ ∙ p≤𝟘 = there (valid-var-usage (sub (var {x = x}) γ≤γ′))
