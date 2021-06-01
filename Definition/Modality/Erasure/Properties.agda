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

-- nr is a decreasing function on its first argument
-- nr p q r ≤ q

nr-decreasingˡ : (p q r : Erasure) → nr p q r ≤ p
nr-decreasingˡ 𝟘 𝟘 r = PE.refl
nr-decreasingˡ 𝟘 ω r = PE.refl
nr-decreasingˡ ω 𝟘 r = PE.refl
nr-decreasingˡ ω ω r = PE.refl

-- nr is a decreasing function on its second argument
-- nr p q r ≤ q

nr-decreasingʳ : (p q r : Erasure) → nr p q r ≤ q
nr-decreasingʳ 𝟘 𝟘 r = PE.refl
nr-decreasingʳ 𝟘 ω 𝟘 = PE.refl
nr-decreasingʳ 𝟘 ω ω = PE.refl
nr-decreasingʳ ω 𝟘 r = PE.refl
nr-decreasingʳ ω ω r = PE.refl


-- nrᶜ is a decreasing function on its first argument
-- nrᶜ γ δ r ≤ γ

nrᶜ-decreasingˡ : (γ δ : Conₘ n) (r : Erasure) → nrᶜ γ δ r ≤ᶜ γ
nrᶜ-decreasingˡ ε ε r = ≤ᶜ-refl
nrᶜ-decreasingˡ (γ ∙ 𝟘) (δ ∙ 𝟘) r = (nrᶜ-decreasingˡ γ δ r) ∙ PE.refl
nrᶜ-decreasingˡ (γ ∙ 𝟘) (δ ∙ ω) r = (nrᶜ-decreasingˡ γ δ r) ∙ PE.refl
nrᶜ-decreasingˡ (γ ∙ ω) (δ ∙ 𝟘) r = (nrᶜ-decreasingˡ γ δ r) ∙ PE.refl
nrᶜ-decreasingˡ (γ ∙ ω) (δ ∙ ω) r = (nrᶜ-decreasingˡ γ δ r) ∙ PE.refl
-- (nrᶜ-decreasingˡ γ δ r) ∙ (nr-decreasingˡ p q r)

-- nrᶜ is a decreasing function on its second argument
-- nrᶜ γ δ r ≤ δ

nrᶜ-decreasingʳ : (γ δ : Conₘ n) (r : Erasure)  → nrᶜ γ δ r ≤ᶜ δ
nrᶜ-decreasingʳ ε ε r = ≤ᶜ-refl
nrᶜ-decreasingʳ (γ ∙ 𝟘) (δ ∙ 𝟘) r = nrᶜ-decreasingʳ γ δ r ∙ PE.refl
nrᶜ-decreasingʳ (γ ∙ 𝟘) (δ ∙ ω) r = nrᶜ-decreasingʳ γ δ r ∙ PE.refl
nrᶜ-decreasingʳ (γ ∙ ω) (δ ∙ 𝟘) r = nrᶜ-decreasingʳ γ δ r ∙ PE.refl
nrᶜ-decreasingʳ (γ ∙ ω) (δ ∙ ω) r = nrᶜ-decreasingʳ γ δ r ∙ PE.refl

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


-- 𝟘ᶜ is the greatest erasure modality context
-- γ ≤ 𝟘ᶜ

greatest-elemᶜ : (γ : Conₘ n) → γ ≤ᶜ 𝟘ᶜ
greatest-elemᶜ ε = ε
greatest-elemᶜ (γ ∙ p) = (greatest-elemᶜ γ) ∙ (greatest-elem p)

-- 𝟙ᶜ is the least erasure modality context
-- 𝟙ᶜ ≤ γ

least-elemᶜ : (γ : Conₘ n) → 𝟙ᶜ ≤ᶜ γ
least-elemᶜ ε = ε
least-elemᶜ (γ ∙ p) = (least-elemᶜ γ) ∙ (least-elem p)



-- Variables are always annotated with ω
-- If γ ▸ var x then x ◂ ω ∈ γ

valid-var-usage : γ ▸ var x → x ◂ ω ∈ γ
valid-var-usage γ▸x with inv-usage-var γ▸x
valid-var-usage {x = x0} γ▸x | γ≤γ′ ∙ p≤ω rewrite least-elem′ _ p≤ω = here
valid-var-usage {x = x +1} γ▸x | γ≤γ′ ∙ p≤𝟘 = there (valid-var-usage (sub (var {x = x}) γ≤γ′))
