------------------------------------------------------------------------
-- Properties of meet.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Context.Properties.Meet
  {a} {M : Set a} (𝕄 : Modality M) where

open import Graded.Context 𝕄
open import Graded.Context.Properties.Equivalence 𝕄
open import Graded.Context.Properties.PartialOrder 𝕄
open import Graded.Modality.Properties 𝕄

open import Tools.Nat using (Nat)

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
∧ᶜ-cong (γ≈ᶜγ′ ∙ p≡p′) (δ≈ᶜδ′ ∙ q≡q′) =
  ∧ᶜ-cong γ≈ᶜγ′ δ≈ᶜδ′ ∙ ∧-cong p≡p′ q≡q′

-- Congruence of ∧ᶜ on the left
-- If δ ≈ᶜ δ′ then γ ∧ᶜ δ ≈ᶜ γ ∧ᶜ δ′

∧ᶜ-congˡ : δ ≈ᶜ δ′ → γ ∧ᶜ δ ≈ᶜ γ ∧ᶜ δ′
∧ᶜ-congˡ δ≈ᶜδ′ = ∧ᶜ-cong ≈ᶜ-refl δ≈ᶜδ′

-- Congruence of ∧ᶜ on the right
-- If γ ≈ᶜ γ′ then γ ∧ᶜ δ ≈ᶜ γ′ ∧ᶜ δ

∧ᶜ-congʳ : γ ≈ᶜ γ′ → γ ∧ᶜ δ ≈ᶜ γ′ ∧ᶜ δ
∧ᶜ-congʳ γ≈ᶜγ′ = ∧ᶜ-cong γ≈ᶜγ′ ≈ᶜ-refl

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

-- The result of the meet operation is a greatest lower bound of its
-- two arguments.

∧ᶜ-greatest-lower-bound : γ ≤ᶜ δ → γ ≤ᶜ η → γ ≤ᶜ δ ∧ᶜ η
∧ᶜ-greatest-lower-bound {γ = ε} {δ = ε} {η = ε} ε ε =
  ε
∧ᶜ-greatest-lower-bound
  {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (γ≤δ ∙ p≤q) (γ≤η ∙ p≤r) =
  ∧ᶜ-greatest-lower-bound γ≤δ γ≤η ∙ ∧-greatest-lower-bound p≤q p≤r

-- If _+_ is pointwise bounded by _∧_, then _+ᶜ_ is pointwise bounded
-- by _∧ᶜ_.

+ᶜ≤ᶜ∧ᶜ :
  (∀ p q → p + q ≤ p ∧ q) →
  γ +ᶜ δ ≤ᶜ γ ∧ᶜ δ
+ᶜ≤ᶜ∧ᶜ {γ = ε}     {δ = ε}     _   = ε
+ᶜ≤ᶜ∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} +≤∧ = +ᶜ≤ᶜ∧ᶜ +≤∧ ∙ +≤∧ _ _

-- If _∧_ is pointwise bounded by _+_, then _∧ᶜ_ is pointwise bounded
-- by _+ᶜ_.

∧ᶜ≤ᶜ+ᶜ :
  (∀ p q → p ∧ q ≤ p + q) →
  γ ∧ᶜ δ ≤ᶜ γ +ᶜ δ
∧ᶜ≤ᶜ+ᶜ {γ = ε}     {δ = ε}     _   = ε
∧ᶜ≤ᶜ+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} ∧≤+ = ∧ᶜ≤ᶜ+ᶜ ∧≤+ ∙ ∧≤+ _ _
