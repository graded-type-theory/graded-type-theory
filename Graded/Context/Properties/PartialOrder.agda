------------------------------------------------------------------------
-- Properties of the partial order relation.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Context.Properties.PartialOrder
  {a} {M : Set a} (𝕄 : Modality M) where

open import Graded.Context 𝕄
open import Graded.Context.Properties.Equivalence 𝕄
open import Graded.Modality.Properties 𝕄

open import Tools.Function
open import Tools.Nat using (Nat)
import Tools.Reasoning.PartialOrder
open import Tools.Relation

open Modality 𝕄

private
  variable
    n : Nat
    γ δ η : Conₘ n

-- ≤ᶜ is reflexive
-- γ ≤ᶜ γ

≤ᶜ-refl : γ ≤ᶜ γ
≤ᶜ-refl {γ = ε} = ε
≤ᶜ-refl {γ = γ ∙ p} = ≤ᶜ-refl ∙ ≤-refl

-- ≤ᶜ is transitive
-- If γ ≤ᶜ δ and δ ≤ᶜ η then γ ≤ᶜ η

≤ᶜ-trans : γ ≤ᶜ δ → δ ≤ᶜ η → γ ≤ᶜ η
≤ᶜ-trans {γ = ε}     {δ = ε}     {η = ε}     _           _           = ε
≤ᶜ-trans {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (γ≤δ ∙ p≤q) (δ≤η ∙ q≤r) =
  (≤ᶜ-trans γ≤δ δ≤η) ∙ (≤-trans p≤q q≤r)

-- ≤ᶜ is antisymmetric
-- If γ ≤ᶜ δ and δ ≤ᶜ γ then γ ≈ᶜ δ

≤ᶜ-antisym : γ ≤ᶜ δ → δ ≤ᶜ γ → γ ≈ᶜ δ
≤ᶜ-antisym {γ = ε}     {δ = ε}     _           _           = ε
≤ᶜ-antisym {γ = _ ∙ _} {δ = _ ∙ _} (γ≤δ ∙ p≤q) (δ≤γ ∙ q≤p) =
  (≤ᶜ-antisym γ≤δ δ≤γ) ∙ (≤-antisym p≤q q≤p)

-- ≤ᶜ is a non-strict order relation
-- If γ ≈ᶜ δ then γ ≤ᶜ δ

≤ᶜ-reflexive : γ ≈ᶜ δ → γ ≤ᶜ δ
≤ᶜ-reflexive {γ = ε}     {δ = ε}     _            = ε
≤ᶜ-reflexive {γ = _ ∙ _} {δ = _ ∙ _} (γ≈ᶜδ ∙ p≡q) =
  ≤ᶜ-reflexive γ≈ᶜδ ∙ ≤-reflexive p≡q

-- ≤ᶜ is a preorder

≤ᶜ-preorder : IsPreorder (_≈ᶜ_ {n = n}) _≤ᶜ_
≤ᶜ-preorder = record
  { isEquivalence = ≈ᶜ-equivalence
  ; reflexive = ≤ᶜ-reflexive
  ; trans = ≤ᶜ-trans
  }

-- ≤ᶜ is a partial order

≤ᶜ-partial : IsPartialOrder (_≈ᶜ_ {n = n}) _≤ᶜ_
≤ᶜ-partial = record
  { isPreorder = ≤ᶜ-preorder
  ; antisym = ≤ᶜ-antisym
  }

-- (Conₘ, ≤ᶜ) is a poset

≤ᶜ-poset : {n : Nat} → Poset _ _ _
≤ᶜ-poset {n} = record
  { Carrier = Conₘ n
  ; _≈_ = _≈ᶜ_
  ; _≤_ = _≤ᶜ_
  ; isPartialOrder = ≤ᶜ-partial
  }

-- Partial order reasoning for _≤ᶜ_.

module ≤ᶜ-reasoning {n : Nat} =
  Tools.Reasoning.PartialOrder (≤ᶜ-poset {n = n})

-- If _≤_ is decidable, then _≤ᶜ_ is decidable.

≤ᶜ-decidable : Decidable _≤_ → Decidable (_≤ᶜ_ {n = n})
≤ᶜ-decidable _≤?_ = λ where
  ε       ε       → yes ε
  (γ ∙ p) (δ ∙ q) → case p ≤? q of λ where
    (no p≰q)  → no λ where
                  (_ ∙ p≤q) → p≰q p≤q
    (yes p≤q) → case ≤ᶜ-decidable _≤?_ γ δ of λ where
      (no γ≰δ)  → no λ where
                    (γ≤δ ∙ _) → γ≰δ γ≤δ
      (yes γ≤δ) → yes (γ≤δ ∙ p≤q)

-- If 𝟘 is the largest quantity, then 𝟘ᶜ is the largest context (for
-- each length).

≤ᶜ𝟘ᶜ : (∀ {p} → p ≤ 𝟘) → γ ≤ᶜ 𝟘ᶜ
≤ᶜ𝟘ᶜ {γ = ε}     _  = ε
≤ᶜ𝟘ᶜ {γ = _ ∙ _} ≤𝟘 = ≤ᶜ𝟘ᶜ ≤𝟘 ∙ ≤𝟘
