open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.PartialOrder {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties.Equivalence 𝕄
open import Definition.Modality.Properties 𝕄

open import Tools.Nat

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
≤ᶜ-trans {γ = ε} {ε} {ε} _ _ = ε
≤ᶜ-trans {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) (δ≤η ∙ q≤r) =
  (≤ᶜ-trans γ≤δ δ≤η) ∙ (≤-trans p≤q q≤r)

-- ≤ᶜ is antisymmetric
-- If γ ≤ᶜ δ and δ ≤ᶜ γ then γ ≈ᶜ δ

≤ᶜ-antisym : γ ≤ᶜ δ → δ ≤ᶜ γ → γ ≈ᶜ δ
≤ᶜ-antisym {γ = ε} {ε} _ _ = ε
≤ᶜ-antisym {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) (δ≤γ ∙ q≤p) =
  (≤ᶜ-antisym γ≤δ δ≤γ) ∙ (≤-antisym p≤q q≤p)

-- ≤ᶜ is a non-strict order relation
-- If γ ≈ᶜ δ then γ ≤ᶜ δ

≤ᶜ-reflexive : γ ≈ᶜ δ → γ ≤ᶜ δ
≤ᶜ-reflexive {γ = ε} {ε} _ = ε
≤ᶜ-reflexive {γ = γ ∙ p} {δ ∙ q} (γ≈δ ∙ p≈q) =
  (≤ᶜ-reflexive γ≈δ) ∙ (≤-reflexive p≈q)

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
