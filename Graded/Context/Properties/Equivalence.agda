------------------------------------------------------------------------
-- Properties of equality.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Context.Properties.Equivalence
  {a} {M : Set a} (𝕄 : Modality M) where

open import Graded.Context 𝕄

open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality
import Tools.Reasoning.Equivalence
open import Tools.Relation

open Modality 𝕄

private
  variable
    n : Nat
    γ δ η : Conₘ n


-- ≈ᶜ is reflexive
-- γ ≈ᶜ γ

≈ᶜ-refl : γ ≈ᶜ γ
≈ᶜ-refl {γ = ε} = ε
≈ᶜ-refl {γ = γ ∙ p} = ≈ᶜ-refl ∙ refl

-- ≈ᶜ is transitive
-- If γ ≈ᶜ δ and δ ≈ᶜ η then γ ≈ᶜ η

≈ᶜ-trans : γ ≈ᶜ δ → δ ≈ᶜ η → γ ≈ᶜ η
≈ᶜ-trans {γ = ε} {ε} {ε} _ _ = ε
≈ᶜ-trans {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≈ᶜδ ∙ p≡q) (δ≈ᶜη ∙ q≡r) =
  ≈ᶜ-trans γ≈ᶜδ δ≈ᶜη ∙ trans p≡q q≡r

-- ≈ᶜ is symmetric
-- If γ ≈ᶜ δ and δ ≈ᶜ γ then γ ≈ᶜ δ

≈ᶜ-sym : γ ≈ᶜ δ → δ ≈ᶜ γ
≈ᶜ-sym {γ = ε} {ε} a = ε
≈ᶜ-sym {γ = γ ∙ p} {δ ∙ q} (γ≈ᶜδ ∙ p≡q) = ≈ᶜ-sym γ≈ᶜδ ∙ sym p≡q

-- ≈ᶜ is an equivalence relation

≈ᶜ-equivalence : {n : Nat} → IsEquivalence (_≈ᶜ_ {n = n})
≈ᶜ-equivalence = record
  { refl  = ≈ᶜ-refl
  ; sym   = ≈ᶜ-sym
  ; trans = ≈ᶜ-trans
  }

Conₘ-setoid : {n : Nat} → Setoid a a
Conₘ-setoid {n} = record
  { Carrier = Conₘ n ; _≈_ = _≈ᶜ_ ; isEquivalence = ≈ᶜ-equivalence }

-- Equational reasoning for _≈ᶜ_.

module ≈ᶜ-reasoning {n : Nat} =
  Tools.Reasoning.Equivalence (Conₘ-setoid {n = n})

-- Equivalent contexts are equal.

≈ᶜ→≡ : γ ≈ᶜ δ → γ ≡ δ
≈ᶜ→≡ ε           = refl
≈ᶜ→≡ (ps ∙ refl) = cong (_∙ _) (≈ᶜ→≡ ps)

-- If _≡_ is decidable (for M), then _≈ᶜ_ is decidable.

≈ᶜ-decidable : Decidable (_≡_ {A = M}) → Decidable (_≈ᶜ_ {n = n})
≈ᶜ-decidable _≡?_ = λ where
  ε       ε       → yes ε
  (γ ∙ p) (δ ∙ q) → case p ≡? q of λ where
    (no p≢q)  → no λ where
                  (_ ∙ p≡q) → p≢q p≡q
    (yes p≡q) → case ≈ᶜ-decidable _≡?_ γ δ of λ where
      (no γ≉ᶜδ)  → no λ where
                     (γ≈ᶜδ ∙ _) → γ≉ᶜδ γ≈ᶜδ
      (yes γ≈ᶜδ) → yes (γ≈ᶜδ ∙ p≡q)
