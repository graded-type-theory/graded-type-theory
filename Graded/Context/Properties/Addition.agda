------------------------------------------------------------------------
-- Properties of addition.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Context.Properties.Addition
  {a} {M : Set a} (𝕄 : Modality M) where

open import Graded.Context 𝕄
open import Graded.Context.Properties.Equivalence 𝕄
open import Graded.Context.Properties.PartialOrder 𝕄
open import Graded.Modality.Properties 𝕄

open import Tools.Algebra
open import Tools.Bool
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

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

-- The operation _+ᶜ_ is sub-interchangeable with _∧ᶜ_ (with respect
-- to _≤ᶜ_).

+ᶜ-sub-interchangeable-∧ᶜ :
  _SubInterchangeable_by_ (Conₘ n) _+ᶜ_ _∧ᶜ_ _≤ᶜ_
+ᶜ-sub-interchangeable-∧ᶜ ε       ε       ε       ε       = ε
+ᶜ-sub-interchangeable-∧ᶜ (_ ∙ _) (_ ∙ _) (_ ∙ _) (_ ∙ _) =
  +ᶜ-sub-interchangeable-∧ᶜ _ _ _ _ ∙ +-sub-interchangeable-∧ _ _ _ _

-- Congruence of +ᶜ
-- If γ ≈ᶜ γ′ and δ ≈ᶜ δ′ then γ +ᶜ δ ≈ᶜ γ′ +ᶜ δ′

+ᶜ-cong : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → γ +ᶜ δ ≈ᶜ γ′ +ᶜ δ′
+ᶜ-cong ε ε = ≈ᶜ-refl
+ᶜ-cong (γ≈ᶜγ′ ∙ p≡p′) (δ≈ᶜδ′ ∙ q≡q′) =
  (+ᶜ-cong γ≈ᶜγ′ δ≈ᶜδ′) ∙ (+-cong p≡p′ q≡q′)

-- Congruence for γ +ᶜ_.

+ᶜ-congˡ : δ ≈ᶜ δ′ → γ +ᶜ δ ≈ᶜ γ +ᶜ δ′
+ᶜ-congˡ δ≈ᶜδ′ = +ᶜ-cong ≈ᶜ-refl δ≈ᶜδ′

-- Congruence for _+ᶜ δ.

+ᶜ-congʳ : γ ≈ᶜ γ′ → γ +ᶜ δ ≈ᶜ γ′ +ᶜ δ
+ᶜ-congʳ γ≈ᶜγ′ = +ᶜ-cong γ≈ᶜγ′ ≈ᶜ-refl

-- Addition on the left is monotone
-- If γ ≤ᶜ δ then γ +ᶜ η ≤ᶜ δ +ᶜ η

+ᶜ-monotoneˡ : γ ≤ᶜ δ → γ +ᶜ η ≤ᶜ δ +ᶜ η
+ᶜ-monotoneˡ {γ = ε}     {δ = ε}     {η = ε}     ε           = ≤ᶜ-refl
+ᶜ-monotoneˡ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (γ≤δ ∙ p≤q) =
  +ᶜ-monotoneˡ γ≤δ ∙ +-monotoneˡ p≤q

-- Addition on the right is monotone
-- If γ ≤ᶜ δ then η +ᶜ γ ≤ᶜ η +ᶜ δ

+ᶜ-monotoneʳ : γ ≤ᶜ δ → η +ᶜ γ ≤ᶜ η +ᶜ δ
+ᶜ-monotoneʳ {γ = ε}     {δ = ε}     {η = ε}     ε           = ≤ᶜ-refl
+ᶜ-monotoneʳ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (γ≤δ ∙ p≤q) =
  +ᶜ-monotoneʳ γ≤δ ∙ +-monotoneʳ p≤q

-- Addition is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ + δ ≤ᶜ γ′ +ᶜ δ′

+ᶜ-monotone : γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → γ +ᶜ δ ≤ᶜ γ′ +ᶜ δ′
+ᶜ-monotone γ≤γ′ δ≤δ′ = ≤ᶜ-trans (+ᶜ-monotoneˡ γ≤γ′) (+ᶜ-monotoneʳ δ≤δ′)

opaque

  -- If 𝟙 ≤ 𝟘, then _+ᶜ δ is decreasing.

  +ᶜ-decreasingˡ : 𝟙 ≤ 𝟘 → γ +ᶜ δ ≤ᶜ γ
  +ᶜ-decreasingˡ {γ = ε}     {δ = ε}     _   = ε
  +ᶜ-decreasingˡ {γ = _ ∙ _} {δ = _ ∙ _} 𝟙≤𝟘 =
    +ᶜ-decreasingˡ 𝟙≤𝟘 ∙ +-decreasingˡ 𝟙≤𝟘

opaque

  -- If 𝟙 ≤ 𝟘, then γ +ᶜ_ is decreasing.

  +ᶜ-decreasingʳ : 𝟙 ≤ 𝟘 → γ +ᶜ δ ≤ᶜ δ
  +ᶜ-decreasingʳ {γ = γ} {δ = δ} 𝟙≤𝟘 = begin
    γ +ᶜ δ  ≈⟨ +ᶜ-comm _ _ ⟩
    δ +ᶜ γ  ≤⟨ +ᶜ-decreasingˡ 𝟙≤𝟘 ⟩
    δ       ∎
    where
    open ≤ᶜ-reasoning

-- Addition forms a commutative monoid.

+ᶜ-commutativeMonoid : ∀ {n} → IsCommutativeMonoid (Conₘ n) _+ᶜ_ 𝟘ᶜ
+ᶜ-commutativeMonoid = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = PE.isEquivalence
        ; ∙-cong = PE.cong₂ _+ᶜ_
        }
      ; assoc = λ γ δ η → ≈ᶜ→≡ (+ᶜ-assoc γ δ η)
      }
    ; identity = (λ γ → ≈ᶜ→≡ (+ᶜ-identityˡ γ)) , λ γ → ≈ᶜ→≡ (+ᶜ-identityʳ γ)
    }
  ; comm = λ γ δ → ≈ᶜ→≡ (+ᶜ-comm γ δ)
  }

opaque

  -- The context ω ·ᶜ (γ +ᶜ δ) is bounded by ω ·ᶜ δ.

  ω·ᶜ+ᶜ≤ω·ᶜʳ : ω ·ᶜ (γ +ᶜ δ) ≤ᶜ ω ·ᶜ δ
  ω·ᶜ+ᶜ≤ω·ᶜʳ {γ = ε}     {δ = ε}     = ε
  ω·ᶜ+ᶜ≤ω·ᶜʳ {γ = _ ∙ _} {δ = _ ∙ _} = ω·ᶜ+ᶜ≤ω·ᶜʳ ∙ ω·+≤ω·ʳ

opaque

  -- The context ω ·ᶜ (γ +ᶜ δ) is bounded by ω ·ᶜ γ.

  ω·ᶜ+ᶜ≤ω·ᶜˡ : ω ·ᶜ (γ +ᶜ δ) ≤ᶜ ω ·ᶜ γ
  ω·ᶜ+ᶜ≤ω·ᶜˡ {γ = ε}     {δ = ε}     = ε
  ω·ᶜ+ᶜ≤ω·ᶜˡ {γ = _ ∙ _} {δ = _ ∙ _} = ω·ᶜ+ᶜ≤ω·ᶜˡ ∙ ω·+≤ω·ˡ
