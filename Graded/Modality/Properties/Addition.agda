------------------------------------------------------------------------
-- Properties of addition.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality

module Graded.Modality.Properties.Addition
  {a} {M : Set a} (𝕄 : Semiring-with-meet M) where

open Semiring-with-meet 𝕄

open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Algebra M
open import Tools.Function
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    p p′ q q′ r r′ : M

-- Addition on the left is a monotone function
-- If p ≤ q then p + r ≤ q + r

+-monotoneˡ : p ≤ q → p + r ≤ q + r
+-monotoneˡ p≤q = trans (+-congʳ p≤q) (+-distribʳ-∧ _ _ _)

-- Addition on the right is a monotone function
-- If p ≤ q then r + p ≤ r + q

+-monotoneʳ : p ≤ q → r + p ≤ r + q
+-monotoneʳ p≤q = trans (+-congˡ p≤q) (+-distribˡ-∧ _ _ _)

-- Addition is a monotone function
-- If p ≤ p′ and q ≤ q′ then p + q ≤ p′ + q′

+-monotone : p ≤ p′ → q ≤ q′ → p + q ≤ p′ + q′
+-monotone p≤p′ q≤q′ = ≤-trans (+-monotoneˡ p≤p′) (+-monotoneʳ q≤q′)

-- The operation _+_ is sub-interchangeable with _∧_ (with respect
-- to _≤_).

+-sub-interchangeable-∧ : _+_ SubInterchangeable _∧_ by _≤_
+-sub-interchangeable-∧ p q p′ q′ = begin
  (p ∧ q) + (p′ ∧ q′)                            ≈⟨ +-distribˡ-∧ _ _ _ ⟩
  ((p ∧ q) + p′) ∧ ((p ∧ q) + q′)                ≈⟨ ∧-cong (+-distribʳ-∧ _ _ _) (+-distribʳ-∧ _ _ _) ⟩
  ((p + p′) ∧ (q + p′)) ∧ ((p + q′) ∧ (q + q′))  ≤⟨ ∧-monotone (∧-decreasingˡ _ _) (∧-decreasingʳ _ _) ⟩
  (p + p′) ∧ (q + q′)                            ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- The operation _+_ is sub-interchangeable with itself (with respect
-- to _≡_).

+-sub-interchangeable-+ : _+_ SubInterchangeable _+_ by _≡_
+-sub-interchangeable-+ p q r s =
  (p + q) + (r + s)  ≡⟨ +-assoc _ _ _ ⟩
  p + (q + (r + s))  ≡˘⟨ cong (_ +_) (+-assoc _ _ _) ⟩
  p + ((q + r) + s)  ≡⟨ cong (_ +_) (cong (_+ _) (+-comm _ _)) ⟩
  p + ((r + q) + s)  ≡⟨ cong (_ +_) (+-assoc _ _ _) ⟩
  p + (r + (q + s))  ≡˘⟨ +-assoc _ _ _ ⟩
  (p + r) + (q + s)  ∎
  where
  open Tools.Reasoning.PropositionalEquality

opaque

  -- The grade ω · (p + q) is bounded by ω · p.

  ω·+≤ω·ˡ : ω · (p + q) ≤ ω · p
  ω·+≤ω·ˡ {p} {q} = begin
    ω · (p + q)  ≡⟨ ·-congˡ $ +-comm _ _ ⟩
    ω · (q + p)  ≤⟨ ω·+≤ω·ʳ ⟩
    ω · p        ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- The grade ω is bounded by 𝟘.

  ω≤𝟘 : ω ≤ 𝟘
  ω≤𝟘 = begin
    ω            ≡˘⟨ ·-identityʳ _ ⟩
    ω · 𝟙        ≡˘⟨ ·-congˡ $ +-identityʳ _ ⟩
    ω · (𝟙 + 𝟘)  ≤⟨ ω·+≤ω·ʳ ⟩
    ω · 𝟘        ≡⟨ ·-zeroʳ _ ⟩
    𝟘            ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- The grade ω is bounded by 𝟘 ∧ 𝟙.

  ω≤𝟘∧𝟙 : ω ≤ 𝟘 ∧ 𝟙
  ω≤𝟘∧𝟙 = ∧-greatest-lower-bound ω≤𝟘 ω≤𝟙

opaque

  -- The grade ω + ω is bounded by ω.

  ω+ω≤ω : ω + ω ≤ ω
  ω+ω≤ω = begin
    ω + ω          ≡˘⟨ +-cong (·-identityʳ _) (·-identityʳ _) ⟩
    ω · 𝟙 + ω · 𝟙  ≡˘⟨ ·-distribˡ-+ _ _ _ ⟩
    ω · (𝟙 + 𝟙)    ≤⟨ ω·+≤ω·ʳ ⟩
    ω · 𝟙          ≡⟨ ·-identityʳ _ ⟩
    ω              ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset
