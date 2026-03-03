------------------------------------------------------------------------
-- Properties of multiplication.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.Multiplication
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Algebra M
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder


private
  variable
    p p′ q q′ r r′ : M

-- Multiplication on the left is a monotone function
-- If p ≤ q then p · r ≤ q · r

·-monotoneˡ : p ≤ q → p · r ≤ q · r
·-monotoneˡ {p} {q} {r} p≤q = trans (·-congʳ p≤q) (·-distribʳ-∧ r p q)

-- Multiplication on the right is a monotone function
-- If p ≤ q then r · p ≤ r · q

·-monotoneʳ : p ≤ q → r · p ≤ r · q
·-monotoneʳ {p} {q} {r} p≤q = trans (·-congˡ p≤q) (·-distribˡ-∧ r p q)

-- Multiplication is a monotone function
-- If p ≤ p′ and q ≤ q′ then p · q ≤ p′ · q′

·-monotone : p ≤ p′ → q ≤ q′ → p · q ≤ p′ · q′
·-monotone p≤p′ q≤q′ = ≤-trans (·-monotoneˡ p≤p′) (·-monotoneʳ q≤q′)

opaque

  -- 𝟘 is a largest element if and only if 𝟙 ≤ 𝟘.

  ≤𝟘⇔𝟙≤𝟘 : (∀ {p} → p ≤ 𝟘) ⇔ 𝟙 ≤ 𝟘
  ≤𝟘⇔𝟙≤𝟘 =
      (λ ≤𝟘 → ≤𝟘)
    , (λ 𝟙≤𝟘 {p = p} → begin
         p      ≡˘⟨ ·-identityʳ _ ⟩
         p · 𝟙  ≤⟨ ·-monotoneʳ 𝟙≤𝟘 ⟩
         p · 𝟘  ≡⟨ ·-zeroʳ _ ⟩
         𝟘      ∎)
    where
    open Tools.Reasoning.PartialOrder ≤-poset

-- Multiplication by ω (from the left) is decreasing.

ω·-decreasing : ω · p ≤ p
ω·-decreasing {p = p} = begin
  ω · p  ≤⟨ ·-monotoneˡ ω≤𝟙 ⟩
  𝟙 · p  ≡⟨ ·-identityˡ _ ⟩
  p      ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- Multiplication by ω (from the right) is decreasing.

  ·ω-decreasing : p · ω ≤ p
  ·ω-decreasing {p = p} = begin
    p · ω  ≤⟨ ·-monotoneʳ ω≤𝟙 ⟩
    p · 𝟙  ≡⟨ ·-identityʳ _ ⟩
    p      ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

-- If the function p ·_ is injective, then it is order-reflecting.

·-order-reflectingˡ :
  (∀ q r → p · q ≡ p · r → q ≡ r) →
  p · q ≤ p · r → q ≤ r
·-order-reflectingˡ {p = p} {q = q} {r = r} inj =
  p · q ≤ p · r          →⟨ idᶠ ⟩
  p · q ≡ p · q ∧ p · r  →⟨ flip trans (sym (·-distribˡ-∧ _ _ _)) ⟩
  p · q ≡ p · (q ∧ r)    →⟨ inj _ _ ⟩
  q ≡ q ∧ r              →⟨ idᶠ ⟩
  q ≤ r                  □

-- If the function _· p is injective, then it is order-reflecting.

·-order-reflectingʳ :
  (∀ q r → q · p ≡ r · p → q ≡ r) →
  q · p ≤ r · p → q ≤ r
·-order-reflectingʳ {p = p} {q = q} {r = r} inj =
  q · p ≤ r · p          →⟨ idᶠ ⟩
  q · p ≡ q · p ∧ r · p  →⟨ flip trans (sym (·-distribʳ-∧ _ _ _)) ⟩
  q · p ≡ (q ∧ r) · p    →⟨ inj _ _ ⟩
  q ≡ q ∧ r              →⟨ idᶠ ⟩
  q ≤ r                  □

-- The operation _·_ is sub-interchangeable with _∧_ (with respect
-- to _≤_).

·-sub-interchangeable-∧ : _·_ SubInterchangeable _∧_ by _≤_
·-sub-interchangeable-∧ p q p′ q′ = begin
  (p ∧ q) · (p′ ∧ q′)                            ≈⟨ ·-distribˡ-∧ _ _ _ ⟩
  ((p ∧ q) · p′) ∧ ((p ∧ q) · q′)                ≈⟨ ∧-cong (·-distribʳ-∧ _ _ _) (·-distribʳ-∧ _ _ _) ⟩
  ((p · p′) ∧ (q · p′)) ∧ ((p · q′) ∧ (q · q′))  ≤⟨ ∧-monotone (∧-decreasingˡ _ _) (∧-decreasingʳ _ _) ⟩
  (p · p′) ∧ (q · q′)                            ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset
