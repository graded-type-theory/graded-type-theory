------------------------------------------------------------------------
-- Properties of multiplication.
------------------------------------------------------------------------

open import Definition.Modality

module Definition.Modality.Properties.Multiplication
  {a} {M : Set a} (𝕄 : Semiring-with-meet M) where

open Semiring-with-meet 𝕄

open import Definition.Modality.Properties.Meet 𝕄
open import Definition.Modality.Properties.PartialOrder 𝕄

open import Tools.Algebra M
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder


private
  variable
    p p′ q q′ r r′ : M

-- Multiplication on the left is a monotone function
-- If p ≤ q then p · r ≤ q · r

·-monotoneˡ : p ≤ q → p · r ≤ q · r
·-monotoneˡ {p} {q} {r} p≤q = ≈-trans (·-congʳ p≤q) (·-distribʳ-∧ r p q)

-- Multiplication on the right is a monotone function
-- If p ≤ q then r · p ≤ r · q

·-monotoneʳ : p ≤ q → r · p ≤ r · q
·-monotoneʳ {p} {q} {r} p≤q = ≈-trans (·-congˡ p≤q) (·-distribˡ-∧ r p q)

-- Multiplication is a monotone function
-- If p ≤ p′ and q ≤ q′ then p · q ≤ p′ · q′

·-monotone : p ≤ p′ → q ≤ q′ → p · q ≤ p′ · q′
·-monotone p≤p′ q≤q′ = ≤-trans (·-monotoneˡ p≤p′) (·-monotoneʳ q≤q′)

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
