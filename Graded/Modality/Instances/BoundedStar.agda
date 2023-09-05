------------------------------------------------------------------------
-- A natrec-star operator can be defined for a "semiring with meet"
-- with a unary operator _* which satisfies p * ≡ 𝟙 + p p*, and p* ≤ 𝟘
-- or p* ≤ 𝟙, for all p
------------------------------------------------------------------------

import Graded.Modality
import Tools.Algebra as A
open import Tools.PropositionalEquality
open import Tools.Sum
open import Tools.Bool hiding (_∧_)

module Graded.Modality.Instances.BoundedStar
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Semiring-with-meet)
  (open Semiring-with-meet 𝕄)
  (_* : A.Op₁ M)
  (*-rec : (p : M) → ((p *) ≡ 𝟙 + p · (p *)))
  (bounds : (p : M) → (p *) ≤ 𝟘 ⊎ (p *) ≤ 𝟙)
  where

open import Graded.Modality.Properties.PartialOrder 𝕄
open import Graded.Modality.Properties.Addition 𝕄
open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.Multiplication 𝕄
import Graded.Modality.Properties.Star 𝕄 as Star
open import Graded.Modality.Variant a

open import Tools.Nullary
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.Algebra M

private
  variable
    p p′ q q′ r r′ : M


_⊛_▷_ : Op₃ M
p ⊛ q ▷ r = (r *) · (p ∧ q)

⊛-ineq₁ : (p q r : M) → (p ⊛ q ▷ r) ≤ q + r · (p ⊛ q ▷ r)
⊛-ineq₁ p q r = begin
  p ⊛ q ▷ r ≡⟨⟩
  (r *) · (p ∧ q)
     ≈⟨ ·-congʳ (*-rec r) ⟩
  (𝟙 + r · (r *)) · (p ∧ q)
     ≈⟨ ·-distribʳ-+ (p ∧ q) 𝟙 (r · (r *)) ⟩
  𝟙 · (p ∧ q) + (r · (r *)) · (p ∧ q)
    ≈⟨ +-cong (·-identityˡ (p ∧ q)) (·-assoc r (r *) (p ∧ q)) ⟩
  (p ∧ q) + r · ((r *) · (p ∧ q))
     ≤⟨ +-monotoneˡ (∧-decreasingʳ p q) ⟩
  q + r · (p ⊛ q ▷ r) ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

⊛-ineq₂ : (p q r : M) → p ⊛ q ▷ r ≤ p
⊛-ineq₂ p q r with bounds r
... | inj₁ r*≤𝟘 = begin
  p ⊛ q ▷ r ≈⟨⟩
  (r *) · (p ∧ q)         ≤⟨ ·-monotoneʳ (∧-decreasingˡ p q) ⟩
  (r *) · p               ≈⟨ ·-congʳ (*-rec r) ⟩
  (𝟙 + r · (r *)) · p     ≈⟨ ·-distribʳ-+ p 𝟙 _ ⟩
  𝟙 · p + (r · (r *)) · p ≈⟨ +-congʳ (·-identityˡ p) ⟩
  p + (r · (r *)) · p     ≤⟨ +-monotoneʳ (·-monotoneˡ (·-monotoneʳ r*≤𝟘)) ⟩
  p + (r · 𝟘) · p         ≈⟨ +-congˡ (·-congʳ (·-zeroʳ r)) ⟩
  p + 𝟘 · p               ≈⟨ +-congˡ (·-zeroˡ p) ⟩
  p + 𝟘                   ≈⟨ +-identityʳ p ⟩
  p ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset
... | inj₂ r*≤𝟙 = begin
  (r *) · (p ∧ q) ≤⟨ ·-monotone r*≤𝟙 (∧-decreasingˡ p q) ⟩
  𝟙 · p           ≈⟨ ·-identityˡ p ⟩
  p ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

⊛-cong : p ≡ p′ → q ≡ q′ → r ≡ r′ → p ⊛ q ▷ r ≡ p′ ⊛ q′ ▷ r′
⊛-cong p≡p′ q≡q′ r≡r′ = ·-cong (cong _* r≡r′) (∧-cong p≡p′ q≡q′)

+-sub-interchangeable-⊛ : (r : M) → _+_ SubInterchangeable _⊛_▷ r by _≤_
+-sub-interchangeable-⊛ r p q p′ q′ = begin
  (p ⊛ q ▷ r) + (p′ ⊛ q′ ▷ r) ≡⟨⟩
  (r *) · (p ∧ q) + (r *) · (p′ ∧ q′)
     ≈˘⟨ ·-distribˡ-+ (r *) _ _ ⟩
  (r *) · ((p ∧ q) + (p′ ∧ q′))
     ≈⟨ ·-congˡ (+-distribˡ-∧ (p ∧ q) p′ q′) ⟩
  (r *) · (((p ∧ q) + p′) ∧ ((p ∧ q) + q′))
     ≈⟨ ·-congˡ (∧-cong (+-distribʳ-∧ p′ p q) (+-distribʳ-∧ q′ p q)) ⟩
  (r *) · (((p + p′) ∧ (q + p′)) ∧ ((p + q′) ∧ (q + q′)))
     ≤⟨ ·-monotoneʳ (∧-monotone (∧-decreasingˡ _ _) (∧-decreasingʳ _ _)) ⟩
  (r *) · ((p + p′) ∧ (q + q′)) ≡⟨⟩
  (p + p′) ⊛ (q + q′) ▷ r ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

·-sub-distribʳ-⊛ : (r : M) → _·_ SubDistributesOverʳ _⊛_▷ r by _≤_
·-sub-distribʳ-⊛ r q p p′ = begin
  (p ⊛ p′ ▷ r) · q ≡⟨⟩
  ((r *) · (p ∧ p′)) · q ≈⟨ ·-assoc (r *) (p ∧ p′) q ⟩
  (r *) · (p ∧ p′) · q ≈⟨ ·-congˡ (·-distribʳ-∧ q p p′) ⟩
  (r *) · (p · q ∧ p′ · q) ≡⟨⟩
  (p · q) ⊛ (p′ · q) ▷ r ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

⊛-sub-distribˡ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverˡ _∧_ by _≤_
⊛-sub-distribˡ-∧ r p q q′ = begin
  p ⊛ (q ∧ q′) ▷ r ≡⟨⟩
  (r *) · (p ∧ (q ∧ q′))
     ≈˘⟨ ·-congˡ (∧-congʳ (∧-idem p)) ⟩
  (r *) · ((p ∧ p) ∧ q ∧ q′)
     ≈˘⟨ ·-congˡ (∧-assoc (p ∧ p) q q′) ⟩
  (r *) · (((p ∧ p) ∧ q) ∧ q′)
     ≈⟨ ·-congˡ (∧-congʳ (∧-assoc p p q)) ⟩
  (r *) · ((p ∧ (p ∧ q)) ∧ q′)
     ≈⟨ ·-congˡ (∧-congʳ (∧-congˡ (∧-comm p q))) ⟩
  (r *) · ((p ∧ (q ∧ p)) ∧ q′)
     ≈˘⟨ ·-congˡ (∧-congʳ (∧-assoc p q p)) ⟩
  (r *) · (((p ∧ q) ∧ p) ∧ q′)
     ≈⟨ ·-congˡ (∧-assoc (p ∧ q) p q′) ⟩
  (r *) · ((p ∧ q) ∧ (p ∧ q′))
     ≈⟨ ·-distribˡ-∧ (r *) (p ∧ q) (p ∧ q′) ⟩
  (r *) · (p ∧ q) ∧ (r *) · (p ∧ q′) ≡⟨⟩
  (p ⊛ q ▷ r) ∧ (p ⊛ q′ ▷ r) ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

⊛-sub-distribʳ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverʳ _∧_ by _≤_
⊛-sub-distribʳ-∧ r q p p′ = begin
  (p ∧ p′) ⊛ q ▷ r ≡⟨⟩
  (r *) · ((p ∧ p′) ∧ q) ≈˘⟨ ·-congˡ (∧-congˡ (∧-idem q)) ⟩
  (r *) · ((p ∧ p′) ∧ q ∧ q) ≈˘⟨ ·-congˡ (∧-assoc (p ∧ p′) q q) ⟩
  (r *) · (((p ∧ p′) ∧ q) ∧ q) ≈⟨ ·-congˡ (∧-congʳ (∧-assoc p p′ q)) ⟩
  (r *) · ((p ∧ p′ ∧ q) ∧ q) ≈⟨ ·-congˡ (∧-congʳ (∧-congˡ (∧-comm p′ q))) ⟩
  (r *) · ((p ∧ q ∧ p′) ∧ q) ≈˘⟨ ·-congˡ (∧-congʳ (∧-assoc p q p′)) ⟩
  (r *) · (((p ∧ q) ∧ p′) ∧ q) ≈⟨ ·-congˡ (∧-assoc (p ∧ q) p′ q) ⟩
  (r *) · ((p ∧ q) ∧ (p′ ∧ q)) ≈⟨ ·-distribˡ-∧ (r *) (p ∧ q) (p′ ∧ q) ⟩
  (r *) · (p ∧ q) ∧ (r *) · (p′ ∧ q) ≡⟨⟩
  (p ⊛ q ▷ r) ∧ (p′ ⊛ q ▷ r) ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

has-star : Has-star 𝕄
has-star = record
  { _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
  ; +-sub-interchangeable-⊛ = +-sub-interchangeable-⊛
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
  }

-- If certain properties hold, then 𝕄 can be turned into a certain
-- kind of modality.

isModality :
  (variant : Modality-variant) →
  let open Modality-variant variant in
  (T 𝟘ᵐ-allowed → Has-well-behaved-zero 𝕄) →
  (T 𝟘ᵐ-allowed → ¬ Nr-available → ∀ p q → p + q ≤ p) →
  Modality
isModality variant 𝟘-well-behaved +-decreasingˡ = record
  { variant            = variant
  ; semiring-with-meet = 𝕄
  ; 𝟘-well-behaved     = 𝟘-well-behaved
  ; has-nr             = λ _ → Star.has-nr ⦃ has-star = has-star ⦄
  ; +-decreasingˡ      = +-decreasingˡ
  }

-- For an instance with a least element the solution given by _⊛_▷_ is
-- (pointwise) greater than or equal to the one defined in
-- Graded.Modality.Instances.LowerBounded.

module LowerBounded (∞ : M) (∞-min : (p : M) → ∞ ≤ p) where
  open import Graded.Modality.Instances.LowerBounded 𝕄 ∞ ∞-min
    using () renaming (_⊛_▷_ to _⊛′_▷_)

  ⊛′≤⊛ : (p q r : M) → p ⊛′ q ▷ r ≤ p ⊛ q ▷ r
  ⊛′≤⊛ p q r = ·-monotoneˡ (∞-min (r *))
