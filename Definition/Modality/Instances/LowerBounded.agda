------------------------------------------------------------------------
-- A semiring with a global least element ∞ is a modality instance.
------------------------------------------------------------------------

open import Definition.Modality
open import Definition.Mode.Restrictions
open import Tools.Bool hiding (_∧_)

module Definition.Modality.Instances.LowerBounded
  {a} {M : Set a} (𝕄 : Semiring-with-meet M)
  (open Semiring-with-meet 𝕄)
  (∞ : M) (∞-min : (p : M) → ∞ ≤ p)
  (rs : Mode-restrictions)
  (open Mode-restrictions rs)
  (𝟘-well-behaved : T 𝟘ᵐ-allowed → Has-well-behaved-zero M 𝕄) where

open import Definition.Modality.Properties.Addition 𝕄
open import Definition.Modality.Properties.Meet 𝕄
open import Definition.Modality.Properties.Multiplication 𝕄
open import Definition.Modality.Properties.PartialOrder 𝕄

open import Tools.Algebra M
open import Tools.Product
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder

private variable
  p q r : M

_⊛_▷_ : Op₃ M
p ⊛ q ▷ r = ∞ · (p ∧ q)

+-IdempotentOn-∞ : _+_ IdempotentOn ∞
+-IdempotentOn-∞ = ≤-antisym (≤-trans (+-monotoneʳ (∞-min 𝟘))
                                      (≤-reflexive (+-identityʳ ∞)))
                             (∞-min (∞ + ∞))

⊛-ineq₁ : (p q r : M) → (p ⊛ q ▷ r) ≤ q + r · (p ⊛ q ▷ r)
⊛-ineq₁ p q r = begin
  p ⊛ q ▷ r ≡⟨⟩
  ∞ · (p ∧ q) ≈˘⟨ ·-congʳ +-IdempotentOn-∞ ⟩
  (∞ + ∞) · (p ∧ q) ≤⟨ ·-monotoneˡ (+-monotoneˡ (∞-min 𝟙)) ⟩
  (𝟙 + ∞) · (p ∧ q) ≈⟨ ·-distribʳ-+ (p ∧ q) 𝟙 ∞ ⟩
  𝟙 · (p ∧ q) + ∞ · (p ∧ q) ≈⟨ +-congʳ (·-identityˡ (p ∧ q)) ⟩
  (p ∧ q) + ∞ · (p ∧ q) ≤⟨ +-monotone (∧-decreasingʳ p q) (·-monotoneˡ (∞-min (r · ∞))) ⟩
  q + (r · ∞) · (p ∧ q) ≈⟨ +-congˡ (·-assoc r ∞ (p ∧ q)) ⟩
  q + r · (∞ · (p ∧ q)) ≡⟨⟩
  q + r · (p ⊛ q ▷ r) ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

⊛-ineq₂ : (p q r : M) → (p ⊛ q ▷ r) ≤ p
⊛-ineq₂ p q r = ≤-trans (·-monotone (∞-min 𝟙) (∧-decreasingˡ p q))
                        (≤-reflexive (·-identityˡ p))

+-sub-interchangeable-⊛ : (r : M) → _+_ SubInterchangeable _⊛_▷ r by _≤_
+-sub-interchangeable-⊛ r p q p′ q′ = begin
  (p ⊛ q ▷ r) + (p′ ⊛ q′ ▷ r) ≡⟨⟩
  ∞ · (p ∧ q) + ∞ · (p′ ∧ q′)
    ≈˘⟨ ·-distribˡ-+ ∞ _ _ ⟩
  ∞ · ((p ∧ q) + (p′ ∧ q′))
    ≈⟨ ·-congˡ (+-distribˡ-∧ (p ∧ q) p′ q′) ⟩
  ∞ · (((p ∧ q) + p′) ∧ ((p ∧ q) + q′))
    ≈⟨ ·-congˡ (∧-cong (+-distribʳ-∧ p′ p q) (+-distribʳ-∧ q′ p q)) ⟩
  ∞ · (((p + p′) ∧ (q + p′)) ∧ ((p + q′) ∧ (q + q′)))
    ≤⟨ ·-monotoneʳ (∧-monotone (∧-decreasingˡ _ _) (∧-decreasingʳ _ _)) ⟩
  ∞ · ((p + p′) ∧ (q + q′)) ≡⟨⟩
  (p + p′) ⊛ (q + q′) ▷ r ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

·-sub-distribʳ-⊛ : (r : M) → _·_ SubDistributesOverʳ _⊛_▷ r by _≤_
·-sub-distribʳ-⊛ r q p p′ = begin
  (p ⊛ p′ ▷ r) · q ≡⟨⟩
  (∞ · (p ∧ p′)) · q ≈⟨ ·-assoc ∞ (p ∧ p′) q ⟩
  ∞ · (p ∧ p′) · q ≈⟨ ·-congˡ (·-distribʳ-∧ q p p′) ⟩
  ∞ · (p · q ∧ p′ · q) ≡⟨⟩
  (p · q) ⊛ (p′ · q) ▷ r ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

⊛-sub-distribˡ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverˡ _∧_ by _≤_
⊛-sub-distribˡ-∧ r p q q′ = begin
  p ⊛ (q ∧ q′) ▷ r ≡⟨⟩
  ∞ · (p ∧ (q ∧ q′))
    ≈˘⟨ ·-congˡ (∧-congʳ (∧-idem p)) ⟩
  ∞ · ((p ∧ p) ∧ q ∧ q′)
    ≈˘⟨ ·-congˡ (∧-assoc (p ∧ p) q q′) ⟩
  ∞ · (((p ∧ p) ∧ q) ∧ q′)
    ≈⟨ ·-congˡ (∧-congʳ (∧-assoc p p q)) ⟩
  ∞ · ((p ∧ (p ∧ q)) ∧ q′)
    ≈⟨ ·-congˡ (∧-congʳ (∧-congˡ (∧-comm p q))) ⟩
  ∞ · ((p ∧ (q ∧ p)) ∧ q′)
    ≈˘⟨ ·-congˡ (∧-congʳ (∧-assoc p q p)) ⟩
  ∞ · (((p ∧ q) ∧ p) ∧ q′)
    ≈⟨ ·-congˡ (∧-assoc (p ∧ q) p q′) ⟩
  ∞ · ((p ∧ q) ∧ (p ∧ q′))
    ≈⟨ ·-distribˡ-∧ ∞ (p ∧ q) (p ∧ q′) ⟩
  ∞ · (p ∧ q) ∧ ∞ · (p ∧ q′) ≡⟨⟩
  (p ⊛ q ▷ r) ∧ (p ⊛ q′ ▷ r) ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

⊛-sub-distribʳ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverʳ _∧_ by _≤_
⊛-sub-distribʳ-∧ r q p p′ = begin
  (p ∧ p′) ⊛ q ▷ r ≡⟨⟩
  ∞ · ((p ∧ p′) ∧ q) ≈˘⟨ ·-congˡ (∧-congˡ (∧-idem q)) ⟩
  ∞ · ((p ∧ p′) ∧ q ∧ q) ≈˘⟨ ·-congˡ (∧-assoc (p ∧ p′) q q) ⟩
  ∞ · (((p ∧ p′) ∧ q) ∧ q) ≈⟨ ·-congˡ (∧-congʳ (∧-assoc p p′ q)) ⟩
  ∞ · ((p ∧ p′ ∧ q) ∧ q) ≈⟨ ·-congˡ (∧-congʳ (∧-congˡ (∧-comm p′ q))) ⟩
  ∞ · ((p ∧ q ∧ p′) ∧ q) ≈˘⟨ ·-congˡ (∧-congʳ (∧-assoc p q p′)) ⟩
  ∞ · (((p ∧ q) ∧ p′) ∧ q) ≈⟨ ·-congˡ (∧-assoc (p ∧ q) p′ q) ⟩
  ∞ · ((p ∧ q) ∧ (p′ ∧ q)) ≈⟨ ·-distribˡ-∧ ∞ (p ∧ q) (p′ ∧ q) ⟩
  ∞ · (p ∧ q) ∧ ∞ · (p′ ∧ q) ≡⟨⟩
  (p ⊛ q ▷ r) ∧ (p′ ⊛ q ▷ r) ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset

is-semiring-with-meet-and-star : Semiring-with-meet-and-star M
is-semiring-with-meet-and-star = record
  { semiring-with-meet = 𝕄
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
  ; +-sub-interchangeable-⊛ = +-sub-interchangeable-⊛
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
  }

isModality : Modality M
isModality = record
  { semiring-with-meet-and-star = is-semiring-with-meet-and-star
  ; mode-restrictions = rs
  ; 𝟘-well-behaved = 𝟘-well-behaved
  }
