open import Definition.Modality

-- A ringoid with a global least element ∞ is a modality instance.

module Definition.Modality.Instances.LowerBounded
  {a} {M : Set a} (𝕄 : ModalityWithout⊛ M)
  (∞ : M) (∞-min : (p : M) → ModalityWithout⊛._≤_ 𝕄 ∞ p) where

open ModalityWithout⊛ 𝕄

open import Definition.Modality.Properties.Addition 𝕄
open import Definition.Modality.Properties.Meet 𝕄
open import Definition.Modality.Properties.Multiplication 𝕄
open import Definition.Modality.Properties.PartialOrder 𝕄

open import Tools.Algebra M
open import Tools.Product
open import Tools.PropositionalEquality using (_≈_; setoid)
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
open import Tools.Sum

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

+-sub-interchangable-⊛ : (r : M) → _+_ SubInterchangable _⊛_▷ r by _≤_
+-sub-interchangable-⊛ r p q p′ q′ = begin
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

⊛≤𝟘ˡ : ∀ r → p ⊛ q ▷ r ≈ 𝟘 → p ≤ 𝟘
⊛≤𝟘ˡ {p = p} {q = q} r p⊛q▷r≈𝟘 with zero-product p⊛q▷r≈𝟘
… | inj₂ p∧q≈𝟘 = ∧≤𝟘ˡ p∧q≈𝟘
… | inj₁ ∞≈𝟘   = ≤-reflexive (𝟘≮ (begin
  𝟘  ≈˘⟨ ∞≈𝟘 ⟩
  ∞  ≤⟨ ∞-min _ ⟩
  p  ∎))
  where
  open Tools.Reasoning.PartialOrder ≤-poset

⊛≤𝟘ʳ : ∀ r → p ⊛ q ▷ r ≈ 𝟘 → q ≤ 𝟘
⊛≤𝟘ʳ {p = p} {q = q} r p⊛q▷r≈𝟘 = ⊛≤𝟘ˡ r (begin
  q ⊛ p ▷ r    ≡⟨⟩
  ∞ · (q ∧ p)  ≈⟨ ·-congˡ (∧-comm _ _) ⟩
  ∞ · (p ∧ q)  ≡⟨⟩
  p ⊛ q ▷ r    ≈⟨ p⊛q▷r≈𝟘 ⟩
  𝟘            ∎)
  where
  open Tools.Reasoning.Equivalence (setoid M)

isModality : Modality M
isModality = record
  { modalityWithout⊛ = 𝕄
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
  ; +-sub-interchangable-⊛ = +-sub-interchangable-⊛
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
  ; ⊛≤𝟘ˡ = λ {_ _ r} → ⊛≤𝟘ˡ r
  ; ⊛≤𝟘ʳ = λ {_ _ r} → ⊛≤𝟘ʳ r
  }
