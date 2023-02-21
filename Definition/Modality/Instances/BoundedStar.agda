open import Tools.Relation
open import Definition.Modality
import Tools.Algebra as A
open import Tools.Sum

-- A star-ringoid with a unary operator _* satisfying
-- p * ≈ 𝟙 + p p*
-- and p* ≤ 𝟘 or p* ≤ 𝟙 for all p is a modality instance.

module Definition.Modality.Instances.BoundedStar
  {a ℓ} {M′ : Setoid a ℓ} (𝕄 : ModalityWithout⊛ M′)
  (_* : A.Op₁ (Setoid.Carrier M′))
  (*-rec : (p : Setoid.Carrier M′)
         → (Setoid._≈_ M′ (p *) (ModalityWithout⊛._+_ 𝕄 (ModalityWithout⊛.𝟙 𝕄) (ModalityWithout⊛._·_ 𝕄 p (p *)))))
  (*-cong : {p p′ : Setoid.Carrier M′} → Setoid._≈_ M′ p p′ → Setoid._≈_ M′ (p *) (p′ *))
  (bounds : (p : Setoid.Carrier M′) → ModalityWithout⊛._≤_ 𝕄 (p *) (ModalityWithout⊛.𝟘 𝕄)
                                    ⊎ ModalityWithout⊛._≤_ 𝕄 (p *) (ModalityWithout⊛.𝟙 𝕄)) where

open Setoid M′ renaming (Carrier to M)
open ModalityWithout⊛ 𝕄

open import Definition.Modality.Properties.Equivalence 𝕄
open import Definition.Modality.Properties.PartialOrder 𝕄
open import Definition.Modality.Properties.Addition 𝕄
open import Definition.Modality.Properties.Meet 𝕄
open import Definition.Modality.Properties.Multiplication 𝕄

open import Tools.Function
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.Algebra M′

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

⊛-cong : p ≈ p′ → q ≈ q′ → r ≈ r′ → p ⊛ q ▷ r ≈ p′ ⊛ q′ ▷ r′
⊛-cong p≈p′ q≈q′ r≈r′ = ·-cong (*-cong r≈r′) (∧-cong p≈p′ q≈q′)

+-sub-interchangable-⊛ : (r : M) → _+_ SubInterchangable _⊛_▷ r by _≤_
+-sub-interchangable-⊛ r p q p′ q′ = begin
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

⊛≤𝟘ˡ : p ⊛ q ▷ r ≈ 𝟘 → p ≤ 𝟘
⊛≤𝟘ˡ {p = p} {q = q} {r = r} p⊛q▷r≈𝟘 =
  case zero-product r*p≈𝟘 of λ where
    (inj₂ p≈𝟘)  → ≤-reflexive p≈𝟘
    (inj₁ r*≈𝟘) → ≈-trivial (positiveˡ (begin
      𝟙 + r · (r *)  ≈˘⟨ *-rec _ ⟩
      (r *)          ≈⟨ r*≈𝟘 ⟩
      𝟘              ∎))
  where
  open Tools.Reasoning.Equivalence M′

  r*p≈𝟘 : (r *) · p ≈ 𝟘
  r*p≈𝟘 = ∧≈𝟘ˡ (begin
    (r *) · p ∧ (r *) · q  ≈˘⟨ ·-distribˡ-∧ _ _ _ ⟩
    (r *) · (p ∧ q)        ≡⟨⟩
    p ⊛ q ▷ r              ≈⟨ p⊛q▷r≈𝟘 ⟩
    𝟘                      ∎)

⊛≤𝟘ʳ : p ⊛ q ▷ r ≈ 𝟘 → q ≤ 𝟘
⊛≤𝟘ʳ {p = p} {q = q} {r = r} p⊛q▷r≈𝟘 = ⊛≤𝟘ˡ (begin
  q ⊛ p ▷ r        ≡⟨⟩
  (r *) · (q ∧ p)  ≈⟨ ·-congˡ (∧-comm _ _) ⟩
  (r *) · (p ∧ q)  ≡⟨⟩
  p ⊛ q ▷ r        ≈⟨ p⊛q▷r≈𝟘 ⟩
  𝟘                ∎)
  where
  open Tools.Reasoning.Equivalence M′

isModality : Modality M′
isModality = record
  { modalityWithout⊛ = 𝕄
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
  ; ⊛-cong = ⊛-cong
  ; +-sub-interchangable-⊛ = +-sub-interchangable-⊛
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
  ; ⊛≤𝟘ˡ = ⊛≤𝟘ˡ
  ; ⊛≤𝟘ʳ = ⊛≤𝟘ʳ
  }
