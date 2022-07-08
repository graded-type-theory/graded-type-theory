{-# OPTIONS --without-K --safe #-}

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

open import Definition.Modality.Properties.PartialOrder 𝕄
open import Definition.Modality.Properties.Addition 𝕄
open import Definition.Modality.Properties.Meet 𝕄
open import Definition.Modality.Properties.Multiplication 𝕄


open import Tools.Reasoning.PartialOrder ≤-poset
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
     ≈⟨ ·-cong (*-rec r) ≈-refl ⟩
  (𝟙 + r · (r *)) · (p ∧ q)
     ≈⟨ proj₂ ·-distrib-+ (p ∧ q) 𝟙 (r · (r *)) ⟩
  𝟙 · (p ∧ q) + (r · (r *)) · (p ∧ q)
    ≈⟨ +-cong (proj₁ ·-identity (p ∧ q)) (·-assoc r (r *) (p ∧ q)) ⟩
  (p ∧ q) + r · ((r *) · (p ∧ q))
     ≤⟨ +-monotoneˡ (∧-decreasingʳ p q) ⟩
  q + r · (p ⊛ q ▷ r) ∎

⊛-ineq₂ : (p q r : M) → p ⊛ q ▷ r ≤ p
⊛-ineq₂ p q r with bounds r
... | inj₁ r*≤𝟘 = begin
  p ⊛ q ▷ r ≈⟨⟩
  (r *) · (p ∧ q)         ≤⟨ ·-monotoneʳ (∧-decreasingˡ p q) ⟩
  (r *) · p               ≈⟨ ·-cong (*-rec r) ≈-refl ⟩
  (𝟙 + r · (r *)) · p     ≈⟨ proj₂ ·-distrib-+ p 𝟙 _ ⟩
  𝟙 · p + (r · (r *)) · p ≈⟨ +-cong (proj₁ ·-identity p) ≈-refl ⟩
  p + (r · (r *)) · p     ≤⟨ +-monotoneʳ (·-monotoneˡ (·-monotoneʳ r*≤𝟘)) ⟩
  p + (r · 𝟘) · p         ≈⟨ +-cong ≈-refl (·-cong (proj₂ ·-zero r) ≈-refl) ⟩
  p + 𝟘 · p               ≈⟨ +-cong ≈-refl (proj₁ ·-zero p) ⟩
  p + 𝟘                   ≈⟨ proj₂ +-identity p ⟩
  p ∎
... | inj₂ r*≤𝟙 = begin
  (r *) · (p ∧ q) ≤⟨ ·-monotone r*≤𝟙 (∧-decreasingˡ p q) ⟩
  𝟙 · p           ≈⟨ proj₁ ·-identity p ⟩
  p ∎

⊛-cong : p ≈ p′ → q ≈ q′ → r ≈ r′ → p ⊛ q ▷ r ≈ p′ ⊛ q′ ▷ r′
⊛-cong p≈p′ q≈q′ r≈r′ = ·-cong (*-cong r≈r′) (∧-cong p≈p′ q≈q′)

+-sub-interchangable-⊛ : (r : M) → _+_ SubInterchangable _⊛_▷ r by _≤_
+-sub-interchangable-⊛ r p q p′ q′ = begin
  (p ⊛ q ▷ r) + (p′ ⊛ q′ ▷ r) ≡⟨⟩
  (r *) · (p ∧ q) + (r *) · (p′ ∧ q′)
     ≈˘⟨ proj₁ ·-distrib-+ (r *) _ _ ⟩
  (r *) · ((p ∧ q) + (p′ ∧ q′))
     ≈⟨ ·-cong ≈-refl (proj₁ +-distrib-∧ (p ∧ q) p′ q′) ⟩
  (r *) · (((p ∧ q) + p′) ∧ ((p ∧ q) + q′))
     ≈⟨ ·-cong ≈-refl (∧-cong (proj₂ +-distrib-∧ p′ p q) (proj₂ +-distrib-∧ q′ p q)) ⟩
  (r *) · (((p + p′) ∧ (q + p′)) ∧ ((p + q′) ∧ (q + q′)))
     ≤⟨ ·-monotoneʳ (∧-monotone (∧-decreasingˡ _ _) (∧-decreasingʳ _ _)) ⟩
  (r *) · ((p + p′) ∧ (q + q′)) ≡⟨⟩
  (p + p′) ⊛ (q + q′) ▷ r ∎

·-sub-distribʳ-⊛ : (r : M) → _·_ SubDistributesOverʳ _⊛_▷ r by _≤_
·-sub-distribʳ-⊛ r q p p′ = begin
  (p ⊛ p′ ▷ r) · q ≡⟨⟩
  ((r *) · (p ∧ p′)) · q ≈⟨ ·-assoc (r *) (p ∧ p′) q ⟩
  (r *) · (p ∧ p′) · q ≈⟨ ·-cong ≈-refl (proj₂ ·-distrib-∧ q p p′) ⟩
  (r *) · (p · q ∧ p′ · q) ≡⟨⟩
  (p · q) ⊛ (p′ · q) ▷ r ∎

⊛-sub-distribˡ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverˡ _∧_ by _≤_
⊛-sub-distribˡ-∧ r p q q′ = begin
  p ⊛ (q ∧ q′) ▷ r ≡⟨⟩
  (r *) · (p ∧ (q ∧ q′))
     ≈˘⟨ ·-cong ≈-refl (∧-cong (∧-idem p) ≈-refl) ⟩
  (r *) · ((p ∧ p) ∧ q ∧ q′)
     ≈˘⟨ ·-cong ≈-refl (∧-assoc (p ∧ p) q q′) ⟩
  (r *) · (((p ∧ p) ∧ q) ∧ q′)
     ≈⟨ ·-cong ≈-refl (∧-cong (∧-assoc p p q) ≈-refl) ⟩
  (r *) · ((p ∧ (p ∧ q)) ∧ q′)
     ≈⟨ ·-cong ≈-refl (∧-cong (∧-cong ≈-refl (∧-comm p q)) ≈-refl) ⟩
  (r *) · ((p ∧ (q ∧ p)) ∧ q′)
     ≈˘⟨ ·-cong ≈-refl (∧-cong (∧-assoc p q p) ≈-refl) ⟩
  (r *) · (((p ∧ q) ∧ p) ∧ q′)
     ≈⟨ ·-cong ≈-refl (∧-assoc (p ∧ q) p q′) ⟩
  (r *) · ((p ∧ q) ∧ (p ∧ q′))
     ≈⟨ proj₁ ·-distrib-∧ (r *) (p ∧ q) (p ∧ q′) ⟩
  (r *) · (p ∧ q) ∧ (r *) · (p ∧ q′) ≡⟨⟩
  (p ⊛ q ▷ r) ∧ (p ⊛ q′ ▷ r) ∎

⊛-sub-distribʳ-∧ : (r : M) → (_⊛_▷ r) SubDistributesOverʳ _∧_ by _≤_
⊛-sub-distribʳ-∧ r q p p′ = begin
  (p ∧ p′) ⊛ q ▷ r ≡⟨⟩
  (r *) · ((p ∧ p′) ∧ q) ≈˘⟨ ·-cong ≈-refl (∧-cong ≈-refl (∧-idem q)) ⟩
  (r *) · ((p ∧ p′) ∧ q ∧ q) ≈˘⟨ ·-cong ≈-refl (∧-assoc (p ∧ p′) q q) ⟩
  (r *) · (((p ∧ p′) ∧ q) ∧ q) ≈⟨ ·-cong ≈-refl (∧-cong (∧-assoc p p′ q) ≈-refl) ⟩
  (r *) · ((p ∧ p′ ∧ q) ∧ q) ≈⟨ ·-cong ≈-refl (∧-cong (∧-cong ≈-refl (∧-comm p′ q)) ≈-refl) ⟩
  (r *) · ((p ∧ q ∧ p′) ∧ q) ≈˘⟨ ·-cong ≈-refl (∧-cong (∧-assoc p q p′) ≈-refl) ⟩
  (r *) · (((p ∧ q) ∧ p′) ∧ q) ≈⟨ ·-cong ≈-refl (∧-assoc (p ∧ q) p′ q) ⟩
  (r *) · ((p ∧ q) ∧ (p′ ∧ q)) ≈⟨ proj₁ ·-distrib-∧ (r *) (p ∧ q) (p′ ∧ q) ⟩
  (r *) · (p ∧ q) ∧ (r *) · (p′ ∧ q) ≡⟨⟩
  (p ⊛ q ▷ r) ∧ (p′ ⊛ q ▷ r) ∎

isModality : Modality M′
isModality = record
  { modalityWithout⊛ = 𝕄
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
  ; ⊛-cong = ⊛-cong
  ; +-sub-interchangable-⊛ = +-sub-interchangable-⊛
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
  }
