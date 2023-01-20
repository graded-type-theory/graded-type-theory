{-# OPTIONS --without-K --safe #-}

import Tools.Algebra as A
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.Relation
open import Definition.Modality renaming (ModalityWithout⊛ to MW⊛)

-- A ringoid with the following recursively defined nr operator is a modality instance.
-- nr 0 p q r = 𝟘
-- nr (1+ n) p q r = p ∧ (q + r nr n p q r)
-- ∃ n → nr (1+ n) p q r ≈ nr n p q r

module Definition.Modality.Instances.Recursive
  {a ℓ} {M′ : Setoid a ℓ} (𝕄 : MW⊛ M′)
  (nr : Nat → A.Op₃ M′ (Setoid.Carrier M′))
  (nr-rec : (n : Nat) (p q r : Setoid.Carrier M′)
          → Setoid._≈_ M′ (nr (1+ n) p q r)
                       (MW⊛._∧_ 𝕄 p (MW⊛._+_ 𝕄 q (MW⊛._·_ 𝕄 r (nr n p q r)))))
  (nr-0 : (p q r : Setoid.Carrier M′) → Setoid._≈_ M′ (nr 0 p q r) (MW⊛.𝟘 𝕄))
  (nr-fix : ∃ λ n → (p q r : Setoid.Carrier M′) → Setoid._≈_ M′ (nr (1+ n) p q r) (nr n p q r) ) where

open Setoid M′ renaming (Carrier to M)
open MW⊛ 𝕄

open import Definition.Modality.Properties.Addition 𝕄
open import Definition.Modality.Properties.Meet 𝕄
open import Definition.Modality.Properties.Multiplication 𝕄
open import Definition.Modality.Properties.PartialOrder 𝕄
open import Tools.Algebra M′

_⊛_▷_ : Op₃ M
_⊛_▷_ = nr (proj₁ nr-fix)

solvesIneqs : ((p q r : M) → (p ⊛ q ▷ r) ≤ q + r · (p ⊛ q ▷ r)) ×
              ((p q r : M) → (p ⊛ q ▷ r) ≤ p)
solvesIneqs =
  let n , fix = nr-fix
  in  (λ p q r → ≤-trans (≤-reflexive (trans (sym (fix p q r)) (nr-rec n p q r))) (∧-decreasingʳ p _))
    , (λ p q r → ≤-trans (≤-reflexive (trans (sym (fix p q r)) (nr-rec n p q r))) (∧-decreasingˡ p _))

nr-cong : {p p′ q q′ r r′ : M} → (n : Nat) → p ≈ p′ → q ≈ q′ → r ≈ r′ → nr n p q r ≈ nr n p′ q′ r′
nr-cong 0 p≈p′ q≈q′ r≈r′ = trans (nr-0 _ _ _) (sym (nr-0 _ _ _))
nr-cong {p} {p′} {q} {q′} {r} {r′} (1+ n) p≈p′ q≈q′ r≈r′ = begin
  nr (1+ n) p q r              ≈⟨ nr-rec n p q r ⟩
  p ∧ q + r · nr n p q r       ≈⟨ ∧-cong p≈p′ (+-cong q≈q′ (·-cong r≈r′ (nr-cong n p≈p′ q≈q′ r≈r′))) ⟩
  p′ ∧ q′ + r′ · nr n p′ q′ r′ ≈˘⟨ nr-rec n p′ q′ r′ ⟩
  nr (1+ n) p′ q′ r′ ∎
  where open import Tools.Reasoning.Equivalence M′

open import Tools.Reasoning.PartialOrder ≤-poset

+-sub-interchangable-nr : (n : Nat) (r : M) → _+_ SubInterchangable (λ p q → nr n p q r) by _≤_
+-sub-interchangable-nr 0 r p q p′ q′ = begin
  nr 0 p q r + nr 0 p′ q′ r ≈⟨ +-cong (nr-0 p q r) (nr-0 p′ q′ r) ⟩
  𝟘 + 𝟘                     ≈⟨ +-identityˡ 𝟘 ⟩
  𝟘                         ≈˘⟨ nr-0 (p + p′) (q + q′) r ⟩
  nr 0 (p + p′) (q + q′) r ∎
+-sub-interchangable-nr (1+ n) r p q p′ q′ = begin
  nr (1+ n) p q r + nr (1+ n) p′ q′ r
    ≈⟨ +-cong (nr-rec n p q r) (nr-rec n p′ q′ r) ⟩
  (p ∧ (q + r · nr n p q r)) + (p′ ∧ (q′ + r · nr n p′ q′ r))
    ≈⟨ +-distribʳ-∧ _ _ _ ⟩
  (p + (p′ ∧ (q′ + r · nr n p′ q′ r))) ∧ ((q + r · nr n p q r) + (p′ ∧ (q′ + r · nr n p′ q′ r)))
    ≈⟨ ∧-cong (+-distribˡ-∧ _ _ _) (+-distribˡ-∧ _ _ _) ⟩
  ((p + p′) ∧ (p + (q′ + r · nr n p′ q′ r))) ∧ (((q + r · nr n p q r) + p′)
    ∧ ((q + r · nr n p q r) + (q′ + r · nr n p′ q′ r)))
    ≤⟨ ∧-monotone (∧-decreasingˡ _ _) (∧-decreasingʳ _ _) ⟩
  (p + p′) ∧ (q + r · nr n p q r) + q′ + r · nr n p′ q′ r
    ≈⟨ ∧-congˡ (+-assoc _ _ _) ⟩
  (p + p′) ∧ (q + r · nr n p q r + q′ + r · nr n p′ q′ r)
    ≈˘⟨ ∧-congˡ (+-congˡ (+-assoc _ _ _)) ⟩
  (p + p′) ∧ (q + (r · nr n p q r + q′) + r · nr n p′ q′ r)
    ≈⟨ ∧-congˡ  (+-congˡ (+-congʳ (+-comm _ _))) ⟩
  (p + p′) ∧ (q + (q′ + r · nr n p q r) + r · nr n p′ q′ r)
    ≈⟨ ∧-congˡ (+-congˡ (+-assoc _ _ _)) ⟩
  (p + p′) ∧ (q + q′ + r · nr n p q r + r · nr n p′ q′ r)
    ≈˘⟨ ∧-congˡ (+-assoc _ _ _) ⟩
  (p + p′) ∧ ((q + q′) + (r · nr n p q r + r · nr n p′ q′ r))
    ≈˘⟨ ∧-congˡ (+-congˡ (·-distribˡ-+ _ _ _)) ⟩
  (p + p′) ∧ ((q + q′) + (r · (nr n p q r + nr n p′ q′ r)))
    ≤⟨ ∧-monotoneʳ (+-monotoneʳ (·-monotoneʳ (+-sub-interchangable-nr n r p q p′ q′))) ⟩
  (p + p′) ∧ ((q + q′) + (r · nr n (p + p′) (q + q′) r))
    ≈˘⟨ nr-rec n (p + p′) (q + q′) r ⟩
  nr (1+ n) (p + p′) (q + q′) r ∎

·-sub-distribʳ-nr : (n : Nat) (r : M) → _·_ SubDistributesOverʳ (λ p q → nr n p q r) by _≤_
·-sub-distribʳ-nr 0 r q p p′ = begin
  nr 0 p p′ r · q ≈⟨ ·-congʳ (nr-0 p p′ r) ⟩
  𝟘 · q           ≈⟨ ·-zeroˡ q ⟩
  𝟘               ≈˘⟨ nr-0 (p · q) (p′ · q) r ⟩
  nr 0 (p · q) (p′ · q) r ∎
·-sub-distribʳ-nr (1+ n) r q p p′ = begin
  nr (1+ n) p p′ r · q
    ≈⟨ ·-congʳ (nr-rec n p p′ r) ⟩
  (p ∧ p′ + r · nr n p p′ r) · q
    ≈⟨ ·-distribʳ-∧ q p _ ⟩
  (p · q) ∧ (p′ + r · nr n p p′ r) · q
    ≈⟨ ∧-congˡ (·-distribʳ-+ q p′ _) ⟩
  (p · q) ∧ (p′ · q) + (r · nr n p p′ r) · q
    ≈⟨ ∧-congˡ (+-congˡ (·-assoc r _ q)) ⟩
  (p · q) ∧ (p′ · q) + r · (nr n p p′ r · q)
    ≤⟨ ∧-monotoneʳ (+-monotoneʳ (·-monotoneʳ (·-sub-distribʳ-nr n r q p p′))) ⟩
  (p · q) ∧ (p′ · q) + r · nr n (p · q) (p′ · q) r
    ≈˘⟨ nr-rec n (p · q) (p′ · q) r ⟩
  nr (1+ n) (p · q) (p′ · q) r ∎

nr-sub-distribˡ-∧ : (n : Nat) (r : M) → (λ p q  → nr n p q r) SubDistributesOverˡ _∧_ by _≤_
nr-sub-distribˡ-∧ 0 r p q q′ = begin
  nr 0 p (q ∧ q′) r ≈⟨ nr-0 p (q ∧ q′) r ⟩
  𝟘                 ≈˘⟨ ∧-idem 𝟘 ⟩
  𝟘 ∧ 𝟘             ≈˘⟨ ∧-cong (nr-0 p q r) (nr-0 p q′ r) ⟩
  nr 0 p q r ∧ nr 0 p q′ r ∎
nr-sub-distribˡ-∧ (1+ n) r p q q′ = begin
  nr (1+ n) p (q ∧ q′) r
    ≈⟨ nr-rec n p (q ∧ q′) r ⟩
  p ∧ ((q ∧ q′) + r · nr n p (q ∧ q′) r)
    ≈⟨ ∧-cong (sym (∧-idem p)) (+-distribʳ-∧ _ q q′) ⟩
  (p ∧ p) ∧ ((q + r · nr n p (q ∧ q′) r) ∧ (q′ + r · nr n p (q ∧ q′) r))
    ≤⟨ ∧-monotoneʳ (∧-monotone (+-monotoneʳ (·-monotoneʳ (nr-sub-distribˡ-∧ n r p q q′)))
                              (+-monotoneʳ (·-monotoneʳ (nr-sub-distribˡ-∧ n r p q q′)))) ⟩
  (p ∧ p) ∧ ((q + r · (nr n p q r ∧ nr n p q′ r)) ∧ (q′ + r · (nr n p q r ∧ nr n p q′ r)))
    ≤⟨ ∧-monotoneʳ (∧-monotone (+-monotoneʳ (·-monotoneʳ (∧-decreasingˡ _ _)))
                              (+-monotoneʳ (·-monotoneʳ (∧-decreasingʳ _ _)))) ⟩
  (p ∧ p) ∧ ((q + r · nr n p q r) ∧ (q′ + r · nr n p q′ r))
    ≈˘⟨ ∧-assoc (p ∧ p) _ _ ⟩
  ((p ∧ p) ∧ (q + r · nr n p q r)) ∧ (q′ + r · nr n p q′ r)
    ≈⟨ ∧-congʳ (∧-assoc p p _) ⟩
  (p ∧ p ∧ (q + r · nr n p q r)) ∧ (q′ + r · nr n p q′ r)
    ≈⟨ ∧-congʳ (∧-congˡ (∧-comm p _)) ⟩
  (p ∧ (q + r · nr n p q r) ∧ p) ∧ (q′ + r · nr n p q′ r)
    ≈˘⟨ ∧-congʳ (∧-assoc p _ p) ⟩
  ((p ∧ (q + r · nr n p q r)) ∧ p) ∧ (q′ + r · nr n p q′ r)
    ≈⟨ ∧-assoc _ _ _ ⟩
  (p ∧ q + r · nr n p q r) ∧ (p ∧ q′ + r · nr n p q′ r)
    ≈˘⟨ ∧-cong (nr-rec n p q r) (nr-rec n p q′ r) ⟩
  nr (1+ n) p q r ∧ nr (1+ n) p q′ r ∎

nr-sub-distribʳ-∧ : (n : Nat) (r : M) → (λ p q  → nr n p q r) SubDistributesOverʳ _∧_ by _≤_
nr-sub-distribʳ-∧ 0 r q p p′ = begin
  nr 0 (p ∧ p′) q r ≈⟨ nr-0 (p ∧ p′) q r ⟩
  𝟘                 ≈˘⟨ ∧-idem 𝟘 ⟩
  𝟘 ∧ 𝟘             ≈˘⟨ ∧-cong (nr-0 p q r) (nr-0 p′ q r) ⟩
  nr 0 p q r ∧ nr 0 p′ q r ∎
nr-sub-distribʳ-∧ (1+ n) r q p p′ = begin
  nr (1+ n) (p ∧ p′) q r ≈⟨ nr-rec n (p ∧ p′) q r ⟩
  (p ∧ p′) ∧ (q + r · nr n (p ∧ p′) q r) ≤⟨ ∧-monotoneʳ (+-monotoneʳ (·-monotoneʳ (nr-sub-distribʳ-∧ n r q p p′))) ⟩
  (p ∧ p′) ∧ (q + r · (nr n p q r ∧ nr n p′ q r)) ≈⟨ ∧-congˡ (+-congˡ (·-distribˡ-∧ r _ _)) ⟩
  (p ∧ p′) ∧ (q + (r · nr n p q r ∧ r · nr n p′ q r)) ≈⟨ ∧-congˡ (+-distribˡ-∧ q _ _) ⟩
  (p ∧ p′) ∧ (q + r · nr n p q r) ∧ (q + r · nr n p′ q r) ≈˘⟨ ∧-assoc _ _ _ ⟩
  ((p ∧ p′) ∧ (q + r · nr n p q r)) ∧ (q + r · nr n p′ q r) ≈⟨ ∧-congʳ (∧-assoc p p′ _) ⟩
  (p ∧ p′ ∧ (q + r · nr n p q r)) ∧ (q + r · nr n p′ q r) ≈⟨ ∧-congʳ (∧-congˡ (∧-comm p′ _)) ⟩
  (p ∧ (q + r · nr n p q r) ∧ p′) ∧ (q + r · nr n p′ q r) ≈˘⟨ ∧-congʳ (∧-assoc p _ p′) ⟩
  ((p ∧ (q + r · nr n p q r)) ∧ p′) ∧ (q + r · nr n p′ q r) ≈⟨ ∧-assoc _ _ _ ⟩
  (p ∧ q + r · nr n p q r) ∧ (p′ ∧ q + r · nr n p′ q r) ≈˘⟨ ∧-cong (nr-rec n p q r) (nr-rec n p′ q r) ⟩
  nr (1+ n) p q r ∧ nr (1+ n) p′ q r ∎

isModality : Modality M′
isModality = record
  { modalityWithout⊛ = 𝕄
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = solvesIneqs
  ; ⊛-cong = nr-cong (proj₁ nr-fix)
  ; +-sub-interchangable-⊛ = +-sub-interchangable-nr (proj₁ nr-fix)
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-nr (proj₁ nr-fix)
  ; ⊛-sub-distrib-∧ = λ r → nr-sub-distribˡ-∧ (proj₁ nr-fix) r , nr-sub-distribʳ-∧ (proj₁ nr-fix) r
  }

module 𝟘-bound (𝟘-max : (p : M) → p ≤ 𝟘) where

  private
    variable
      p q r : M

  greatestSolnr : ∀ {x} (n : Nat) → x ≤ q + r · x → x ≤ p → x ≤ nr n p q r
  greatestSolnr 0 x≤q+rx x≤p = ≤-trans (𝟘-max _) (≤-reflexive (sym (nr-0 _ _ _)))
  greatestSolnr {q} {r} {p} {x} (1+ n) x≤q+rx x≤p = begin
    x ≈˘⟨ ∧-idem x ⟩
    x ∧ x ≤⟨ ∧-monotone x≤p x≤q+rx ⟩
    p ∧ (q + r · x) ≤⟨ ∧-monotoneʳ (+-monotoneʳ (·-monotoneʳ (greatestSolnr n x≤q+rx x≤p))) ⟩
    p ∧ (q + r · nr n p q r) ≈˘⟨ nr-rec n p q r ⟩
    nr (1+ n) p q r ∎

  greatestSol : ∀ {x} → x ≤ q + r · x → x ≤ p → x ≤ p ⊛ q ▷ r
  greatestSol {q} {r} {p} {x} x≤q+rx x≤p = greatestSolnr (proj₁ nr-fix) x≤q+rx x≤p
