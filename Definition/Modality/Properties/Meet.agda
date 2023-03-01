{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Properties.Meet {a ℓ}
  {M′ : Setoid a ℓ}
  (𝕄 : ModalityWithout⊛ M′)
  where

open ModalityWithout⊛ 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Properties.Addition 𝕄
open import Definition.Modality.Properties.PartialOrder 𝕄

open import Tools.Algebra M′

private
  variable
    p p′ q q′ r r′ : M

-- Meet on the left is a monotone function
-- If p ≤ q then p ∧ r ≤ q ∧ r

∧-monotoneˡ : p ≤ q → p ∧ r ≤ q ∧ r
∧-monotoneˡ {p} {q} {r} p≤q = begin
  p ∧ r             ≈⟨ ∧-cong p≤q (≈-sym (∧-idem r)) ⟩
  (p ∧ q) ∧ r ∧ r   ≈⟨ ∧-assoc p q (r ∧ r) ⟩
  p ∧ q ∧ r ∧ r     ≈⟨ ∧-congˡ (∧-comm q (r ∧ r)) ⟩
  p ∧ (r ∧ r) ∧ q   ≈⟨ ∧-congˡ (∧-assoc r r q) ⟩
  p ∧ r ∧ r ∧ q     ≈⟨ ≈-sym (∧-assoc p r (r ∧ q)) ⟩
  (p ∧ r) ∧ r ∧ q   ≈⟨ ∧-congˡ (∧-comm r q) ⟩
  (p ∧ r) ∧ (q ∧ r) ∎
  where open import Tools.Reasoning.Equivalence M′

-- Meet on the right is a monotone function
-- If p ≤ q then r ∧ p ≤ r ∧ q

∧-monotoneʳ : p ≤ q → r ∧ p ≤ r ∧ q
∧-monotoneʳ {p} {q} {r} p≤q = begin
  r ∧ p             ≈⟨ ∧-cong (≈-sym (∧-idem r)) p≤q ⟩
  (r ∧ r) ∧ (p ∧ q) ≈⟨ ∧-assoc r r (p ∧ q) ⟩
  r ∧ r ∧ p ∧ q     ≈⟨ ∧-congˡ (∧-comm r (p ∧ q)) ⟩
  r ∧ (p ∧ q) ∧ r   ≈⟨ ∧-congˡ (∧-assoc p q r) ⟩
  r ∧ p ∧ (q ∧ r)   ≈˘⟨ ∧-assoc r p (q ∧ r) ⟩
  (r ∧ p) ∧ (q ∧ r) ≈⟨ ∧-congˡ (∧-comm q r) ⟩
  (r ∧ p) ∧ (r ∧ q) ∎
  where open import Tools.Reasoning.Equivalence M′

-- Meet is a monotone function
-- If p ≤ p′ and q ≤ q′ then p ∧ q ≤ p′ ∧ q′

∧-monotone : p ≤ p′ → q ≤ q′ → p ∧ q ≤ p′ ∧ q′
∧-monotone p≤p′ q≤q′ = ≤-trans (∧-monotoneˡ  p≤p′) (∧-monotoneʳ q≤q′)

-- Meet on the left is a decreasing function
-- p ∧ q ≤ p

∧-decreasingˡ : (p q : M) → p ∧ q ≤ p
∧-decreasingˡ p q = begin
  p ∧ q       ≈⟨ ∧-congʳ (≈-sym (∧-idem p)) ⟩
  (p ∧ p) ∧ q ≈⟨ ∧-assoc p p q ⟩
  p ∧ (p ∧ q) ≈⟨ ∧-comm p (p ∧ q) ⟩
  (p ∧ q) ∧ p ∎
  where open import Tools.Reasoning.Equivalence M′

-- Meet on the right is a decreasing function
-- p ∧ q ≤ q

∧-decreasingʳ : (p q : M) → p ∧ q ≤ q
∧-decreasingʳ p q = begin
  p ∧ q       ≈⟨ ∧-congˡ (≈-sym (∧-idem q)) ⟩
  p ∧ (q ∧ q) ≈˘⟨ ∧-assoc p q q ⟩
  (p ∧ q) ∧ q ∎
  where open import Tools.Reasoning.Equivalence M′

+-sub-interchangable-∧ : _+_ SubInterchangable _∧_ by _≤_
+-sub-interchangable-∧ p q p′ q′ = begin
  (p ∧ q) + (p′ ∧ q′)
    ≈⟨ +-distribˡ-∧ (p ∧ q) p′ q′ ⟩
  ((p ∧ q) + p′) ∧ ((p ∧ q) + q′)
    ≤⟨ ∧-monotone (+-monotoneˡ (∧-decreasingˡ p q)) (+-monotoneˡ (∧-decreasingʳ p q)) ⟩
  (p + p′) ∧ (q + q′) ∎
  where
  open import Tools.Reasoning.PartialOrder ≤-poset
