{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Properties.Meet {a ℓ}
  {M′ : Setoid a ℓ}
  (𝕄 : ModalityWithout⊛ M′)
  where

open ModalityWithout⊛ 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Properties.PartialOrder 𝕄

open import Tools.Algebra M′
open import Tools.Nat hiding (_+_)
open import Tools.Product


private
  variable
    p p′ q q′ r r′ : M

-- Meet on the left is a monotone function
-- If p ≤ q then p ∧ r ≤ q ∧ r

∧-monotoneˡ : p ≤ q → p ∧ r ≤ q ∧ r
∧-monotoneˡ {p} {q} {r} p≤q = begin
  p ∧ r             ≈⟨ ∧-cong p≤q (≈-sym (∧-idem r)) ⟩
  (p ∧ q) ∧ r ∧ r   ≈⟨ ∧-assoc p q (r ∧ r) ⟩
  p ∧ q ∧ r ∧ r     ≈⟨ ∧-cong ≈-refl (∧-comm q (r ∧ r)) ⟩
  p ∧ (r ∧ r) ∧ q   ≈⟨ ∧-cong ≈-refl (∧-assoc r r q) ⟩
  p ∧ r ∧ r ∧ q     ≈⟨ ≈-sym (∧-assoc p r (r ∧ q)) ⟩
  (p ∧ r) ∧ r ∧ q   ≈⟨ ∧-cong ≈-refl (∧-comm r q) ⟩
  (p ∧ r) ∧ (q ∧ r) ∎
  where open import Tools.Reasoning.Equivalence M′

-- Meet on the right is a monotone function
-- If p ≤ q then r ∧ p ≤ r ∧ q

∧-monotoneʳ : p ≤ q → r ∧ p ≤ r ∧ q
∧-monotoneʳ {p} {q} {r} p≤q = begin
  r ∧ p             ≈⟨ ∧-cong (≈-sym (∧-idem r)) p≤q ⟩
  (r ∧ r) ∧ (p ∧ q) ≈⟨ ∧-assoc r r (p ∧ q) ⟩
  r ∧ r ∧ p ∧ q     ≈⟨ ∧-cong ≈-refl (∧-comm r (p ∧ q)) ⟩
  r ∧ (p ∧ q) ∧ r   ≈⟨ ∧-cong ≈-refl (∧-assoc p q r) ⟩
  r ∧ p ∧ (q ∧ r)   ≈⟨ ≈-sym (∧-assoc r p (q ∧ r)) ⟩
  (r ∧ p) ∧ (q ∧ r) ≈⟨ ∧-cong ≈-refl (∧-comm q r) ⟩
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
  p ∧ q       ≈⟨ ∧-cong (≈-sym (∧-idem p)) ≈-refl ⟩
  (p ∧ p) ∧ q ≈⟨ ∧-assoc p p q ⟩
  p ∧ (p ∧ q) ≈⟨ ∧-comm p (p ∧ q) ⟩
  (p ∧ q) ∧ p ∎
  where open import Tools.Reasoning.Equivalence M′

-- Meet on the right is a decreasing function
-- p ∧ q ≤ q

∧-decreasingʳ : (p q : M) → p ∧ q ≤ q
∧-decreasingʳ p q = begin
  p ∧ q       ≈⟨ ∧-cong ≈-refl (≈-sym (∧-idem q)) ⟩
  p ∧ (q ∧ q) ≈⟨ ≈-sym (∧-assoc p q q) ⟩
  (p ∧ q) ∧ q ∎
  where open import Tools.Reasoning.Equivalence M′
