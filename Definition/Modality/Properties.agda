{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Properties
  {M : Set} {_≈_ : Rel M _}
  (𝕄 : Modality M _≈_)
  where

open Modality 𝕄 renaming (≈-sym to sym ; ≈-refl to refl ; ≈-trans to trans)

open import Tools.Product
open import Tools.Reasoning _≈_ trans

private
  variable
    p p′ q q′ r : M

-- ≤ is reflexive
-- p ≤ p

≤-refl : p ≤ p
≤-refl {p} = sym (∧-idem p)

-- ≤ is transitive
-- If p ≤ q and q ≤ r then p ≤ r

≤-trans : p ≤ q → q ≤ r → p ≤ r
≤-trans {p} {q} {r} p≤q q≤r = trans p≤q
  (trans (≈-cong-∧ refl q≤r)
  (trans (sym (∧-assoc p q r)) (≈-cong-∧ (sym p≤q) refl)))

-- ≤ is antisymmetric
-- If p ≤ q and q ≤ p then p ≡ q

≤-antisym : p ≤ q → q ≤ p → p ≈ q
≤-antisym {p} {q} p≤q q≤p = trans p≤q (trans (∧-comm p q) (sym q≤p))

-- Addition on the left is a monotone function
-- If p ≤ q then p + r ≤ q + r

+-monotoneˡ : p ≤ q → p + r ≤ q + r
+-monotoneˡ p≤q = trans (≈-cong-+ p≤q refl) (proj₂ +-distrib-∧ _ _ _)

-- Addition on the right is a monotone function
-- If p ≤ q then r + p ≤ r + q

+-monotoneʳ : p ≤ q → r + p ≤ r + q
+-monotoneʳ p≤q = trans (≈-cong-+ refl p≤q) (proj₁ +-distrib-∧ _ _ _)

-- Addition is a monotone function
-- If p ≤ p′ and q ≤ q′ then p + q ≤ p′ + q′

+-monotone : p ≤ p′ → q ≤ q′ → p + q ≤ p′ + q′
+-monotone p≤p′ q≤q′ = ≤-trans (+-monotoneˡ p≤p′) (+-monotoneʳ q≤q′)

-- Meet on the left is a monotone function
-- If p ≤ q then p ∧ r ≤ q ∧ r

∧-monotoneˡ : p ≤ q → p ∧ r ≤ q ∧ r
∧-monotoneˡ {p} {q} {r} p≤q = begin
  p ∧ r             ∼⟨ ≈-cong-∧ p≤q (sym (∧-idem r)) ⟩
  (p ∧ q) ∧ r ∧ r   ∼⟨ ∧-assoc p q (r ∧ r) ⟩
  p ∧ q ∧ r ∧ r     ∼⟨ ≈-cong-∧ refl (∧-comm q (r ∧ r)) ⟩
  p ∧ (r ∧ r) ∧ q   ∼⟨ ≈-cong-∧ refl (∧-assoc r r q) ⟩
  p ∧ r ∧ r ∧ q     ∼⟨ sym (∧-assoc p r (r ∧ q)) ⟩
  (p ∧ r) ∧ r ∧ q   ∼⟨ ≈-cong-∧ refl (∧-comm r q) ⟩
  (p ∧ r) ∧ (q ∧ r) ∎⟨ refl ⟩

-- Meet on the right is a monotone function
-- If p ≤ q then r ∧ p ≤ r ∧ q

∧-monotoneʳ : p ≤ q → r ∧ p ≤ r ∧ q
∧-monotoneʳ {p} {q} {r} p≤q = begin
  r ∧ p             ∼⟨ ≈-cong-∧ (sym (∧-idem r)) p≤q ⟩
  (r ∧ r) ∧ (p ∧ q) ∼⟨ ∧-assoc r r (p ∧ q) ⟩
  r ∧ r ∧ p ∧ q     ∼⟨ ≈-cong-∧ refl (∧-comm r (p ∧ q)) ⟩
  r ∧ (p ∧ q) ∧ r   ∼⟨ ≈-cong-∧ refl (∧-assoc p q r) ⟩
  r ∧ p ∧ (q ∧ r)   ∼⟨ sym (∧-assoc r p (q ∧ r)) ⟩
  (r ∧ p) ∧ (q ∧ r) ∼⟨ ≈-cong-∧ refl (∧-comm q r) ⟩
  (r ∧ p) ∧ (r ∧ q) ∎⟨ refl ⟩

-- Meet is a monotone function
-- If p ≤ p′ and q ≤ q′ then p ∧ q ≤ p′ ∧ q′

∧-monotone : p ≤ p′ → q ≤ q′ → p ∧ q ≤ p′ ∧ q′
∧-monotone p≤p′ q≤q′ = ≤-trans (∧-monotoneˡ  p≤p′) (∧-monotoneʳ q≤q′)

-- Multiplication on the left is a monotone function
-- If p ≤ q then p · r ≤ q · r

·-monotoneˡ : p ≤ q → p · r ≤ q · r
·-monotoneˡ {p} {q} {r} p≤q = trans (≈-cong-· p≤q refl) (proj₂ ·-distrib-∧ r p q)

-- Multiplication on the right is a monotone function
-- If p ≤ q then r · p ≤ r · q

·-monotoneʳ : p ≤ q → r · p ≤ r · q
·-monotoneʳ {p} {q} {r} p≤q = trans (≈-cong-· refl p≤q) (proj₁ ·-distrib-∧ r p q)

-- Multiplication is a monotone function
-- If p ≤ p′ and q ≤ q′ then p · q ≤ p′ · q′

·-monotone : p ≤ p′ → q ≤ q′ → p · q ≤ p′ · q′
·-monotone p≤p′ q≤q′ = ≤-trans (·-monotoneˡ p≤p′) (·-monotoneʳ q≤q′)

-- Meet on the left is a decreasing function
-- p ∧ q ≤ p

∧-decreasingˡ : (p q : M) → p ∧ q ≤ p
∧-decreasingˡ p q = begin
  p ∧ q       ∼⟨ ≈-cong-∧ (sym (∧-idem p)) refl ⟩
  (p ∧ p) ∧ q ∼⟨ ∧-assoc p p q ⟩
  p ∧ (p ∧ q) ∼⟨ ∧-comm p (p ∧ q) ⟩
  (p ∧ q) ∧ p ∎⟨ refl ⟩

-- Meet on the right is a decreasing function
-- p ∧ q ≤ q

∧-decreasingʳ : (p q : M) → p ∧ q ≤ q
∧-decreasingʳ p q = begin
  p ∧ q       ∼⟨ ≈-cong-∧ refl (sym (∧-idem q)) ⟩
  p ∧ (q ∧ q) ∼⟨ sym (∧-assoc p q q) ⟩
  (p ∧ q) ∧ q ∎⟨ refl ⟩
