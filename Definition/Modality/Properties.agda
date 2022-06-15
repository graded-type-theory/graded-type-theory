{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Properties {a ℓ}
  {M′ : Setoid a ℓ}
  (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Tools.Algebra M′
open import Tools.Nat hiding (_+_)
open import Tools.Product


private
  variable
    p p′ q q′ r r′ : M


-- ≤ is reflexive
-- p ≤ p

≤-refl : p ≤ p
≤-refl {p} = ≈-sym (∧-idem p)

-- ≤ is transitive
-- If p ≤ q and q ≤ r then p ≤ r

≤-trans : p ≤ q → q ≤ r → p ≤ r
≤-trans {p} {q} {r} p≤q q≤r = ≈-trans p≤q
  (≈-trans (∧-cong ≈-refl q≤r)
  (≈-trans (≈-sym (∧-assoc p q r)) (∧-cong (≈-sym p≤q) ≈-refl)))

-- ≤ is antisymmetric
-- If p ≤ q and q ≤ p then p ≈ q

≤-antisym : p ≤ q → q ≤ p → p ≈ q
≤-antisym {p} {q} p≤q q≤p = ≈-trans p≤q (≈-trans (∧-comm p q) (≈-sym q≤p))

-- ≤ is a non-strict ordering relation
-- If p ≈ q then p ≤ q

≤-reflexive : p ≈ q → p ≤ q
≤-reflexive {p} p≈q = ≈-trans (≈-sym (∧-idem p)) (∧-cong ≈-refl p≈q)

-- ≤ is a preorder relation

≤-preorder : IsPreorder _≈_ _≤_
≤-preorder = record
  { isEquivalence = ≈-equivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

-- ≤ is a partial ordering relation

≤-partial : IsPartialOrder _≈_ _≤_
≤-partial = record
  { isPreorder = ≤-preorder
  ; antisym    = ≤-antisym
  }

-- (M, ≤) is a poset

≤-poset : Poset _ _ _
≤-poset = record
  { Carrier        = M
  ; _≈_            = _≈_
  ; _≤_            = _≤_
  ; isPartialOrder = ≤-partial
  }

-- Addition on the left is a monotone function
-- If p ≤ q then p + r ≤ q + r

+-monotoneˡ : p ≤ q → p + r ≤ q + r
+-monotoneˡ p≤q = ≈-trans (+-cong p≤q ≈-refl) (proj₂ +-distrib-∧ _ _ _)

-- Addition on the right is a monotone function
-- If p ≤ q then r + p ≤ r + q

+-monotoneʳ : p ≤ q → r + p ≤ r + q
+-monotoneʳ p≤q = ≈-trans (+-cong ≈-refl p≤q) (proj₁ +-distrib-∧ _ _ _)

-- Addition is a monotone function
-- If p ≤ p′ and q ≤ q′ then p + q ≤ p′ + q′

+-monotone : p ≤ p′ → q ≤ q′ → p + q ≤ p′ + q′
+-monotone p≤p′ q≤q′ = ≤-trans (+-monotoneˡ p≤p′) (+-monotoneʳ q≤q′)

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

-- Multiplication on the left is a monotone function
-- If p ≤ q then p · r ≤ q · r

·-monotoneˡ : p ≤ q → p · r ≤ q · r
·-monotoneˡ {p} {q} {r} p≤q = ≈-trans (·-cong p≤q ≈-refl) (proj₂ ·-distrib-∧ r p q)

-- Multiplication on the right is a monotone function
-- If p ≤ q then r · p ≤ r · q

·-monotoneʳ : p ≤ q → r · p ≤ r · q
·-monotoneʳ {p} {q} {r} p≤q = ≈-trans (·-cong ≈-refl p≤q) (proj₁ ·-distrib-∧ r p q)

-- Multiplication is a monotone function
-- If p ≤ p′ and q ≤ q′ then p · q ≤ p′ · q′

·-monotone : p ≤ p′ → q ≤ q′ → p · q ≤ p′ · q′
·-monotone p≤p′ q≤q′ = ≤-trans (·-monotoneˡ p≤p′) (·-monotoneʳ q≤q′)

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

-- ⊛ is monotone on the first two arguments
-- If p ≤ p′ and q ≤ q′ then p ⊛ q ▷ r ≤ p′ ⊛ q′ ≤ r

⊛-monotone : p ≤ p′ → q ≤ q′ → p ⊛ q ▷ r ≤ p′ ⊛ q′ ▷ r
⊛-monotone {p} {p′} {q} {q′} {r} p≤p′ q≤q′ = begin
  p ⊛ q ▷ r
    ≈⟨ ⊛-cong p≤p′ q≤q′ ≈-refl ⟩
  (p ∧ p′) ⊛ (q ∧ q′) ▷ r
    ≤⟨ proj₁ (⊛-sub-distrib-∧ r) (p ∧ p′) q q′ ⟩
  ((p ∧ p′) ⊛ q ▷ r) ∧ ((p ∧ p′) ⊛ q′ ▷ r)
    ≤⟨ ∧-monotone (proj₂ (⊛-sub-distrib-∧ r) q p p′) (proj₂ (⊛-sub-distrib-∧ r) q′ p p′) ⟩
  ((p ⊛ q ▷ r) ∧ (p′ ⊛ q ▷ r)) ∧ (p ⊛ q′ ▷ r ∧ p′ ⊛ q′ ▷ r)
    ≤⟨ ∧-decreasingʳ _ _ ⟩
  p ⊛ q′ ▷ r ∧ p′ ⊛ q′ ▷ r
    ≤⟨ ∧-decreasingʳ _ _ ⟩
  p′ ⊛ q′ ▷ r ∎
  where open import Tools.Reasoning.PartialOrder ≤-poset

-- ⊛ is idempotent on 𝟘 w.r.t the first two arguments
-- 𝟘 ⊛ 𝟘 ▷ r ≈ 𝟘
⊛-idem-𝟘 : (r : M) → (_⊛_▷ r) IdempotentOn 𝟘
⊛-idem-𝟘 r = ≤-antisym (⊛-ineq₂ 𝟘 𝟘 r) 𝟘≤𝟘⊛𝟘
  where
  open import Tools.Reasoning.PartialOrder ≤-poset
  𝟘≤𝟘⊛𝟘 = begin
    𝟘                     ≈˘⟨ proj₂ ·-zero (𝟘 ⊛ 𝟘 ▷ r) ⟩
    (𝟘 ⊛ 𝟘 ▷ r) · 𝟘       ≤⟨ ·-sub-distribʳ-⊛ r 𝟘 𝟘 𝟘 ⟩
    (𝟘 · 𝟘) ⊛ (𝟘 · 𝟘) ▷ r ≈⟨ ⊛-cong (proj₁ ·-zero 𝟘) (proj₁ ·-zero 𝟘) ≈-refl ⟩
    𝟘 ⊛ 𝟘 ▷ r ∎
