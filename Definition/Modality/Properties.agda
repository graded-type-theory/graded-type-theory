{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Properties
  {M : Set} {_≈_ : Rel M ℓ₀}
  (𝕄 : Modality M _≈_)
  where

open Modality 𝕄 renaming (≈-sym to sym ; ≈-refl to refl ; ≈-trans to trans)

open import Tools.Nat hiding (_+_)
open import Tools.Product

private
  variable
    p p′ q q′ r r′ : M

-- ≤ is reflexive
-- p ≤ p

≤-refl : p ≤ p
≤-refl {p} = sym (∧-idem p)

-- ≤ is transitive
-- If p ≤ q and q ≤ r then p ≤ r

≤-trans : p ≤ q → q ≤ r → p ≤ r
≤-trans {p} {q} {r} p≤q q≤r = trans p≤q
  (trans (∧-cong refl q≤r)
  (trans (sym (∧-assoc p q r)) (∧-cong (sym p≤q) refl)))

-- ≤ is antisymmetric
-- If p ≤ q and q ≤ p then p ≡ q

≤-antisym : p ≤ q → q ≤ p → p ≈ q
≤-antisym {p} {q} p≤q q≤p = trans p≤q (trans (∧-comm p q) (sym q≤p))

-- ≤ is a non-strict ordering relation
-- If p ≈ q then p ≤ q

≤-reflexive : p ≈ q → p ≤ q
≤-reflexive {p} p≈q = trans (sym (∧-idem p)) (∧-cong refl p≈q)

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
+-monotoneˡ p≤q = trans (+-cong p≤q refl) (proj₂ +-distrib-∧ _ _ _)

-- Addition on the right is a monotone function
-- If p ≤ q then r + p ≤ r + q

+-monotoneʳ : p ≤ q → r + p ≤ r + q
+-monotoneʳ p≤q = trans (+-cong refl p≤q) (proj₁ +-distrib-∧ _ _ _)

-- Addition is a monotone function
-- If p ≤ p′ and q ≤ q′ then p + q ≤ p′ + q′

+-monotone : p ≤ p′ → q ≤ q′ → p + q ≤ p′ + q′
+-monotone p≤p′ q≤q′ = ≤-trans (+-monotoneˡ p≤p′) (+-monotoneʳ q≤q′)

-- Meet on the left is a monotone function
-- If p ≤ q then p ∧ r ≤ q ∧ r

∧-monotoneˡ : p ≤ q → p ∧ r ≤ q ∧ r
∧-monotoneˡ {p} {q} {r} p≤q = begin
  p ∧ r             ≈⟨ ∧-cong p≤q (sym (∧-idem r)) ⟩
  (p ∧ q) ∧ r ∧ r   ≈⟨ ∧-assoc p q (r ∧ r) ⟩
  p ∧ q ∧ r ∧ r     ≈⟨ ∧-cong refl (∧-comm q (r ∧ r)) ⟩
  p ∧ (r ∧ r) ∧ q   ≈⟨ ∧-cong refl (∧-assoc r r q) ⟩
  p ∧ r ∧ r ∧ q     ≈⟨ sym (∧-assoc p r (r ∧ q)) ⟩
  (p ∧ r) ∧ r ∧ q   ≈⟨ ∧-cong refl (∧-comm r q) ⟩
  (p ∧ r) ∧ (q ∧ r) ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence

-- Meet on the right is a monotone function
-- If p ≤ q then r ∧ p ≤ r ∧ q

∧-monotoneʳ : p ≤ q → r ∧ p ≤ r ∧ q
∧-monotoneʳ {p} {q} {r} p≤q = begin
  r ∧ p             ≈⟨ ∧-cong (sym (∧-idem r)) p≤q ⟩
  (r ∧ r) ∧ (p ∧ q) ≈⟨ ∧-assoc r r (p ∧ q) ⟩
  r ∧ r ∧ p ∧ q     ≈⟨ ∧-cong refl (∧-comm r (p ∧ q)) ⟩
  r ∧ (p ∧ q) ∧ r   ≈⟨ ∧-cong refl (∧-assoc p q r) ⟩
  r ∧ p ∧ (q ∧ r)   ≈⟨ sym (∧-assoc r p (q ∧ r)) ⟩
  (r ∧ p) ∧ (q ∧ r) ≈⟨ ∧-cong refl (∧-comm q r) ⟩
  (r ∧ p) ∧ (r ∧ q) ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence

-- Meet is a monotone function
-- If p ≤ p′ and q ≤ q′ then p ∧ q ≤ p′ ∧ q′

∧-monotone : p ≤ p′ → q ≤ q′ → p ∧ q ≤ p′ ∧ q′
∧-monotone p≤p′ q≤q′ = ≤-trans (∧-monotoneˡ  p≤p′) (∧-monotoneʳ q≤q′)

-- Multiplication on the left is a monotone function
-- If p ≤ q then p · r ≤ q · r

·-monotoneˡ : p ≤ q → p · r ≤ q · r
·-monotoneˡ {p} {q} {r} p≤q = trans (·-cong p≤q refl) (proj₂ ·-distrib-∧ r p q)

-- Multiplication on the right is a monotone function
-- If p ≤ q then r · p ≤ r · q

·-monotoneʳ : p ≤ q → r · p ≤ r · q
·-monotoneʳ {p} {q} {r} p≤q = trans (·-cong refl p≤q) (proj₁ ·-distrib-∧ r p q)

-- Multiplication is a monotone function
-- If p ≤ p′ and q ≤ q′ then p · q ≤ p′ · q′

·-monotone : p ≤ p′ → q ≤ q′ → p · q ≤ p′ · q′
·-monotone p≤p′ q≤q′ = ≤-trans (·-monotoneˡ p≤p′) (·-monotoneʳ q≤q′)

-- Meet on the left is a decreasing function
-- p ∧ q ≤ p

∧-decreasingˡ : (p q : M) → p ∧ q ≤ p
∧-decreasingˡ p q = begin
  p ∧ q       ≈⟨ ∧-cong (sym (∧-idem p)) refl ⟩
  (p ∧ p) ∧ q ≈⟨ ∧-assoc p p q ⟩
  p ∧ (p ∧ q) ≈⟨ ∧-comm p (p ∧ q) ⟩
  (p ∧ q) ∧ p ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence

-- Meet on the right is a decreasing function
-- p ∧ q ≤ q

∧-decreasingʳ : (p q : M) → p ∧ q ≤ q
∧-decreasingʳ p q = begin
  p ∧ q       ≈⟨ ∧-cong refl (sym (∧-idem q)) ⟩
  p ∧ (q ∧ q) ≈⟨ sym (∧-assoc p q q) ⟩
  (p ∧ q) ∧ q ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence

-- Characteristic reccurence relation for nr
-- nr p q r ≈ p ∧ (q + r · nr p q r)

nr-rec : (p q r : M) → nr p q r ≈ p ∧ (q + r · nr p q r)
nr-rec p q r with nrⁿ-fix
... | n , fix = begin
  nrⁿ n p q r               ≈˘⟨ fix p q r ⟩
  nrⁿ (1+ n) p q r          ≈⟨ nrⁿ-rec n p q r ⟩
  p ∧ (q + r · nrⁿ n p q r) ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence

-- nrⁿ is idempotent on 𝟘 for its first two (non Nat) arguments
-- nrⁿ n 𝟘 𝟘 r ≈ 𝟘

nrⁿ-idem-𝟘 : (n : Nat) → nrⁿ n 𝟘 𝟘 r ≈ 𝟘
nrⁿ-idem-𝟘 {r} 0 = nrⁿ-0 𝟘 𝟘 r
nrⁿ-idem-𝟘 {r} (1+ n) = begin
  nrⁿ (1+ n) 𝟘 𝟘 r ≈⟨ nrⁿ-rec n 𝟘 𝟘 r ⟩
  𝟘 ∧ (𝟘 + r · nrⁿ n 𝟘 𝟘 r) ≈⟨ ∧-cong refl (proj₁ +-identity _) ⟩
  𝟘 ∧ (r · nrⁿ n 𝟘 𝟘 r) ≈⟨ ∧-cong refl (·-cong refl (nrⁿ-idem-𝟘 n)) ⟩
  𝟘 ∧ (r · 𝟘) ≈⟨ ∧-cong refl (proj₂ ·-zero r) ⟩
  𝟘 ∧ 𝟘 ≈⟨ ∧-idem 𝟘 ⟩
  𝟘 ∎
 where open import Tools.Reasoning.Equivalence ≈-equivalence

-- nr is idempotent on 𝟘 for its first two arguments
-- nr 𝟘 𝟘 r ≈ 𝟘

nr-idem-𝟘 : (r : M) → nr 𝟘 𝟘 r ≈ 𝟘
nr-idem-𝟘 r with nrⁿ-fix
... | n , fix = nrⁿ-idem-𝟘 n

-- nrⁿ is monotone
-- If p ≤ p′ and q ≤ q′ and r ≤ r′ then nrⁿ n p q r ≤ nrⁿ n p′ q′ r′

nrⁿ-monotone : (n : Nat) → p ≤ p′ → q ≤ q′ → r ≤ r′ → nrⁿ n p q r ≤ nrⁿ n p′ q′ r′
nrⁿ-monotone {p} {p′} {q} {q′} {r} {r′} 0 x y z = begin
  nrⁿ 0 p q r    ≈⟨ nrⁿ-0 p q r ⟩
  𝟘              ≈˘⟨ nrⁿ-0 p′ q′ r′ ⟩
  nrⁿ 0 p′ q′ r′ ∎
  where open import Tools.Reasoning.PartialOrder ≤-poset
nrⁿ-monotone {p} {p′} {q} {q′} {r} {r′} (1+ n) p≤p′ q≤q′ r≤r′ = begin
  nrⁿ (1+ n) p q r
    ≈⟨ nrⁿ-rec n p q r ⟩
  p ∧ (q + r · nrⁿ n p q r)
    ≤⟨ ∧-monotone p≤p′ (+-monotone q≤q′ (·-monotone r≤r′ (nrⁿ-monotone n p≤p′ q≤q′ r≤r′))) ⟩
  p′ ∧ (q′ + r′ · nrⁿ n p′ q′ r′)
    ≈˘⟨ nrⁿ-rec n p′ q′ r′ ⟩
  nrⁿ (1+ n) p′ q′ r′ ∎
  where open import Tools.Reasoning.PartialOrder ≤-poset

-- nr is monotone
-- If p ≤ p′ and q ≤ q′ and r ≤ r′ then nr n p q r ≤ nr n p′ q′ r′

nr-monotone : p ≤ p′ → q ≤ q′ → r ≤ r′ → nr p q r ≤ nr p′ q′ r′
nr-monotone {p} {p′} {q} {q′} {r} {r′} p≤p′ q≤q′ r≤r′ with nrⁿ-fix
... | n , fix = nrⁿ-monotone n p≤p′ q≤q′ r≤r′

-- Multiplication is right distributive over nrⁿ
-- nrⁿ n (p′ · p) (p′ · q) r ≈ p′ · nrⁿ n p q r

·-distribʳ-nrⁿ : (n : Nat) (p′ p q r : M)
               → nrⁿ n (p · p′) (q · p′) r ≈ nrⁿ n p q r · p′
·-distribʳ-nrⁿ 0 p′ p q r = begin
  nrⁿ 0 (p · p′) (q · p′) r ≈⟨ nrⁿ-0 (p · p′) (q · p′) r ⟩
  𝟘                         ≈˘⟨ proj₁ ·-zero p′ ⟩
  𝟘 · p′                    ≈˘⟨ ·-cong (nrⁿ-0 p q r) refl ⟩
  nrⁿ 0 p q r · p′          ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence
·-distribʳ-nrⁿ (1+ n) p′ p q r = begin
  nrⁿ (1+ n) (p · p′) (q · p′) r
     ≈⟨ nrⁿ-rec n (p · p′) (q · p′) r ⟩
  (p · p′) ∧ ((q · p′) + r · nrⁿ n (p · p′) (q · p′) r)
     ≈⟨  ∧-cong refl (+-cong refl (·-cong refl (·-distribʳ-nrⁿ n p′ p q r)))  ⟩
  (p · p′) ∧ ((q · p′) + r · nrⁿ n p q r · p′)
     ≈˘⟨ ∧-cong refl (+-cong refl (·-assoc r _ p′)) ⟩
  (p · p′) ∧ ((q · p′) + (r · nrⁿ n p q r) · p′)
     ≈˘⟨ ∧-cong refl (proj₂ ·-distrib-+ p′ q _) ⟩
  (p · p′) ∧ ((q + r · nrⁿ n p q r) · p′)
     ≈˘⟨ proj₂ ·-distrib-∧ p′ p _ ⟩
  (p ∧ (q + r · nrⁿ n p q r)) · p′
     ≈˘⟨ ·-cong (nrⁿ-rec n p q r) refl ⟩
  nrⁿ (1+ n) p q r · p′ ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence

-- Multiplication is right distributive over nr
-- nr (p′ · p) (p′ · q) r ≈ p′ · nr p q r

·-distribʳ-nr : (p′ p q r : M) → nr (p · p′) (q · p′) r ≈ nr p q r · p′
·-distribʳ-nr p′ p q r with nrⁿ-fix
... | (n , fix) = ·-distribʳ-nrⁿ n p′ p q r

-- Addition is super-distributive over nrⁿ
-- nrⁿ n p q r + nrⁿ n p′ q′ r ≤ nrⁿ n (p + p′) (q + q′) r

+-super-distrib-nrⁿ : (n : Nat) (p p′ q q′ r : M)
                     → nrⁿ n p q r + nrⁿ n p′ q′ r ≤ nrⁿ n (p + p′) (q + q′) r
+-super-distrib-nrⁿ 0 p p′ q q′ r = begin
  nrⁿ 0 p q r + nrⁿ 0 p′ q′ r ≈⟨ +-cong (nrⁿ-0 p q r) (nrⁿ-0 p′ q′ r) ⟩
  𝟘 + 𝟘                       ≈⟨ proj₁ +-identity 𝟘 ⟩
  𝟘                           ≈˘⟨ nrⁿ-0 (p + p′) (q + q′) r ⟩
  nrⁿ 0 (p + p′) (q + q′) r   ∎
  where open import Tools.Reasoning.PartialOrder ≤-poset
+-super-distrib-nrⁿ (1+ n) p p′ q q′ r = begin
  nrⁿ (1+ n) p q r + nrⁿ (1+ n) p′ q′ r
     ≈⟨ +-cong (nrⁿ-rec n p q r) (nrⁿ-rec n p′ q′ r) ⟩
  (p ∧ (q + r · nrⁿ n p q r)) + (p′ ∧ (q′ + r · nrⁿ n p′ q′ r))
     ≈⟨ proj₂ +-distrib-∧ _ _ _ ⟩
  (p + (p′ ∧ (q′ + r · nrⁿ n p′ q′ r))) ∧ ((q + r · nrⁿ n p q r) + (p′ ∧ (q′ + r · nrⁿ n p′ q′ r)))
     ≈⟨ ∧-cong (proj₁ +-distrib-∧ _ _ _) (proj₁ +-distrib-∧ _ _ _) ⟩
  ((p + p′) ∧ (p + (q′ + r · nrⁿ n p′ q′ r))) ∧ (((q + r · nrⁿ n p q r) + p′) ∧ ((q + r · nrⁿ n p q r) + (q′ + r · nrⁿ n p′ q′ r)))
     ≤⟨ ∧-monotone (∧-decreasingˡ _ _) (∧-decreasingʳ _ _) ⟩
  (p + p′) ∧ (q + r · nrⁿ n p q r) + q′ + r · nrⁿ n p′ q′ r
     ≈⟨ ∧-cong refl (+-assoc _ _ _) ⟩
  (p + p′) ∧ (q + r · nrⁿ n p q r + q′ + r · nrⁿ n p′ q′ r)
     ≈˘⟨ ∧-cong refl (+-cong refl (+-assoc _ _ _)) ⟩
  (p + p′) ∧ (q + (r · nrⁿ n p q r + q′) + r · nrⁿ n p′ q′ r)
     ≈⟨ ∧-cong refl (+-cong refl (+-cong (+-comm _ _) refl)) ⟩
  (p + p′) ∧ (q + (q′ + r · nrⁿ n p q r) + r · nrⁿ n p′ q′ r)
     ≈⟨ ∧-cong refl (+-cong refl (+-assoc _ _ _)) ⟩
  (p + p′) ∧ (q + q′ + r · nrⁿ n p q r + r · nrⁿ n p′ q′ r)
     ≈˘⟨ ∧-cong refl (+-assoc _ _ _) ⟩
  (p + p′) ∧ ((q + q′) + (r · nrⁿ n p q r + r · nrⁿ n p′ q′ r))
     ≈˘⟨ ∧-cong refl (+-cong refl (proj₁ ·-distrib-+ _ _ _)) ⟩
  (p + p′) ∧ ((q + q′) + (r · (nrⁿ n p q r + nrⁿ n p′ q′ r)))
     ≤⟨ ∧-monotoneʳ (+-monotoneʳ (·-monotoneʳ (+-super-distrib-nrⁿ _ _ _ _ _ _))) ⟩
  (p + p′) ∧ ((q + q′) + (r · nrⁿ n (p + p′) (q + q′) r))
     ≈˘⟨ nrⁿ-rec n (p + p′) (q + q′) r ⟩
  nrⁿ (1+ n) (p + p′) (q + q′) r ∎
  where open import Tools.Reasoning.PartialOrder ≤-poset

-- Addition is super-distributive over nr
-- nr p q r + nr p′ q′ r ≤ nr (p + p′) (q + q′) r

+-super-distrib-nr : (p p′ q q′ r : M) → nr p q r + nr p′ q′ r ≤ nr (p + p′) (q + q′) r
+-super-distrib-nr p p′ q q′ r with nrⁿ-fix
... | (n , fix) = +-super-distrib-nrⁿ n p p′ q q′ r

-- Congruence of nrⁿ
-- If p ≈ p′ and q ≈ q′ and r ≈ r′ then nrⁿ n p q r ≈ nrⁿ n p′ q′ r′

nrⁿ-cong : (n : Nat) → p ≈ p′ → q ≈ q′ → r ≈ r′ → nrⁿ n p q r ≈ nrⁿ n p′ q′ r′
nrⁿ-cong {p} {p′} {q} {q′} {r} {r′} 0 p≈p′ q≈q′ r≈r′ = begin
  nrⁿ 0 p q r    ≈⟨ nrⁿ-0 p q r ⟩
  𝟘              ≈˘⟨ nrⁿ-0 p′ q′ r′ ⟩
  nrⁿ 0 p′ q′ r′ ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence
nrⁿ-cong {p} {p′} {q} {q′} {r} {r′} (1+ n) p≈p′ q≈q′ r≈r′ = begin
  nrⁿ (1+ n) p q r
    ≈⟨ nrⁿ-rec n p q r ⟩
  p ∧ (q + r · nrⁿ n p q r)
    ≈⟨ ∧-cong p≈p′ (+-cong q≈q′ (·-cong r≈r′ (nrⁿ-cong n p≈p′ q≈q′ r≈r′))) ⟩
  (p′ ∧ (q′ + (r′ · nrⁿ n p′ q′ r′)))
    ≈˘⟨ nrⁿ-rec n p′ q′ r′ ⟩
  nrⁿ (1+ n) p′ q′ r′ ∎
  where open import Tools.Reasoning.Equivalence ≈-equivalence

-- Congruence of nr
-- If p ≈ p′ and q ≈ q′ and r ≈ r′ then nr p q r ≈ nr p′ q′ r′

nr-cong : p ≈ p′ → q ≈ q′ → r ≈ r′ → nr p q r ≈ nr p′ q′ r′
nr-cong p≈p′ q≈q′ r≈r′ with nrⁿ-fix
... | n , fix = nrⁿ-cong n p≈p′ q≈q′ r≈r′
