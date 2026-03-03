------------------------------------------------------------------------
-- Properties of natrec-star operators
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Properties.Star
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  ⦃ has-star : Has-star 𝕄 ⦄
  where

open Modality 𝕄

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties.PartialOrder 𝕄
open import Graded.Modality.Properties.Addition 𝕄
open import Graded.Modality.Properties.Has-well-behaved-zero 𝕄
open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.Multiplication 𝕄

open import Tools.Algebra M
open import Tools.Bool using (Bool; T)
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    n n₁ n₂ p p′ q q′ r r′ s s₁ s₂ z z₁ z₂ : M
    𝟘ᵐ-allowed                             : Bool

-- Variants of ⊛-congurence

⊛-cong : p ≡ p′ → q ≡ q′ → r ≡ r′ → p ⊛ q ▷ r ≡ p′ ⊛ q′ ▷ r′
⊛-cong = cong₃ _⊛_▷_

⊛ᵣ-cong : p ≡ p′ → q ≡ q′ → p ⊛ q ▷ r ≡ p′ ⊛ q′ ▷ r
⊛ᵣ-cong p≡p′ q≡q′ = ⊛-cong p≡p′ q≡q′ refl

⊛ᵣ-congˡ : q ≡ q′ → p ⊛ q ▷ r ≡ p ⊛ q′ ▷ r
⊛ᵣ-congˡ q≡q′ = ⊛ᵣ-cong refl q≡q′

⊛ᵣ-congʳ : p ≡ p′ → p ⊛ q ▷ r ≡ p′ ⊛ q ▷ r
⊛ᵣ-congʳ p≡p′ = ⊛ᵣ-cong p≡p′ refl

-- ⊛ is monotone on the first two arguments
-- If p ≤ p′ and q ≤ q′ then p ⊛ q ▷ r ≤ p′ ⊛ q′ ≤ r

⊛-monotone : p ≤ p′ → q ≤ q′ → p ⊛ q ▷ r ≤ p′ ⊛ q′ ▷ r
⊛-monotone {p} {p′} {q} {q′} {r} p≤p′ q≤q′ = begin
  p ⊛ q ▷ r
    ≈⟨ ⊛ᵣ-cong p≤p′ q≤q′ ⟩
  (p ∧ p′) ⊛ (q ∧ q′) ▷ r
    ≤⟨ ⊛-sub-distribˡ-∧ r (p ∧ p′) q q′ ⟩
  ((p ∧ p′) ⊛ q ▷ r) ∧ ((p ∧ p′) ⊛ q′ ▷ r)
    ≤⟨ ∧-monotone (⊛-sub-distribʳ-∧ r q p p′) (⊛-sub-distribʳ-∧ r q′ p p′) ⟩
  ((p ⊛ q ▷ r) ∧ (p′ ⊛ q ▷ r)) ∧ (p ⊛ q′ ▷ r ∧ p′ ⊛ q′ ▷ r)
    ≤⟨ ∧-decreasingʳ _ _ ⟩
  p ⊛ q′ ▷ r ∧ p′ ⊛ q′ ▷ r
    ≤⟨ ∧-decreasingʳ _ _ ⟩
  p′ ⊛ q′ ▷ r ∎
  where open import Tools.Reasoning.PartialOrder ≤-poset

-- The operator _⊛_▷ r is idempotent on 𝟘.

⊛-idem-𝟘 : (r : M) → (_⊛_▷ r) IdempotentOn 𝟘
⊛-idem-𝟘 r = ≤-antisym (⊛-ineq₂ 𝟘 𝟘 r) 𝟘≤𝟘⊛𝟘
  where
  open import Tools.Reasoning.PartialOrder ≤-poset
  𝟘≤𝟘⊛𝟘 = begin
    𝟘                     ≈˘⟨ ·-zeroʳ (𝟘 ⊛ 𝟘 ▷ r) ⟩
    (𝟘 ⊛ 𝟘 ▷ r) · 𝟘       ≤⟨ ·-sub-distribʳ-⊛ r 𝟘 𝟘 𝟘 ⟩
    (𝟘 · 𝟘) ⊛ (𝟘 · 𝟘) ▷ r ≈⟨ ⊛ᵣ-cong (·-zeroˡ 𝟘) (·-zeroˡ 𝟘) ⟩
    𝟘 ⊛ 𝟘 ▷ r ∎

-- If a "semiring with meet" has a natrec-star operator, then it has
-- an nr function.

has-nr : Has-nr 𝕄
has-nr = record
  { nr          = nr′
  ; nr-monotone = nr′-monotone
  ; nr-·        = nr′-·
  ; nr-+        = nr′-+
  ; nr-positive = nr′-positive
  ; nr-zero     = nr′-zero
  ; nr-suc      = nr′-suc
  }
  where
  nr′ : M → M → M → M → M → M
  nr′ p r z s n = (z ∧ n) ⊛ s + p · n ▷ r

  nr′-monotone :
    z₁ ≤ z₂ → s₁ ≤ s₂ → n₁ ≤ n₂ →
    nr′ p r z₁ s₁ n₁ ≤ nr′ p r z₂ s₂ n₂
  nr′-monotone
    {z₁ = z₁} {z₂ = z₂} {s₁ = s₁} {s₂ = s₂} {n₁ = n₁} {n₂ = n₂}
    {p = p} {r = r}
    z₁≤z₂ s₁≤s₂ n₁≤n₂ = begin
    (z₁ ∧ n₁) ⊛ s₁ + p · n₁ ▷ r  ≤⟨ ⊛-monotone (∧-monotone z₁≤z₂ n₁≤n₂)
                                      (+-monotone s₁≤s₂ (·-monotoneʳ n₁≤n₂)) ⟩
    (z₂ ∧ n₂) ⊛ s₂ + p · n₂ ▷ r  ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  nr′-· : nr′ p r z s n · q ≤ nr′ p r (z · q) (s · q) (n · q)
  nr′-· {p = p} {r = r} {z = z} {s = s} {n = n} {q = q} = begin
    ((z ∧ n) ⊛ s + p · n ▷ r) · q              ≤⟨ ·-sub-distribʳ-⊛ _ _ _ _ ⟩
    ((z ∧ n) · q) ⊛ (s + p · n) · q ▷ r        ≡⟨ ⊛ᵣ-cong (·-distribʳ-∧ _ _ _) (·-distribʳ-+ _ _ _) ⟩
    (z · q ∧ n · q) ⊛ s · q + (p · n) · q ▷ r  ≡⟨ ⊛ᵣ-congˡ (+-congˡ (·-assoc _ _ _)) ⟩
    (z · q ∧ n · q) ⊛ s · q + p · n · q ▷ r    ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  nr′-+ :
    nr′ p r z₁ s₁ n₁ + nr′ p r z₂ s₂ n₂ ≤
    nr′ p r (z₁ + z₂) (s₁ + s₂) (n₁ + n₂)
  nr′-+
    {p = p} {r = r}
    {z₁ = z₁} {s₁ = s₁} {n₁ = n₁} {z₂ = z₂} {s₂ = s₂} {n₂ = n₂} = begin
    (z₁ ∧ n₁) ⊛ s₁ + p · n₁ ▷ r + (z₂ ∧ n₂) ⊛ s₂ + p · n₂ ▷ r    ≤⟨ +-sub-interchangeable-⊛ _ _ _ _ _ ⟩
    ((z₁ ∧ n₁) + (z₂ ∧ n₂)) ⊛ (s₁ + p · n₁) + (s₂ + p · n₂) ▷ r  ≤⟨ ⊛-monotone (+-sub-interchangeable-∧ _ _ _ _) lemma ⟩
    ((z₁ + z₂) ∧ (n₁ + n₂)) ⊛ (s₁ + s₂) + p · (n₁ + n₂) ▷ r      ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

    lemma = begin
      (s₁ + p · n₁) + (s₂ + p · n₂)  ≡⟨ +-assoc _ _ _ ⟩
      s₁ + (p · n₁ + (s₂ + p · n₂))  ≡˘⟨ cong (_ +_) (+-assoc _ _ _) ⟩
      s₁ + ((p · n₁ + s₂) + p · n₂)  ≡⟨ cong (_ +_) (cong (flip _+_ _) (+-comm _ _)) ⟩
      s₁ + ((s₂ + p · n₁) + p · n₂)  ≡⟨ cong (_ +_) (+-assoc _ _ _) ⟩
      s₁ + (s₂ + (p · n₁ + p · n₂))  ≡˘⟨ +-assoc _ _ _ ⟩
      (s₁ + s₂) + (p · n₁ + p · n₂)  ≡˘⟨ cong (_+_ _) (·-distribˡ-+ _ _ _) ⟩
      (s₁ + s₂) + p · (n₁ + n₂)      ∎

  nr′-positive :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄ →
    nr′ p r z s n ≡ 𝟘 → z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘
  nr′-positive {p = p} {r = r} {z = z} {s = s} {n = n} =
    (z ∧ n) ⊛ s + p · n ▷ r ≡ 𝟘  →⟨ (λ hyp → ⊛≡𝟘ˡ hyp , ⊛≡𝟘ʳ hyp) ⟩
    z ∧ n ≡ 𝟘 × s + p · n ≡ 𝟘    →⟨ (λ (hyp₁ , hyp₂) →
                                       ∧-positiveˡ hyp₁ , +-positiveˡ hyp₂ , ∧-positiveʳ hyp₁) ⟩
    z ≡ 𝟘 × s ≡ 𝟘 × n ≡ 𝟘        □

  -- The argument of type n ≤ 𝟘 is not used.

  nr′-zero : n ≤ 𝟘 → nr′ p r z s n ≤ z
  nr′-zero {n = n} {p = p} {r = r} {z = z} {s = s} _ = begin
    (z ∧ n) ⊛ s + p · n ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
    z ∧ n                    ≤⟨ ∧-decreasingˡ _ _ ⟩
    z                        ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  nr′-suc : nr′ p r z s n ≤ s + p · n + r · nr′ p r z s n
  nr′-suc {p = p} {r = r} {z = z} {s = s} {n = n} = begin
    (z ∧ n) ⊛ s + p · n ▷ r                      ≤⟨ ⊛-ineq₁ _ _ _ ⟩
    (s + p · n) + r · ((z ∧ n) ⊛ s + p · n ▷ r)  ≡⟨ +-assoc _ _ _ ⟩
    s + p · n + r · ((z ∧ n) ⊛ s + p · n ▷ r)    ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

-- The function Has-nr.nr has-nr p r z s is decreasing.

nr-decreasing : Has-nr.nr has-nr p r z s n ≤ n
nr-decreasing {p = p} {r = r} {z = z} {s = s} {n = n} = begin
  (z ∧ n) ⊛ s + p · n ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
  z ∧ n                    ≤⟨ ∧-decreasingʳ _ _ ⟩
  n                        ∎
  where
  open Tools.Reasoning.PartialOrder ≤-poset
