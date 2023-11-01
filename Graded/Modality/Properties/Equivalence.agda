------------------------------------------------------------------------
-- Properties of equality.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.Equivalence
  {a} {M : Set a} (𝕄 : Semiring-with-meet M) where

open Semiring-with-meet 𝕄

open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Function
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  p q : M

------------------------------------------------------------------------
-- Decision procedures

-- If _≤_ is decidable, then _≡_ is decidable (for M).

≤-decidable→≡-decidable : Decidable _≤_ → Decidable (_≡_ {A = M})
≤-decidable→≡-decidable _≤?_ p q = case p ≤? q of λ where
  (no p≰q)  → no λ p≡q → p≰q (≤-reflexive p≡q)
  (yes p≤q) → case q ≤? p of λ where
    (no q≰p)  → no λ p≡q → q≰p (≤-reflexive (sym p≡q))
    (yes q≤p) → yes (≤-antisym p≤q q≤p)

------------------------------------------------------------------------
-- Some lemmas related to Trivial

-- If the semiring with meet is trivial, then every value is equal
-- to 𝟘.

≡𝟘 : Trivial → p ≡ 𝟘
≡𝟘 {p = p} 𝟙≡𝟘 = begin
  p      ≡˘⟨ ·-identityˡ _ ⟩
  𝟙 · p  ≡⟨ ·-congʳ 𝟙≡𝟘 ⟩
  𝟘 · p  ≡⟨ ·-zeroˡ _ ⟩
  𝟘      ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If the semiring with meet is trivial, then _≡_ is trivial.

≡-trivial : Trivial → p ≡ q
≡-trivial {p = p} {q = q} 𝟙≡𝟘 = begin
  p  ≡⟨ ≡𝟘 𝟙≡𝟘 ⟩
  𝟘  ≡˘⟨ ≡𝟘 𝟙≡𝟘 ⟩
  q  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If there are two distinct values, then the semiring with meet is
-- non-trivial.

≢→non-trivial : p ≢ q → ¬ Trivial
≢→non-trivial p≢q = p≢q ∘→ ≡-trivial
