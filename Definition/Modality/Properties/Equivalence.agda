open import Definition.Modality

module Definition.Modality.Properties.Equivalence
  {a} {M : Set a} (𝕄 : ModalityWithout⊛ M) where

open ModalityWithout⊛ 𝕄

open import Definition.Modality.Properties.PartialOrder 𝕄

open import Tools.Function
open import Tools.PropositionalEquality
import Tools.Reasoning.Equivalence
open import Tools.Relation

private variable
  p q : M

------------------------------------------------------------------------
-- Decision procedures

-- If _≤_ is decidable, then _≈_ is decidable (for M).

≤-decidable→≈-decidable : Decidable _≤_ → Decidable (_≈_ {A = M})
≤-decidable→≈-decidable _≤?_ p q = case p ≤? q of λ where
  (no p≰q)  → no λ p≈q → p≰q (≤-reflexive p≈q)
  (yes p≤q) → case q ≤? p of λ where
    (no q≰p)  → no λ p≈q → q≰p (≤-reflexive (≈-sym p≈q))
    (yes q≤p) → yes (≤-antisym p≤q q≤p)

------------------------------------------------------------------------
-- Properties that hold if 𝟙 ≈ 𝟘

-- If 𝟙 ≈ 𝟘, then every value is equal to 𝟘.

≈𝟘 : 𝟙 ≈ 𝟘 → p ≈ 𝟘
≈𝟘 {p = p} 𝟙≈𝟘 = begin
  p      ≈˘⟨ ·-identityˡ _ ⟩
  𝟙 · p  ≈⟨ ·-congʳ 𝟙≈𝟘 ⟩
  𝟘 · p  ≈⟨ ·-zeroˡ _ ⟩
  𝟘      ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)

-- If 𝟙 ≈ 𝟘, then _≈_ is trivial.

≈-trivial : 𝟙 ≈ 𝟘 → p ≈ q
≈-trivial {p = p} {q = q} 𝟙≈𝟘 = begin
  p  ≈⟨ ≈𝟘 𝟙≈𝟘 ⟩
  𝟘  ≈˘⟨ ≈𝟘 𝟙≈𝟘 ⟩
  q  ∎
  where
  open Tools.Reasoning.Equivalence (setoid M)
