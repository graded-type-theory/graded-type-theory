open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Properties.Equivalence {a ℓ}
  {M′ : Setoid a ℓ}
  (𝕄 : ModalityWithout⊛ M′)
  where

open ModalityWithout⊛ 𝕄
open Setoid M′ renaming (Carrier to M)

import Tools.Reasoning.Equivalence

private variable
  p q : M

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
  open Tools.Reasoning.Equivalence M′

-- If 𝟙 ≈ 𝟘, then _≈_ is trivial.

≈-trivial : 𝟙 ≈ 𝟘 → p ≈ q
≈-trivial {p = p} {q = q} 𝟙≈𝟘 = begin
  p  ≈⟨ ≈𝟘 𝟙≈𝟘 ⟩
  𝟘  ≈˘⟨ ≈𝟘 𝟙≈𝟘 ⟩
  q  ∎
  where
  open Tools.Reasoning.Equivalence M′
