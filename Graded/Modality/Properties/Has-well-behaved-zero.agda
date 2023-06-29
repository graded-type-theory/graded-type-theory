------------------------------------------------------------------------
-- Properties of the modality semiring that hold if 𝟘 is well-behaved.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.Has-well-behaved-zero
  {a} {M : Set a} (𝕄 : Semiring-with-meet-and-star M)
  (open Semiring-with-meet-and-star 𝕄)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet) where


open Has-well-behaved-zero 𝟘-well-behaved public

open import Graded.Modality.Properties.Meet semiring-with-meet
open import Graded.Modality.Properties.PartialOrder semiring-with-meet
open import Tools.PropositionalEquality

import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    p q r : M

-- If p + q is zero, then q is zero.

+-positiveʳ : p + q ≡ 𝟘 → q ≡ 𝟘
+-positiveʳ p+q≡𝟘 = +-positiveˡ (trans (+-comm _ _) p+q≡𝟘)

-- If p ∧ q is zero, then q is zero.

∧-positiveʳ : p ∧ q ≡ 𝟘 → q ≡ 𝟘
∧-positiveʳ p∧q≡𝟘 = ∧-positiveˡ (trans (∧-comm _ _) p∧q≡𝟘)

-- Every value that is "greater than or
-- equal to" 𝟘 is equivalent to 𝟘.
--
-- This property matches one of the assumptions in Conor McBride's "I
-- Got Plenty o’ Nuttin’".

𝟘≮ : 𝟘 ≤ p → p ≡ 𝟘
𝟘≮ {p = p} 𝟘≤p = ∧-positiveˡ (begin
  p ∧ 𝟘  ≡⟨ ∧-comm _ _ ⟩
  𝟘 ∧ p  ≡˘⟨ 𝟘≤p ⟩
  𝟘      ∎)
  where
  open Tools.Reasoning.PropositionalEquality

-- 𝟘 is not less than or equal to 𝟙

𝟘≰𝟙 : 𝟘 ≤ 𝟙 → ⊥
𝟘≰𝟙 𝟘≤𝟙 = 𝟙≢𝟘 (𝟘≮ 𝟘≤𝟙)

-- If the mode 𝟘ᵐ is allowed and p ⊛ q ▷ r is equal to zero, then p is
-- equal to zero.

⊛≡𝟘ˡ : p ⊛ q ▷ r ≡ 𝟘 → p ≡ 𝟘
⊛≡𝟘ˡ {p = p} {q = q} {r = r} p⊛q▷r≡𝟘 = 𝟘≮ (begin
  𝟘          ≈˘⟨ p⊛q▷r≡𝟘 ⟩
  p ⊛ q ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
  p          ∎)
  where
  open import Tools.Reasoning.PartialOrder ≤-poset

-- If the mode 𝟘ᵐ is allowed and p ⊛ q ▷ r is equal to zero, then q is
-- equal to zero.

⊛≡𝟘ʳ : p ⊛ q ▷ r ≡ 𝟘 → q ≡ 𝟘
⊛≡𝟘ʳ {p = p} {q = q} {r = r} p⊛q▷r≡𝟘 = +-positiveˡ (𝟘≮ (begin
  𝟘                  ≈˘⟨ p⊛q▷r≡𝟘 ⟩
  p ⊛ q ▷ r          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
  q + r · p ⊛ q ▷ r  ∎))
  where
  open import Tools.Reasoning.PartialOrder ≤-poset
