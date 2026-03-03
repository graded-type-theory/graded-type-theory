------------------------------------------------------------------------
-- Properties of the modality structure that hold if 𝟘 is well-behaved.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Properties.Has-well-behaved-zero
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Modality 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero 𝕄 ⦄
  where


open Has-well-behaved-zero 𝟘-well-behaved public

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties.Addition 𝕄
open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄
open import Tools.PropositionalEquality

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    p q r : M

-- If p + q is zero, then q is zero.

+-positiveʳ : p + q ≡ 𝟘 → q ≡ 𝟘
+-positiveʳ p+q≡𝟘 = +-positiveˡ (trans (+-comm _ _) p+q≡𝟘)

-- If p + q is zero, then p and q are zero.

+-positive : p + q ≡ 𝟘 → p ≡ 𝟘 × q ≡ 𝟘
+-positive p+q≡𝟘 = +-positiveˡ p+q≡𝟘 , +-positiveʳ p+q≡𝟘

-- If p ∧ q is zero, then q is zero.

∧-positiveʳ : p ∧ q ≡ 𝟘 → q ≡ 𝟘
∧-positiveʳ p∧q≡𝟘 = ∧-positiveˡ (trans (∧-comm _ _) p∧q≡𝟘)

-- If p ∧ q is zero, then p and q are zero.

∧-positive : p ∧ q ≡ 𝟘 → p ≡ 𝟘 × q ≡ 𝟘
∧-positive p∧q≡𝟘 = ∧-positiveˡ p∧q≡𝟘 , ∧-positiveʳ p∧q≡𝟘

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

-- If p is bounded by q and p is 𝟘, then q is 𝟘.

≤→≡𝟘→≡𝟘 : p ≤ q → p ≡ 𝟘 → q ≡ 𝟘
≤→≡𝟘→≡𝟘 p≤q refl = 𝟘≮ p≤q

-- 𝟘 is not less than or equal to 𝟙

𝟘≰𝟙 : 𝟘 ≤ 𝟙 → ⊥
𝟘≰𝟙 𝟘≤𝟙 = non-trivial (𝟘≮ 𝟘≤𝟙)

-- The meet of 𝟘 and 𝟙 is strictly below 𝟘.

𝟘∧𝟙<𝟘 : 𝟘 ∧ 𝟙 < 𝟘
𝟘∧𝟙<𝟘 =
    ∧-decreasingˡ _ _
  , (𝟘 ∧ 𝟙 ≡ 𝟘  →⟨ sym ⟩
     𝟘 ≤ 𝟙      →⟨ 𝟘≰𝟙 ⟩
     ⊥          □)

opaque

  -- The grade ω is strictly less than 𝟘.

  ω<𝟘 : ω < 𝟘
  ω<𝟘 = ≤<-trans ω≤𝟘∧𝟙 𝟘∧𝟙<𝟘

-- The grade ω is not equal to 𝟘.

ω≢𝟘 : ω ≢ 𝟘
ω≢𝟘 = ω<𝟘 .proj₂

-- If p ⊛ q ▷ r is equal to zero, then p is equal to zero.

⊛≡𝟘ˡ :
  ⦃ has-star : Has-star 𝕄 ⦄ →
  p ⊛ q ▷ r ≡ 𝟘 → p ≡ 𝟘
⊛≡𝟘ˡ {p = p} {q = q} {r = r} p⊛q▷r≡𝟘 = 𝟘≮ (begin
  𝟘          ≈˘⟨ p⊛q▷r≡𝟘 ⟩
  p ⊛ q ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
  p          ∎)
  where
  open import Tools.Reasoning.PartialOrder ≤-poset

-- If p ⊛ q ▷ r is equal to zero, then q is equal to zero.

⊛≡𝟘ʳ :
  ⦃ has-star : Has-star 𝕄 ⦄ →
  p ⊛ q ▷ r ≡ 𝟘 → q ≡ 𝟘
⊛≡𝟘ʳ {p = p} {q = q} {r = r} p⊛q▷r≡𝟘 = +-positiveˡ (𝟘≮ (begin
  𝟘                  ≈˘⟨ p⊛q▷r≡𝟘 ⟩
  p ⊛ q ▷ r          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
  q + r · p ⊛ q ▷ r  ∎))
  where
  open import Tools.Reasoning.PartialOrder ≤-poset
