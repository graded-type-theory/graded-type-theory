------------------------------------------------------------------------
-- Properties of meet.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.Meet
  {a} {M : Set a} (𝕄 : Semiring-with-meet M) where

open Semiring-with-meet 𝕄

open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    p p′ q q′ r r′ : M

-- Meet on the left is a monotone function
-- If p ≤ q then p ∧ r ≤ q ∧ r

∧-monotoneˡ : p ≤ q → p ∧ r ≤ q ∧ r
∧-monotoneˡ {p} {q} {r} p≤q = begin
  p ∧ r             ≡⟨ ∧-cong p≤q (sym (∧-idem r)) ⟩
  (p ∧ q) ∧ r ∧ r   ≡⟨ ∧-assoc p q (r ∧ r) ⟩
  p ∧ q ∧ r ∧ r     ≡⟨ ∧-congˡ (∧-comm q (r ∧ r)) ⟩
  p ∧ (r ∧ r) ∧ q   ≡⟨ ∧-congˡ (∧-assoc r r q) ⟩
  p ∧ r ∧ r ∧ q     ≡˘⟨ ∧-assoc p r (r ∧ q) ⟩
  (p ∧ r) ∧ r ∧ q   ≡⟨ ∧-congˡ (∧-comm r q) ⟩
  (p ∧ r) ∧ (q ∧ r) ∎
  where open Tools.Reasoning.PropositionalEquality

-- Meet on the right is a monotone function
-- If p ≤ q then r ∧ p ≤ r ∧ q

∧-monotoneʳ : p ≤ q → r ∧ p ≤ r ∧ q
∧-monotoneʳ {p} {q} {r} p≤q = begin
  r ∧ p             ≡⟨ ∧-cong (sym (∧-idem r)) p≤q ⟩
  (r ∧ r) ∧ (p ∧ q) ≡⟨ ∧-assoc r r (p ∧ q) ⟩
  r ∧ r ∧ p ∧ q     ≡⟨ ∧-congˡ (∧-comm r (p ∧ q)) ⟩
  r ∧ (p ∧ q) ∧ r   ≡⟨ ∧-congˡ (∧-assoc p q r) ⟩
  r ∧ p ∧ (q ∧ r)   ≡˘⟨ ∧-assoc r p (q ∧ r) ⟩
  (r ∧ p) ∧ (q ∧ r) ≡⟨ ∧-congˡ (∧-comm q r) ⟩
  (r ∧ p) ∧ (r ∧ q) ∎
  where open Tools.Reasoning.PropositionalEquality

-- Meet is a monotone function
-- If p ≤ p′ and q ≤ q′ then p ∧ q ≤ p′ ∧ q′

∧-monotone : p ≤ p′ → q ≤ q′ → p ∧ q ≤ p′ ∧ q′
∧-monotone p≤p′ q≤q′ = ≤-trans (∧-monotoneˡ  p≤p′) (∧-monotoneʳ q≤q′)

-- Meet on the left is a decreasing function
-- p ∧ q ≤ p

∧-decreasingˡ : (p q : M) → p ∧ q ≤ p
∧-decreasingˡ p q = begin
  p ∧ q       ≡˘⟨ ∧-congʳ (∧-idem p) ⟩
  (p ∧ p) ∧ q ≡⟨ ∧-assoc p p q ⟩
  p ∧ (p ∧ q) ≡⟨ ∧-comm p (p ∧ q) ⟩
  (p ∧ q) ∧ p ∎
  where open Tools.Reasoning.PropositionalEquality

-- Meet on the right is a decreasing function
-- p ∧ q ≤ q

∧-decreasingʳ : (p q : M) → p ∧ q ≤ q
∧-decreasingʳ p q = begin
  p ∧ q       ≡˘⟨ ∧-congˡ (∧-idem q) ⟩
  p ∧ (q ∧ q) ≡˘⟨ ∧-assoc p q q ⟩
  (p ∧ q) ∧ q ∎
  where open Tools.Reasoning.PropositionalEquality

-- The result of the meet operation is a greatest lower bound of its
-- two arguments.

∧-greatest-lower-bound : p ≤ q → p ≤ r → p ≤ q ∧ r
∧-greatest-lower-bound {p = p} {q = q} {r = r} p≤q p≤r = begin
  p            ≡⟨ p≤q ⟩
  p ∧ q        ≡⟨ ∧-congʳ p≤r ⟩
  (p ∧ r) ∧ q  ≡⟨ ∧-assoc _ _ _ ⟩
  p ∧ (r ∧ q)  ≡⟨ ∧-congˡ (∧-comm _ _) ⟩
  p ∧ (q ∧ r)  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- If p is strictly below q ∧ r, then p is strictly below q.

<∧ˡ : p < q ∧ r → p < q
<∧ˡ {p = p} {q = q} {r = r} (p≤q∧r , p≢q∧r) =
    (let open Tools.Reasoning.PartialOrder ≤-poset in begin
       p      ≤⟨ p≤q∧r ⟩
       q ∧ r  ≤⟨ ∧-decreasingˡ _ _ ⟩
       q      ∎)
  , (let open Tools.Reasoning.PropositionalEquality in λ p≡q →
     p≢q∧r (
       p            ≡⟨ p≤q∧r ⟩
       p ∧ (q ∧ r)  ≡˘⟨ ∧-assoc _ _ _ ⟩
       (p ∧ q) ∧ r  ≡⟨ cong (λ p → (p ∧ _) ∧ _) p≡q ⟩
       (q ∧ q) ∧ r  ≡⟨ cong (_∧ _) (∧-idem _) ⟩
       q ∧ r        ∎))

-- If p is strictly below q ∧ r, then p is strictly below r.

<∧ʳ : p < q ∧ r → p < r
<∧ʳ p<q∧r = <∧ˡ (subst (_ <_) (∧-comm _ _) p<q∧r)

-- If _+_ is pointwise bounded by _∧_, then 𝟘 is larger than all other
-- quantities.

+≤∧→≤𝟘 :
  (∀ p q → p + q ≤ p ∧ q) →
  (∀ p → p ≤ 𝟘)
+≤∧→≤𝟘 +≤∧ p =
  p                  ≡˘⟨ +-identityʳ _ ⟩
  p + 𝟘              ≡⟨ +≤∧ _ _ ⟩
  (p + 𝟘) ∧ (p ∧ 𝟘)  ≡⟨ ∧-congʳ (+-identityʳ _) ⟩
  p ∧ (p ∧ 𝟘)        ≡˘⟨ ∧-assoc _ _ _ ⟩
  (p ∧ p) ∧ 𝟘        ≡⟨ ∧-congʳ (∧-idem _) ⟩
  p ∧ 𝟘              ∎
  where
  open Tools.Reasoning.PropositionalEquality
