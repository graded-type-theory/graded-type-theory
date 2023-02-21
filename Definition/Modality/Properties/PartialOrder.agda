open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Properties.PartialOrder {a ℓ}
  {M′ : Setoid a ℓ}
  (𝕄 : ModalityWithout⊛ M′)
  where

open ModalityWithout⊛ 𝕄
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
  (≈-trans (∧-congˡ q≤r)
  (≈-trans (≈-sym (∧-assoc p q r)) (∧-congʳ (≈-sym p≤q))))

-- ≤ is antisymmetric
-- If p ≤ q and q ≤ p then p ≈ q

≤-antisym : p ≤ q → q ≤ p → p ≈ q
≤-antisym {p} {q} p≤q q≤p = ≈-trans p≤q (≈-trans (∧-comm p q) (≈-sym q≤p))

-- ≤ is a non-strict ordering relation
-- If p ≈ q then p ≤ q

≤-reflexive : p ≈ q → p ≤ q
≤-reflexive {p} p≈q = ≈-trans (≈-sym (∧-idem p)) (∧-congˡ p≈q)

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
