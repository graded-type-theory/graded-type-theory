------------------------------------------------------------------------
-- Properties of the partial order relation.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.PartialOrder
  {a} {M : Set a} (𝕄 : Semiring-with-meet M) where

open Semiring-with-meet 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation

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
  (trans (∧-congˡ q≤r)
     (sym (trans (∧-congʳ p≤q) (∧-assoc p q r))))

-- The relation _≤_ is antisymmetric.

≤-antisym : p ≤ q → q ≤ p → p ≡ q
≤-antisym {p} {q} p≤q q≤p = trans p≤q (trans (∧-comm p q) (sym q≤p))

-- The relation _≤_ is a non-strict ordering relation.

≤-reflexive : p ≡ q → p ≤ q
≤-reflexive {p} p≡q = trans (sym (∧-idem p)) (∧-congˡ p≡q)

-- ≤ is a preorder relation

≤-preorder : IsPreorder _≡_ _≤_
≤-preorder = record
  { isEquivalence = PE.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

-- ≤ is a partial ordering relation

≤-partial : IsPartialOrder _≡_ _≤_
≤-partial = record
  { isPreorder = ≤-preorder
  ; antisym    = ≤-antisym
  }

-- (M, ≤) is a poset

≤-poset : Poset _ _ _
≤-poset = record
  { Carrier        = M
  ; _≈_            = _≡_
  ; _≤_            = _≤_
  ; isPartialOrder = ≤-partial
  }

-- If _≡_ is decidable (for M), then _≤_ is decidable.

≡-decidable→≤-decidable : Decidable (_≡_ {A = M}) → Decidable _≤_
≡-decidable→≤-decidable _≡?_ p q = p ≡? (p ∧ q)

-- If _≡_ is decidable (for M), then _<_ is decidable.

≡-decidable→<-decidable : Decidable (_≡_ {A = M}) → Decidable _<_
≡-decidable→<-decidable _≡?_ p q with ≡-decidable→≤-decidable _≡?_ p q
… | no p≰q  = no (p≰q ∘→ proj₁)
… | yes p≤q with p ≡? q
…   | no p≢q  = yes (p≤q , p≢q)
…   | yes p≡q = no ((_$ p≡q) ∘→ proj₂)

-- If p is strictly below q, then q is not bounded by p.

<→≰ : p < q → ¬ q ≤ p
<→≰ (p≤q , p≢q) q≤p = p≢q (≤-antisym p≤q q≤p)

opaque

  -- A kind of transitivity for _<_.

  <≤-trans : p < q → q ≤ r → p < r
  <≤-trans {p} {q} {r} (p≤q , p≢q) q≤r =
      ≤-trans p≤q q≤r
    , (p ≡ r  →⟨ flip (subst (_ ≤_)) q≤r ∘→ sym ⟩
       q ≤ p  →⟨ ≤-antisym p≤q ⟩
       p ≡ q  →⟨ p≢q ⟩
       ⊥      □)

opaque

  -- Another kind of transitivity for _<_.

  ≤<-trans : p ≤ q → q < r → p < r
  ≤<-trans {p} {q} {r} p≤q (q≤r , q≢r) =
      ≤-trans p≤q q≤r
    , (p ≡ r  →⟨ flip (subst (_≤ _)) p≤q ⟩
       r ≤ q  →⟨ ≤-antisym q≤r ⟩
       q ≡ r  →⟨ q≢r ⟩
       ⊥      □)
