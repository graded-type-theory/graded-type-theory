------------------------------------------------------------------------
-- Equational resoning for equivalences
------------------------------------------------------------------------

open import Tools.Relation

-- Reasoning for equivalence relations using preorder relation syntax

module Tools.Reasoning.Equivalence {a ℓ} (S : Setoid a ℓ) where

open Setoid S

-- ≈ is a preorder

≈-isPreorder : IsPreorder _≈_ _≈_
≈-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive = λ x → x
  ; trans = trans
  }

≈-preorder : Preorder _ _ _
≈-preorder = record
  { Carrier = Carrier
  ; _≈_ = _≈_
  ; _∼_ = _≈_
  ; isPreorder = ≈-isPreorder
  }

open import Tools.Reasoning.Preorder ≈-preorder public
