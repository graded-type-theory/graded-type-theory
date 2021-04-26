{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

-- Reasoning for equivalence relations using preorder relation syntax

module Tools.Reasoning.Equivalence
  {ℓ} {A : Set} {_≈_ : Rel A ℓ} (E : IsEquivalence _≈_)
  where

-- ≈ is a preorder

≈-isPreorder : IsPreorder _≈_ _≈_
≈-isPreorder = record
  { isEquivalence = E
  ; reflexive = λ x → x
  ; trans = IsEquivalence.trans E
  }

≈-preorder : Preorder _ _ _
≈-preorder = record
  { Carrier = A
  ; _≈_ = _≈_
  ; _∼_ = _≈_
  ; isPreorder = ≈-isPreorder
  }

open import Tools.Reasoning.Preorder ≈-preorder public
