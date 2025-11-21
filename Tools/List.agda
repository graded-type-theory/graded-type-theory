------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Tools.List where

open import Data.List.Membership.Propositional public using (_∈_)

module L where
  open import Data.List public
  open import Data.List.Properties public

open L public
  using (List; []; _∷_; foldr; map; _++_; length; length-++; ≡-dec)

module All where
  open import Data.List.Relation.Unary.All public
  open import Data.List.Relation.Unary.All.Properties public

open All public using (All; []; _∷_; lookup) hiding (module All)

module Any where
  open import Data.List.Relation.Unary.Any public
  open import Data.List.Relation.Unary.Any.Properties public

open Any public using (here; there)

module Pointwise where
  open import Data.List.Relation.Binary.Pointwise public

open import Tools.Maybe
open import Tools.PropositionalEquality

private variable
  A : Set _

-- A list membership test.

member? :
  ((x y : A) → Maybe (x ≡ y)) →
  ((x : A) (xs : List A) → Maybe (x ∈ xs))
member? _   _ []       = nothing
member? _≟_ x (y ∷ xs) with x ≟ y
… | just eq = just (here eq)
… | nothing = there <$> member? _≟_ x xs
