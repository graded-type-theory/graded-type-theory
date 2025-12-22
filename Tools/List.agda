------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Tools.List where

open import Agda.Builtin.List public using (List; []; _∷_)
open import Data.List.Base public using (_++_; map; foldr; length)
open import Data.List.Membership.Propositional public using (_∈_)
open import Data.List.Properties public using (≡-dec; length-++)
open import Data.List.Relation.Unary.All public
  using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.Any public using (here; there)

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
