------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Tools.List where

open import Data.List.Membership.Propositional public using (_∈_)

module L where
  open import Data.List public
  open import Data.List.Properties public

open L public
  using
    (List; []; _∷_; foldr; map; _++_; length; length-++; filterᵇ; ≡-dec)

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

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Maybe
open import Tools.Product
open import Tools.PropositionalEquality

private variable
  A B : Set _
  P   : A → Set _
  p   : A → B
  xs  : List _

-- A list membership test.

member? :
  ((x y : A) → Maybe (x ≡ y)) →
  ((x : A) (xs : List A) → Maybe (x ∈ xs))
member? _   _ []       = nothing
member? _≟_ x (y ∷ xs) with x ≟ y
… | just eq = just (here eq)
… | nothing = there <$> member? _≟_ x xs

opaque

  -- A characterisation lemma for All and filterᵇ.

  All-filterᵇ :
    All P (filterᵇ p xs) ⇔ All (λ x → T (p x) → P x) xs
  All-filterᵇ {p} = to _ , from _
    where
    to : ∀ xs → All P (filterᵇ p xs) → All (λ x → T (p x) → P x) xs
    to []       _          = []
    to (x ∷ xs) _          with p x in eq
    to (_ ∷ xs) (px ∷ pxs) | true  = (λ _ → px) ∷ to xs pxs
    to (_ ∷ xs) pxs        | false = ⊥-elim ∘→ ¬-T .proj₂ eq ∷ to xs pxs

    from : ∀ xs → All (λ x → T (p x) → P x) xs → All P (filterᵇ p xs)
    from []       _          = []
    from (x ∷ xs) _          with p x in eq
    from (_ ∷ xs) (_  ∷ pxs) | false = from xs pxs
    from (_ ∷ xs) (px ∷ pxs) | true  =
      px (T-true .proj₂ eq) ∷ from xs pxs
