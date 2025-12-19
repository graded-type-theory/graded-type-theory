------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Tools.List where

open import Agda.Builtin.List public using (List; []; _∷_)
open import Data.List.Base public using (_++_; map; foldr; length)
open import Data.List.Membership.Propositional public using (_∈_)
open import Data.List.Properties public using (≡-dec; length-++)
open import Data.List.Relation.Unary.Any public using (here; there)

open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

private variable
  A   : Set _
  x y : A
  ys  : List _

opaque

  -- A characterisation lemma for _∈_.

  ∈∷⇔ : x ∈ y ∷ ys ⇔ (x ≡ y ⊎ x ∈ ys)
  ∈∷⇔ =
    (λ where
       (here eq)  → inj₁ eq
       (there x∈) → inj₂ x∈) ,
    (λ where
       (inj₁ eq) → here eq
       (inj₂ x∈) → there x∈)
