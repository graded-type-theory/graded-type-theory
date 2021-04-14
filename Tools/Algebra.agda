{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Tools.Algebra
  {a ℓ} {A : Set a}
  (_≈_ : Rel A ℓ)
  where

open import Algebra.Core public
open import Algebra.Definitions (_≈_) public
open import Algebra.Structures (_≈_) public

Op₃ : Set ℓ → Set ℓ
Op₃ A = A → A → A → A
