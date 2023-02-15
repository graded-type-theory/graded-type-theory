{-# OPTIONS --without-K --safe #-}

module Tools.Bool where

open import Data.Bool.Base
  using (Bool; true; false; _∧_; _∨_; if_then_else_; T)
  public

open import Tools.PropositionalEquality

-- The function T is pointwise propositional.

T-propositional : ∀ {b} {x y : T b} → x ≡ y
T-propositional {b = true} = refl
