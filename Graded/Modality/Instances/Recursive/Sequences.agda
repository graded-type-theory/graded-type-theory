------------------------------------------------------------------------
-- The family of sequences that Graded.Modality.Instances.Recursive is
-- about
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Instances.Recursive.Sequences
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality

-- The family of sequences that Graded.Modality.Instances.Recursive is
-- about (for each r the function λ n p q → nr n p q r is a sequence).

nr : Nat → M → M → M → M
nr 0      _ _ _ = 𝟘
nr (1+ n) p q r = p ∧ (q + r · nr n p q r)

-- Has-fixpoints-nr holds if every sequence in the family has a
-- certain kind of fixpoint.

Has-fixpoints-nr : Set a
Has-fixpoints-nr =
  ∀ r → ∃ λ n → ∀ p q → nr (1+ n) p q r ≡ nr n p q r
