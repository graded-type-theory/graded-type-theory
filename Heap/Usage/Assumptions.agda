------------------------------------------------------------------------
-- Assumptions used to prove preservation of usage (among other things)
------------------------------------------------------------------------

open import Graded.Usage.Restrictions

module Heap.Usage.Assumptions where

open import Graded.Modality
open import Graded.Modality.Properties.Subtraction
open import Graded.Mode
open import Graded.Usage.Erased-matches
import Graded.Modality.Dedicated-nr as DNr

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

record UsageAssumptions {a} {M : Set a}
                        {𝕄 : Modality M}
                        (UR : Usage-restrictions 𝕄) : Set a where
  open Modality 𝕄
  open Usage-restrictions UR

  -- natrec
  field
    nr-avail : Nr-available

  instance
    hasNr : Has-nr M semiring-with-meet
    hasNr = has-nr nr-avail

    dedicatedNr : DNr.Dedicated-nr 𝕄
    dedicatedNr = DNr.dedicated-nr nr-avail

  field instance
    has-factoring-nr : Has-factoring-nr M semiring-with-meet

  field
    -- Erased matches
    no-erased-unitrec : ∀ {p q} → Unitrec-allowed 𝟙ᵐ p q → p ≤ 𝟙
    no-erased-prodrec : ∀ {p q r} → Prodrec-allowed 𝟙ᵐ r p q → r ≢ 𝟘
    no-erased-J       : erased-matches-for-J 𝟙ᵐ ≡ none
    no-erased-K       : erased-matches-for-K 𝟙ᵐ ≡ none
    no-[]-cong        : ∀ {s} → ¬ []-cong-allowed-mode s 𝟙ᵐ

    -- Properties of the semiring
    subtraction-ok : Supports-subtraction semiring-with-meet
    instance
      well-behaved-𝟘 : Has-well-behaved-zero M semiring-with-meet


  no-erased-J-some : erased-matches-for-J 𝟙ᵐ ≢ some
  no-erased-J-some x with trans (sym x) no-erased-J
  ... | ()
  no-erased-J-all : erased-matches-for-J 𝟙ᵐ ≢ all
  no-erased-J-all x with trans (sym x) no-erased-J
  ... | ()

  no-erased-K-some : erased-matches-for-K 𝟙ᵐ ≢ some
  no-erased-K-some x with trans (sym x) no-erased-K
  ... | ()
  no-erased-K-all : erased-matches-for-K 𝟙ᵐ ≢ all
  no-erased-K-all x with trans (sym x) no-erased-K
  ... | ()
