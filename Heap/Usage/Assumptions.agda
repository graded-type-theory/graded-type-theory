------------------------------------------------------------------------
-- Assumptions used to prove preservation of usage (among other things)
------------------------------------------------------------------------

module Heap.Usage.Assumptions where

open import Graded.Modality
open import Graded.Modality.Properties.Subtraction
open import Graded.Mode
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions
import Graded.Modality.Dedicated-nr as DNr

open import Definition.Typed.Variant

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

record UsageAssumptions {a} {M : Set a}
                        {𝕄 : Modality M}
                        (type-variant : Type-variant)
                        (UR : Usage-restrictions 𝕄) : Set a where
  open Modality 𝕄
  open Usage-restrictions UR
  open Type-variant type-variant

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
    no-erased-unitrec   : ∀ {m p q} → ¬ Unitʷ-η → Unitrec-allowed m p q → p ≢ 𝟘
    no-erased-unitrec-η : ∀ {m p q} → Unitʷ-η → Unitrec-allowed m p q → p ≤ 𝟘
    no-erased-prodrec   : ∀ {m p q r} → Prodrec-allowed m r p q → r ≢ 𝟘
    no-erased-J         : ∀ {m} → erased-matches-for-J m ≡ none
    no-erased-K         : ∀ {m} → erased-matches-for-K m ≡ none
    no-[]-cong          : ∀ {m s} → ¬ []-cong-allowed-mode s m

    -- An assumption used for the weak unit type with η-equality


    -- Properties of the semiring
    subtraction-ok : Supports-subtraction semiring-with-meet
    instance
      well-behaved-𝟘 : Has-well-behaved-zero M semiring-with-meet


  no-erased-J-some : ∀ {m} → erased-matches-for-J m ≢ some
  no-erased-J-some x with trans (sym x) no-erased-J
  ... | ()
  no-erased-J-all : ∀ {m} → erased-matches-for-J m ≢ all
  no-erased-J-all x with trans (sym x) no-erased-J
  ... | ()

  no-erased-K-some : ∀ {m} → erased-matches-for-K m ≢ some
  no-erased-K-some x with trans (sym x) no-erased-K
  ... | ()
  no-erased-K-all : ∀ {m} → erased-matches-for-K m ≢ all
  no-erased-K-all x with trans (sym x) no-erased-K
  ... | ()
