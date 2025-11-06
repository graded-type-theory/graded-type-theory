------------------------------------------------------------------------
-- Assumptions used to prove some properties of the heap semantics.
-- In particular used for Bisimilarity, Termination and Soundness.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Heap.Assumptions
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Mode 𝕄
open import Graded.Modality.Properties.Subtraction semiring-with-meet
open import Graded.Usage.Restrictions.Natrec 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

-- Assumptions that are used to prove some bisimilarity properties
-- as well as some properties elsewhere that follow from them

record Assumptions : Set a where
  field
    -- The type Level is not allowed.
    Level-not-allowed : ¬ Level-allowed
    -- The modality supports subtraction.
    subtraction-ok : Supports-subtraction
    -- An assumption related to the weak unit type when η-equality is
    -- enabled.
    Unitʷ-η→ : ∀ {p q} → Unitʷ-η → Unitrec-allowed 𝟙ᵐ p q → p ≤ 𝟘
    -- Either the usage rule for natrec with an nr function is used
    -- (in which case it is assumed to be factoring) or the usage rule
    -- using greatest lower bounds is used.
    natrec-mode-ok :
      (Σ Nr-available λ has-nr →
        Is-factoring-nr M (Natrec-mode-Has-nr has-nr)) ⊎
      Nr-not-available-GLB
    instance
      -- The modality has a well-behaved zero
      has-well-behaved-zero : Has-well-behaved-zero M semiring-with-meet

  opaque

    -- The usage rule without nr functions and without greatest lower
    -- bounds is not used.

    ¬Nr-not-available : ¬ Nr-not-available
    ¬Nr-not-available x =
      case natrec-mode-ok of λ where
        (inj₁ (y , _)) → ¬[Nr∧No-nr] y x
        (inj₂ y) → ¬[No-nr∧No-nr-glb] x y

  opaque

    -- If the usage rule for natrec with an nr function is used then
    -- the nr funciton is factoring.

    factoring-nr :
      ⦃ has-nr : Nr-available ⦄ →
      Is-factoring-nr M (Natrec-mode-Has-nr has-nr)
    factoring-nr ⦃ has-nr ⦄ =
      case natrec-mode-ok of λ where
        (inj₁ (has-nr′ , factoring)) →
          case Nr-available-propositional has-nr has-nr′ of λ where
            refl → factoring
        (inj₂ no-nr) → ⊥-elim (¬[Nr∧No-nr-glb] has-nr no-nr)
