------------------------------------------------------------------------
-- Assumptions used to prove that the usage relation is decidable
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage.Decidable.Assumptions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Properties 𝕄 hiding (has-nr)

open import Tools.Nat using (Nat)
open import Tools.PropositionalEquality
open import Tools.Relation

private variable
  n : Nat

record Assumptions : Set a where
  no-eta-equality
  infix 10 _≟_ _≤?_ _≤ᶜ?_
  field
    -- Equality is assumed to be decidable for M.
    _≟_ : Decidable (_≡_ {A = M})

    -- The Prodrec-allowed relation is assumed to be decidable.
    Prodrec-allowed? : ∀ m r p q → Dec (Prodrec-allowed m r p q)

    -- The Unitrec-allowed relation is assumed to be decidable.
    Unitrec-allowed? : ∀ m p q → Dec (Unitrec-allowed m p q)

    -- The Emptyrec-allowed relation is assumed to be decidable.
    Emptyrec-allowed? : ∀ m p → Dec (Emptyrec-allowed m p)

    -- The []-cong-allowed-mode relation is assumed to be decidable.
    []-cong-allowed-mode? : ∀ s m → Dec ([]-cong-allowed-mode s m)

    instance
      -- A dedicated nr function is assumed to exist.
      ⦃ has-nr ⦄ : Dedicated-nr

      -- Strong unit types are not allowed to be used as sinks.
      ⦃ no-sink ⦄ : ¬Starˢ-sink

  -- Inequality is decidable.

  _≤?_ : Decidable _≤_
  _≤?_ = ≡-decidable→≤-decidable _≟_

  -- Context inequality is decidable.

  _≤ᶜ?_ : Decidable (_≤ᶜ_ {n = n})
  _≤ᶜ?_ = ≤ᶜ-decidable _≤?_
