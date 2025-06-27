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
open import Graded.Modality.Properties 𝕄 hiding (has-nr)
open import Graded.Mode 𝕄 using (𝟘ᵐ; 𝟙ᵐ)
open import Graded.Usage.Restrictions.Natrec 𝕄

open import Tools.Nat using (Nat)
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  n : Nat

record Assumptions : Set a where
  no-eta-equality
  infix 10 _≟_ _≤?_ _≤ᶜ?_
  field
    -- Equality is assumed to be decidable for M.
    _≟_ : Decidable (_≡_ {A = M})

    -- The relation Prodrec-allowed-𝟙ᵐ is assumed to be decidable.
    Prodrec-allowed-𝟙ᵐ? : ∀ r p q → Dec (Prodrec-allowed-𝟙ᵐ r p q)

    -- The relation Unitrec-allowed-𝟙ᵐ is assumed to be decidable.
    Unitrec-allowed-𝟙ᵐ? : ∀ p q → Dec (Unitrec-allowed-𝟙ᵐ p q)

    -- The relation Emptyrec-allowed-𝟙ᵐ is assumed to be decidable.
    Emptyrec-allowed-𝟙ᵐ? : ∀ p → Dec (Emptyrec-allowed-𝟙ᵐ p)

    -- The relation []-cong-allowed-mode-𝟙ᵐ is assumed to be
    -- decidable.
    []-cong-allowed-mode-𝟙ᵐ? : ∀ s → Dec ([]-cong-allowed-mode-𝟙ᵐ s)

    instance
      -- The inference function is supported
      ⦃ inference-ok ⦄ : Natrec-mode-supports-usage-inference natrec-mode

    -- Either strong unit types are not allowed to be used as sinks,
    -- or 𝟘 is a greatest grade.
    no-sink-or-≤𝟘 : ¬ Starˢ-sink ⊎ (∀ {p} → p ≤ 𝟘)

  -- Inequality is decidable.

  _≤?_ : Decidable _≤_
  _≤?_ = ≡-decidable→≤-decidable _≟_

  -- Context inequality is decidable.

  _≤ᶜ?_ : Decidable (_≤ᶜ_ {n = n})
  _≤ᶜ?_ = ≤ᶜ-decidable _≤?_

  opaque

    -- The relation Prodrec-allowed is decidable.

    Prodrec-allowed? : ∀ m r p q → Dec (Prodrec-allowed m r p q)
    Prodrec-allowed? 𝟘ᵐ = λ _ _ _ → yes _
    Prodrec-allowed? 𝟙ᵐ = Prodrec-allowed-𝟙ᵐ?

  opaque

    -- The relation Unitrec-allowed is decidable.

    Unitrec-allowed? : ∀ m p q → Dec (Unitrec-allowed m p q)
    Unitrec-allowed? 𝟘ᵐ = λ _ _ → yes _
    Unitrec-allowed? 𝟙ᵐ = Unitrec-allowed-𝟙ᵐ?

  opaque

    -- The relation Emptyrec-allowed is decidable.

    Emptyrec-allowed? : ∀ m p → Dec (Emptyrec-allowed m p)
    Emptyrec-allowed? 𝟘ᵐ = λ _ → yes _
    Emptyrec-allowed? 𝟙ᵐ = Emptyrec-allowed-𝟙ᵐ?

  opaque

    -- The relation []-cong-allowed-mode is decidable.

    []-cong-allowed-mode? : ∀ s m → Dec ([]-cong-allowed-mode s m)
    []-cong-allowed-mode? _ 𝟘ᵐ = yes _
    []-cong-allowed-mode? s 𝟙ᵐ = []-cong-allowed-mode-𝟙ᵐ? s
