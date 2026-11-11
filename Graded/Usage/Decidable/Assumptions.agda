------------------------------------------------------------------------
-- Assumptions used to prove that the usage relation is decidable
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Graded.Mode

module Graded.Usage.Decidable.Assumptions
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (C : Configuration 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Configuration C

open import Configuration-types.Natrec 𝕄

import Definition.Typechecking.Decidable.Assumptions TC as TC

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄 hiding (has-nr)

open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  n : Nat

record Assumptions : Set (a ⊔ b) where
  no-eta-equality
  field
    -- Assumptions used to decide typing.
    --
    -- Most of these are not needed to decide usage, but in practice
    -- one is likely to decide usage together with typing.
    assumptions : TC.Assumptions

  open TC.Assumptions assumptions public

  field
    -- The relation Prodrec-allowed is assumed to be decidable.
    Prodrec-allowed? : ∀ m r p q → Dec (Prodrec-allowed m r p q)

    -- The relation Unitrec-allowed is assumed to be decidable.
    Unitrec-allowed? : ∀ m p q → Dec (Unitrec-allowed m p q)

    -- The relation Emptyrec-allowed is assumed to be decidable.
    Emptyrec-allowed? : ∀ m p → Dec (Emptyrec-allowed m p)

    -- The relation []-cong-allowed-mode is assumed to be
    -- decidable.
    []-cong-allowed-mode? : ∀ s m → Dec ([]-cong-allowed-mode s m)

    instance
      -- The inference function is supported
      ⦃ inference-ok ⦄ : Natrec-mode-supports-usage-inference natrec-mode

    -- Either strong unit types are not allowed to be used as sinks,
    -- or 𝟘 is a greatest grade.
    no-sink-or-≤𝟘 : ¬ Starˢ-sink ⊎ (∀ {p} → p ≤ 𝟘)

  -- Inequality is decidable.

  infix 10 _≤?_

  _≤?_ : Decidable _≤_
  _≤?_ = ≡-decidable→≤-decidable _≟_

  -- Context inequality is decidable.

  infix 10 _≤ᶜ?_

  _≤ᶜ?_ : Decidable (_≤ᶜ_ {n = n})
  _≤ᶜ?_ = ≤ᶜ-decidable _≤?_
