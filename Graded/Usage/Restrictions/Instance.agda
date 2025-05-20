------------------------------------------------------------------------
-- Instances related to Usage-restrictions
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage.Restrictions.Instance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Usage-restrictions 𝕄)
  where

open import Graded.Usage.Restrictions.Natrec 𝕄

open Usage-restrictions R
open Modality 𝕄

instance

  Nr-available-Has-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Has-nr M semiring-with-meet
  Nr-available-Has-nr ⦃ has-nr ⦄ =
    Natrec-mode-Has-nr has-nr

instance

  Nr-not-available-Has-well-behaved-GLBs :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    Has-well-behaved-GLBs M semiring-with-meet
  Nr-not-available-Has-well-behaved-GLBs ⦃ no-nr ⦄ =
    Natrec-mode-Has-well-behaved-GLBs no-nr
