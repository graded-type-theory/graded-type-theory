------------------------------------------------------------------------
-- Instances related to Configuration
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Graded.Mode

module Configuration-types.Instance
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (C : Configuration 𝐌)
  where

open import Configuration-types.Natrec 𝕄
open import Configuration-types.Omega 𝕄

open Configuration-types.Configuration C
open Modality 𝕄

instance

  Nr-available-Has-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Has-nr M 𝕄
  Nr-available-Has-nr ⦃ has-nr ⦄ =
    Natrec-mode-Has-nr has-nr

instance

  Nr-not-available-Has-well-behaved-GLBs :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    Has-well-behaved-GLBs M 𝕄
  Nr-not-available-Has-well-behaved-GLBs ⦃ no-nr ⦄ =
    Natrec-mode-Has-well-behaved-GLBs no-nr

instance

  Usage-allows-omega-has-omega :
    ⦃ ok : Usage-allows-omega ⦄ →
    Has-omega M 𝕄
  Usage-allows-omega-has-omega ⦃ ok ⦄ =
    Usage-with-omega-has-omega ok
