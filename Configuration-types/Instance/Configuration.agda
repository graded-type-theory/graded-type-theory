------------------------------------------------------------------------
-- Instances related to Configuration
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Graded.Mode

module Configuration-types.Instance.Configuration
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (C : Configuration 𝐌)
  where

open Configuration-types.Configuration C

open import Configuration-types.Natrec 𝕄

open import Configuration-types.Instance.Type-configuration TC public

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
