------------------------------------------------------------------------
-- Instances related to Natrec-mode
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Usage.Restrictions.Natrec.Instance
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open import Graded.Usage.Restrictions.Natrec 𝕄

open Modality 𝕄

instance

  Nr-has-nr :
    ⦃ has-nr : Has-nr _ semiring-with-meet ⦄ →
    Natrec-mode-has-nr Nr
  Nr-has-nr = Nr

  No-nr-no-nr :
    Natrec-mode-no-nr No-nr
  No-nr-no-nr = No-nr

  No-nr-glb-no-nr-glb :
   ⦃ ok : Has-well-behaved-GLBs _ semiring-with-meet ⦄ →
   Natrec-mode-no-nr-glb No-nr-glb
  No-nr-glb-no-nr-glb = No-nr-glb
