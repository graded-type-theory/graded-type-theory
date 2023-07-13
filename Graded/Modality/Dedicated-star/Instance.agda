------------------------------------------------------------------------
-- An instance related to Dedicated-star
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Dedicated-star.Instance
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  where

open Modality 𝕄

open import Graded.Modality.Dedicated-star 𝕄

instance

  -- If the modality is supposed to come with a dedicated
  -- natrec-star operator, then such an operator is available.

  has-dedicated-star :
    ⦃ star : Dedicated-star ⦄ → Has-star semiring-with-meet
  has-dedicated-star ⦃ star = dedicated-star star ⦄ =
    has-star star
