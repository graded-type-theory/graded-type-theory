------------------------------------------------------------------------
-- An instance related to Dedicated-nr
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Dedicated-nr.Instance
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  where

open Modality 𝕄

open import Graded.Modality.Dedicated-nr 𝕄

instance

  -- If the modality is supposed to come with a dedicated nr function,
  -- then such a function is available.

  has-dedicated-nr :
    ⦃ nr : Dedicated-nr ⦄ → Has-nr semiring-with-meet
  has-dedicated-nr ⦃ nr = dedicated-nr nr ⦄ =
    has-nr nr
