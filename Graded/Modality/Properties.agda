------------------------------------------------------------------------
-- Properties of the modality semiring.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Graded.Modality.Properties.Addition semiring-with-meet public
open import Graded.Modality.Properties.Equivalence semiring-with-meet
  public
open import Graded.Modality.Properties.Meet semiring-with-meet public
open import Graded.Modality.Properties.Multiplication semiring-with-meet public
open import Graded.Modality.Properties.PartialOrder semiring-with-meet public
open import Graded.Modality.Properties.Star semiring-with-meet-and-star public

open import Tools.Bool

-- Export properties that hold if 𝟘 is well behaved
-- under the assumption that 𝟘ᵐ is allowed.

module _ (ok : T 𝟘ᵐ-allowed) where
  open import Graded.Modality.Properties.Has-well-behaved-zero
    semiring-with-meet-and-star (𝟘-well-behaved ok) public
    renaming (𝟙≉𝟘 to 𝟘ᵐ→𝟙≉𝟘)
