------------------------------------------------------------------------
-- A modality for affine types.
------------------------------------------------------------------------

open import Tools.Bool

open import Definition.Modality.Instances.Zero-one-many true as 𝟘𝟙ω

open import Definition.Modality.Restrictions Zero-one-many

module Definition.Modality.Instances.Affine
  (restrictions : Restrictions)
  where

open 𝟘𝟙ω renaming (Zero-one-many to Affine) public

open import Definition.Modality Affine

-- An "affine types" modality.

affineModality : Modality
affineModality = zero-one-many-greatest restrictions
