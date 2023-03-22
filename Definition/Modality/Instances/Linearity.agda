open import Tools.Bool

open import Definition.Modality.Instances.Zero-one-many false as 𝟘𝟙ω

open import Definition.Modality.Restrictions Zero-one-many

module Definition.Modality.Instances.Linearity
  (restrictions : Restrictions)
  where

open 𝟘𝟙ω renaming (Zero-one-many to Linearity) public

open import Definition.Modality Linearity

-- A "linear types" modality.

linearityModality : Modality
linearityModality = zero-one-many-greatest restrictions
