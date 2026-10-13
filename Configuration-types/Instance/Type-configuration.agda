------------------------------------------------------------------------
-- Instances related to Type-configuration
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Configuration-types.Instance.Type-configuration
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open Configuration-types.Type-configuration TC

open import Configuration-types.Omega 𝕄

instance

  Omega-allowed→Has-omega :
    ⦃ ok : Omega-allowed ⦄ →
    Has-omega M 𝕄
  Omega-allowed→Has-omega ⦃ ok ⦄ =
    With-omega→Has-omega ok
