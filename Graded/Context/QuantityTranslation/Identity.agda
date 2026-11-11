------------------------------------------------------------------------
-- If Graded.Context.QuantityTranslation is instantiated with a single
-- modality and identity functions, then the translation is pointwise
-- equal to an identity function
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Context.QuantityTranslation.Identity
  {a} {M : Set a} (𝕄 : Modality M)
  where

open import Tools.Function
open import Tools.PropositionalEquality

open import Graded.Context 𝕄
open import Graded.Context.QuantityTranslation 𝕄 𝕄 idᶠ

private variable
  γ : Conₘ _

opaque

  -- The function tr-Conₘ is pointwise equal to an identity function.

  tr-Conₘ-id : tr-Conₘ γ ≡ γ
  tr-Conₘ-id {γ = ε}     = refl
  tr-Conₘ-id {γ = _ ∙ _} = cong (_∙ _) tr-Conₘ-id
