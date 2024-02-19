------------------------------------------------------------------------
-- An instance related to Neutrals-included
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.EqualityRelation.Instance
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eq : EqRelSet R ⦄
  where

open EqRelSet eq

open import Definition.Untyped M

private variable
  Γ : Con Term _

instance

  -- A variant of included.

  included′ :
    ⦃ inc : Neutrals-included ⦄ →
    Neutrals-included or-empty Γ
  included′ = included
