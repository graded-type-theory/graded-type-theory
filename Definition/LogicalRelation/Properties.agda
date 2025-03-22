------------------------------------------------------------------------
-- Properties of the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open import Definition.LogicalRelation.Properties.Kit R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Primitive R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Reflexivity R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Symmetry R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Transitivity R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Conversion R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Escape R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Neutral R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Reduction R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Embedding R ⦃ eqrel ⦄ public
