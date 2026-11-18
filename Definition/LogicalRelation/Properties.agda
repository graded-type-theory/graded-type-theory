------------------------------------------------------------------------
-- Properties of the logical relation
------------------------------------------------------------------------

open import Configuration-types
open import Definition.Typed.EqualityRelation
open import Graded.Modality

module Definition.LogicalRelation.Properties
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  ⦃ eqrel : EqRelSet TC ⦄
  where

open import Definition.LogicalRelation.Properties.Kit TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Quotient eqrel public
open import Definition.LogicalRelation.Properties.Whnf TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Primitive TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Reflexivity TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Symmetry TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Transitivity TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Conversion TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Escape TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Neutral TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Reduction TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Properties.Embedding TC ⦃ eqrel ⦄ public
