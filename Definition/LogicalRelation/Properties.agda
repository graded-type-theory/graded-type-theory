------------------------------------------------------------------------
-- Properties of the logical relation
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.LogicalRelation.Properties.Kit R public
open import Definition.LogicalRelation.Properties.Whnf R public
open import Definition.LogicalRelation.Properties.Reflexivity R public
open import Definition.LogicalRelation.Properties.Symmetry R public
open import Definition.LogicalRelation.Properties.Transitivity R public
open import Definition.LogicalRelation.Properties.Conversion R public
open import Definition.LogicalRelation.Properties.Escape R public
open import Definition.LogicalRelation.Properties.Neutral R public
open import Definition.LogicalRelation.Properties.Reduction R public
open import Definition.LogicalRelation.Properties.Embedding R public
