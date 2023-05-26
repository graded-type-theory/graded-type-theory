------------------------------------------------------------------------
-- Properties of the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Properties
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open import Definition.LogicalRelation.Properties.Reflexivity R public
open import Definition.LogicalRelation.Properties.Symmetry R public
open import Definition.LogicalRelation.Properties.Transitivity R public
open import Definition.LogicalRelation.Properties.Conversion R public
open import Definition.LogicalRelation.Properties.Escape R public
open import Definition.LogicalRelation.Properties.Universe R public
open import Definition.LogicalRelation.Properties.Neutral R public
open import Definition.LogicalRelation.Properties.Reduction R public
open import Definition.LogicalRelation.Properties.Successor R public
open import Definition.LogicalRelation.Properties.MaybeEmb R public
