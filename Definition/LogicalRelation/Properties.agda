{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties (M : Set) {{eqrel : EqRelSet M}} where


open import Definition.LogicalRelation.Properties.Reflexivity M public
open import Definition.LogicalRelation.Properties.Symmetry M public
open import Definition.LogicalRelation.Properties.Transitivity M public
open import Definition.LogicalRelation.Properties.Conversion M public
open import Definition.LogicalRelation.Properties.Escape M public
open import Definition.LogicalRelation.Properties.Universe M public
open import Definition.LogicalRelation.Properties.Neutral M public
open import Definition.LogicalRelation.Properties.Reduction M public
open import Definition.LogicalRelation.Properties.Successor M public
open import Definition.LogicalRelation.Properties.MaybeEmb M public
