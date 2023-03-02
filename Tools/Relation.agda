{-# OPTIONS --without-K --safe #-}

module Tools.Relation where

open import Relation.Binary.Core using (Rel) public
open import Relation.Binary.Definitions using (Decidable; Reflexive; Symmetric; Transitive) public
open import Relation.Binary.Bundles using (Poset; Preorder; Setoid; DecSetoid) public
open import Relation.Binary.Structures using (IsPartialOrder; IsPreorder; IsEquivalence) public
