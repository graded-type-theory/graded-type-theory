{-# OPTIONS --without-K --safe #-}

module Tools.Relation where

open import Relation.Binary using
  (Rel; IsEquivalence; Reflexive; Symmetric; Transitive)
  public

open import Relation.Binary.Bundles using (Poset; Preorder; Setoid; DecSetoid) public
open import Relation.Binary.Structures using (IsPartialOrder; IsPreorder) public
