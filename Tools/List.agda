------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Tools.List where

module L where
  open import Data.List public
  open import Data.List.Properties public

open L using (List; []; _∷_) public

module All where
  open import Data.List.Relation.Unary.All public
  open import Data.List.Relation.Unary.All.Properties public

module Any where
  open import Data.List.Relation.Unary.Any public
  open import Data.List.Relation.Unary.Any.Properties public

module Pointwise where
  open import Data.List.Relation.Binary.Pointwise public
