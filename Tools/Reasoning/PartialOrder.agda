{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Tools.Reasoning.PartialOrder
  {a ℓ ℓ′} (P : Poset a ℓ ℓ′)
  where

open import Relation.Binary.Reasoning.PartialOrder P public
