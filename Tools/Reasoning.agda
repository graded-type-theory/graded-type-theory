{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Tools.Reasoning
  {a ℓ} {A : Set a}
  (_≈_ : Rel A ℓ) (≈-trans : Transitive _≈_)
  where

open import Relation.Binary.Reasoning.Base.Partial _≈_ ≈-trans public
