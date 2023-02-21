open import Tools.Relation

module Tools.Reasoning.Preorder
  {a ℓ ℓ′} (P : Preorder a ℓ ℓ′)
  where

open import Relation.Binary.Reasoning.Preorder P public
