{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Tools.Algebra {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)


open import Algebra.Core using (Op₁; Op₂) public
open import Algebra.Definitions (_≈_)
     using (Associative; Commutative; Congruent₂; _DistributesOver_;
            _DistributesOverˡ_; _DistributesOverʳ_; Idempotent; Identity;
            LeftIdentity; LeftZero; RightIdentity; RightZero; Zero) public
open import Algebra.Structures (_≈_)
     using (IsBand; IsCommutativeMonoid; IsMagma;
            IsMonoid; IsSemigroup; IsSemilattice) public

Op₃ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₃ A = A → A → A → A
