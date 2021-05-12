-- Σ type (also used as existential) and
-- cartesian product (also used as conjunction).

{-# OPTIONS --without-K --safe #-}

module Tools.Product where

open import Level

open import Data.Product public using (Σ; ∃; ∃₂; _×_; _,_; proj₁; proj₂)

∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
     (D : (x : A) → (y : B x) → C x y → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ D = ∃ λ a → ∃ λ b → ∃ λ c → D a b c
