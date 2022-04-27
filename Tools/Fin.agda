{-# OPTIONS --without-K --safe #-}

module Tools.Fin where

open import Tools.Nat
open import Tools.Nullary
open import Tools.PropositionalEquality

open import Data.Fin.Properties using () renaming (_≟_ to _≟ⱽ_) public
open import Data.Fin.Base using (Fin) renaming (zero to x0 ; suc to _+1) public
