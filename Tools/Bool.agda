{-# OPTIONS --without-K --safe #-}

module Tools.Bool where

open import Data.Bool.Base
  using (Bool; true; false; _∧_; _∨_; if_then_else_)
  public
open import Data.Bool.Properties
  using (∨-∧-isCommutativeSemiring)
  public
