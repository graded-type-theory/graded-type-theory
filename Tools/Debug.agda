{-# OPTIONS --no-main #-}

-- Debug printing

module Tools.Debug where

open import Agda.Builtin.String

postulate
  trace : ∀{a} {A : Set a} → String → A → A
  traceShow : ∀{a b} {A : Set a} {B : Set b} → A → B → B

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Debug.Trace #-}

{-# COMPILE GHC trace = \ _ _ t x -> Debug.Trace.trace (Data.Text.unpack t) x #-}
-- {-# COMPILE GHC traceShow = \ _ _ _ _ a x -> Debug.Trace.trace (show a) x #-}
