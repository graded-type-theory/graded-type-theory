------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Tools.List where

open import Agda.Builtin.List public using (List; []; _∷_)
open import Data.List.Base public using (_++_; length)
open import Data.List.Properties public using (length-++)
