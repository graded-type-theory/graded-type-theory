------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Tools.List where

open import Agda.Builtin.List using (List; []; _∷_) public
open import Data.List public using (_++_; length)
open import Data.List.Properties public using (length-++)
