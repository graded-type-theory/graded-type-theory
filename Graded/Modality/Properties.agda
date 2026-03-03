------------------------------------------------------------------------
-- Properties of the modality structure.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Properties
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open import Graded.Modality.Properties.Addition 𝕄 public
open import Graded.Modality.Properties.Division 𝕄
  public
open import Graded.Modality.Properties.Equivalence 𝕄
  public
open import Graded.Modality.Properties.Greatest-lower-bound 𝕄
  public
open import
  Graded.Modality.Properties.Has-well-behaved-zero 𝕄 as H
  public
open import Graded.Modality.Properties.Meet 𝕄 public
open import Graded.Modality.Properties.Multiplication 𝕄 public
open import Graded.Modality.Properties.Natrec 𝕄 public
open import Graded.Modality.Properties.PartialOrder 𝕄 public
open import Graded.Modality.Properties.Star 𝕄 public
open import Graded.Modality.Properties.Subtraction 𝕄 public

open import Tools.Bool
