open import Definition.Modality

module Definition.Modality.Properties
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Properties.Addition modalityWithout⊛ public
open import Definition.Modality.Properties.Equivalence modalityWithout⊛
  public
open import Definition.Modality.Properties.Meet modalityWithout⊛ public
open import Definition.Modality.Properties.Multiplication modalityWithout⊛ public
open import Definition.Modality.Properties.PartialOrder modalityWithout⊛ public
open import Definition.Modality.Properties.Star 𝕄 public
