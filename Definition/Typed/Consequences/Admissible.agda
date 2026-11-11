------------------------------------------------------------------------
-- Derived typing rules
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Consequences.Admissible
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (TC : Type-configuration 𝕄)
  where

open import Definition.Typed.Consequences.Admissible.Bool 𝐌 TC public
open import Definition.Typed.Consequences.Admissible.Erased 𝐌 TC public
open import Definition.Typed.Consequences.Admissible.Identity 𝐌 TC public
open import Definition.Typed.Consequences.Admissible.Pi TC public
open import Definition.Typed.Consequences.Admissible.Sigma TC public
