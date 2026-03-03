------------------------------------------------------------------------
-- Derived typing rules
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Consequences.Admissible
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed.Consequences.Admissible.Bool 𝐌 R public
open import Definition.Typed.Consequences.Admissible.Erased R public
open import Definition.Typed.Consequences.Admissible.Identity 𝐌 R public
open import Definition.Typed.Consequences.Admissible.Pi R public
open import Definition.Typed.Consequences.Admissible.Sigma R public
