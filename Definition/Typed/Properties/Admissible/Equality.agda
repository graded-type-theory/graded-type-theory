------------------------------------------------------------------------
-- An admissible rule related to definitional equality
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Equality
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open Type-configuration TC

open import Definition.Untyped M

open import Definition.Typed TC
open import Definition.Typed.Well-formed TC

open import Tools.Product

private variable
  Γ     : Cons _ _
  A t u : Term _

opaque

  -- A variant of sym.

  sym′ : Γ ⊢ t ≡ u ∷ A → Γ ⊢ u ≡ t ∷ A
  sym′ t≡u = sym (wf-⊢ t≡u .proj₁) t≡u
