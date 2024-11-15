------------------------------------------------------------------------
-- An admissible rule related to definitional equality
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Equality
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M

open import Definition.Typed R
open import Definition.Typed.Well-formed R

open import Tools.Product

private variable
  Γ     : Con Term _
  A t u : Term _

opaque

  -- A variant of sym.

  sym′ : Γ ⊢ t ≡ u ∷ A → Γ ⊢ u ≡ t ∷ A
  sym′ t≡u = sym (wf-⊢≡∷ t≡u .proj₁) t≡u
