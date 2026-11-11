------------------------------------------------------------------------
-- Syntactic validity of the reduction relations
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Typed.Syntactic
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed TC
open import Definition.Typed.Properties.Reduction TC
open import Definition.Typed.Well-formed TC

open import Tools.Function
open import Tools.Product

private variable
  Γ       : Cons _ _
  A B t u : Term _

opaque

  -- A well-formedness lemma for _⊢_⇒*_.

  syntacticRed : Γ ⊢ A ⇒* B → Γ ⊢ A × Γ ⊢ B
  syntacticRed = wf-⊢ ∘→ subset*

opaque

  -- A well-formedness lemma for _⊢_⇒*_∷_.

  syntacticRedTerm : Γ ⊢ t ⇒* u ∷ A → (Γ ⊢ A) × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  syntacticRedTerm = wf-⊢ ∘→ subset*Term
