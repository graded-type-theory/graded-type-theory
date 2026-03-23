------------------------------------------------------------------------
-- Syntactic validity of the typing and reduction relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Syntactic
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties.Reduction R
import Definition.Typed.Well-formed R as W

open import Tools.Function
open import Tools.Product

open W public
  using ()
  renaming
    (wf-∷∈ to syntacticVar;
     wf-⊢  to syntacticTerm)

open W public
  using ()
  renaming (wf-⊢ to syntacticEq)

open W public
  using ()
  renaming (wf-⊢ to syntacticEqTerm)

private variable
  Γ       : Cons _ _
  A B t u : Term _

opaque

  -- A well-formedness lemma for _⊢_⇒*_.

  syntacticRed : Γ ⊢ A ⇒* B → Γ ⊢ A × Γ ⊢ B
  syntacticRed = syntacticEq ∘→ subset*

opaque

  -- A well-formedness lemma for _⊢_⇒*_∷_.

  syntacticRedTerm : Γ ⊢ t ⇒* u ∷ A → (Γ ⊢ A) × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  syntacticRedTerm = syntacticEqTerm ∘→ subset*Term
