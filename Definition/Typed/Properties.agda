------------------------------------------------------------------------
-- Properties of the typing and reduction relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant

open import Definition.Typed R
open import Definition.Typed.Inversion R

open import Tools.Fin
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

open import Definition.Typed.Properties.Admissible.Bool R public
open import Definition.Typed.Properties.Admissible.Empty R public
open import Definition.Typed.Properties.Admissible.Equality R public
open import Definition.Typed.Properties.Admissible.Erased R public
open import Definition.Typed.Properties.Admissible.Identity R public
open import Definition.Typed.Properties.Admissible.Level R public
open import Definition.Typed.Properties.Admissible.Lift R public
open import Definition.Typed.Properties.Admissible.Nat R public
open import Definition.Typed.Properties.Admissible.Pi-Sigma R public
open import Definition.Typed.Properties.Admissible.Pi R public
open import Definition.Typed.Properties.Admissible.Sigma R public
open import Definition.Typed.Properties.Admissible.U R public
open import Definition.Typed.Properties.Admissible.Unit R public
open import Definition.Typed.Properties.Admissible.Var R public
open import Definition.Typed.Properties.Reduction R public
open import Definition.Typed.Properties.Well-formed R public

private variable
  x     : Fin _
  Γ     : Con Term _
  A B t : Term _

------------------------------------------------------------------------
-- A lemma related to _∷_∈_

opaque

  -- If x ∷ A ∈ Γ and x ∷ B ∈ Γ both hold, then A is equal to B.

  det∈ : x ∷ A ∈ Γ → x ∷ B ∈ Γ → A PE.≡ B
  det∈ here      here      = PE.refl
  det∈ (there x) (there y) = PE.cong wk1 (det∈ x y)

------------------------------------------------------------------------
-- A lemma related to Neutral and Neutralᵃ

opaque

  -- Neutral terms with types that are not equal to Level are atomic
  -- neutral.
  --
  -- See also
  -- Definition.Typed.Consequences.Inequality.Neutral→Neutralᵃ-⊢.

  Neutral→Neutralᵃ-⊢∷ :
    Γ ⊢ t ∷ A → ¬ Γ ⊢ A ≡ Level → Neutral t → Neutralᵃ t
  Neutral→Neutralᵃ-⊢∷ ⊢t A≢Level t-ne =
    ne t-ne λ where
      is-supᵘ →
        let _ , _ , A≡Level = inversion-supᵘ ⊢t in
        A≢Level A≡Level
