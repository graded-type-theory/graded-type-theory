------------------------------------------------------------------------
-- Properties of the typing and reduction relations
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Tools.Nat

module Definition.Typed.Properties
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open Type-configuration TC

open import Definition.Untyped M
open import Definition.Untyped.Neutral M TC⁻
open import Definition.Untyped.Neutral.Atomic M TC⁻

open import Definition.Typed TC
open import Definition.Typed.Inversion TC

open import Tools.Fin
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

open import Definition.Typed.Properties.Admissible.Empty TC public
open import Definition.Typed.Properties.Admissible.Equality TC public
open import Definition.Typed.Properties.Admissible.Erased TC public
open import Definition.Typed.Properties.Admissible.Identity TC public
open import Definition.Typed.Properties.Admissible.Level TC public
open import Definition.Typed.Properties.Admissible.Lift TC public
open import Definition.Typed.Properties.Admissible.Nat TC public
open import Definition.Typed.Properties.Admissible.Non-dependent TC
  public
open import Definition.Typed.Properties.Admissible.Omega TC public
open import Definition.Typed.Properties.Admissible.Pi-Sigma TC public
open import Definition.Typed.Properties.Admissible.Pi TC public
open import Definition.Typed.Properties.Admissible.Quotient TC public
open import Definition.Typed.Properties.Admissible.Sigma TC public
open import Definition.Typed.Properties.Admissible.U TC public
open import Definition.Typed.Properties.Admissible.Unit TC public
open import Definition.Typed.Properties.Admissible.Var TC public
open import Definition.Typed.Properties.Definition TC public
open import Definition.Typed.Properties.Reduction TC public
open import Definition.Typed.Properties.Transparentisation TC public
open import Definition.Typed.Properties.Well-formed TC public

private variable
  V                   : Set _
  x                   : Fin _
  ∇                   : DCon _ _
  Δ                   : Con Term _
  Γ                   : Cons _ _
  A A′ B B′ t t′ u u′ : Term _

------------------------------------------------------------------------
-- A lemma related to _∷_∈_

opaque

  -- If x ∷ A ∈ Δ and x ∷ B ∈ Δ both hold, then A is equal to B.

  det∈ : x ∷ A ∈ Δ → x ∷ B ∈ Δ → A PE.≡ B
  det∈ here      here      = PE.refl
  det∈ (there x) (there y) = PE.cong wk1 (det∈ x y)

------------------------------------------------------------------------
-- Variants of type conversion for propositionally equal types

opaque

  -- Conversion for well-formed terms for propositionally equal types

  ⊢∷-conv-PE : Γ ⊢ t ∷ A → A PE.≡ B → Γ ⊢ t ∷ B
  ⊢∷-conv-PE ⊢t PE.refl = ⊢t

opaque

  -- Conversion for term equality for propositionally equal types

  ⊢≡∷-conv-PE : Γ ⊢ t ≡ u ∷ A → A PE.≡ B → Γ ⊢ t ≡ u ∷ B
  ⊢≡∷-conv-PE ⊢t≡u PE.refl = ⊢t≡u

opaque

  -- Conversion for term reduction for propositionally equal types

  ⊢⇒∷-conv-PE : Γ ⊢ t ⇒ u ∷ A → A PE.≡ B → Γ ⊢ t ⇒ u ∷ B
  ⊢⇒∷-conv-PE ⊢t⇒u PE.refl = ⊢t⇒u

opaque

  -- Conversion for term reduction for propositionally equal types

  ⊢⇒*∷-conv-PE : Γ ⊢ t ⇒* u ∷ A → A PE.≡ B → Γ ⊢ t ⇒* u ∷ B
  ⊢⇒*∷-conv-PE ⊢t⇒u PE.refl = ⊢t⇒u

------------------------------------------------------------------------
-- Congruence properties for typing judgments for propositional equality

opaque

  -- Congruence of well-formedness of types

  ⊢-cong : Γ ⊢ A → A PE.≡ B → Γ ⊢ B
  ⊢-cong ⊢A PE.refl = ⊢A


opaque

  -- Congruence of well-formedness of types

  ⊢∷-cong : Γ ⊢ t ∷ A → t PE.≡ u → Γ ⊢ u ∷ A
  ⊢∷-cong ⊢t PE.refl = ⊢t

opaque

  -- Congruence of type equality

  ⊢≡-cong : Γ ⊢ A ≡ B → A PE.≡ A′ → B PE.≡ B′ → Γ ⊢ A′ ≡ B′
  ⊢≡-cong ⊢A≡B PE.refl PE.refl = ⊢A≡B


opaque

  -- Congruence of type equality

  ⊢≡-congˡ : Γ ⊢ A ≡ B → B PE.≡ B′ → Γ ⊢ A ≡ B′
  ⊢≡-congˡ ⊢A≡B PE.refl = ⊢A≡B


opaque

  -- Congruence of type equality

  ⊢≡-congʳ : Γ ⊢ A ≡ B → A PE.≡ A′ → Γ ⊢ A′ ≡ B
  ⊢≡-congʳ ⊢A≡B PE.refl = ⊢A≡B

opaque

  -- Congruence of term reduction

  ⊢⇒∷-cong : Γ ⊢ t ⇒ u ∷ A → t PE.≡ t′ → u PE.≡ u′ → Γ ⊢ t′ ⇒ u′ ∷ A
  ⊢⇒∷-cong t⇒u PE.refl PE.refl = t⇒u

opaque

  -- Congruence of term reduction

  ⊢⇒∷-congʳ : Γ ⊢ t ⇒ u ∷ A → t PE.≡ t′ → Γ ⊢ t′ ⇒ u ∷ A
  ⊢⇒∷-congʳ t⇒u PE.refl = t⇒u

opaque

  -- Congruence of term reduction

  ⊢⇒∷-congˡ : Γ ⊢ t ⇒ u ∷ A → u PE.≡ u′ → Γ ⊢ t ⇒ u′ ∷ A
  ⊢⇒∷-congˡ t⇒u PE.refl = t⇒u

opaque

  -- Congruence of term reduction

  ⊢⇒*∷-cong : Γ ⊢ t ⇒* u ∷ A → t PE.≡ t′ → u PE.≡ u′ → Γ ⊢ t′ ⇒* u′ ∷ A
  ⊢⇒*∷-cong t⇒*u PE.refl PE.refl = t⇒*u

opaque

  -- Congruence of term reduction

  ⊢⇒*∷-congʳ : Γ ⊢ t ⇒* u ∷ A → t PE.≡ t′ → Γ ⊢ t′ ⇒* u ∷ A
  ⊢⇒*∷-congʳ t⇒*u PE.refl = t⇒*u

opaque

  -- Congruence of term reduction

  ⊢⇒*∷-congˡ : Γ ⊢ t ⇒* u ∷ A → u PE.≡ u′ → Γ ⊢ t ⇒* u′ ∷ A
  ⊢⇒*∷-congˡ t⇒*u PE.refl = t⇒*u

------------------------------------------------------------------------
-- Variants of equality rules

opaque

  -- Reflexivity for propositionally equal types

  ⊢≡-refl-PE : A PE.≡ B → Γ ⊢ A → Γ ⊢ A ≡ B
  ⊢≡-refl-PE PE.refl = refl

opaque

  -- Reflexivity for propositionally equal types

  ⊢≡-refl-PE′ : A PE.≡ B → Γ ⊢ B → Γ ⊢ A ≡ B
  ⊢≡-refl-PE′ PE.refl = refl

opaque

  -- Reflexivity for propositionally equal terms

  ⊢≡∷-refl-PE : t PE.≡ u → Γ ⊢ t ∷ A → Γ ⊢ t ≡ u ∷ A
  ⊢≡∷-refl-PE PE.refl = refl

opaque

  -- Reflexivity for propositionally equal terms

  ⊢≡∷-refl-PE′ : t PE.≡ u → Γ ⊢ u ∷ A → Γ ⊢ t ≡ u ∷ A
  ⊢≡∷-refl-PE′ PE.refl = refl

------------------------------------------------------------------------
-- A lemma related to Neutral and Neutralᵃ

opaque

  -- Neutral terms with types that are not equal to Level are atomic
  -- neutral.
  --
  -- See also
  -- Definition.Typed.Consequences.Inequality.Neutral→Neutralᵃ-⊢.

  Neutral→Neutralᵃ-⊢∷ :
    Γ ⊢ t ∷ A → ¬ Γ ⊢ A ≡ Level → Neutral V ∇ t → Neutralᵃ V ∇ t
  Neutral→Neutralᵃ-⊢∷ ⊢t A≢Level t-ne =
    ne t-ne λ where
      is-supᵘ →
        let _ , _ , A≡Level = inversion-supᵘ ⊢t in
        A≢Level A≡Level
