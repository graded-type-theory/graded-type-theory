------------------------------------------------------------------------
-- Validity lemmata.
------------------------------------------------------------------------

open import Configuration-types
open import Definition.Typed.EqualityRelation
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  ⦃ eqrel : EqRelSet TC ⦄
  where

open import
  Definition.LogicalRelation.Substitution.Introductions.Definition
    TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Substitution.Introductions.Empty TC ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Identity TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Level TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Lift TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Nat TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Pi TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Quotient eqrel public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma.Strong TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma.Weak TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Unit TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Universe TC ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Var TC ⦃ eqrel ⦄  public
