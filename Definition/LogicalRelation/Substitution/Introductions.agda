------------------------------------------------------------------------
-- Validity lemmata.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open import Definition.LogicalRelation.Substitution.Introductions.Empty R ⦃ eqrel ⦄ public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Identity R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Level R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Nat R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Pi R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma.Strong R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma.Weak R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Unit R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Universe R ⦃ eqrel ⦄  public
open import Definition.LogicalRelation.Substitution.Introductions.Var R ⦃ eqrel ⦄  public
