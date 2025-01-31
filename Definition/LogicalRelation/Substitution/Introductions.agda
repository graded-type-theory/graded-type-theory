------------------------------------------------------------------------
-- Validity lemmata.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.LogicalRelation.Substitution.Introductions.Empty R public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec R public
open import Definition.LogicalRelation.Substitution.Introductions.Identity R public
open import Definition.LogicalRelation.Substitution.Introductions.Nat R public
open import Definition.LogicalRelation.Substitution.Introductions.Pi R public
open import Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma R public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma R public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma.Strong R public
open import Definition.LogicalRelation.Substitution.Introductions.Sigma.Weak R public
open import Definition.LogicalRelation.Substitution.Introductions.Unit R public
open import Definition.LogicalRelation.Substitution.Introductions.Universe R public
open import Definition.LogicalRelation.Substitution.Introductions.Var R public
