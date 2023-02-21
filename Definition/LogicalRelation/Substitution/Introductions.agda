open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Introductions {a ℓ} (M′ : Setoid a ℓ)
                                                             {{eqrel : EqRelSet M′}} where

open import Definition.LogicalRelation.Substitution.Introductions.Pi M′ public
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Lambda M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Application M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Prod M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Fst M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Snd M′ public
open import Definition.LogicalRelation.Substitution.Introductions.ProdBetaEta M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Prodrec M′ public
open import Definition.LogicalRelation.Substitution.Introductions.DoubleSubst M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Nat M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Natrec M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Empty M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Unit M′ public
open import Definition.LogicalRelation.Substitution.Introductions.Universe M′ public
