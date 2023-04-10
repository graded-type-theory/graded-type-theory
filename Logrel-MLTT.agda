-- A Logical Relation for Dependent Type Theory Formalized in Agda

module Logrel-MLTT where

-- README
import README

-- Minimal library
import Tools.Empty
import Tools.Unit
import Tools.Nat
import Tools.Sum
import Tools.Product
import Tools.Function
import Tools.Nullary
import Tools.List
import Tools.PropositionalEquality
import Tools.Fin
import Tools.Algebra
import Tools.Level
import Tools.Relation
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.Preorder
import Tools.Reasoning.PropositionalEquality


-- Modality structure
import Definition.Modality.Restrictions
import Definition.Modality.Restrictions.Definitions
import Definition.Modality
import Definition.Modality.Properties
import Definition.Modality.Context
import Definition.Modality.Context.Properties
import Definition.Modality.Usage
import Definition.Modality.Usage.Decidable
import Definition.Modality.Usage.Inversion
import Definition.Modality.Usage.Properties
import Definition.Modality.Usage.Weakening
import Definition.Modality.Substitution
import Definition.Modality.Substitution.Properties
import Definition.Modality.Substitution.Decidable

-- Instances
import Definition.Modality.Instances.Erasure.Modality
import Definition.Modality.Instances.Unit
import Definition.Modality.Instances.Affine
import Definition.Modality.Instances.Linearity
import Definition.Modality.Instances.Linear-or-affine
import Definition.Modality.Instances.BoundedStar
import Definition.Modality.Instances.Finite
import Definition.Modality.Instances.LowerBounded
import Definition.Modality.Instances.Recursive
import Definition.Modality.Instances.Zero-one-many

-- Modality morphisms
import Definition.Modality.Morphism


-- Modes
import Definition.Mode

-- Grammar of the language
import Definition.Untyped
import Definition.Untyped.BindingType
import Definition.Untyped.Properties

-- Typing and conversion rules of language
import Definition.Typed
import Definition.Typed.Properties
import Definition.Typed.Weakening
import Definition.Typed.Reduction
import Definition.Typed.RedSteps
import Definition.Typed.EqualityRelation
import Definition.Typed.EqRelInstance
import Definition.Typed.Usage

-- Quantity translation.
import Definition.Untyped.QuantityTranslation
import Definition.Typed.QuantityTranslation
import Definition.Modality.Context.QuantityTranslation
import Definition.Mode.QuantityTranslation
import Definition.Modality.Usage.QuantityTranslation

-- Combined usage and typing relations
import Definition.Usage

-- Logical relation
import Definition.LogicalRelation
import Definition.LogicalRelation.ShapeView
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Weakening
import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Application

import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance
import Definition.LogicalRelation.Substitution.Conversion
import Definition.LogicalRelation.Substitution.Reduction
import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.Reducibility
import Definition.LogicalRelation.Substitution.Escape
import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.Introductions

import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consequences of the logical relation for typing and conversion
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Syntactic
import Definition.Typed.Consequences.DerivedRules
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Inequality
import Definition.Typed.Consequences.Substitution
import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.InverseUniv
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Consequences.NeTypeEq
import Definition.Typed.Consequences.SucCong
import Definition.Typed.Consequences.Consistency
import Definition.Typed.Consequences.RedSteps

-- Algorithmic equality with lemmas that depend on typing consequences
import Definition.Conversion
import Definition.Conversion.Conversion
import Definition.Conversion.Lift
import Definition.Conversion.Reduction
import Definition.Conversion.Soundness
import Definition.Conversion.Stability
import Definition.Conversion.Symmetry
import Definition.Conversion.Transitivity
import Definition.Conversion.Universe
import Definition.Conversion.Weakening
import Definition.Conversion.Whnf
import Definition.Conversion.Decidable
import Definition.Conversion.EqRelInstance
import Definition.Conversion.FullReduction

-- A "full reduction" lemma for modalities.
import Definition.Modality.FullReduction

-- Consequences of the logical relation for algorithmic equality
import Definition.Conversion.Consequences.Completeness

-- Decidability of conversion
import Definition.Typed.Decidable

-- The type Erased.
import Definition.Untyped.Erased
import Definition.Modality.Usage.Erased
import Definition.Typed.Erased

-- Erasure

import Definition.Modality.Instances.Erasure.Properties

-- Target language

import Erasure.Target
import Erasure.Target.Properties

-- Extraction

import Erasure.Extraction
import Erasure.Extraction.Properties

-- Logical relation for Erasure

import Erasure.LogicalRelation
import Erasure.LogicalRelation.Conversion
import Erasure.LogicalRelation.Irrelevance
import Erasure.LogicalRelation.Reduction
import Erasure.LogicalRelation.Subsumption
import Erasure.LogicalRelation.Fundamental
import Erasure.LogicalRelation.Fundamental.Counterexample

-- Soundness of Extraction function

import Erasure.Consequences.Soundness

-- Application: consistent negative axioms preserve canonicity
import Application.NegativeAxioms.Canonicity.Negative

-- Application: consistent negative/erased axioms preserve canonicity
import Application.NegativeAxioms.Canonicity.NegativeErased
import Application.NegativeAxioms.Canonicity.Erased
-- ... but not if matching is allowed on erased pairs
import Application.NegativeAxioms.Canonicity.EliminateErased
