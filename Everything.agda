------------------------------------------------------------------------
-- Graded modal type theory formalized in Agda
------------------------------------------------------------------------

module Everything where

------------------------------------------------------------------------
-- A small library

import Tools.Level
import Tools.Unit
import Tools.Relation
import Tools.Product
import Tools.PropositionalEquality
import Tools.Empty
import Tools.Sum
import Tools.Function
import Tools.Bool
import Tools.Nat
import Tools.Fin
import Tools.List
import Tools.Algebra

import Tools.Reasoning.Preorder
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Graded modalities

import Graded.Modality.Variant
import Graded.Modality
import Graded.Modality.Nr-instances
import Graded.Modality.Dedicated-nr
import Graded.Modality.Dedicated-nr.Instance

------------------------------------------------------------------------
-- Properties of the modality semiring

import Graded.Modality.Properties.PartialOrder
import Graded.Modality.Properties.Equivalence
import Graded.Modality.Properties.Meet
import Graded.Modality.Properties.Multiplication
import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Division
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties.Star
import Graded.Modality.Properties.Subtraction
import Graded.Modality.Properties

------------------------------------------------------------------------
-- The type theory's syntax

import Definition.Untyped.NotParametrised
import Definition.Untyped
import Definition.Untyped.Inversion
import Definition.Untyped.Properties.NotParametrised
import Definition.Untyped.Properties
import Definition.Untyped.Identity
import Definition.Untyped.Sigma
import Definition.Untyped.Unit
import Definition.Untyped.Lift
import Graded.Derived.Erased.Eta.Untyped
import Graded.Derived.Erased.NoEta.Untyped
import Graded.Derived.Erased.Untyped
import Graded.Derived.Unrestricted.Eta.Untyped
import Definition.Typed.Variant
import Definition.Untyped.Neutral
import Definition.Untyped.Properties.Neutral

------------------------------------------------------------------------
-- Modality contexts and their properties

import Graded.Context
import Graded.Context.Properties.Equivalence
import Graded.Context.Properties.PartialOrder
import Graded.Context.Properties.Meet
import Graded.Context.Properties.Addition
import Graded.Context.Properties.Multiplication
import Graded.Context.Properties.Natrec
import Graded.Context.Properties.Star
import Graded.Context.Properties.Lookup
import Graded.Context.Properties.Update
import Graded.Context.Properties.Has-well-behaved-zero
import Graded.Context.Properties
import Graded.Context.Weakening

------------------------------------------------------------------------
-- Usage modes

import Graded.Mode

------------------------------------------------------------------------
-- The type theory, along with some basic properties

import Definition.Typed.Restrictions
import Definition.Typed
import Definition.Typed.Reasoning.Type
import Definition.Typed.Properties.Well-formed
import Graded.Derived.Erased.Typed.Primitive
import Definition.Typed.Properties
import Definition.Typed.Reasoning.Term
import Definition.Typed.RedSteps
import Definition.Typed.Reasoning.Reduction.Primitive
import Definition.Typed.Reasoning.Reduction.Well-typed
import Definition.Typed.Weakening
import Definition.Typed.Reduction
import Definition.Typed.EqualityRelation
import Definition.Typed.EqRelInstance

------------------------------------------------------------------------
-- The usage relation

import Graded.Usage.Erased-matches
import Graded.Usage.Restrictions
import Graded.Usage
import Graded.Usage.Inversion
import Graded.Usage.Properties
import Graded.Usage.Restrictions.Satisfied
import Graded.Usage.Properties.Has-well-behaved-zero
import Graded.Usage.Weakening
import Graded.Usage.Decidable.Assumptions
import Graded.Usage.Decidable

------------------------------------------------------------------------
-- Grade substitutions

import Graded.Substitution
import Graded.Substitution.Properties
import Graded.Substitution.Decidable

------------------------------------------------------------------------
-- Some derived definitions related to usage

-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa.
import Graded.Derived.Sigma

-- Properties related to usage and certain type formers.
import Graded.Derived.Identity
import Graded.Derived.Unit
import Graded.Derived.Lift
import Graded.Derived.Erased.Eta.Usage
import Graded.Derived.Erased.NoEta.Usage
import Graded.Derived.Erased.Usage
import Graded.Derived.Unrestricted.Eta.Usage

------------------------------------------------------------------------
-- Assumptions used to state the theorems in Graded.FullReduction

import Graded.FullReduction.Assumptions

------------------------------------------------------------------------
-- Modality instances

-- Some structures that are not modalities.
import Graded.Modality.Instances.Set
import Graded.Modality.Instances.Set.Non-empty
import Graded.Modality.Instances.Set.Non-empty.Implementation

-- Modality pseudo-instances.
import Graded.Modality.Instances.LowerBounded
import Graded.Modality.Instances.BoundedStar
import Graded.Modality.Instances.Finite
import Graded.Modality.Instances.Recursive.Sequences
import Graded.Modality.Instances.Recursive
import Graded.Modality.Instances.Erasure
import Graded.Modality.Instances.Zero-one-many
import Graded.Modality.Instances.Bounded-distributive-lattice
import Graded.Modality.Instances.Set.Interval

-- Modality instances.
import Graded.Modality.Instances.Erasure.Modality
import Graded.Modality.Instances.Erasure.Properties
import Graded.Modality.Instances.Unit
import Graded.Modality.Instances.Affine
import Graded.Modality.Instances.Linearity
import Graded.Modality.Instances.Linearity.Properties
import Graded.Modality.Instances.Linear-or-affine
import Graded.Modality.Instances.Information-flow
import Graded.Modality.Instances.Zero-below-one
import Graded.Modality.Instances.Nat-plus-infinity
import
  Graded.Modality.Instances.Bounded-distributive-lattice.No-division
import
  Graded.Modality.Instances.Bounded-distributive-lattice.Nat-plus-infinity
import
  Graded.Modality.Instances.Bounded-distributive-lattice.Downward-closed
import Graded.Modality.Instances.Set.Interval.Implementation

-- Some examples.
import Graded.Modality.Instances.Examples
import Graded.Modality.Instances.Affine.Bad
import Graded.Modality.Instances.Affine.Bad.No-dedicated-nr
import Graded.Modality.Instances.Affine.Good
import Graded.Modality.Instances.Linear-or-affine.Bad
import Graded.Modality.Instances.Linear-or-affine.Bad.No-dedicated-nr
import Graded.Modality.Instances.Linear-or-affine.Good
import Graded.Modality.Instances.Linearity.Bad
import Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr
import Graded.Modality.Instances.Linearity.Good

------------------------------------------------------------------------
-- Properties of the type theory

-- The logical relation for reducibility.
import Definition.LogicalRelation
import Definition.LogicalRelation.Properties.Kit
import Definition.LogicalRelation.Properties.Whnf
import Definition.LogicalRelation.Properties.Reflexivity
import Definition.LogicalRelation.Properties.Escape
import Definition.LogicalRelation.ShapeView
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Properties.Conversion
import Definition.LogicalRelation.Properties.Embedding
import Definition.LogicalRelation.Properties.Symmetry
import Definition.LogicalRelation.Properties.Neutral
import Definition.LogicalRelation.Properties.Universe
import Definition.LogicalRelation.Properties.Transitivity
import Definition.LogicalRelation.Properties.Reduction
import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Weakening
import Definition.LogicalRelation.Hidden

-- The logical relation for validity.
import Definition.LogicalRelation.Substitution

-- The fundamental lemma of the logical relations.
import Definition.LogicalRelation.Substitution.Introductions.Var
import Definition.LogicalRelation.Substitution.Introductions.Universe
import Definition.LogicalRelation.Substitution.Introductions.Empty
import Definition.LogicalRelation.Substitution.Introductions.Emptyrec
import Definition.LogicalRelation.Substitution.Introductions.Unit
import Definition.LogicalRelation.Substitution.Introductions.Nat
import Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma
import Definition.LogicalRelation.Substitution.Introductions.Pi
import
  Definition.LogicalRelation.Substitution.Introductions.Sigma.Strong
import Definition.LogicalRelation.Substitution.Introductions.Sigma.Weak
import Definition.LogicalRelation.Substitution.Introductions.Sigma
import Definition.LogicalRelation.Substitution.Introductions.Erased
import Definition.LogicalRelation.Substitution.Introductions.Identity
import Definition.LogicalRelation.Substitution.Introductions
import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility

-- Some consequences of the fundamental lemma.
import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Syntactic
import Definition.Typed.Consequences.Inequality
import Definition.Typed.Consequences.Substitution
import Definition.Typed.Consequences.Stability
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Reasoning.Reduction
import Definition.Typed.Consequences.InverseUniv
import Definition.Typed.Consequences.DerivedRules.Nat
import Definition.Typed.Consequences.DerivedRules.Pi-Sigma
import Definition.Typed.Consequences.DerivedRules.Pi
import Definition.Typed.Consequences.DerivedRules.Identity
import Definition.Typed.Consequences.DerivedRules.Sigma
import Definition.Typed.Consequences.DerivedRules.Unit
import Definition.Typed.Consequences.DerivedRules.Lift
import Definition.Typed.Consequences.DerivedRules
import Definition.Typed.Consequences.Consistency
import Definition.Typed.Consequences.RedSteps
import Graded.Derived.Erased.Eta.Typed.Primitive
import Graded.Derived.Erased.Eta.Typed
import Graded.Derived.Erased.NoEta.Typed
import Graded.Derived.Erased.Typed.Inversion
import Graded.Derived.Erased.Eta.Typed.Inversion
import Graded.Derived.Erased.NoEta.Typed.Inversion
import Graded.Derived.Erased.Typed
import Graded.Derived.Unrestricted.Eta.Typed
import Definition.Typed.Consequences.NeTypeEq

-- Algorithmic equality.
import Definition.Conversion
import Definition.Conversion.Whnf
import Definition.Conversion.Reduction
import Definition.Conversion.Soundness
import Definition.Conversion.Inversion
import Definition.Conversion.Stability
import Definition.Conversion.Conversion
import Definition.Conversion.Symmetry
import Definition.Conversion.Transitivity
import Definition.Conversion.Weakening
import Definition.Conversion.Lift
import Definition.Conversion.Universe
import Definition.Conversion.Decidable
import Definition.Conversion.EqRelInstance
import Definition.Conversion.Consequences.Completeness
import Definition.Conversion.Consequences.InverseUniv
import Definition.Conversion.Consequences.Var
import Definition.Untyped.Normal-form
import Definition.Typed.Eta-long-normal-form
import Definition.Conversion.FullReduction

-- Bidirectional typechecking.
import Definition.Typechecking
import Definition.Typechecking.Deterministic
import Definition.Typechecking.Soundness
import Definition.Typechecking.Completeness

-- Decidability of typing (given certain assumptions).
import Definition.Typed.Decidable.Equality
import Definition.Typed.Decidable.Reduction
import Definition.Typechecking.Decidable.Assumptions
import Definition.Typechecking.Decidable
import Definition.Typed.Decidable

------------------------------------------------------------------------
-- Definitions related to type and usage restrictions

import Graded.Restrictions

------------------------------------------------------------------------
-- Subject reduction for modalities

import Graded.Reduction
import Graded.FullReduction

------------------------------------------------------------------------
-- Modality morphisms and quantity translations

import Definition.Untyped.QuantityTranslation
import Definition.Untyped.QuantityTranslation.Identity
import Graded.Modality.Morphism
import Graded.Modality.Morphism.Examples
import Graded.Modality.Morphism.Forward-instances
import Graded.Modality.Morphism.Backward-instances
import Graded.Modality.Morphism.Type-restrictions
import Graded.Modality.Morphism.Type-restrictions.Examples
import Graded.Modality.Morphism.Usage-restrictions
import Graded.Modality.Morphism.Usage-restrictions.Examples
import Definition.Typed.QuantityTranslation
import Graded.Context.QuantityTranslation
import Graded.Mode.QuantityTranslation
import Graded.Usage.QuantityTranslation

------------------------------------------------------------------------
-- Extended modalities

import Graded.Modality.Extended
import Graded.Modality.Extended.K-allowed
import Graded.Modality.Extended.K-not-allowed.Erased-matches
import Graded.Modality.Extended.K-not-allowed.Only-some-erased-matches
import Graded.Modality.Extended.K-not-allowed.No-erased-matches

------------------------------------------------------------------------
-- A case study: erasure

-- The target language.
import Graded.Erasure.Target
import Graded.Erasure.Target.Properties.Weakening
import Graded.Erasure.Target.Properties.Substitution
import Graded.Erasure.Target.Properties.Reduction
import Graded.Erasure.Target.Properties
import Graded.Erasure.Target.Reasoning
import Graded.Erasure.Target.Non-terminating

-- Extraction.
import Graded.Erasure.Extraction
import Graded.Erasure.Extraction.Properties
import Graded.Erasure.Extraction.Non-terminating

-- The logical relation for erasure.
import Graded.Erasure.LogicalRelation.Assumptions
import Graded.Erasure.LogicalRelation
import Graded.Erasure.LogicalRelation.Conversion
import Graded.Erasure.LogicalRelation.Irrelevance
import Graded.Erasure.LogicalRelation.Reduction
import Graded.Erasure.LogicalRelation.Hidden
import Graded.Erasure.LogicalRelation.Value

-- The fundamental lemma of the logical relation for erasure.
import Graded.Erasure.LogicalRelation.Fundamental.Empty
import Graded.Erasure.LogicalRelation.Fundamental.Nat
import Graded.Erasure.LogicalRelation.Fundamental.Pi-Sigma
import Graded.Erasure.LogicalRelation.Fundamental.Unit
import Graded.Erasure.LogicalRelation.Fundamental.Identity
import Graded.Erasure.LogicalRelation.Fundamental.Universe
import Graded.Erasure.LogicalRelation.Fundamental.Assumptions
import Graded.Erasure.LogicalRelation.Fundamental

-- Soundness of extraction.
import Graded.Erasure.SucRed
import Graded.Erasure.Consequences.Soundness
import Graded.Erasure.Consequences.Soundness.Erased-matches
import Graded.Erasure.LogicalRelation.Fundamental.Counterexample

-- Some consequences of the fundamental lemma.
import Graded.Erasure.Consequences.Non-interference
import Graded.Erasure.Consequences.Identity
import Graded.Erasure.Consequences.Resurrectable

-- Some examples related to the erasure modality and extraction.
import Graded.Erasure.Examples

------------------------------------------------------------------------
-- A result related to neutral terms and usage

import Graded.Neutral

------------------------------------------------------------------------
-- Some discussion of under what circumstances a []-cong combinator
-- can be defined

import Graded.Box-cong

------------------------------------------------------------------------
-- A resource aware abstract machine

-- The abstract machine
import Graded.Heap.Untyped
import Graded.Heap.Untyped.Properties
import Graded.Heap.Options
import Graded.Heap.Reduction
import Graded.Heap.Reduction.Inversion
import Graded.Heap.Reduction.Properties

-- Typing for the abstract machine
import Graded.Heap.Typed
import Graded.Heap.Typed.Substitution
import Graded.Heap.Typed.Weakening
import Graded.Heap.Typed.Inversion
import Graded.Heap.Typed.Properties
import Graded.Heap.Typed.Reduction

-- Usage for the abstract machine
import Graded.Heap.Usage
import Graded.Heap.Usage.Weakening
import Graded.Heap.Usage.Properties
import Graded.Heap.Usage.Reduction

-- Other properties of the abstract machine
import Graded.Heap.Normalization
import Graded.Heap.Bisimilarity
import Graded.Heap.Termination

-- Resource correctness of the abstract machine
import Graded.Heap.Soundness

------------------------------------------------------------------------
-- Some applications

-- An application: consistent negative axioms preserve canonicity.
import Application.NegativeAxioms.NegativeType
import Application.NegativeAxioms.NegativeContext
import Application.NegativeAxioms.Canonicity

-- An application: consistent negative or erased axioms preserve
-- canonicity (if erased matches are not allowed).
import Application.NegativeOrErasedAxioms.NegativeOrErasedType
import Application.NegativeOrErasedAxioms.NegativeOrErasedContext
import Application.NegativeOrErasedAxioms.Canonicity
import Application.NegativeOrErasedAxioms.Canonicity.ErasedMatches

------------------------------------------------------------------------
-- Pointers to code related to the paper "A Graded Modal Dependent
-- Type Theory with a Universe and Erasure, Formalized"

import README
