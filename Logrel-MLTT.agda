-- A Logical Relation for Dependent Type Theory Formalized in Agda

module Logrel-MLTT where

-- Minimal library
import Tools.Level
import Tools.Empty
import Tools.Unit
import Tools.Relation
import Tools.PropositionalEquality
import Tools.Nullary
import Tools.Bool
import Tools.Nat
import Tools.Fin
import Tools.Sum
import Tools.Product
import Tools.Function
import Tools.List
import Tools.Algebra

import Tools.Reasoning.Preorder
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

-- Grammar of the language
import Definition.Untyped.NotParametrised
import Definition.Untyped
import Definition.Untyped.BindingType

-- Properties of the untyped syntax
import Definition.Untyped.Inversion
import Definition.Untyped.Properties

-- Typing and conversion rules of language
import Definition.Typed
import Definition.Typed.Properties
import Definition.Typed.Weakening
import Definition.Typed.Reduction
import Definition.Typed.RedSteps
import Definition.Typed.EqualityRelation
import Definition.Typed.EqRelInstance

-- The logical relation for reducibility
import Definition.LogicalRelation
import Definition.LogicalRelation.Properties.Escape
import Definition.LogicalRelation.Properties.Reflexivity
import Definition.LogicalRelation.ShapeView
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Weakening
import Definition.LogicalRelation.Properties.Conversion
import Definition.LogicalRelation.Properties.MaybeEmb
import Definition.LogicalRelation.Properties.Symmetry
import Definition.LogicalRelation.Properties.Neutral
import Definition.LogicalRelation.Properties.Universe
import Definition.LogicalRelation.Properties.Reduction
import Definition.LogicalRelation.Properties.Successor
import Definition.LogicalRelation.Properties.Transitivity
import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Application

-- The logical relation for validity
import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Substitution.Irrelevance
import Definition.LogicalRelation.Substitution.Conversion
import Definition.LogicalRelation.Substitution.Reduction
import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Reducibility
import Definition.LogicalRelation.Substitution.Escape

-- The fundamental lemma of the logical relations
import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
import Definition.LogicalRelation.Substitution.Introductions.Universe
import Definition.LogicalRelation.Substitution.Introductions.Empty
import Definition.LogicalRelation.Substitution.Introductions.Emptyrec
import Definition.LogicalRelation.Substitution.Introductions.Unit
import Definition.LogicalRelation.Substitution.Introductions.Nat
import Definition.LogicalRelation.Substitution.Introductions.Natrec
import Definition.LogicalRelation.Substitution.Introductions.Pi
import Definition.LogicalRelation.Substitution.Introductions.Lambda
import Definition.LogicalRelation.Substitution.Introductions.Application
import Definition.LogicalRelation.Substitution.Introductions.Prod
import Definition.LogicalRelation.Substitution.Introductions.Fst
import Definition.LogicalRelation.Substitution.Introductions.Snd
import Definition.LogicalRelation.Substitution.Introductions.ProdBetaEta
import Definition.LogicalRelation.Substitution.Introductions.DoubleSubst
import Definition.LogicalRelation.Substitution.Introductions.Prodrec
import Definition.LogicalRelation.Substitution.Introductions
import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consequences of the logical relation for typing and conversion
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Syntactic
import Definition.Typed.Consequences.Inequality
import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.Substitution
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.DerivedRules
import Definition.Typed.Consequences.InverseUniv
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Consequences.NeTypeEq
import Definition.Typed.Consequences.SucCong
import Definition.Typed.Consequences.Consistency
import Definition.Typed.Consequences.RedSteps

-- Algorithmic equality with lemmas that depend on typing consequences
import Definition.Conversion
import Definition.Conversion.Whnf
import Definition.Conversion.Reduction
import Definition.Conversion.Soundness
import Definition.Conversion.Stability
import Definition.Conversion.Conversion
import Definition.Conversion.Symmetry
import Definition.Conversion.Transitivity
import Definition.Conversion.Weakening
import Definition.Conversion.Lift
import Definition.Conversion.Universe
import Definition.Conversion.Decidable
import Definition.Conversion.EqRelInstance
import Definition.Conversion.FullReduction

-- Consequences of the logical relation for algorithmic equality
import Definition.Conversion.Consequences.Completeness

-- Bi-directional typechecking
import Definition.Typechecking
import Definition.Typechecking.Deterministic
import Definition.Typechecking.Soundness
import Definition.Typechecking.Completeness

-- Decidability of typing
import Definition.Typed.Decidable.Equality
import Definition.Typed.Decidable.Reduction
import Definition.Typechecking.Decidable
import Definition.Typed.Decidable

-- Modality structure
import Definition.Modality.Restrictions
import Definition.Modality
import Definition.Modality.Restrictions.Definitions

-- Properties of the modality semiring
import Definition.Modality.Properties.PartialOrder
import Definition.Modality.Properties.Equivalence
import Definition.Modality.Properties.Meet
import Definition.Modality.Properties.Addition
import Definition.Modality.Properties.Multiplication
import Definition.Modality.Properties.Star
import Definition.Modality.Properties.Has-well-behaved-zero
import Definition.Modality.Properties

-- Modality contexts and their properties
import Definition.Modality.Context
import Definition.Modality.Context.Properties.Equivalence
import Definition.Modality.Context.Properties.PartialOrder
import Definition.Modality.Context.Properties.Meet
import Definition.Modality.Context.Properties.Addition
import Definition.Modality.Context.Properties.Multiplication
import Definition.Modality.Context.Properties.Star
import Definition.Modality.Context.Properties.Lookup
import Definition.Modality.Context.Properties.Update
import Definition.Modality.Context.Properties

-- Usage modes
import Definition.Mode

-- The usage relation and its properties
import Definition.Modality.Usage
import Definition.Modality.Usage.Inversion
import Definition.Modality.Usage.Properties
import Definition.Modality.Usage.Weakening
import Definition.Modality.Usage.Decidable

-- Modality substitutions
import Definition.Modality.Substitution
import Definition.Modality.Substitution.Properties
import Definition.Modality.Substitution.Decidable

-- Modality pseudo-instances
import Definition.Modality.Instances.BoundedStar
import Definition.Modality.Instances.LowerBounded
import Definition.Modality.Instances.Finite
import Definition.Modality.Instances.Recursive
import Definition.Modality.Instances.Erasure
import Definition.Modality.Instances.Zero-one-many

-- Modality instances
import Definition.Modality.Instances.Erasure.Modality
import Definition.Modality.Instances.Erasure.Properties
import Definition.Modality.Instances.Unit
import Definition.Modality.Instances.Affine
import Definition.Modality.Instances.Linearity
import Definition.Modality.Instances.Linear-or-affine

-- The type Erased.
import Definition.Untyped.Erased
import Definition.Modality.Usage.Erased
import Definition.Typed.Erased

-- The type Unrestricted (defined using a Σ-type with η-equality).
import Definition.Untyped.Unrestricted.Eta
import Definition.Modality.Usage.Unrestricted.Eta
import Definition.Typed.Unrestricted.Eta

-- Subject reduction for modalities
import Definition.Typed.Usage

-- A "full reduction" lemma for modalities.
import Definition.Modality.FullReduction

-- Modality morphisms and quantity translations
import Definition.Untyped.QuantityTranslation
import Definition.Modality.Morphism
import Definition.Typed.QuantityTranslation
import Definition.Modality.Context.QuantityTranslation
import Definition.Mode.QuantityTranslation
import Definition.Modality.Usage.QuantityTranslation

-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa.
import Definition.Sigma

-- The erasure case study
---------------------------------

-- Target language

import Erasure.Target
import Erasure.Target.Properties.Weakening
import Erasure.Target.Properties.Substitution
import Erasure.Target.Properties.Reduction
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

-- The fundamental lemma of the logical relation

import Erasure.LogicalRelation.Fundamental.Application
import Erasure.LogicalRelation.Fundamental.Empty
import Erasure.LogicalRelation.Fundamental.Lambda
import Erasure.LogicalRelation.Fundamental.Nat
import Erasure.LogicalRelation.Fundamental.Natrec
import Erasure.LogicalRelation.Fundamental.Prodrec
import Erasure.LogicalRelation.Fundamental.Product
import Erasure.LogicalRelation.Fundamental.Unit
import Erasure.LogicalRelation.Fundamental

-- The fundamental lemma does not hold if erased matches
-- is allowed for open contexts
import Erasure.LogicalRelation.Fundamental.Counterexample

-- Soundness of Extraction function
import Erasure.SucRed
import Erasure.Consequences.Soundness

-- Application: consistent negative axioms preserve canonicity
import Application.NegativeAxioms.NegativeType
import Application.NegativeAxioms.NegativeContext
import Application.NegativeAxioms.Canonicity.Negative

-- Application: consistent negative/erased axioms preserve canonicity
import Application.NegativeAxioms.NegativeOrErasedType
import Application.NegativeAxioms.NegativeErasedContext
import Application.NegativeAxioms.Canonicity.NegativeErased
import Application.NegativeAxioms.Canonicity.Erased
-- ... but not if matching is allowed on erased pairs
import Application.NegativeAxioms.Canonicity.EliminateErased
