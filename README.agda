--------------------------------------------------------------------------
-- Code related to the paper "Normalisation for First-Class Universe Levels".
--------------------------------------------------------------------------

-- See also the file README.md for a summary of the previous contributions
-- that this work builds upon.
--
-- The code depends on some libraries:
--
-- * Agda's standard library, version 2.2.
-- * The builtin modules that are shipped with Agda 2.7.0.1.
--
-- When HTML code is generated from this file code is also generated
-- for the two libraries above, so URLs for their licences are
-- included here. At the time of writing the licence texts can be
-- found at the following URLs:
--
-- * https://github.com/agda/agda-stdlib/blob/v2.2/LICENCE
-- * https://github.com/agda/agda/blob/v2.7.0.1/LICENSE

module README where

-- Untyped syntax.
import Definition.Untyped

-- Typing and reduction rules.
import Definition.Typed

-- Well-formedness and subject reduction.
import Definition.Typed.Syntactic

-- Admissible properties of Level, Lift, and Π/Σ.
import Definition.Typed.Properties.Admissible.Level
import Definition.Typed.Properties.Admissible.Lift
import Definition.Typed.Properties.Admissible.Pi-Sigma
import Definition.Typed.Properties.Admissible.Pi

-- The logical relation.
import Definition.LogicalRelation

-- Fundamental lemma.
import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consistency, canonicity, injectivity of type formers,
-- and other consequences of the fundamental lemma.
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Consistency
import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.Inequality

-- Algorithmic equality.
import Definition.Conversion

-- Decidability of algorithmic equality, judgemental equality,
-- typechecking, and typing.
import Definition.Conversion.Decidable
import Definition.Typed.Decidable.Equality
import Definition.Typechecking.Decidable
import Definition.Typed.Decidable

-- Full reduction / deep normalisation.
import Definition.Untyped.Normal-form
import Definition.Typed.Eta-long-normal-form
import Definition.Conversion.FullReduction

-- The erasure modality.
import Graded.Modality.Instances.Erasure
import Graded.Modality.Instances.Erasure.Modality

-- Soundness of erasure.
import Graded.Usage
import Graded.Erasure.Consequences.Soundness
