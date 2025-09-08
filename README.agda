--------------------------------------------------------------------------
-- Code related to the paper "Normalisation for First-Class Universe Levels".
--------------------------------------------------------------------------

-- Note: in order for the hyperlinks in the PDF to work, the `agda`
-- directory should be placed in the same directory as the PDF: this
-- file should have the path `agda/README.agda` relative to the PDF.
-- You may also have to use a specific PDF viewer as not all viewers
-- support links to local files; Evince (the GNOME Document Viewer)
-- is known to work.
--
-- See also README.md for a summary of the previous contributions
-- that this work builds upon.
--
-- The code depends on some libraries:
--
-- * Agda's standard library, version 2.3.
-- * The builtin modules that are shipped with Agda 2.8.0.
--
-- To type-check the code and generate HTML, after installing Agda and
-- the standard library, run `agda --html README.agda`.
--
-- When HTML code is generated from this file code is also generated
-- for the two libraries above, so URLs for their licences are
-- included here. At the time of writing the licence texts can be
-- found at the following URLs:
--
-- * https://github.com/agda/agda-stdlib/blob/v2.3/LICENCE
-- * https://github.com/agda/agda/blob/v2.8.0/LICENSE

module README where

------------------------------------------------------------------------
-- 2: A type theory with first-class universe levels

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
import Definition.Typed.Properties.Admissible.Sigma

------------------------------------------------------------------------
-- 3: A logical relation

-- The logical relation.
import Definition.LogicalRelation

-- Validity.
import Definition.LogicalRelation.Substitution

-- The fundamental lemma.
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

------------------------------------------------------------------------
-- 4: Decidability of equality

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

------------------------------------------------------------------------
-- 5: Erasing levels is safe

-- The erasure modality.
import Graded.Modality.Instances.Erasure
import Graded.Modality.Instances.Erasure.Modality

-- Soundness of erasure.
import Graded.Usage
import Graded.Erasure.Consequences.Soundness
