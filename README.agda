module README where

------------------------------------------------------------------------
-- Code related to the paper "Normalisation for First-Class Universe
-- Levels" by Nils Anders Danielsson, Naïm Favier and Ondřej Kubánek
------------------------------------------------------------------------

-- Note that Andreas Abel, Oskar Eriksson, Gaëtan Gilbert, Wojciech
-- Nawrocki, Joakim Öhman and Andrea Vezzosi have also contributed to
-- the code, and some changes to the code were made after feedback
-- from anonymous reviewers.

------------------------------------------------------------------------
-- Dependencies and licences

-- The code depends on some libraries:
--
-- * Agda's standard library, version 2.3.
-- * The builtin modules that are shipped with Agda 2.8.0.

-- When HTML code is generated from this file code is also generated
-- for the two libraries above, so URLs for their licences are
-- included here. At the time of writing the licence texts can be
-- found at the following URLs:
--
-- * https://github.com/agda/agda-stdlib/blob/v2.3/LICENCE
-- * https://github.com/agda/agda/blob/v2.8.0/LICENSE
--
-- The licence for this project can be found in the file LICENSE.

------------------------------------------------------------------------
-- Project history

-- This formalization originated as a fork of logrel-mltt
-- (https://github.com/mr-ohman/logrel-mltt). That work consisted of
-- the following contributions:
--
-- * "A Logical Relation for Martin-Löf Type Theory in Agda", code
--   mostly written by Joakim Öhman in 2016 as part of a master's
--   thesis supervised by Andrea Vezzosi and Andreas Abel.
--
--   That development is described in the article "Decidability of
--   Conversion for Type Theory in Type Theory", Andreas Abel, Joakim
--   Öhman and Andrea Vezzosi, Proceedings of the ACM on Programming
--   Languages, Volume 2, Issue POPL, 2017
--   (https://doi.org/10.1145/3158111).
--
-- * The empty type was added by Gaëtan Gilbert (2018).
--
-- * A unit type and Σ-types were added by Wojciech Nawrocki (2021).
--
-- * The code was refactored to use well-scoped syntax by Oskar
--   Eriksson (2021).
--
-- The formalization was lifted to graded modal type theory: this is
-- the basis of the paper "A Graded Modal Type Theory with a Universe
-- and Erasure, Formalized", Andreas Abel, Nils Anders Danielsson and
-- Oskar Eriksson, Proceedings of the ACM on Programming Languages,
-- Volume 7, Issue ICFP, 2023 (https://doi.org/10.1145/3607862).
--
-- Later other additions were made:
--
-- * Identity types were added by Nils Anders Danielsson (2023).
--
-- * A weak unit type was added by Oskar Eriksson (2023).
--
-- * A universe hierarchy with first-class universe levels were added
--   by Nils Anders Danielsson, Naïm Favier and Ondřej Kubánek
--   (2024-2025): this is the focus of the discussion below.

------------------------------------------------------------------------
-- 2: A type theory with first-class universe levels

------------------------------------------------------------------------
-- 2.1: Syntax

-- Note that large parts of the development are parametrised by a
-- grade type or a modality. Grades and modalities are to a large part
-- ignored in the paper. If one does not care about grades, then one
-- can use a unit type or a trivial modality:

import Graded.Modality.Instances.Unit using (UnitModality)

-- Terms.
--
-- The notation does not match the paper exactly. The notation zeroᵘ
-- is used for 0, sucᵘ for _⁺, and _supᵘ_ for _⊔_. Instead of a
-- constructor Π for Π-types there is a constructor ΠΣ⟨_⟩_,_▷_▹_ for
-- *graded* Π- and Σ-types, and the constructors for lambdas and
-- applications also take grades. The derived notation k + t is
-- denoted by sucᵘᵏ k t, and ↓ k is denoted by ↓ᵘ k.

import Definition.Untyped using (Term; sucᵘᵏ; ↓ᵘ_)

-- Contexts.
--
-- The type is more general than in the paper: the instantiation
-- Con Term corresponds to what is called Con in the paper.
--
-- Furthermore the notation does not match that used in the paper: the
-- notation ε is used for ·, and _∙_ is used instead of _,_.

import Definition.Untyped using (Con)

-- Substitution.

import Definition.Untyped using (_[_])

-- Weakening.
--
-- The notation wk ρ t is used instead of t[ρ], and the notation
-- ρ ∷ʷ Δ ⊇ Γ means that ρ is a well-formed weakening from Γ to Δ
-- (Δ ⊢ ρ : Γ in the paper). The single-step weakening p is written
-- step id: in the code this weakening is often used via
-- wk1 = wk (step id), and the lemmas wk₁ and wkTerm₁ show that this
-- operation is type-preserving.

import Definition.Untyped using (wk; step; id; wk1)
import Definition.Typed.Weakening using (_∷ʷ_⊇_; wk₁; wkTerm₁)

------------------------------------------------------------------------
-- 2.2: Typing rules
-- 2.3: Reduction rules

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
