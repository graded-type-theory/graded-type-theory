------------------------------------------------------------------------
-- Code related to the paper "On Recursion in Graded Modal Type Theory"
-- Oskar Eriksson, Andreas Abel and Nils Anders Danielsson.
------------------------------------------------------------------------

-- Note that Naïm Camille Favier, Eve Geng, Gaëtan Gilbert, Ondřej
-- Kubánek, Wojciech Nawrocki, Joakim Öhman and Andrea Vezzosi have also
-- contributed to the code.
--
-- The code also depends on some libraries:
--
-- * Agda's standard library, version 2.4.
-- * The builtin modules that are shipped with Agda 2.8.0.
--
-- When HTML code is generated from this file code is also generated
-- for the two libraries above, so URLs for their licences are
-- included here. At the time of writing the licence texts can be
-- found at the following URLs:
--
-- * https://github.com/agda/agda-stdlib/blob/v2.4/LICENCE
-- * https://github.com/agda/agda/blob/v2.8.0/LICENSE

module README where

import Definition.LogicalRelation
import Definition.Typed
import Definition.Typed.Consequences.Canonicity
import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Inversion
import Definition.Typed.Properties.Reduction
import Definition.Typed.Restrictions
import Definition.Untyped
import Definition.Untyped.Bool.Greatest-lower-bound
import Definition.Untyped.Nat
import Definition.Untyped.NotParametrised
import Definition.Untyped.Vec
import Definition.Untyped.Whnf

import Graded.Context
import Graded.Context.Properties.Natrec
import Graded.Context.Properties.PartialOrder
import Graded.Context.Weakening
import Graded.Derived.Bool.Greatest-lower-bound
import Graded.Derived.Nat
import Graded.Derived.Vec
import Graded.Erasure.Consequences.Soundness
import Graded.Heap.Assumptions
import Graded.Heap.Bisimilarity
import Graded.Heap.Non-interference
import Graded.Heap.Normalization
import Graded.Heap.Reduction
import Graded.Heap.Reduction.Properties
import Graded.Heap.Soundness
import Graded.Heap.Soundness.Counterexample
import Graded.Heap.Termination
import Graded.Heap.Typed
import Graded.Heap.Typed.Reduction
import Graded.Heap.Untyped
import Graded.Heap.Untyped.Properties
import Graded.Heap.Usage
import Graded.Heap.Usage.Inversion
import Graded.Heap.Usage.Properties
import Graded.Heap.Usage.Reduction
import Graded.Modality
import Graded.Modality.Instances.Affine
import Graded.Modality.Instances.Affine.Examples.Good.Greatest-lower-bound
import Graded.Modality.Instances.Bounded-distributive-lattice
import Graded.Modality.Instances.Erasure.Modality
import Graded.Modality.Instances.Erasure.Properties
import Graded.Modality.Instances.Linearity
import Graded.Modality.Instances.Linearity.Examples.Bad.Nr
import Graded.Modality.Instances.Linearity.Examples.Bad.No-nr
import Graded.Modality.Instances.Linearity.Examples.Good.Greatest-lower-bound
import Graded.Modality.Instances.Nat
import Graded.Modality.Instances.Nat-plus-infinity
import Graded.Modality.Instances.Zero-one-many
import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Greatest-lower-bound
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties.Natrec
import Graded.Modality.Properties.PartialOrder
import Graded.Modality.Properties.Star
import Graded.Modality.Properties.Subtraction
import Graded.Mode
import Graded.Mode.Instances.Bounded-distributive-lattice
import Graded.Mode.Instances.Zero-one
import Graded.Mode.Instances.Zero-one.Variant
import Graded.Reduction
import Graded.Reduction.Necessary
import Graded.Substitution.Properties
import Graded.Usage
import Graded.Usage.Decidable
import Graded.Usage.Inversion
import Graded.Usage.Restrictions
import Graded.Usage.Restrictions.Natrec
import Graded.Usage.Weakening

import Tools.Algebra
import Tools.Fin
import Tools.Nat

------------------------------------------------------------------------
-- Differences between the paper and the code
------------------------------------------------------------------------

-- The code does not follow the paper exactly.
-- A notable difference is that the paper uses named variables and
-- pointers while the formalization uses de Bruijn indices. Some
-- definitions etc. are somewhat different in the formalization as a
-- result. For instance, we sometimes apply weakenings to shift indices.
-- Note that, as we wrote in the paper, "the definitions and results [in
-- the paper] should be read as if well-scoped de Bruijn indices had
-- been used".
--
-- The formalization contains several features that are not
-- discussed in the paper. The most notable of these are:
--
-- * Unit types. There are two kinds of unit types, one with η-equality
--   (strong) and one with pattern matching (weak), corresponding to the
--   two kinds of Σ-types. These are excluded from the paper for brevity
--   but the results hold also when they are included.
--
-- * Identity types. The formalization supports identity (equality)
--   types with the eliminators J and K (optionally). There is also an
--   eliminator []-cong related to erased equality proofs. We do not
--   discuss identity types in the paper but the results we present hold
--   also when they are included.
--
-- * Universe levels. In the paper, universe levels are restricted to be
--   (meta level) natural number literals. The formalization also
--   supports levels as terms of type Level. Some of our results have
--   only been proven in the case of only allowing level literals. In
--   particular, the abstract machine has not been designed with
--   evaluating terms of type Level in mind.
--
-- * Definitions. The formalization supports (opaque) definitions.
--   These are not discussed in the paper and some results are proven
--   under the assumption that there are no definitions.

-- Since identity and unit types are excluded, the notion of
-- "erased-matches" is somewhat different in the paper and the
-- formalization because the additional eliminators provide additional
-- possibilities for erased matches. When the assumption of no erased
-- matches appears in the paper, this is extended to include the
-- additional eliminators in the code.

-- Another notable difference is that the formalization contains
-- parameters that make it possible to control whether certain features
-- should be included or not as well as choose what grade semiring and
-- mode structure to use. The four most prominent parameters are
-- `Modality`, `IsMode`, `Type-restrictions`, and `Usage-restrictions`.
-- Parts of the presentation in the paper is done for certain
-- instantiations of these parameters as discussed below:

-- `Modality` controls the algebraic structure of grades (which is
-- called a "grade semiring" in the paper).

Modality = Graded.Modality.Modality

-- `IsMode` controls the structure of modes (with respect to a given
-- grade semiring).

IsMode = Graded.Mode.IsMode

-- With the exception of Section 6, we use a structure with two modes
-- (zero and one).

Zero-one-isMode = Graded.Mode.Instances.Zero-one.Zero-one-isMode

-- There is also a structure with only one mode (one). The results we
-- present in the paper generally hold with minor changes also in this
-- setting.

One-isMode = Graded.Mode.Instances.Zero-one.Zero-one-isMode

-- These two mode instances are defined simultaneously. The choice of
-- whether the mode zero is allowed or not is determined by a module
-- parameter "Mode-variant".

Mode-variant = Graded.Mode.Instances.Zero-one.Variant.Mode-variant

-- In Section 6 we use a grade semiring that is a bounded distributive
-- lattice and use the same structure for modes.

Bounded-distributive-lattice-isMode =
  Graded.Mode.Instances.Bounded-distributive-lattice.bounded-distributive-lattice-isMode

-- `Type-restrictions` control the typing judgments and the reduction
-- relation.

Type-restrictions = Definition.Typed.Restrictions.Type-restrictions

-- One can choose whether to allow strong and/or weak unit types as well
-- as binders of the form B_p^q, where p and q are grades and B is "Π",
-- "strong Σ" or "weak Σ".
--
-- If a term has a certain type ("Unit" or "B_p^q C D"), then this type
-- must be allowed by the Type-restrictions:

Unit-allowed = Definition.Typed.Inversion.⊢∷Unit→Unit-allowed
ΠΣ-allowed   = Definition.Typed.Inversion.⊢∷ΠΣ→ΠΣ-allowed

-- In the paper, we restrict the theory to exclude unit types but our
-- results hold also if such restrictions are removed. Similar choices
-- can also be made for some terms related to identity types. We do not
-- discuss these in the paper but again our results hold regardless of
-- whether they are allowed or not.

-- One can choose to allow a form of η-equality for the weak unit type.
-- Enabling this rule changes the definition of typing and reduction for
-- the weak unit element and the eliminator unitrec. The results
-- presented in the paper hold both with and without this kind of
-- η-equality but the semantics of the abstract machine are slightly
-- different.

η-for-Unitʷ = Definition.Typed.Restrictions.Type-restrictions.η-for-Unitʷ

-- One can choose whether the eliminators K and []-cong are allowed. We
-- do not include these in the paper but our results hold with them
-- enabled.

K-allowed =
  Definition.Typed.Restrictions.Type-restrictions.K-allowed
[]-cong-allowed =
  Definition.Typed.Restrictions.Type-restrictions.[]-cong-allowed

-- One can choose how opaque definitions are unfolded. Since we do not
-- discuss definitions in the paper this is of no consequence to our
-- results.

unfolding-mode =
  Definition.Typed.Restrictions.Type-restrictions.unfolding-mode

-- One can choose whether to allow equality reflection. We do not
-- discuss equality types in the paper so this is of no consequence in
-- that regard. The formalized results hold for closed terms when this
-- is enabled. For open terms some of our results are only shown with
-- equality reflection turned off.

Equality-reflection =
  Definition.Typed.Restrictions.Type-restrictions.Equality-reflection

-- `Usage-restrictions` control the usage relation.

Usage-restrictions = Graded.Usage.Restrictions.Usage-restrictions

-- One can choose for some terms which grade annotations should be
-- allowed (for a given mode). This corresponds to the side conditions
-- for some usage rules in the paper. For the terms presented in the
-- paper this is available for prodrec_r^p and emptyrec_r. One can also
-- similarly control the eliminators not discussed in the paper to
-- e.g. exclude erased matches also for these.

Prodrec-allowed =
  Graded.Usage.Restrictions.Usage-restrictions.Prodrec-allowed
Emptyrec-allowed =
  Graded.Usage.Restrictions.Usage-restrictions.Emptyrec-allowed

-- If a certain term is well-resourced then (with respect to a given
-- mode) then the term is allowed for that mode.

prodrec-allowed = Graded.Usage.Inversion.inv-usage-prodrec
emptyrec-allowed = Graded.Usage.Inversion.inv-usage-emptyrec

-- One can choose between three mutually exclusive usage rules for
-- natrec. One corresponds to (a generalization of) the usage rule using
-- the natrec-star operator, one corresponds to the usage rule we define
-- in the paper and the third is only mentioned briefly in the paper. We
-- have not shown that our results hold when the third usage rule is
-- used.

Natrec-mode = Graded.Usage.Restrictions.Natrec.Natrec-mode

------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

-- The remainder of this file contains pointers to results from the
-- paper as well as some discussion about how the code relates to
-- the results in the paper, such as any additional differences to
-- those mentioned above and how the notation of the paper and the
-- formalization differs.

------------------------------------------------------------------------
-- 3: A Graded Modal Dependent Type Theory

------------------------------------------------------------------------
-- 3.1: Grade Semirings

-- Definition 3.1: Grade Semirings.
--
-- The formalized definition differs somewhat from the definition in the
-- paper:
--
-- In the formalization, a grade semiring comes with an additional
-- special grade ω which is assumed to satisfy certain properties. This
-- grade is used to state the usage rules for the eliminators for the
-- identity type which we do not include in the paper.
--
-- Throughout the formalization, the word "modality" is used for what
-- we call a "grade semiring" in the paper.

Grade-semiring = Graded.Modality.Modality

-- The partial order relation for grades.

_≤_ = Graded.Modality.Modality._≤_

-- The order is a partial order.

≤-partial-order = Graded.Modality.Properties.PartialOrder.≤-poset

-- Example grade semirings.
--
-- Several other instances are available in the formalization.
-- See Graded/Modality/Instances.

-- The linearity semiring.

linearitySemiring =
  Graded.Modality.Instances.Linearity.linearityModality

-- The affine types semiring.

affineTypesSemiring =
  Graded.Modality.Instances.Affine.affineModality

-- The erasure semiring.

erasureSemiring =
  Graded.Modality.Instances.Erasure.Modality.ErasureModality

-- The "natural numbers" grade semiring.
--
-- This module which defines this semiring takes a boolean parameter
-- controling whether the partial order should be total giving an
-- "at most" interpretation, or flat, giving an "exact" interpretation.
--
-- In the paper we refer to a grade ω as representing "any" uses. In the
-- formalization this is denoted with ∞.

natSemiring = Graded.Modality.Instances.Nat-plus-infinity.ℕ⊎∞-modality

-- The property of a grade semiring having a well-behaved zero.

Has-well-behaved-zero = Graded.Modality.Has-well-behaved-zero

-- In the formalization, we only require that p is zero if p + q or
-- p ∧ q is zero. It follows that q is also zero from commutativity of
-- the operators.

+-positiveʳ =
  Graded.Modality.Properties.Has-well-behaved-zero.+-positiveʳ
∧-positiveʳ =
  Graded.Modality.Properties.Has-well-behaved-zero.∧-positiveʳ

-- The example grade semirings have a well-behaved zero.

linearityHasWellBehavedZero =
    Graded.Modality.Instances.Linearity.linearity-has-well-behaved-zero

affineTypesHasWellBehavedZero =
  Graded.Modality.Instances.Affine.affine-has-well-behaved-zero

erasureHasWellBehavedZero =
  Graded.Modality.Instances.Erasure.Modality.erasure-has-well-behaved-zero

natHasWellBehavedZero =
  Graded.Modality.Instances.Nat-plus-infinity.ℕ⊎∞-has-well-behaved-zero

------------------------------------------------------------------------
-- 3.2: Syntax, Typing and Usage

-- Figure 2

-- Universe level
--
-- As discussed above, we only support level literals in the paper.

Universe-level = Definition.Untyped.NotParametrised.Universe-level

-- Grade
--
-- Grades are elements of the chosen grade semiring.

grade = Graded.Modality.Modality

-- Σ-type Strength

Strength = Definition.Untyped.NotParametrised.Strength

-- Typing context
--
-- Like terms (see below), typing contexts are well-scoped. The first
-- term in a context is closed and each consequent term (can) contain an
-- additional variable.

Con = Definition.Untyped.NotParametrised.Con

-- Grade context

Conₘ = Graded.Context.Conₘ

-- Mode
--
-- As discussed above, this part of the paper uses a structure with two
-- modes.

Mode = Graded.Mode.Instances.Zero-one.Mode

-- Term
--
-- The type of terms is indexed by a natural number, representing the
-- which free variables it may refer to. The representation of de Bruijn
--- indices (discussed above) ensures that no variable indices are
-- out-of-scope, making the syntax well-scoped. In the paper, named
-- variables are used for readability.
--
-- The syntax defined in the formalization is the full syntax, including
-- terms which we do not discuss in this section or in the paper at all.
-- In particular, this includes `natrec`, the eliminator for natural
-- numbers and the terms related to the Identity type (`Id`, `rfl`, `J`,
-- `K`, and `[]-cong`). The formalization also has support for opaque
-- definitions which we do not discuss in the paper.
--
-- In the formalized syntax, Π and Σ-types have been merged. The
-- corresponding type constructor takes an argument of type `BinderMode`
-- which determines whether the term is a Π-type or a Σ-type (as well as
-- the strength in the latter case). This is done to aid the
-- formalization effort and reduce code duplication since the two types
-- can often be treated the same in proofs.
--
-- Some terms come with an additional grade annotation which is used to
-- assign a grade to the variable bound by the motive of eliminators.
-- For the usage relation with two modes, these are forced to be zero so
-- we have left out these grade in the paper.

Term = Definition.Untyped.Term

-- The type system
--
-- Like the syntax, the typing judgements are defined for the whole
-- language, including those terms which are not covered by this
-- section or the paper (though Type-restrictions can be used to exclude
-- certain types).
--
-- The contexts used in these judgements are pairs of a typing context
-- as introduced above and a "definition context", containing the
-- available definitions. Since we do not cover definitions in the paper
-- we assume that this context is empty and thus exclude it from the
-- paper. Some of our results hold also when it is not empty while other
-- are only proven for the empty case.

-- Definition contexts

DCon = Definition.Untyped.NotParametrised.DCon

-- Context pairs

Cons = Definition.Untyped.Cons

-- Well-formed contexts

⊢_ = Definition.Typed.⊢_

-- Well-formed types

_⊢_ = Definition.Typed._⊢_

-- Well-formed terms

_⊢_∷_ = Definition.Typed._⊢_∷_

-- Definitional equality for types

_⊢_≡_ = Definition.Typed._⊢_≡_

-- Definitional equality for terms

_⊢_≡_∷_ = Definition.Typed._⊢_≡_∷_

-- Well-typed applications to lambdas have matching grades

⊢λʳtᵖu→p≡r = Definition.Typed.Consequences.Inversion.inversion-lam-app

-- The usage relation
--
-- Like the syntax and typing judgements, the usage relation is defined
-- for the whole language, including those terms which are not covered
-- by this section or the paper.
--
-- In the formalization, the mode argument is written as a superscript
-- while it is written in brackets in the code.

_▸[_]_ = Graded.Usage._▸[_]_

-- Grade context lookup.

_⟨_⟩ = Graded.Context._⟨_⟩

-- Lifted operators and order relation to grade contexts.

_+ᶜ_ = Graded.Context._+ᶜ_
_∧ᶜ_ = Graded.Context._∧ᶜ_
_·ᶜ_ = Graded.Context._·ᶜ_
_≤ᶜ_ = Graded.Context._≤ᶜ_

-- The lifted order relation is a partial order.

≤ᶜ-partial-order = Graded.Context.Properties.PartialOrder.≤ᶜ-poset

-- The zero grade context.

𝟘ᶜ = Graded.Context.𝟘ᶜ

-- The variable grade context.
--
-- This context is defined as the zero context with entry i updated to
-- grade one.

𝕖ₓ = Graded.Context._,_≔_

-- Conversion between grades and modes.
--
-- Note that the conversion functions described here are for the
-- two-moded structure used in the paper. Other mode structures may have
-- different conversion functions.
--
-- In the paper we implicitly convert from modes to grades.

-- Conversion from grades to modes. In the paper this is denoted with an
-- underline.

⌞_⌟ = Graded.Mode.Instances.Zero-one.⌞_⌟

-- Conversion from modes to grades. This operation is implicit in the
-- paper but explicit in the formalization.

⌜_⌝ = Graded.Mode.Instances.Zero-one.⌜_⌝

-- The call-by-name, weak-head reduction relation.

_⊢_⇒_∷_ = Definition.Typed._⊢_⇒_∷_

-- The reflexive, transitive closure of the reduction relation.

_⊢_⇒*_∷_ = Definition.Typed._⊢_⇒*_∷_

-- Subject reduction for the usage relation
--
-- This property is proven under an assumption related to η-equality for
-- the weak unit type. In the (perhaps typical) case that η-equality is
-- turned off for this type, this assumption is vacuously true.

usage-subject-reduction = Graded.Reduction.usagePresTerm

-- The logical relation.

Logical-relation = Definition.LogicalRelation.LogRelKit

-- Weak-head normalization.

wh-normalization = Definition.Typed.Consequences.Reduction.whNorm

-- Terms in weak head normal form.

Whnf = Definition.Untyped.Whnf.Whnf

-- Consistency.

consistency = Definition.Typed.Consequences.Canonicity.¬Empty

-- Inversion of typing.

⊢∷-inversion = Definition.Typed.Consequences.Inversion.inversion-lam-Π′

-- Injectivity of Π- and Σ-types.

ΠΣ-injectivity =
  Definition.Typed.Consequences.Injectivity.ΠΣ-injectivity

------------------------------------------------------------------------
-- 4: A Resource Aware Abstract Machine

------------------------------------------------------------------------
-- 4.1: Subtraction of Grades

-- Grade semirings supporting subtraction.

Supports-subtraction =
  Graded.Modality.Properties.Subtraction.Supports-subtraction

-- The subtraction relations.

_-_≡_ = Graded.Modality.Properties.Subtraction._-_≡_
_-_≤_ = Graded.Modality.Properties.Subtraction._-_≤_

-- Subtraction of the least grade is the identity.

ω-≡ = Graded.Modality.Properties.Subtraction.∞-p≡∞

-- Subtraction by zero is the identity.

-𝟘≡ = Graded.Modality.Properties.Subtraction.p-𝟘≡p

-- The example grade semirings support subtraction and define
-- subtraction as specified in the paper.
--
-- To help illustrate the latter point, we link here to alternative
-- subtraction relations (for each instance) from which it is clearer
-- for which grades subtraction is defined and what the result is.
-- These relations are proved to be equivalent to the proper subtraction
-- relation.

-- Linear types

linearity-supports-subtraction =
  Graded.Modality.Instances.Zero-one-many.supports-subtraction
linearity-subtraction-def =
  Graded.Modality.Instances.Zero-one-many._-_≡′_
linearity-subtraction-def-correct =
  Graded.Modality.Instances.Zero-one-many.-≡↔-≡′

-- Affine types

affine-supports-subtraction =
  Graded.Modality.Instances.Zero-one-many.supports-subtraction
affine-subtraction-def =
  Graded.Modality.Instances.Zero-one-many._-_≡′_
affine-subtraction-def-correct =
  Graded.Modality.Instances.Zero-one-many.-≡↔-≡′

-- Erasure

erasure-supports-subtraction =
  Graded.Modality.Instances.Erasure.Properties.supports-subtraction
erasure-subtraction-def =
  Graded.Modality.Instances.Erasure.Properties._-_≡′_
erasure-subtraction-def-correct =
  Graded.Modality.Instances.Erasure.Properties.-≡↔-≡′

-- Nat

nat-supports-subtraction =
  Graded.Modality.Instances.Nat-plus-infinity.supports-subtraction
nat-subtraction-def =
  Graded.Modality.Instances.Nat-plus-infinity._-_≡′_
nat-subtraction-def-correct =
  Graded.Modality.Instances.Nat-plus-infinity.-≡↔-≡′

------------------------------------------------------------------------
-- 4.2: The Abstract Machine

-- In this, and following sections, we define the abstract machine for
-- a subset of the formalized language. In particular, we do not include
-- natrec or all available types. The formalization, however, includes
-- these. This means that some properties do not hold exactly as stated
-- in this section. We discuss such cases in more detail below.
--
-- Another difference between the presentation in this section and the
-- formalization is that we only consider closed terms at this point
-- though the formalization allows open terms. Again, we discuss this
-- further below.
--
-- Also note that we have assumed to be working with a grade semiring
-- supporting subtraction. Some properties mentioned below are proved
-- under these assumptions.

-- Heap entries
--
-- The type of heap entries is indexed by two natural numbers which
-- denote the size of the heap in which the entry lives and the number
-- of free variables of its term.

Entry = Graded.Heap.Untyped.Entry

-- Heaps
--
-- The formalization uses de Bruijn indices for pointers whereas the
-- paper uses names.
--
-- The type of heaps is indexed by two natural numbers. The first is the
-- size of the heap (the total number of entries) and is used to ensure
-- well-scopedness (that is, ensuring that pointers have a corresponding
-- entry). The second index represents the number of dummy indices the
-- heap contains. These are used when running open programs with erased
-- free variables but are not discussed in the paper. When only dealing
-- with closed terms this index is zero.

Heap = Graded.Heap.Untyped.Heap

-- Environments
--
-- In the paper, environments are essentially maps from variable names
-- to pointer names. In the formalization, both are de Bruijn indices
-- so we represent environments as weakenings (renaming the variable
-- indices to pointer indices).

Env = Definition.Untyped.NotParametrised.Wk

-- Continuations
--
-- Continuations are indexed by one natural number, representing the
-- size of the heap to which it is associated. Again, this is used to
-- achieve well-scopedness.
--
-- The formalization contains additional continuations compared to the
-- paper, corresponding to natrec and the eliminators related to
-- the excluded types.

Continuation = Graded.Heap.Untyped.Cont

-- Stacks
--
-- Stacks are indexed in the same way as continuations.

Stack = Graded.Heap.Untyped.Stack

-- Machine states
--
-- Machine states are parametrized by three natural numbers. One
-- corresponds to the size of the heap, one to the number of free
-- variables of the head (these two ensure that the weakening contains
-- translations from variable indices to pointer indices). The last
-- index represents the number of dummy entries in the heap.

State = Graded.Heap.Untyped.State

-- Lookup with heap update
--
-- In the paper the number of copies to look up is written as a
-- superscript. In the formalization it is written inside brackets.

_⊢_↦[_]_⨾_ = Graded.Heap.Untyped._⊢_↦[_]_⨾_

-- Lookup can fail if the heap does not contain enough resources (as
-- determined by the subtraction of the grade semiring).

-≢-no-lookup = Graded.Heap.Untyped.Properties.-≢-no-lookup

-- Lookup without heap update.

_⊢_↦_ = Graded.Heap.Untyped._⊢_↦_

-- Heap lookup without heap update always succeeds. This property is
-- proven under the assumption that the heap does not contain dummy
-- entries as is the case in this section.

⊢↦-succeeds = Graded.Heap.Untyped.Properties.¬erased-heap→↦

-- Heaps as substitutions.

⦅_⦆ʰ = Graded.Heap.Untyped.toSubstₕ

-- Applying a term to a continuation.

⦅_⦆ᶜ_ = Graded.Heap.Untyped.⦅_⦆ᶜ_

-- Applying a term to a stack.

⦅_⦆ˢ_ = Graded.Heap.Untyped.⦅_⦆ˢ_

-- Translating a state into a term.

⦅_⦆ = Graded.Heap.Untyped.⦅_⦆

-- Initial states.

⟨_⟩ = Graded.Heap.Untyped.initial

-- The multiplicity of a stack is unique (if it exists).

∣∣-functional = Graded.Heap.Untyped.Properties.∣∣-functional

-- Multiplicity of a stack.
--
-- Note that the multiplicity of the empty stack is given as a module
-- parameter. In the paper it is 1 (except in section 6). Most results
-- we present here hold regardless of the value but the main correctness
-- theorem is shown only for the case when it is 1.

∣_∣≡_ = Graded.Heap.Untyped.∣_∣≡_

-- Multiplicity of a continuation.
--
-- In the formalization, this relation also includes a mode argument
-- which is only used to decide the multiplicity for the J and K
-- eliminators. Since these are not discussed in the paper we do not
-- include the mode argument there.

∣_∣ᶜ≡_ = Graded.Heap.Untyped.∣_∣ᶜ[_]≡_

-- In this section we do not consider the eliminator for natural numbers
-- in which case the multiplicity of a stack always exist.

∃∣∣≡ = Graded.Heap.Untyped.Properties.nr∉-∣∣≡

-- The formalized statement contains an additional assumption that the
-- stack does not contain any continuations corresponding to natrec
-- which is expressed by the following relation:

natrec∈ = Graded.Heap.Untyped.natrec_,_∈

-- Reduction of eliminators and variables.

_⇾ₑ_ = Graded.Heap.Reduction._⇾ₑ_

-- This relation is defined using an auxiliary reduction relation that
-- excludes the variable rule. The reduction without tracking is defined
-- using the same auxiliary reduction.

_⇒ₑ_ = Graded.Heap.Reduction._⇒ₑ_

-- Reduction of values.

_⇒ᵥ_ = Graded.Heap.Reduction._⇒ᵥ_

-- Values.

Value = Graded.Heap.Untyped.Value

-- Values are non-neutral terms in weak head normal form.
--
-- The first property shows that values are either terms in weak head
-- normal form or an application of unitrec with η-equality for weak
-- unit types enabled (which we do not discuss in the paper). The second
-- property shows that values are not neutral terms.

Value→Whnf = Graded.Heap.Untyped.Properties.Value→Whnf
Value→¬Neutral = Graded.Heap.Untyped.Properties.Value→¬Neutral

-- The weak head semantics of the machine.

_⇾_ = Graded.Heap.Reduction._⇾_

-- The reflexive, transitive closure of the weak head semantics.

_⇾*_ = Graded.Heap.Reduction._⇾*_

-- States with variables in head position can get stuck if the heap
-- does not contain enough resources to perform a lookup.

var-noRed = Graded.Heap.Reduction.Properties.var-noRed

-- Evaluation in _⇒ᵥ_ can fail if the head does not match the stack.
--
-- A term is said to be matching a stack if it is a value and the
-- continuation on top of the stack corresponds to an eliminator for
-- that value.

⇒ᵥ-noRed = Graded.Heap.Reduction.Properties.¬Matching→¬⇒̬
Matching = Graded.Heap.Untyped.Matching

-- The stack multiplicity is zero iff it contains erased prodrec or
-- emptyrec.
--
-- Because the formalized theory contains natrec and identity types,
-- this property does not hold exactly as stated. The first direction,
-- showing that the stack multiplicity is zero if the stack contains
-- an erased prodrec or emptyrec assumes that the stack does not
-- contain a continuation related to natrec.
--
-- The second direction, showing that the stack contains erased prodrec
-- or emptyrec if the stack multiplicity is zero does not necessarily
-- hold if the stack contains certain continuations not discussed in the
-- paper. In the formalized statement we have shown that the stack
-- contains erased prodrec, unitrec or emptyrec or a continuation
-- related the identity type (J, K, or []-cong).

∣∣≡𝟘-if-erased-elim = Graded.Heap.Untyped.Properties.nr∉→∣∣≡𝟘
erased-elim-if-∣∣≡𝟘 = Graded.Heap.Untyped.Properties.∣∣≡𝟘→erased-match

-- Reduction of eliminators and variables without resource tracking.

_⇢ₑ_ = Graded.Heap.Reduction._⇢ₑ_

-- The weak head semantics without resource tracking.

_⇢_ = Graded.Heap.Reduction._⇢_

-- Reduction for numerals.

_⇒ₙ_ = Graded.Heap.Reduction._⇒ₙ_

-- A stack consisting only of (a given number of) successor
-- continuations

sucᵏ = Graded.Heap.Untyped.sucₛ

-- The property of a term being a numeral.

Numeral = Definition.Untyped.Numeral

-- The reduction relations are deterministic.

⇾-det = Graded.Heap.Reduction.Properties.⇾-det
⇢-det = Graded.Heap.Reduction.Properties.⇢-det
↠-det = Graded.Heap.Reduction.Properties.↠-det

-- The full semantics of the machine.

_↠_ = Graded.Heap.Reduction._↠_

-- Reduction can fail in three different ways.
--
-- Due to the formalization including natrec, this property does not
-- hold quite as stated. The linked property contains an additional
-- assumption that the stack does not contain any continuations
-- corresponding to natrec.
--
-- Another difference is that the formalized statement includes five
-- ways reduction can fail. Two of these are related to level terms
-- and definitions which are not discussed in the paper. The remaining
-- three are as in the paper.

Final-reasons = Graded.Heap.Reduction.Properties.nr∉-Final-reasons′

------------------------------------------------------------------------
-- 4.3: Usage and Typing for the Machine

-- Usage for heaps
--
-- The usage relation for heaps includes an additional rule not
-- mentioned in the paper related to dummy entries. We do not discuss
-- heaps with such entries so this rule cannot apply.

_▸ʰ_ = Graded.Heap.Usage._▸ʰ_

-- Renaming a grade context from variables to pointers.
-- Since the formalization uses weakenings for environments, this
-- corresponds to applying a Weakening to the grade context.
--
-- In the paper, the notation _[_] is used for this operation.

wkConₘ = Graded.Context.Weakening.wkConₘ

-- Usage for continuations
--
-- The usage relation for continuations includes additional rules
-- corresponding to the eliminators not included in this section or the
-- paper. The case for natrec is discussed in Section 5.

_▸ᶜ[_]_ = Graded.Heap.Usage._▸ᶜ[_]_

-- Usage for Stacks
--
-- The usage rule for non-empty stacks contains the assumption that the
-- stack multiplicity exists. In the paper this assumption is implicit.

_▸ˢ_ = Graded.Heap.Usage._▸ˢ_

-- Usage for states
--
-- The usage rule contains the assumption that the stack multiplicity
-- exists. In the paper this assumption is implicit.

▸_ = Graded.Heap.Usage.▸_

-- Theorem 4.1: Heap lookups succeed for well-resourced states.
--
-- This theorem is stated with an additional assumption that the stack
-- multiplicity exists. In the paper this assumption is implicit.

heap-lookup-succeeds = Graded.Heap.Usage.Properties.▸↦[]-closed

-- Theorem 4.2: Usage preservation for the abstract machine.

▸-⇾ = Graded.Heap.Usage.Reduction.▸-⇾
▸-⇾* = Graded.Heap.Usage.Reduction.▸-⇾*

-- Reduction cannot fail due to failing heap lookups.
--
-- In the formalization, this is stated as there being four ways
-- reduction can fail, two of which are related to levels and
-- definitions not discussed in the paper (see above). Of the original
-- five reasons mentioned earlier, the case for states with variables in
-- head position is no longer possible.

▸Final-reasons = Graded.Heap.Usage.Reduction.▸Final-reasons-closed

-- Typing for states.

-- The formalized version of this judgment is the one including support
-- for evaluating open programs. There, the judgment mentions an
-- additional context which does not appear in the paper. When only
-- empty terms are considered, this context is empty.

⊢ₛ_∷_ = Graded.Heap.Typed._⊢ₛ_∷_

-- Type preservation for the abstract machine.

⊢-⇾ = Graded.Heap.Typed.Reduction.⊢ₛ-⇾
⊢-⇾* = Graded.Heap.Typed.Reduction.⊢ₛ-⇾*

-- Well-typed states with values in head position reduce.
--
-- In the formalization, this theorem additionally assumes that the
-- stack multiplicity exists. As have been discussed above, this is the
-- case for the theory presented in this section.

⊢Value-⇒ᵥ = Graded.Heap.Typed.Reduction.⊢Value-⇒ᵥ

-- Theorem 4.3: For well-typed and well-resourced states, reduction
-- terminates only for states with value in head position and an empty
-- stack.
--
-- Note that unlike the similar properties discussed above, this theorem
-- holds as stated in the paper. The cases related to levels and
-- definitions are ruled out due to type restrictions and enforcing an
-- empty definition context.

⊢▸Final-reasons = Graded.Heap.Termination.⊢▸Final-reasons-closed

------------------------------------------------------------------------
-- 4.4: Resource Correctness
--
-- Some properties in this section are stated in the paper for empty
-- contexts whereas the formalized versions hold also for non-empty
-- contexts (when dummy entries are allowed in heaps).

-- Theorem 4.4: Reduction in the abstract machine implies reduction in
-- the call-by-name reduction.

-- The reduction for eliminators and variables corresponds to zero steps
-- in the call-by-name reduction.

⇒ₑ→≡ = Graded.Heap.Reduction.Properties.⇾ₑ-⦅⦆-≡

-- The reduction for values corresponds to one step in the call-by-name
-- reduction.

⇒ᵥ→⇒ = Graded.Heap.Typed.Reduction.⇒ᵥ→⇒

-- The weak-head machine reduction corresponds to the call-by-name
-- reduction.

⇾→⊢⇒ = Graded.Heap.Bisimilarity.⇾→⊢⇒

-- The reflexive, transitive closure of the weak-head machine reduction
-- corresponds to the call-by-name reduction.

⇾*→⊢⇒* = Graded.Heap.Bisimilarity.⇾*→⊢⇒*

-- States in normal form.
--
-- The formalized definition includes two additional kinds of states in
-- normal form. The first is states with a variable in head position for
-- which lookup yields a dummy entry. The second are states where the
-- head is the supremum of two universe levels. Neither of these are
-- applicable for the theory presented in the paper.

Normal = Graded.Heap.Untyped.Normal

-- Bisimilarity between the tracking and non-tracking semantics.

-- Reduction with the tracking semantics implies reduction in the
-- non-tracking semantics.

⇾→⇢ = Graded.Heap.Bisimilarity.⇾→⇢

-- Reduction with the non-tracking semantics implies reduction in the
-- tracking semantics for well-resourced states.

⇢→⇾ = Graded.Heap.Bisimilarity.⇢→⇾

-- Theorem 4.5: Evaluation to normal form

normalize = Graded.Heap.Normalization.normalize
▸normalize = Graded.Heap.Bisimilarity.▸normalize

-- Evaluation for values corresponds to evaluation in the
-- call-by-name reduction.
--
-- This property assumes that the stack multiplicity exists. As
-- discussed above, this is the case for the theory presented in this
-- section.

⊢⇒→⇒ᵥ = Graded.Heap.Bisimilarity.⊢⇒→⇒ᵥ

-- Theorem 4.6: Reduction in the call-by-name semantics implies
-- reduction in the abstract machine.

-- The first part of the theorem, for which evaluation is not
-- necessarily to a term in WHNF:

⊢⇒→⇾* = Graded.Heap.Bisimilarity.⊢⇒→⇾*

-- The second part, for evaluation to a term in WHNF:

⊢⇒→⇾*-whnf = Graded.Heap.Termination.whBisim-closed

-- Theorem 4.7: Termination of the weak-head reduction.

termination = Graded.Heap.Termination.⊢▸-⇘-closed

-- Theorem 4.8: Evaluation to numerals
--
-- This property is shown under the assumption that the stack
-- multiplicity of the empty stack is 1.

redNumeral = Graded.Heap.Soundness.redNumeral-closed

-- The logical relation for natural numbers.

_⊩ℕ_∷ℕ = Definition.LogicalRelation._⊩ℕ_≡_∷ℕ

-- Theorem 4.9: Resource correctness
--
-- The grade associated with each entry in the heap being bounded by 𝟘
-- is expressed using the relation _≤ʰ_ which relates a heap to a grade.
-- H ≤ʰ p is inhabited iff the grade associated with each entry is less
-- than p.
--
-- This property is shown under the assumption that the stack
-- multiplicity of the empty stack is 1.

resourceCorrectness = Graded.Heap.Soundness.soundness-closed

_≤ʰ_ = Graded.Heap.Usage._≤ʰ_

-- One cannot subtract non-zero from zero when the grade semiring has a
-- well-behaved zero.

𝟘-p≡q = Graded.Modality.Properties.Subtraction.𝟘-p≡q

-- Theorem 4.10: Resource correctness for open terms
--
-- The formalized statement also disallows erased matches for
-- eliminators related to excluded types.
--
-- This property is shown under the assumption that the stack
-- multiplicity of the empty stack is 1.

resourceCorrectnessOpen =
  Graded.Heap.Soundness.soundness-open-consistent

-- Counterexamples to the resource correctness theorem for open terms
-- when some assumptions are removed.
-- These counterexamples are constructed under the assumption that some
-- function types are allowed (as given by the type restrictions).

-- Counterexample using inconsistent contexts.

¬resource-correctness-inconsistent =
  Graded.Heap.Soundness.Counterexample.¬soundness-ε-inconsistent

-- Counterexample using erased matches for prodrec.

¬resource-correctness-erased-matches-prodrec =
  Graded.Heap.Soundness.Counterexample.¬soundness-ε-erased-matches-prodrec

-- Counterexample for programs using free variables in a non-erased way.

¬resource-correctness-non-erased =
  Graded.Heap.Soundness.Counterexample.¬soundness-ε-not-erased

-- A version of resource correctness with no erased matches for
-- emptyrec.

resourceCorrectnessOpen″ =
  Graded.Heap.Soundness.soundness-open-¬emptyrec₀

------------------------------------------------------------------------
-- 5: Natural Number Recursion

------------------------------------------------------------------------
-- 5.1: Natrec-star

-- The alternative usage rule has problems related to linearity.

alt-usage-bad =
  Graded.Modality.Instances.Linearity.Examples.Bad.No-nr.▸double

-- The property of a grade semiring having a natrec-star operator.

natrec-star = Graded.Modality.Has-star

-- The usage rule using natrec-star is more general than the one
-- mentioned in the paper and is based on the grade semiring providing a
-- so-called nr-function which is assumed to satisfy certain properties.

-- Any natrec-star operator is an instance of such an nr-function.

natrec-star→nr = Graded.Modality.Properties.Star.has-nr

-- Addition for natural numbers.

plus = Definition.Untyped.Nat.plus′

-- Natrec-star for the linearity semiring.

⊛-linearity = Graded.Modality.Instances.Zero-one-many._⊛_▷_

-- This is the greatest lawful natrec-star operator.

⊛-linearity-greatest =
  Graded.Modality.Instances.Zero-one-many.⊛-greatest

-- A usage rule for plus.

▸plus = Graded.Modality.Instances.Linearity.Examples.Bad.Nr.▸plus′

-- The usage for adding two variables is ω for both variables.

▸plus-x₀-x₁ =
  Graded.Modality.Instances.Linearity.Examples.Bad.Nr.▸plus′-x₀-x₁

-- The usage for adding a variable to itself is 1.

▸plus-x₀-x₀ =
  Graded.Modality.Instances.Linearity.Examples.Bad.Nr.▸plus′-x₀-x₀

------------------------------------------------------------------------
-- 5.2: A Resource-Correct Usage Rule

-- The necessary conditions for natrec are derived in the following
-- module.

module natrec-necessary = Graded.Reduction.Necessary.Natrec₁

-- In this module, an "arbitrary" usage relation is assumed with the
-- "usual" rules for some terms, subject reduction and a few additional
-- properties like weakening.

Usage-relation = Graded.Reduction.Necessary.Usage-relation

-- The usage relation we use in the paper is an instance of such an
-- "arbitrary" usage relation.
--
-- Note that the assumption discussed above related to η-equality
-- for weak unit types is applied here as well in order to show
-- subject reduction.

▸[]-Usage-relation = Graded.Reduction.Necessary.▸[]-Usage-relation

-- In the module, the "arbitrary" usage relation is also assumed to
-- have a usage rule for natrec in the form of our ansatz as well as
-- a corresponding usage inversion lemma.

Usage-relation-natrec =
  Graded.Reduction.Necessary.Usage-relation-natrec₁

-- A "usage rule" for numerals.

▸num = Graded.Reduction.Necessary.Usage.▸sucⁿ

-- A necessary condition for natrec.

natrec-necessary₁ = Graded.Reduction.Necessary.Natrec₁.g-≤-nrᵢᶜ

-- The function nrᵢ.

nrᵢ = Graded.Modality.Modality.nrᵢ

-- The function nrᵢ lifted to contexts.

nrᵢᶜ = Graded.Context.Properties.Natrec.nrᵢᶜ

-- Grade and usage context sequences.
--
-- This defines sequences of any type.

Grade-sequence = Tools.Nat.Sequence

-- Greatest lower bounds of grade sequences.

Greatest-lower-bound = Graded.Modality.Modality.Greatest-lower-bound

-- Greatest lower bounds of context sequences.

Greatest-lower-boundᶜ = Graded.Context.Greatest-lower-boundᶜ

-- Another necessary condition for natrec.
--
-- This property is shown under the additional assumption that there are
-- at least two modes. This is the case in the paper.

natrec-necessary₂ = Graded.Reduction.Necessary.Natrec₁.f-≤-p+rf

-- The necessary condition together with the condition x ≤ 𝟙 can be
-- rewritten in a different form.
-- The greatest lower bound of nrᵢ r 𝟙 p gives the greatest solution to
-- the system of inequalities x ≤ 𝟙 and x ≤ p + r · x.

natrec-alt-condition = Graded.Modality.Properties.Natrec.≤-nrᵢ-GLB

-- The usage rule for natrec.
--
-- The rule in question is natrec-no-nr-glbₘ.

▸natrec = Graded.Usage._▸[_]_

-- Definition 5.1: Grade semirings with well-behaved greatest lower
-- bounds.

Well-behaved-GLB = Graded.Modality.Has-well-behaved-GLBs

-- A "sub-interchange" law for addition and meet.

+-sub-interchangeable-∧ =
  Graded.Modality.Properties.Addition.+-sub-interchangeable-∧

-- The example grade semirings have well-behaved greatest lower bounds.
--
-- Note that the proof for the linear types and affine types instances
-- link to the same property since it is proven independently of the
-- choice of partial order.

linearity-well-behaved-GLB =
  Graded.Modality.Instances.Zero-one-many.zero-one-many-supports-glb-for-natrec
affine-well-behaved-GLB =
  Graded.Modality.Instances.Zero-one-many.zero-one-many-supports-glb-for-natrec
erasure-well-behaved-GLB =
  Graded.Modality.Instances.Erasure.Properties.Erasure-supports-factoring-nr-rule
nat-well-behaved-GLB =
  Graded.Modality.Instances.Nat-plus-infinity.ℕ⊎∞-supports-glb-for-natrec

-- Subject reduction.

usage-subject-reduction′ = Graded.Reduction.usagePresTerm

-- The characteristic inequalities of greatest lower bounds of nrᵢ.

nrᵢ-≤₁ = Graded.Modality.Properties.Natrec.nrᵢ-GLB-≤₀
nrᵢ-≤₂ = Graded.Modality.Properties.Natrec.nrᵢ-GLB-≤

-- The substitution lemma.

subst-lemma = Graded.Substitution.Properties.substₘ-lemma

-- Correctness for erasure.

erasure-correct =
  Graded.Erasure.Consequences.Soundness.Soundness.soundness-ℕ

-- For the linearity semiring the greatest lower bound of nrᵢ r 𝟙 p
-- is 𝟙 iff r ≡ 𝟘 and p ≡ 𝟙 or r ≡ 𝟙 and p ≡ 𝟘.
-- In other words, the natural number argument to natrec is considered
-- to be used linearly in exactly these cases.

natrec-linear = Graded.Modality.Instances.Linearity.nrᵢ-r𝟙p-GLB-𝟙-inv

-- For the affine types semiring, the greatest lower bound of nrᵢ r 𝟙 p
-- is 𝟙 iff r ≡ 𝟘 and p ≡ 𝟙 or r ≡ 𝟙 and p ≡ 𝟘 or r ≡ 𝟘 and p ≡ 𝟘
-- In other words, the natural number argument to natrec is considered
-- to be used in an affine way in exactly these cases.

natrec-affine = Graded.Modality.Instances.Affine.nrᵢ-r𝟙p-GLB-𝟙-inv

-- An admissible usage rule for plus (for any grade semiring).

▸plus′ = Graded.Derived.Nat.▸plus′₂

------------------------------------------------------------------------
-- 5.3: Resource Correctness
--
-- In the paper we discuss how the abstract machine supports the usage
-- rule with greatest lower bounds. In the formalization we also do this
-- for the usage rule with an "nr function" (given certain assumptions).
-- This is not discussed in the paper.

-- Multiplicity of a continuation.
--
-- As above, the formalized version has a mode argument which has no
-- effect when identity types are not considered.

∣_∣ᶜ≡′_ = Graded.Heap.Untyped.∣_∣ᶜ[_]≡_

-- The greatest lower bound does not exist for all nrᵢ sequences for
-- all grade semirings. This example is the semiring of natural numbers
-- (without ω as opposed to the grade semiring discussed above).

¬nrᵢ-GLB = Graded.Modality.Instances.Nat.¬nrᵢ-GLB

-- This instance has a well-behaved zero, supports subtraction and
-- has well-behaved greatest lower bounds.

Nat-well-behaved-zero =
  Graded.Modality.Instances.Nat.Nat-has-well-behaved-zero
Nat-subtraction =
  Graded.Modality.Instances.Nat.supports-subtraction
Nat-well-behaved-GLB =
  Graded.Modality.Instances.Nat.Nat-has-well-behaved-GLBs

-- The stack multiplicity does not necessarily exist.

∣∣≢ = Graded.Heap.Untyped.Properties.∣∣≢

-- The stack multiplicity is functional.

∣∣-functional′ = Graded.Heap.Untyped.Properties.∣∣-functional

-- The greatest lower bound of grade sequences is unique if it exists.

GLB-unique = Graded.Modality.Properties.Greatest-lower-bound.GLB-unique

-- The reduction of eliminators and variables is updated.

_⇾ₑ′_ = Graded.Heap.Reduction._⇾ₑ_

-- In particular, the auxiliary reduction is updated.

_⇒ₑ′_ = Graded.Heap.Reduction._⇒ₑ_

-- Reduction of values is also updated.

_⇒ᵥ′_ = Graded.Heap.Reduction._⇒ᵥ_

-- The reduction relations are deterministic.

⇾-det′ = Graded.Heap.Reduction.Properties.⇾-det
⇢-det′ = Graded.Heap.Reduction.Properties.⇢-det
↠-det′ = Graded.Heap.Reduction.Properties.↠-det

-- The usage for continuations is extended.

_▸ᶜ[_]′_ = Graded.Heap.Usage._▸ᶜ[_]_

-- The stack multiplicity always exists for well-resourced states.

▸∣∣≡ = Graded.Heap.Usage.Inversion.▸ₛ-inv

-- Well-resourced states do not get stuck due to non-existing stack
-- multiplicity.
--
-- In the formalization, this is stated as there being four ways
-- reduction can fail, two of which are related to level terms and
-- definitions which are not discussed in the paper. Of the original
-- three reasons mentioned earlier, the case for states with variables
-- in head position is no longer possible.

▸Final-reasons′ = Graded.Heap.Usage.Reduction.▸Final-reasons-closed

-- Typing for states is updated.

⊢ₛ_∷_′ = Graded.Heap.Typed._⊢ₛ_∷_

------------------------------------------------------------------------
-- 5.4: Usage Counting of the Natural Number Eliminator for Linear and
-- Affine Types

-- For the linearity semiring the greatest lower bound of nrᵢ r 𝟙 p
-- is 𝟙 iff r ≡ 𝟘 and p ≡ 𝟙 or r ≡ 𝟙 and p ≡ 𝟘.
-- In other words, the natural number argument to natrec is used
-- linearly in exactly these cases.

natrec-linear′ = Graded.Modality.Instances.Linearity.nrᵢ-r𝟙p-GLB-𝟙-inv

-- The predecessor function.

pred = Definition.Untyped.Nat.pred′

-- A usage rule for pred. Its argument is considered to be used once
-- i.e. linearly/affine.

▸pred = Graded.Derived.Nat.▸pred′₂

-- For the affine types semiring, the greatest lower bound of nrᵢ r 𝟙 p
-- is 𝟙 ifff r ≡ 𝟘 and p ≡ 𝟙, or r ≡ 𝟙 and p ≡ 𝟘, or r ≡ 𝟘 and p ≡ 𝟘.
-- In other words, the natural number argument to natrec is used
-- in an affine way in exactly these cases.

natrec-affine′ = Graded.Modality.Instances.Affine.nrᵢ-r𝟙p-GLB-𝟙-inv

-- The natural number argument is never considered to be erased. I.e.
-- the greatest lower bound of nrᵢ r 𝟙 p is never 𝟘 for grade semirings
-- with a well-behaved zero.

natrec-not-erased =
  Graded.Modality.Properties.Natrec.nrᵢ-natrec-not-erased

-- For both the linearity and the affine types semirings, the
-- greatest lower bound of nrᵢ 𝟘 p q is p ∧ q.
-- In other words, the contribution of the zero and successor branches
-- of natrec p′ q′ 𝟘 A z s n is γ ∧ δ when γ ▸ z and δ.p.r ▸ s.

natrec-usage-𝟘 = Graded.Modality.Instances.Zero-one-many.nrᵢ-𝟘-GLB

-- The function f.

f = Definition.Untyped.Nat.f

-- f is linear in both arguments.

▸f = Graded.Derived.Nat.▸f

-- For both the linearity and the affine types semirings, the greatest
-- lower bound of nrᵢ 𝟙 p q is p + ω · q. In other words, the
-- contribution of the zero and successor branches of
-- natrec p′ q′ 𝟙 A z s n is γ + ω · δ when γ ▸ z and δ.p.r ▸ s.

natrec-usage-𝟙 = Graded.Modality.Instances.Zero-one-many.nrᵢ-𝟙-GLB

-- For both the linearity and the affine types semirings, the greatest
-- lower bound of nrᵢ ω p q is ω ·(p + q). In other words, the
-- contribution of the zero and successor branches of
-- natrec p q ω A z s n is ω ·(γ + δ) when γ ▸ z and δ.p.r ▸ s.

natrec-usage-ω = Graded.Modality.Instances.Zero-one-many.nrᵢ-ω-GLB

------------------------------------------------------------------------
-- 5.5: Derived Usage Rules for Encoded Booleans and Vectors

-- Encoded booleans.

Bool = Definition.Untyped.Bool.Greatest-lower-bound.Bool
false = Definition.Untyped.Bool.Greatest-lower-bound.false
true = Definition.Untyped.Bool.Greatest-lower-bound.true
boolrec = Definition.Untyped.Bool.Greatest-lower-bound.boolrec

-- A usage rule for boolrec.

▸boolrec = Graded.Derived.Bool.Greatest-lower-bound.▸boolrec

-- Encoded vectors (lists of length n).

Vec = Definition.Untyped.Vec.Vec
nil = Definition.Untyped.Vec.nil′
cons = Definition.Untyped.Vec.cons′
vecrec = Definition.Untyped.Vec.vecrec′

-- A usage rule for vecrec (for any grade semiring).

▸vecrec = Graded.Derived.Vec.▸vecrec′

-- The usage rule for the linearity semiring.

▸vecrec-linear =
  Graded.Modality.Instances.Linearity.Examples.Good.Greatest-lower-bound.Vec.▸vecrec′

-- The usage rule for the affine types semiring.

▸vecrec-affine =
  Graded.Modality.Instances.Affine.Examples.Good.Greatest-lower-bound.Vec.▸vecrec′

-- The usage rule for vecrec for erased recursive calls.
-- The list is used linearly when both the head and tail are
-- used linearly/affine or one of them is affine and the other erased.
-- The list is erased when both the head and tail are erased.
-- Also note that the length of the vector is not erased.

▸vecrec-𝟘-linear =
  Graded.Modality.Instances.Linearity.Examples.Good.Greatest-lower-bound.Vec.▸vecrec′-𝟘
▸vecrec-𝟘-affine =
  Graded.Modality.Instances.Affine.Examples.Good.Greatest-lower-bound.Vec.▸vecrec′-𝟘

-- The usage rule for vecrec for linear/affine recursive calls.
-- The list is used linearly/affine if the tail is erased and the head
-- is used linearly/affine.
-- The list is erased when both the head and tail are erased.
-- Also note that the length of the vector is not erased.

▸vecrec-𝟙-linear =
  Graded.Modality.Instances.Linearity.Examples.Good.Greatest-lower-bound.Vec.▸vecrec′-𝟙
▸vecrec-𝟙-affine =
  Graded.Modality.Instances.Affine.Examples.Good.Greatest-lower-bound.Vec.▸vecrec′-𝟙

-- The usage rule for vecrec for unrestricted recursive calls
-- The list is not used linearly/affine.
-- The list is erased when both the head and tail are erased.
-- Also note that the length of the vector is not erased.

▸vecrec-ω-linear =
  Graded.Modality.Instances.Linearity.Examples.Good.Greatest-lower-bound.Vec.▸vecrec′-ω
▸vecrec-ω-affine =
  Graded.Modality.Instances.Affine.Examples.Good.Greatest-lower-bound.Vec.▸vecrec′-ω

------------------------------------------------------------------------
-- 5.6: Decidability of Usage

-- For the example grade semirings, the greatest lower bound of
-- nrᵢ r p q always exists.
--
-- Note that the proof for the linearity and affine types semirings
-- link to the same property since it is proven independently of the
-- choice of partial order.

linear-GLB-nrᵢ =
  Graded.Modality.Instances.Zero-one-many.nr-nrᵢ-GLB
affine-GLB-nrᵢ =
  Graded.Modality.Instances.Zero-one-many.nr-nrᵢ-GLB
erasure-GLB-nrᵢ =
  Graded.Modality.Instances.Erasure.Properties.Erasure-nrᵢ-glb
nat-GLB-nrᵢ =
  Graded.Modality.Instances.Nat-plus-infinity.nrᵢ-GLB

-- A function computing a usage context from a term.
-- Note that the functions assumes (among other things) that a greatest
-- lower bound exists for all nrᵢ r p q (when the usage rule for natrec
-- using greatest lower bounds is used).

⌈_⌉ = Graded.Usage.⌈_⌉

-- A decision procedure for the usage relation.
-- Note that the decision procedure assumes (among other things) that
-- a greatest lower bound exists for all nrᵢ r p q (when the usage rule
-- for natrec using greatest lower bounds is used).

_▸[_]?_ = Graded.Usage.Decidable._▸[_]?_

-- The natural numbers grade semiring (without ω).

ℕ-semiring = Graded.Modality.Instances.Nat.Nat-modality

-- This instance has a well-behaved zero, supports subtraction and
-- has well-behaved greatest lower bounds.

ℕ-well-behaved-zero =
  Graded.Modality.Instances.Nat.Nat-has-well-behaved-zero
ℕ-subtraction =
  Graded.Modality.Instances.Nat.supports-subtraction
ℕ-well-behaved-GLB =
  Graded.Modality.Instances.Nat.Nat-has-well-behaved-GLBs

-- The grade semiring does not have a least element.

ℕ-no-least = Graded.Modality.Instances.Nat.no-least

-- nrᵢ r p q does not have a greatest lower bound for most values of r,
-- p and q.

ℕ-GLB-inv = Graded.Modality.Instances.Nat.nrᵢ-GLB-inv

------------------------------------------------------------------------
-- 6 Information flow

-- A bounded-distributive lattice is a valid grade semiring.

Bounded-distributive-lattice =
  Tools.Algebra.Bounded-distributive-lattice
Bounded-distributive-lattice-semiring =
  Graded.Modality.Instances.Bounded-distributive-lattice.modality

-- Zero is the greatest element.

≤𝟘 = Graded.Modality.Instances.Bounded-distributive-lattice.≤𝟘

-- One is the least element.

𝟙≤ = Graded.Modality.Instances.Bounded-distributive-lattice.𝟙≤

-- An alternative representation of subtraction when addition and meet
-- coincide.

subtraction-+≡∧ =
  Graded.Modality.Properties.Subtraction.Addition≡Meet.p-q≡r⇔

-- An alternative representation of heap lookups for security lattice
-- instances.

↦[]⇔ = Graded.Heap.Non-interference.↦[]⇔

-- ℓ-equivalent heaps.
--
-- In the formalization, the grade/security level is written in brackets
-- instead of as a subscript.

_∼⟨_⟩_ = Graded.Heap.Untyped._~⟨_⟩_

-- Theorem 6.1: Non-interference.
--
-- The theorem in the paper states that the heaps should have well-typed
-- entries. In the formalization this is expressed using a tpying
-- judgement for heaps that is part of the typing for states but is not
-- discussed in the paper. The formalized statement only requires this
-- assumption to hold for one of the heaps.
--
-- The assumption that the grades of the heaps are given by γ[ρ] is
-- expressed using the usage relation for heaps. In general it is not
-- the case that the grades of the context and entries are equal but
-- for the lattices we consider in this section this is the case (since
-- subtraction is identity). The formalized statement only requires this
-- assumption to hold one of the heaps.
--
-- In the paper there is an environment ρ for mapping variable names to
-- pointer names. In the formalized statement this is the identity
-- weakening since the heaps contain one entry for each variable in
-- scope.
--
-- Note that the multiplicity of the empty stack has been set to the
-- user's level ℓ₀ as given by a module parameter.

non-interference = Graded.Heap.Non-interference.non-interference

-- The property of not allowing secret matches.
--
-- Like erased matches, this is done by disallowing certain matches
-- using the Usage-restrictions.
--
-- Note that the formalized definition also includes matches related to
-- eliminators not discussed in the paper.

secret-matches = Graded.Heap.Non-interference.no-secret-matches

------------------------------------------------------------------------
-- 7 Related Work

------------------------------------------------------------------------
-- 7.2 Natural Numbers and Recursion

-- For erasure, the usage rule we propose coincides with the one using
-- the natrec-star operator.

Erasure-⊛≡GLB = Graded.Modality.Instances.Erasure.Properties.▸⊛≈GLB
