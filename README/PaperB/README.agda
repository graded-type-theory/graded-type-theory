------------------------------------------------------------------------
-- Code related to the paper "A Resource-Correct Graded Modal Dependent
-- Type Theory with Recursion, Formalized" by Oskar Eriksson, Nils
-- Anders Danielsson and Andreas Abel.
------------------------------------------------------------------------

-- Currently, the paper is not published and the code in this file
-- refers to a preliminary version.
--
-- Note that Andreas Abel, Nils Anders Danielsson, Oskar Eriksson,
-- Gaëtan Gilbert, Ondřej Kubánek, Wojciech Nawrocki, Joakim Öhman and
-- Andrea Vezzosi have also contributed to the code.
--
-- The code also depends on some libraries:
--
-- * Agda's standard library, version 2.1.
-- * The builtin modules that are shipped with Agda 2.7.0.1.
--
-- When HTML code is generated from this file code is also generated
-- for the two libraries above, so URLs for their licences are
-- included here. At the time of writing the licence texts can be
-- found at the following URLs:
--
-- * https://github.com/agda/agda-stdlib/blob/v2.1/LICENCE
-- * https://github.com/agda/agda/blob/v2.7.0.1/LICENSE

module README.PaperB.README where

import Definition.Typed
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Inversion
import Definition.Typed.Properties.Reduction
import Definition.Typed.Restrictions
import Definition.Untyped
import Definition.Untyped.NotParametrised

import Graded.Context
import Graded.Context.Properties.Natrec
import Graded.Context.Properties.PartialOrder
import Graded.Context.Weakening
import Graded.Erasure.Consequences.Soundness
import Graded.Heap.Assumptions
import Graded.Heap.Bisimilarity
import Graded.Heap.Examples
import Graded.Heap.Examples.Linearity
import Graded.Heap.Normalization
import Graded.Heap.Reduction
import Graded.Heap.Reduction.Properties
import Graded.Heap.Soundness
import Graded.Heap.Soundness.Counterexample
import Graded.Heap.Termination
import Graded.Heap.Typed
import Graded.Heap.Typed.Properties
import Graded.Heap.Typed.Reduction
import Graded.Heap.Untyped
import Graded.Heap.Untyped.Properties
import Graded.Heap.Usage
import Graded.Heap.Usage.Inversion
import Graded.Heap.Usage.Properties
import Graded.Heap.Usage.Reduction
import Graded.Modality
import Graded.Modality.Instances.Affine
import Graded.Modality.Instances.Erasure.Modality
import Graded.Modality.Instances.Erasure.Properties
import Graded.Modality.Instances.Examples
import Graded.Modality.Instances.Linearity
import Graded.Modality.Instances.Linearity.Bad
import Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr
import Graded.Modality.Instances.Linearity.Good.Greatest-lower-bound
import Graded.Modality.Instances.Nat
import Graded.Modality.Instances.Nat-plus-infinity
import Graded.Modality.Instances.Set
import Graded.Modality.Instances.Zero-one-many
import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Greatest-lower-bound
import Graded.Modality.Properties.Has-well-behaved-zero
import Graded.Modality.Properties.Natrec
import Graded.Modality.Properties.PartialOrder
import Graded.Modality.Properties.Star
import Graded.Modality.Properties.Subtraction
import Graded.Modality.Variant
import Graded.Mode
import Graded.Reduction
import Graded.Substitution.Properties
import Graded.Usage
import Graded.Usage.Inversion
import Graded.Usage.Restrictions
import Graded.Usage.Weakening

import Tools.Fin
import Tools.Nat

------------------------------------------------------------------------
-- Differences between the paper and the code
------------------------------------------------------------------------

-- The code does not follow the paper exactly. Notably, the
-- formalisation contains parameters that make it possible to control
-- whether certain features should be included or not (in addition to
-- the possibility to choose what modality to use). The three most
-- prominent parameters are `Modality-variant`, `Type-restrictions` and
-- `Usage-restrictions`. The presentation in the paper is done for
-- certain instantiations of these parameters as discussed below:

-- Modality-variant controls whether the usage relation should support
-- one or two modes. In the paper, we use two modes but our results hold
-- also for the theory with one mode.

Modality-variant = Graded.Modality.Variant.Modality-variant

-- Type-restrictions control the typing judgments and the reduction
-- relation.

Type-restrictions = Definition.Typed.Restrictions.Type-restrictions

-- One can choose whether to allow strong and/or weak unit types as well
-- as binders of the form B_p^q, where p and q are grades and B is "Π",
-- "strong Σ" or "weak Σ".
--
-- If a term has a certain type ("Unit" or "B_p^q C D"), then this type
-- must be allowed by the Type-restrictions:

Unit-allowed = Definition.Typed.Inversion.⊢∷Unit→Unit-allowed
ΠΣ-allowed   = Definition.Typed.Inversion.⊢∷ΠΣ→ΠΣ-allowed

-- In the paper, we do not have such restrictions (i.e. these types are
-- always allowed) but our results hold also if such restrictions are
-- included. Similar choices can also be made for certain terms related
-- to identity types. We do not discuss these in the paper but again our
-- results hold regardless of whether these are allowed or not.

-- One can choose to allow a form of η-equality for the weak unit type.
-- Enabling this rule changes the definition of typing and reduction for
-- the weak unit element and unitrec.
--
-- In the paper, this is not enabled but a version of our results hold
-- also when it is. In order to be consistent with the reduction, the
-- rules for machine transitions are changed slightly and some
-- properties (including our main correctness theorem) are shown under
-- an additional assumption:

Unitʷ-η-assumption = Graded.Heap.Assumptions.Assumptions.Unitʷ-η→

-- One can choose whether to allow equality reflection. We do not
-- discuss equality types in the paper so this is of no consequence in
-- that regard. The formalized results hold for closed terms when this
-- is enabled. For open terms our proof holds only with equality
-- reflection turned off.

-- Usage-restrictions control the usage relation.

Usage-restrictions = Graded.Usage.Restrictions.Usage-restrictions

-- One can choose for some terms which grade annotations should be
-- allowed (for a given mode). This corresponds to the side conditions
-- for some usage rules in the paper. For the terms presented in the
-- paper this is available for prodrec_r^p, unitrec_p, and emptyrec_p.
--
-- If a certain term is well-resourced then (with respect to a given
-- mode) then the term is allowed for that mode.

prodrec-allowed = Graded.Usage.Inversion.inv-usage-prodrec
unitrec-allowed = Graded.Usage.Inversion.inv-usage-unitrec
emptyrec-allowed = Graded.Usage.Inversion.inv-usage-emptyrec

-- One can choose whether the strong unit element should be
-- well-resourced in any context (as opposed to only in the zero
-- context). In the presentation used in the paper this is allowed but
-- the results hold either way.

-- One can choose between three mutually exclusive usage rules for
-- natrec. One corresponds to the usage rule using the natrec-star
-- operator, one corresponds to the usage rule we define in the paper
-- and the third is only mentioned briefly in the paper. We have not
-- shown that our results hold when this usage rule is used.

------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

-- The remainder of this file contains pointers to results from the
-- paper.

------------------------------------------------------------------------
-- 2: A Graded Modal Dependent Type Theory

------------------------------------------------------------------------
-- 2.1: Modalities

-- Definition 2.1: Modalities.
--
-- The formalized definition differs somewhat from the definition in the
-- paper:
--
-- In the formalization, a modality comes with an additional
-- special grade ω which is assumed to satisfy certain properties. This
-- grade is used to state the usage rules for the eliminators for the
-- identity type which we do not include in the paper.
--
-- Equality between grades is not assumed to be decidable in general but
-- it is decidable whether a grade is equal to zero.
--
-- Modality records contain a field of type Modality-variant in addition
-- to the algebraic structure which is referred to as
-- `Semiring-with-meet` in the formalization.

Modality = Graded.Modality.Modality
Semiring-with-meet = Graded.Modality.Semiring-with-meet

-- Sets of natural numbers are not generally modalities

set-no-modality = Graded.Modality.Instances.Set.𝟙-𝟚.no-modality

-- The partial order relation for modalities

_≤_ = Graded.Modality.Modality._≤_

-- The order is a partial order

≤-partial-order = Graded.Modality.Properties.PartialOrder.≤-poset

-- Definition 2.2: Modalities with a well-behaved zero.

-- The property of having a well-behaved zero is defined for
-- `Semiring-with-meet`, the algebraic structure of the modality.

Has-well-behaved-zero = Graded.Modality.Has-well-behaved-zero

-- The formalized definition does not require q ≡ 𝟘 to follow from
-- p + q ≡ 𝟘 or p ∧ q ≡ 𝟘. This follows from commutativity of the
-- operators.

+-positiveʳ =
  Graded.Modality.Properties.Has-well-behaved-zero.+-positiveʳ
∧-positiveʳ =
  Graded.Modality.Properties.Has-well-behaved-zero.∧-positiveʳ

-- Example modalities.
--
-- All these modality definitions takes an argument of type
-- `Modality-variant`. The modalities can thus be defined to support
-- either the moded or non-moded usage relation.

-- The erasure modality.

erasureModality =
  Graded.Modality.Instances.Erasure.Modality.ErasureModality

-- The affine types modality

affineTypesModality =
  Graded.Modality.Instances.Linearity.linearityModality

-- The linear types modality.

linearTypesModality =
  Graded.Modality.Instances.Linearity.linearityModality

-- The "natural numbers" instances

-- The definition takes a boolean argument, controlling which of the two
-- order relations should be used.
--
-- In the formalization, the grade ∞ is used to represent any number of
-- uses. In the paper we refer to this grade as ω.

ℕω-Modality = Graded.Modality.Instances.Nat-plus-infinity.ℕ⊎∞-Modality

------------------------------------------------------------------------
-- 2.2: Syntax, Typing and Usage

-- de Bruijn index
--
-- In the formalization, de Bruijn indices are represented as the type
-- `Fin`, unlike the paper which uses `Nat`. This representation ensures
-- that the syntax is well-scoped since out-of-scope variable indices
-- cannot occur.

de-Bruijn-index = Tools.Fin.Fin

-- Universe level

Universe-level = Definition.Untyped.NotParametrised.Universe-level

-- Grade
--
-- Grades are elements of the chosen modality

grade = Graded.Modality.Modality

-- Strength

Strength = Definition.Untyped.NotParametrised.Strength

-- Term
--
-- The type of terms is indexed by a natural number, representing the
-- number of free variables it has. The representation of de Bruijn
-- indices (discussed above) ensures that no variable indices are
-- out-of-scope, making the syntax well-scoped.
--
-- The syntax defined in the formalization is the full syntax, including
-- terms which we do not discuss in this section or in the paper at all.
-- In particular, this includes `natrec`, the eliminator for natural
-- numbers and the terms related to the Identity type (`Id`, `rfl`, `J`,
-- `K`, and `[]-cong`).
--
-- In the formalized syntax, Π and Σ-types have been merged. The
-- corresponding type constructor takes an argument of type `BinderMode`
-- which determines whether the term is a Π-type or a Σ-type (as well as
-- the strength in the latter case). This is done to aid the
-- formalization effort and reduce code duplication since the two types
-- can often be treated the same in proofs.
--
-- Another difference is that the unit types exist at any universe level
-- unlike in the paper where we define them at level 0 for simplicity.
-- In the formalized syntax, the terms for the unit types, unit elements
-- and `unitrec`, the eliminator for the weak unit type, all take an
-- argument of type `Universe-level`. The version of this theory that
-- is presented in the paper always set these to zero.
--
-- Some terms come with an additional grade annotation which is used to
-- assign a grade to the variable bound by the motive of eliminators.
-- For the usage relation with two modes, this is forced to be zero so
-- we have left out this grade in the paper.

Term = Definition.Untyped.Term

-- Weakening

Weakening = Definition.Untyped.NotParametrised.Wk

-- Typing context
--
-- Typing contexts are also well-scoped. The first term in a context is
-- closed and each consequent term (can) contain an additional variable.

Con = Definition.Untyped.NotParametrised.Con

-- Grade context

Conₘ = Graded.Context.Conₘ

-- Mode
--
-- As explained above, a modality can either support the two-moded usage
-- relation or not using the `Modality-variant` field of the modality.
-- The type `Mode` contains two elements if the chosen modality supports
-- the moded usage relation and one element if it does not. Again, in
-- the theory presented in the paper, we are using two modes.

Mode = Graded.Mode.Mode

-- Weakenings applied to variable indices. In the paper, the notation
-- _[_] is used for this operation.

wkVar = Definition.Untyped.NotParametrised.wkVar

-- Weakenings applied to terms. In the paper, the notation
-- _[_] is used for this operation.

wk = Definition.Untyped.wk

-- The weakenings ↑ⁿ and ⇑ⁿ

↑ⁿ = Definition.Untyped.NotParametrised.stepn
⇑ⁿ = Definition.Untyped.NotParametrised.liftn

-- Substitutions

Subst = Definition.Untyped.Subst

-- Application of substitutions to terms

_[_] = Definition.Untyped._[_]

-- Extending a substitution σ with a term t.

consSubst = Definition.Untyped.consSubst

-- Substituting a single variable

_[_]₀ = Definition.Untyped._[_]₀

-- Composition of substitutions
--
-- There are four composition operators for composing weakenings and
-- substitutions. In the paper we treat weakenings and substitutions the
-- same and use only one composition operator for all cases. Note that
-- the formalization uses a different symbol for composition than the
-- paper

-- Composing two substitutions

_ₛ•ₛ_ = Definition.Untyped._ₛ•ₛ_

-- Composing two weakenings

_•_ = Definition.Untyped.NotParametrised._•_

-- Composing a weakening with a substitution

_•ₛ_ = Definition.Untyped._•ₛ_

-- Composing a substitution with a weakening

_ₛ•_ = Definition.Untyped._ₛ•_

-- Weakening for substitutions

↑ˢ = Definition.Untyped.wk1Subst
⇑ˢ = Definition.Untyped.liftSubst

-- The type system
--
-- Like the syntax, the typing judgements are defined for the whole
-- language, including those terms which are not covered by this
-- section or the paper.

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

-- Well-formed variables

_∷_∈_ = Definition.Typed._∷_∈_

-- Max for universe levels

_⊔_ = Definition.Untyped.NotParametrised._⊔ᵘ_

-- Well-typed applications to lambdas have matching grades

⊢λʳtᵖu→p≡r = Definition.Typed.Consequences.Inversion.inversion-lam-app

-- The usage relation
--
-- Like the syntax and typing judgements, the usage relation is defined
-- for the whole language, including those terms which are not covered
-- by this section or the paper.

_▸[_]_ = Graded.Usage._▸[_]_

-- Grade context lookup

_⟨_⟩ = Graded.Context._⟨_⟩

-- Lifted operators and order relation to grade contexts

_+ᶜ_ = Graded.Context._+ᶜ_
_∧ᶜ_ = Graded.Context._∧ᶜ_
_·ᶜ_ = Graded.Context._·ᶜ_
_≤ᶜ_ = Graded.Context._≤ᶜ_

-- The lifted order relation is a partial order

≤ᶜ-partial-order = Graded.Context.Properties.PartialOrder.≤ᶜ-poset

-- Conversion between grades and modes.
--
-- In the paper we implicitly convert from modes to grades. In the
-- formalization, these are explicit.

-- Conversion from grades to modes

⌞_⌟ = Graded.Mode.⌞_⌟

-- Conversion from modes to grades

⌜_⌝ = Graded.Mode.⌜_⌝

-- Weakening of usage contexts
--
--  In the paper, the notation _[_] is used for this operation.

wkConₘ = Graded.Context.Weakening.wkConₘ

-- Usage is preserved by weakening

wkUsage = Graded.Usage.Weakening.wkUsage

-- The call-by-name, weak-head reduction relation.

_⊢_⇒_∷_ = Definition.Typed._⊢_⇒_∷_

-- The reflexive, transitive closure of the reduction relation.

_⊢_⇒*_∷_ = Definition.Typed._⊢_⇒*_∷_

-- Reduction is deterministic

⇒-deterministic = Definition.Typed.Properties.Reduction.whrDetTerm

-- Well-typed terms reduce to WHNF.

redWhnf = Definition.Typed.Consequences.Reduction.whNormTerm

-- Terms in WHNF do not reduce.

whnfNoRed = Definition.Typed.Properties.Reduction.whnfRedTerm

------------------------------------------------------------------------
-- 3: A Resource Aware Abstract Machine

------------------------------------------------------------------------
-- 3.1: Subtraction of Grades

-- Definition 3.1: Subtraction

_-_≤_ = Graded.Modality.Properties.Subtraction._-_≤_
_-_≡_ = Graded.Modality.Properties.Subtraction._-_≡_

-- Theorem 3.2: Properties of Subtraction

-- Subtraction is functional

-≡-functional = Graded.Modality.Properties.Subtraction.-≡-functional

-- Subtraction is monotone in its first argument

-≡-monotoneˡ = Graded.Modality.Properties.Subtraction.-≡-monotoneˡ

-- Subtraction is antitone in its second argument

-≡-antitoneʳ = Graded.Modality.Properties.Subtraction.-≡-antitoneʳ

-- Subtraction by zero is the identity

-𝟘≡ = Graded.Modality.Properties.Subtraction.p-𝟘≡p

-- Subtraction of the least grade is the identity

ω-≡ = Graded.Modality.Properties.Subtraction.∞-p≡∞

-- Subtraction of zero by is only possible by zero.

𝟘-≡ = Graded.Modality.Properties.Subtraction.𝟘-p≡q

-- Modalities supporting subtraction

Supports-subtraction =
  Graded.Modality.Properties.Subtraction.Supports-subtraction

-- The example modalities support subtraction and defines subtraction as
-- specified in the paper.
--
-- To help illustrate the latter point, we link here to alternative
-- subtraction relations (for each instance) from which it is clearer
-- for which grades subtraction is defined and what the result is.
-- These relations are proved to be equivalent to the proper subtraction
-- relation.

erasure-supports-subtraction =
  Graded.Modality.Instances.Erasure.Properties.supports-subtraction
erasure-subtraction-def =
  Graded.Modality.Instances.Erasure.Properties._-_≡′_
erasure-subtraction-def-correct =
  Graded.Modality.Instances.Erasure.Properties.-≡↔-≡′

affine-supports-subtraction =
  Graded.Modality.Instances.Zero-one-many.supports-subtraction
affine-subtraction-def =
  Graded.Modality.Instances.Zero-one-many._-_≡′_
affine-subtraction-def-correct =
  Graded.Modality.Instances.Zero-one-many.-≡↔-≡′

linearity-supports-subtraction =
  Graded.Modality.Instances.Zero-one-many.supports-subtraction
linearity-subtraction-def =
  Graded.Modality.Instances.Zero-one-many._-_≡′_
linearity-subtraction-def-correct =
  Graded.Modality.Instances.Zero-one-many.-≡↔-≡′

ℕω-supports-subtraction =
  Graded.Modality.Instances.Nat-plus-infinity.supports-subtraction
ℕω-subtraction-def =
  Graded.Modality.Instances.Nat-plus-infinity._-_≡′_
ℕω-subtraction-def-correct =
  Graded.Modality.Instances.Nat-plus-infinity.-≡↔-≡′

------------------------------------------------------------------------
-- 3.2: The Abstract Machine

-- In this, and following sections, we define the abstract machine for
-- a subset of the formalized language. In particular, we do not include
-- natrec or identity types. The formalization, however, includes these.
-- This means that some properties do not hold exactly as stated in this
-- section. We discuss such cases in more detail below.
--
-- Another difference between the presentation in this section and the
-- formalization is that we only consider closed terms at this point
-- though the formalization allows open terms. Again, we discuss this
-- further below.
--
-- Also note that we have assumed to be working with a modality
-- supporting subtraction and with a well-behaved zero. Some properties
-- mentioned below are proved under these assumptions.

-- Heap entries
--
-- The type of heap entries is indexed by two natural numbers which
-- denote the size of the heap in which the entry lives and the number
-- of free variables of its term.

Entry = Graded.Heap.Untyped.Entry

-- Heaps
--
-- The type of heaps is indexed by two natural numbers. The first is the
-- size of the heap (the total number of entries) and is used to ensure
-- well-scopedness (that is, ensuring that pointers have a corresponding
-- entry). The second index represents the number of dummy indices the
-- heap contains. In this section, we do not consider heaps with
-- dummy entries and consequently require this index to always be zero.

Heap = Graded.Heap.Untyped.Heap

-- Continuations
--
-- Continuations are indexed by one natural number, representing the
-- size of the heap to which it is associated. Again, this is used to
-- achieve well-scopedness.
--
-- The formalization contains additional continuations compared to the
-- paper, corresponding to natrec and the eliminators related to
-- the identity type.
--
-- Some continuations have an additional grade annotation than in the
-- paper. This corresponds to the extra annotations for terms explained
-- above.

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
-- index represents the number of dummy entries in the heap. Again, this
-- is zero in this section.

State = Graded.Heap.Untyped.State

-- Lookup with heap update
--
-- In the paper the number of copies to look up is written as a
-- superscript. In the formalization it is written inside brackets.

_⊢_↦[_]_⨾_ = Graded.Heap.Untyped._⊢_↦[_]_⨾_

-- Lookup can fail if the heap does not contain enough resources (as
-- determined by the subtraction of the modality).

-≢-no-lookup = Graded.Heap.Untyped.Properties.-≢-no-lookup

-- Lookup without heap update.

_⊢_↦_ = Graded.Heap.Untyped._⊢_↦_

-- Heap lookup without heap update always succeeds. This property is
-- proven under the assumption that the heap does not contain dummy
-- entries as is the case in this section.

⊢↦-succeeds = Graded.Heap.Untyped.Properties.¬erased-heap→↦

-- Heaps as substitutions

⦅_⦆ʰ = Graded.Heap.Untyped.toSubstₕ

-- Applying a term to a continuation

⦅_⦆ᶜ_ = Graded.Heap.Untyped.⦅_⦆ᶜ_

-- Applying a term to a stack

⦅_⦆ˢ_ = Graded.Heap.Untyped.⦅_⦆ˢ_

-- Translating a state into a term.

⦅_⦆ = Graded.Heap.Untyped.⦅_⦆

-- Initial states

initial = Graded.Heap.Untyped.initial

-- Multiplicity of a stack.

∣_∣≡_ = Graded.Heap.Untyped.∣_∣≡_

-- Multiplicity of a continuation

∣_∣ᶜ≡_ = Graded.Heap.Untyped.∣_∣ᶜ≡_

-- The multiplicity of a stack is unique (if it exists).

∣∣-functional = Graded.Heap.Untyped.Properties.∣∣-functional

-- The multiplicity of a stack always exists.
--
-- This property does not hold as stated since the formalization
-- contains natrec while the paper does not (in this section). The
-- linked property contains an additional assumption that the stack does
-- not contain any continuations corresponding to natrec.

∃∣∣≡ = Graded.Heap.Untyped.Properties.nr∉-∣∣≡

-- The property that a stack contains a natrec continuation

natrec∈ = Graded.Heap.Untyped.natrec_,_∈

-- Reduction of eliminators and variables

_⇾ₑ_ = Graded.Heap.Reduction._⇾ₑ_

-- This relation is defined using an auxiliary reduction relation that
-- excludes the variable rule. The reduction without tracking is defined
-- using the same auxiliary reduction.

_⇒ₑ_ = Graded.Heap.Reduction._⇒ₑ_

-- Reduction of values

_⇒ᵥ_ = Graded.Heap.Reduction._⇒ᵥ_

-- The weak head semantics of the machine.

_⇾_ = Graded.Heap.Reduction._⇾_

-- The reflexive, transitive closure of the weak head semantics.

_⇾*_ = Graded.Heap.Reduction._⇾*_

-- States with variables in head position can get stuck if the heap
-- does not contain enough resources to perform a lookup.

var-noRed = Graded.Heap.Reduction.Properties.var-noRed

-- Evaluation in _⇒ᵥ_ can fail if the head does not match the stack
--
-- A term is said to be matching a stack if it is a value and the
-- continuation on top of the stack corresponds to an eliminator for
-- that value.

⇒ᵥ-noRed = Graded.Heap.Reduction.Properties.¬Matching→¬⇒̬
Matching = Graded.Heap.Untyped.Matching

-- Weakening of stacks. In the paper, the notation _[_] is used for
-- this operation.

wkˢ = Graded.Heap.Untyped.wkˢ

-- The stack multiplicity is zero iff it contains erased prodrec,
-- unitrec or emptyrec.
--
-- Because the formalized theory contains natrec and identity types,
-- this property does not hold exactly as stated. The first direction,
-- showing that the stack multiplicity is zero if the stack contains
-- an erased prodrec, unitrec, or emptyrec assumes that the stack
-- multiplicity exists. As discussed above, this is the case if the
-- stack does not contain any natrec eliminators.
--
-- The second direction, showing that the stack contains erased prodrec,
-- unitrec, or emptyrec if the stack multiplicity is zero does not
-- necessarily hold if the stack contains continuations related to the
-- identity type since these can have multiplicity zero. In the linked
-- property, we have shown that the stack contains erased prodrec,
-- unitrec or emptyrec or a continuation related the identity type (J,
-- K, or []-cong).

∣∣≡𝟘-if-erased-elim = Graded.Heap.Untyped.Properties.nr∉→∣∣≡𝟘
erased-elim-if-∣∣≡𝟘 = Graded.Heap.Untyped.Properties.∣∣≡𝟘→erased-match

-- Reduction of eliminators and variables without resource tracking

_⇢ₑ_ = Graded.Heap.Reduction._⇢ₑ_

-- The weak head semantics without resource tracking.

_⇢_ = Graded.Heap.Reduction._⇢_

-- Reduction for numerals

_⇒ₙ_ = Graded.Heap.Reduction._⇒ₙ_

-- A stack consisting only of (a given number of) successor
-- continuations

sucᵏ = Graded.Heap.Untyped.sucₛ

-- The reduction relations are deterministic

⇾-det = Graded.Heap.Reduction.Properties.⇾-det
⇢-det = Graded.Heap.Reduction.Properties.⇢-det
↠-det = Graded.Heap.Reduction.Properties.↠-det

-- The full semantics of the machine

_↠_ = Graded.Heap.Reduction._↠_

-- Reduction can fail in three different ways
--
-- Due to the formalization including natrec, this property does not
-- hold quite as stated. The linked property contains an additional
-- assumption that the stack does not contain any continuations
-- corresponding to natrec.

Final-reasons = Graded.Heap.Reduction.Properties.nr∉-Final-reasons′

------------------------------------------------------------------------
-- 3.3: Usage for the Machine

-- Usage for heaps
--
-- The usage relation for heaps includes an additional rule not
-- mentioned in the paper related to dummy entries. In this section,
-- heaps are assumed to not have such entries so this rule cannot apply.
-- This case is discussed in the extended version.

_▸ʰ_ = Graded.Heap.Usage._▸ʰ_

-- Usage for continuations
--
-- The usage relation for continuations includes additional rules
-- corresponding to the eliminators not included in this section or the
-- paper. The case for natrec is discussed in Section 4.
--
-- In the paper the mode is written as a superscript. In the
-- formalization it is written inside brackets.

_▸ᶜ[_]_ = Graded.Heap.Usage._▸ᶜ[_]_

-- Usage for Stacks
--
-- The usage rule for non-empty stacks contains the assumption that the
-- stack multiplicity exists. As mentioned in the paper, this assumption
-- is implicit there.

_▸ˢ_ = Graded.Heap.Usage._▸ˢ_

-- Usage for states
--
-- The usage rule contains the assumption that the stack multiplicity
-- exists. As mentioned in the paper, this assumption is implicit there.

▸_ = Graded.Heap.Usage.▸_

-- Lemma 3.3: Heap lookups in well-resourced heaps yield well-resourced
-- entries and well-resourced updated heaps.

well-resourced-lookup = Graded.Heap.Usage.Properties.▸-heapLookup

-- Theorem 3.4: Usage preservation for the abstract machine

▸-⇾ = Graded.Heap.Usage.Reduction.▸-⇾
▸-⇾* = Graded.Heap.Usage.Reduction.▸-⇾*

-- Theorem 3.5: Heap lookups succeed for well-resourced heaps
--
-- This theorem is stated with an additional assumption that the stack
-- multiplicity exists. In the paper this assumption is implicit.

heap-lookup-succeeds = Graded.Heap.Usage.Properties.▸↦[]-closed

-- Reduction cannot fail due to failing heap lookups.
--
-- In the formalization, this is stated as there being two ways
-- reduction can fail. Of the original three reasons mentioned earlier,
-- the case for states with variables in head position is no longer
-- possible.

▸Final-reasons = Graded.Heap.Usage.Reduction.▸Final-reasons-closed

------------------------------------------------------------------------
-- 3.4: Typing for the Machine

-- Typing for heaps.
--
-- The formalized version of this judgment is the one which includes
-- support for evaluating open programs. There,
-- the judgment mentions an additional context which does not appear in
-- this section. For heaps without dummy entries, which is the case in
-- this section, one can show that this context is always empty.
--
-- The judgment has an additional case related to dummy entries. In this
-- section, heaps are assumed to not contain dummy entries so this rule
-- does not apply.

⊢ʰ_∷_ = Graded.Heap.Typed._⊢ʰ_∷_

-- Typing for continuations
--
-- As for heaps, the formalized judgment contains an additional context.
-- For the theory presented in this section, this context is empty.
--
-- The typing relation for continuations includes additional rules
-- corresponding to the eliminators not included in this section or the
-- paper. The case for natrec is discussed in Section 4.

_⊢ᶜ_⟨_⟩∷_↝_ = Graded.Heap.Typed._⨾_⊢ᶜ_⟨_⟩∷_↝_

-- Typing for stacks
--
-- Again, the formalized judgment contains an additional context.
-- For the theory presented in this section, this context is empty.

_⊢_⟨_⟩∷_↝_ = Graded.Heap.Typed._⨾_⊢_⟨_⟩∷_↝_

-- Typing for states
--
-- Again, the formalized judgment contains an additional context.
-- For the theory presented in this section, this context is empty.

⊢ₛ_∷_ = Graded.Heap.Typed._⊢ₛ_∷_

-- Well-typed states are well-typed when translated back into terms

⊢⦅⦆ = Graded.Heap.Typed.Properties.⊢⦅⦆

-- Theorem 3.6: Type preservation for the abstract machine

⊢-⇾ = Graded.Heap.Typed.Reduction.⊢ₛ-⇾
⊢-⇾* = Graded.Heap.Typed.Reduction.⊢ₛ-⇾*

-- Theorem 3.7: Values in non-empty stacks always reduce.
--
-- In the formalization, this theorem additionally assumes that the
-- stack multiplicity exists. As have been discussed above, this is the
-- case for the theory presented in this section.

⊢Value-⇒ᵥ = Graded.Heap.Typed.Reduction.⊢Value-⇒ᵥ

-- Theorem 3.8: For well-typed and well-resourced states, reduction
-- terminates only for states with value in head position and an empty
-- stack.

⊢▸Final-reasons = Graded.Heap.Termination.⊢▸Final-reasons-closed

------------------------------------------------------------------------
-- 3.5: Bisimilarity and Termination
--
-- Some properties in this section are stated in the paper for empty
-- contexts whereas the formalized versions hold also for non-empty
-- contexts.

-- Theorem 3.9: Reduction in the abstract machine implies reduction in
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

-- States in normal form
--
-- The definition stated here additionally includes states for which
-- lookup yields a dummy entry to be in normal form. This is not
-- applicable for the theory presented in this section.

Normal = Graded.Heap.Untyped.Normal

-- Theorem 3.10: Bisimilarity between the tracking and non-tracking
-- reductions.

-- Reduction with the tracking semantics implies reduction in the
-- non-tracking semantics.

⇾→⇢ = Graded.Heap.Bisimilarity.⇾→⇢

-- Reduction with the non-tracking semantics implies reduction in the
-- tracking semantics for well-resourced states.

⇢→⇾ = Graded.Heap.Bisimilarity.⇢→⇾

-- Theorem 3.11: Evaluation to normal form

normalize = Graded.Heap.Normalization.normalize
▸normalize = Graded.Heap.Bisimilarity.▸normalize

-- Theorem 3.12: Evaluation for values corresponds to evaluation in the
-- call-by-name reduction.
--
-- This property assumes that the stack multiplicity exists. As
-- discussed above, this is the case for the theory presented in this
-- section.

⊢⇒→⇒ᵥ = Graded.Heap.Bisimilarity.⊢⇒→⇒ᵥ

-- Theorem 3.13: Reduction in the call-by-name semantics implies
-- reduction in the abstract machine.

-- The first part of the theorem, for which evaluation is not
-- necessarily to a term in WHNF:

⊢⇒→⇾* = Graded.Heap.Bisimilarity.⊢⇒→⇾*

-- The second part, for evaluation to a term in WHNF:

⊢⇒→⇾*-whnf = Graded.Heap.Termination.whBisim-closed

-- Corollary 3.14: Termination of the weak-head reduction.

termination = Graded.Heap.Termination.⊢▸-⇘-closed

------------------------------------------------------------------------
-- Resource Correctness

-- Bisimilarity does not hold if stacks are allowed to contain
-- successor continuations.

¬sucₑ-bisim = Graded.Heap.Typed.Reduction.¬sucₑ-⇒ᵥ→⇒

-- Lemma 3.15: Adding successor continuations to the bottom of a stack
-- preserves reduction.

++sucₛ-↠* = Graded.Heap.Reduction.Properties.++sucₛ-↠*

-- Theorem 3.16: Evaluation to numerals

redNumeral = Graded.Heap.Soundness.redNumeral-closed

-- Theorem 3.17: Resource correctness
--
-- The grade associated with each entry in the heap being bounded by 𝟘
-- is expressed using the relation _≤ʰ_ which relates a heap to a grade.
-- H ≤ʰ p is inhabited iff the grade associated with each entry is less
-- than p.

resourceCorrectness = Graded.Heap.Soundness.soundness-closed

_≤ʰ_ = Graded.Heap.Usage._≤ʰ_

-- Resource correctness for open terms.
--
-- The formalized statement also disallows erased matches for
-- eliminators related to identity types.

resourceCorrectnessOpen =
  Graded.Heap.Soundness.soundness-open-consistent

-- Example: Projection function for weak Σ-types

-- The projection function.

proj₁ = Graded.Heap.Examples.fstʷ

-- Two entries are added to the heap during evaluation

proj₁↠₁ = Graded.Heap.Examples.fstʷ⟨0,0⟩↠*′

-- The complete evaluation of the example

proj₁↠₂ = Graded.Heap.Examples.fstʷ⟨0,0⟩↠*

¬▸proj₁ = Graded.Heap.Examples.Linearity.fstʷ-no-usage

------------------------------------------------------------------------
-- 4: Usage Counting for Natural Number Recursion

------------------------------------------------------------------------
-- 4.1: Natrec-star

-- The alternative usage rule has problems related to linearity

alt-usage-bad =
  Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr.▸double

-- The natrec-star operator.
--
-- The usage rule using natrec-star is more general than the one
-- mentioned in the paper and is based on the modality providing a so
-- called nr-function which is assumed to satisfy certain properties.
-- any natrec-star operator is an instance of such an nr-function.

natrec-star = Graded.Modality.Has-star

natrec-star→nr = Graded.Modality.Properties.Star.has-nr

-- The problems we describe hold both for the usage relation with modes
-- and the one without modes. Note that this module is parametrized
-- over a Modality-variant

usage-bad-linearity = Graded.Modality.Instances.Linearity.Bad.▸double

-- Addition for natural numbers

plus = Graded.Modality.Instances.Examples.plus′

-- Natrec-star for the linear types modality

⊛-linearity = Graded.Modality.Instances.Zero-one-many._⊛_▷_

-- This is the greatest lawful natrec-star operator

⊛-linearity-greatest =
  Graded.Modality.Instances.Zero-one-many.⊛-greatest

-- A usage rule for plus

▸plus = Graded.Modality.Instances.Linearity.Bad.▸plus′

-- The usage for adding two variables

▸plus-x₀-x₁ = Graded.Modality.Instances.Linearity.Bad.▸plus′-x₀-x₁

-- The usage for adding a variable to itself

▸plus-x₀-x₀ = Graded.Modality.Instances.Linearity.Bad.▸plus′-x₀-x₀

------------------------------------------------------------------------
-- 4.2: A Resource-Correct Usage Rule

-- Grade sequences
--
-- This defines sequences of any type.

Grade-sequence = Tools.Nat.Sequence

-- Greatest lower bounds of grade sequences

Greatest-lower-bound = Graded.Modality.Modality.Greatest-lower-bound

-- Greatest lower bounds of context sequences

Greatest-lower-boundᶜ = Graded.Context.Greatest-lower-boundᶜ

-- The usage rule for natrec
--
-- The rule in question is natrec-no-nr-glbₘ

▸natrec = Graded.Usage._▸[_]_

-- The function nrᵢ

nrᵢ = Graded.Modality.Modality.nrᵢ

-- The function nrᵢ lifted to contexts

nrᵢᶜ = Graded.Context.Properties.Natrec.nrᵢᶜ

-- Definition 4.1: Modalities with well-behaved greatest lower bounds
--
-- This property is defined for Semiring-with-meet

Well-behaved-GLB = Graded.Modality.Has-well-behaved-GLBs

-- A sub-interchange law for addition and meet

+-sub-interchangeable-∧ =
  Graded.Modality.Properties.Addition.+-sub-interchangeable-∧

-- The example modalities have well-behaved greatest lower bounds
--
-- Note that the proof for the linear types and affine types instances
-- link to the same property since it is proven independently of the
-- choice of partial order.

erasure-well-behaved-GLB =
  Graded.Modality.Instances.Erasure.Properties.Erasure-supports-factoring-nr-rule
affine-well-behaved-GLB =
  Graded.Modality.Instances.Zero-one-many.zero-one-many-supports-glb-for-natrec
linearity-well-behaved-GLB =
  Graded.Modality.Instances.Zero-one-many.zero-one-many-supports-glb-for-natrec
ℕω-well-behaved-GLB =
  Graded.Modality.Instances.Nat-plus-infinity.ℕ⊎∞-supports-glb-for-natrec

-- Subject reduction

subject-reduction = Graded.Reduction.usagePresTerm

-- The characteristic inequalities of greatest lower bounds of nrᵢ

nrᵢ-≤₁ = Graded.Modality.Properties.Natrec.nrᵢ-GLB-≤₀
nrᵢ-≤₂ = Graded.Modality.Properties.Natrec.nrᵢ-GLB-≤

-- The substitution lemma

subst-lemma = Graded.Substitution.Properties.substₘ-lemma

-- Correctness for erasure

erasure-correct =
  Graded.Erasure.Consequences.Soundness.Soundness.soundness-ℕ

-- A usage rule for plus for the linear types modality

▸plus′ =
  Graded.Modality.Instances.Linearity.Good.Greatest-lower-bound.▸plus′

-- The usage rule for plus simplified

▸plus″ =
  Graded.Modality.Instances.Linearity.Good.Greatest-lower-bound.▸plus″

------------------------------------------------------------------------
-- 4.3: Resource Correctness for the Natural Number Eliminator

-- Multiplicity of a continuation

∣_∣ᶜ≡′_ = Graded.Heap.Untyped.∣_∣ᶜ≡_

-- The greatest lower bound does not exist for all nrᵢ sequences for
-- all modalities. This example is the modality of natural numbers
-- (without ω).

¬nrᵢ-GLB = Graded.Modality.Instances.Nat.¬nrᵢ-GLB

-- This instance has a well-behaved zero, supports subtraction and
-- has well-behaved greatest lower bounds.

Nat-well-behaved-zero =
  Graded.Modality.Instances.Nat.Nat-has-well-behaved-zero
Nat-subtraction =
  Graded.Modality.Instances.Nat.supports-subtraction
Nat-well-behaved-GLB =
  Graded.Modality.Instances.Nat.Nat-has-well-behaved-GLBs

-- The stack multiplicity does not necessarily exist

∣∣≢ = Graded.Heap.Untyped.Properties.∣∣≢

-- The stack multiplicity is functional

∣∣-functional′ = Graded.Heap.Untyped.Properties.∣∣-functional

-- The greatest lower bound of grade sequences is unique if it exists

GLB-unique = Graded.Modality.Properties.Greatest-lower-bound.GLB-unique

-- Applying a term to a continuation

⦅_⦆ᶜ′_ = Graded.Heap.Untyped.⦅_⦆ᶜ_

-- The reduction of eliminators and variables is updated

_⇾ₑ′_ = Graded.Heap.Reduction._⇾ₑ_

-- In particular, the auxiliary reduction is updated.

_⇒ₑ′_ = Graded.Heap.Reduction._⇒ₑ_

-- Reduction of values is also updated.

_⇒ᵥ′_ = Graded.Heap.Reduction._⇒ᵥ_

-- The reduction relations are deterministic

⇾-det′ = Graded.Heap.Reduction.Properties.⇾-det
⇢-det′ = Graded.Heap.Reduction.Properties.⇢-det
↠-det′ = Graded.Heap.Reduction.Properties.↠-det

-- The usage for continuations is extended

_▸ᶜ[_]′_ = Graded.Heap.Usage._▸ᶜ[_]_

-- The stack multiplicity always exist for well-resourced states

▸∣∣≡ = Graded.Heap.Usage.Inversion.▸ₛ-inv

-- Well-resourced states do not get stuck due to non-existing stack
-- multiplicity
--
-- In the formalization, this is stated as there being two ways
-- reduction can fail. Of the original three reasons mentioned earlier,
-- the case for states with variables in head position is no longer
-- possible.

▸Final-reasons′ = Graded.Heap.Usage.Reduction.▸Final-reasons-closed

-- The typing relation for continuations is extended

_⊢ᶜ_⟨_⟩∷_↝′_ = Graded.Heap.Typed._⨾_⊢ᶜ_⟨_⟩∷_↝_

------------------------------------------------------------------------
-- 4.4: Usage Counting for the Natural Number Eliminator

-- For the example modalities the greatest lower bound of nrᵢ r p q
-- always exists.
--
-- Note that the proof for the linear types and affine types instances
-- link to the same property since it is proven independently of the
-- choice of partial order.

erasure-GLB-nrᵢ =
  Graded.Modality.Instances.Erasure.Properties.Erasure-nrᵢ-glb
affine-GLB-nrᵢ =
  Graded.Modality.Instances.Zero-one-many.nr-nrᵢ-GLB
linear-GLB-nrᵢ =
  Graded.Modality.Instances.Zero-one-many.nr-nrᵢ-GLB
ℕω-GLB-nrᵢ =
  Graded.Modality.Instances.Nat-plus-infinity.nrᵢ-GLB

-- For modalities with a well-behaved zero, the greatest lower bound
-- of any grade sequence is zero only if the sequence is constantly
-- zero.
--
-- Note that this applies to the linear and affine types modalities.

𝟘-GLB = Graded.Modality.Properties.Greatest-lower-bound.𝟘-GLB-inv

-- For the linear types modality, the greatest lower bound
-- of any grade sequence is one only if the sequence is constantly
-- one.

𝟙-GLB-linear = Graded.Modality.Instances.Linearity.𝟙-GLB-inv

-- For the linear types modality, the greatest lower bound
-- of any grade sequence is one only if the sequence only consists
-- of grades zero and one.

𝟙-GLB-affine = Graded.Modality.Instances.Linearity.𝟙-GLB-inv

-- For both the linear and affine types modalities, 𝟘 is the greatest
-- lower bound of nrᵢ r p q only if p ≡ 𝟘 and q ≡ 𝟘

𝟘-GLB-nrᵢ-linearity = Graded.Modality.Instances.Linearity.nrᵢ-GLB-𝟘-inv
𝟘-GLB-nrᵢ-affine = Graded.Modality.Instances.Affine.nrᵢ-GLB-𝟘-inv

-- For the affine types modality, the greatest lower bound of nrᵢ r p q
-- is one only in some cases.

𝟙-GLB-nrᵢ-linearity = Graded.Modality.Instances.Linearity.nrᵢ-GLB-𝟙-inv

-- For the affine types modality, the greatest lower bound of nrᵢ r p q
-- is one only in some cases.

𝟙-GLB-nrᵢ-affine = Graded.Modality.Instances.Affine.nrᵢ-GLB-𝟙-inv

-- For the linear types modality, the greatest lower bound of nrᵢ r 𝟙 p
-- is 𝟙 only if r ≡ 𝟘 and p ≡ 𝟙 or r ≡ 𝟙 and p ≡ 𝟘.
-- In other words, the natural number argument to natrec is used
-- linearly only in these cases

natrec-linear = Graded.Modality.Instances.Linearity.nrᵢ-r𝟙p-GLB-𝟙-inv

-- The predecessor function

pred = Graded.Modality.Instances.Examples.pred′

-- A usage rule for the predecessor function

▸pred = Graded.Modality.Instances.Linearity.Good.Greatest-lower-bound.▸pred′

-- For the affine types modality, the greatest lower bound of nrᵢ r 𝟙 p
-- is 𝟙 only if r ≡ 𝟘 and p ≡ 𝟙 or r ≡ 𝟙 and p ≡ 𝟘 or r ≡ 𝟘 and p ≡ 𝟘
-- In other words, the natural number argument to natrec is used
-- in an affine way only in these cases

natrec-affine = Graded.Modality.Instances.Affine.nrᵢ-r𝟙p-GLB-𝟙-inv

-- The natural number argument is never considered to be erased. I.e.
-- the greatest lower bound of nrᵢ r 𝟙 p is never 𝟘.

natrec-not-erased =
  Graded.Modality.Properties.Natrec.nrᵢ-natrec-not-erased

-- For both the linear types and the affine types modalities, the
-- greatest lower bound of nrᵢ 𝟘 p q is p ∧ q.
-- In other words, the contribution of the zero and successor branches
-- of natrec p′ q′ 𝟘 A z s n is γ ∧ δ when γ ▸ z and δ,p,r▸s

natrec-usage-𝟘 = Graded.Modality.Instances.Zero-one-many.nrᵢ-𝟘-GLB

-- For both the linear types and the affine types modalities, the
-- greatest lower bound of nrᵢ 𝟙 p q is p + ω · q.
-- In other words, the contribution of the zero and successor branches
-- of natrec p′ q′ 𝟙 A z s n is γ + ω · δ when γ ▸ z and δ,p,r▸s

natrec-usage-𝟙 = Graded.Modality.Instances.Zero-one-many.nrᵢ-𝟙-GLB

-- For both the linear types and the affine types modalities, the
-- greatest lower bound of nrᵢ ω p q is p + ω · q.
-- In other words, the contribution of the zero and successor branches
-- of natrec p q ω A z s n is ω ·(γ + δ) when γ ▸ z and δ,p,r▸s

natrec-usage-ω = Graded.Modality.Instances.Zero-one-many.nrᵢ-ω-GLB

------------------------------------------------------------------------
-- 5: Resource Correctness for Open Programs

-- The definition of heap substitutions is extended

⦅_⦆ʰ′ = Graded.Heap.Untyped.toSubstₕ

-- The definition of initial state is updated

initial′ = Graded.Heap.Untyped.initial

-- Reduction can fail in three different ways

Final-reasons-open = Graded.Heap.Reduction.Properties.Final-reasons

-- Typing judgments:

-- Typing for heaps

⊢ʰ_∷′_ = Graded.Heap.Typed._⊢ʰ_∷_

-- Typing for continuations

_⊢ᶜ_⟨_⟩∷_↝″_ = Graded.Heap.Typed._⨾_⊢ᶜ_⟨_⟩∷_↝_

-- Typing for stacks

_⊢_⟨_⟩∷_↝′_ = Graded.Heap.Typed._⨾_⊢_⟨_⟩∷_↝_

-- Typing for states

⊢ₛ_∷′_ = Graded.Heap.Typed._⊢ₛ_∷_

-- Type preservation for the abstract machine

⊢-⇾′ = Graded.Heap.Typed.Reduction.⊢ₛ-⇾
⊢-⇾*′ = Graded.Heap.Typed.Reduction.⊢ₛ-⇾*

-- Values in non-empty stacks always reduce.

⊢Value-⇒ᵥ′ = Graded.Heap.Typed.Reduction.⊢Value-⇒ᵥ

-- Usage preservation for the abstract machine

▸-⇾′ = Graded.Heap.Usage.Reduction.▸-⇾
▸-⇾*′ = Graded.Heap.Usage.Reduction.▸-⇾*

-- Well-resourced dummy entries are assigned grade 𝟘

▸H● = Graded.Heap.Usage.Properties.▸H●

-- Lookups to dummy entries can only occur if the stack multiplicity is 𝟘

▸s● = Graded.Heap.Usage.Properties.▸s●

-- The stack multiplicity is zero iff it contains erased prodrec,
-- unitrec or emptyrec.
--
-- The second direction, showing that the stack contains erased prodrec,
-- unitrec, or emptyrec if the stack multiplicity is zero does not
-- necessarily hold if the stack contains continuations related to the
-- identity type since these can have multiplicity zero. In the linked
-- property, we have shown that the stack contains erased prodrec,
-- unitrec or emptyrec or a continuation related the identity type (J, K,
-- or []-cong).

∣∣≡𝟘-if-erased-elim′ = Graded.Heap.Untyped.Properties.∣∣≡𝟘
erased-elim-if-∣∣≡𝟘′ = Graded.Heap.Untyped.Properties.∣∣≡𝟘→erased-match

-- The multiplicity of the continuation for natrec is never 𝟘

∣nr∣≢𝟘 = Graded.Heap.Untyped.Properties.∣nr∣≢𝟘

-- Theorem 5.1: Heap lookups succeed for well-resourced heaps

heap-lookup-succeeds′ = Graded.Heap.Soundness.lookup-succeeds′

-- States in normal form

Normal′ = Graded.Heap.Untyped.Normal

-- Theorem 5.2: Resource correctness for open terms.
--
-- The formalized statement also disallows erased matches for
-- eliminators related to identity types.

resourceCorrectnessOpen′ =
  Graded.Heap.Soundness.soundness-open-consistent

-- Counterexamples to the resource correctness theorem when some
-- assumptions are removed.
-- These countrexamples are constructed under the assumption that some
-- function types are allowed (as given by the type restrictions).

-- Inconsistent contexts

¬resource-correctness-inconsistent =
  Graded.Heap.Soundness.Counterexample.¬soundness-inconsistent

-- Erased matches for unitrec

¬resource-correctness-erased-matches-unitrec =
  Graded.Heap.Soundness.Counterexample.¬soundness-erased-matches-unitrec

-- Erased matches for prodrec

¬resource-correctness-erased-matches-prodrec =
  Graded.Heap.Soundness.Counterexample.¬soundness-erased-matches-prodrec

-- Programs using free variables in a non-erased way

¬resource-correctness-non-erased =
  Graded.Heap.Soundness.Counterexample.¬soundness-not-erased

-- A version of resource correctness with no erased matches for
-- emptyrec.

resourceCorrectnessOpen″ =
  Graded.Heap.Soundness.soundness-open-¬emptyrec₀

------------------------------------------------------------------------
-- 7: Related Work

-- For erasure, the context in the contexts in the conclusions of the
-- usage rules for natrec using natrec-star and greatest lower bounds
-- coincide

Erasure-⊛≡GLB = Graded.Modality.Instances.Erasure.Properties.▸⊛≈GLB
