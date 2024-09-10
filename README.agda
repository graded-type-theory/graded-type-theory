--------------------------------------------------------------------------
-- Code related to the paper "A Graded Modal Dependent Type Theory
-- with a Universe and Erasure, Formalized" by Andreas Abel, Nils
-- Anders Danielsson and Oskar Eriksson
--------------------------------------------------------------------------

-- Note that Gaëtan Gilbert, Wojciech Nawrocki, Joakim Öhman and
-- Andrea Vezzosi have also contributed to the code, and some changes
-- to the code were made after feedback from anonymous reviewers.
--
-- The code also depends on some libraries:
--
-- * Agda's standard library, version 2.0.
-- * The builtin modules that are shipped with Agda 2.6.4.3.
--
-- When HTML code is generated from this file code is also generated
-- for the two libraries above, so URLs for their licences are
-- included here. At the time of writing the licence texts can be
-- found at the following URLs:
--
-- * https://github.com/agda/agda-stdlib/blob/v2.0/LICENCE
-- * https://github.com/agda/agda/blob/v2.6.4.3/LICENSE

module README where

import Definition.LogicalRelation
import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility
import Definition.LogicalRelation.Substitution
import Definition.Typed
import Definition.Typed.Consequences.DerivedRules
import Definition.Typed.Consequences.DerivedRules.Sigma
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Consequences.Substitution
import Definition.Typed.Consequences.Syntactic
import Definition.Typed.Decidable
import Definition.Typed.Decidable.Equality
import Definition.Typed.Eta-long-normal-form
import Definition.Typed.Properties
import Definition.Typed.Restrictions
import Definition.Typed.Weakening
import Definition.Untyped
import Definition.Untyped.Sigma

import Graded.Context
import Graded.Context.Properties
import Graded.Derived.Sigma
import Graded.Erasure.Consequences.Non-interference
import Graded.Erasure.Consequences.Soundness
import Graded.Erasure.Examples
import Graded.Erasure.Extraction
import Graded.Erasure.Extraction.Properties
import Graded.Erasure.LogicalRelation
import Graded.Erasure.LogicalRelation.Fundamental
import Graded.Erasure.LogicalRelation.Fundamental.Counterexample
import Graded.Erasure.LogicalRelation.Hidden
import Graded.Erasure.LogicalRelation.Reduction
import Graded.Erasure.SucRed
import Graded.Erasure.Target
import Graded.FullReduction
import Graded.Modality
import Graded.Modality.Dedicated-nr
import Graded.Modality.Instances.Affine
import Graded.Modality.Instances.Affine.Bad
import Graded.Modality.Instances.Affine.Bad.No-dedicated-nr
import Graded.Modality.Instances.Affine.Good
import Graded.Modality.Instances.BoundedStar
import Graded.Modality.Instances.Erasure.Modality
import Graded.Modality.Instances.Erasure.Properties
import Graded.Modality.Instances.Examples
import Graded.Modality.Instances.Information-flow
import Graded.Modality.Instances.Linear-or-affine
import Graded.Modality.Instances.Linear-or-affine.Bad
import Graded.Modality.Instances.Linear-or-affine.Bad.No-dedicated-nr
import Graded.Modality.Instances.Linear-or-affine.Good
import Graded.Modality.Instances.Linearity
import Graded.Modality.Instances.Linearity.Bad
import Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr
import Graded.Modality.Instances.Linearity.Good
import Graded.Modality.Instances.LowerBounded
import Graded.Modality.Instances.Nat-plus-infinity
import Graded.Modality.Instances.Recursive
import Graded.Modality.Instances.Unit
import Graded.Modality.Instances.Zero-one-many
import Graded.Modality.Properties.Addition
import Graded.Modality.Properties.Division
import Graded.Modality.Properties.Multiplication
import Graded.Modality.Properties.Star
import Graded.Modality.Variant
import Graded.Mode
import Graded.Reduction
import Graded.Restrictions
import Graded.Substitution
import Graded.Substitution.Properties
import Graded.Usage
import Graded.Usage.Decidable
import Graded.Usage.Inversion
import Graded.Usage.Properties
import Graded.Usage.Properties.Has-well-behaved-zero
import Graded.Usage.Restrictions
import Graded.Usage.Restrictions.Satisfied

------------------------------------------------------------------------
-- Differences between this version of the code and the code that the
-- paper refers to
------------------------------------------------------------------------

-- This is not the version of the code that the paper refers to. Some
-- things have been added, but things have also changed.

-- Some of the changes:
--
-- * Identity types have been added.
--
-- * Universe levels have been added. Instead of a single universe
--   there is now a countably infinite universe hierarchy.
--
-- * A weak unit type has been added. A variant of Theorem 6.13
--   (soundness of extraction) now holds in the presence of erased
--   matches for weak unit types: the statement of this theorem makes
--   use of a type system with η-equality for weak unit types.
--
-- * The strong unit type can now optionally be used as a "sink"
--
-- * One can now restrict uses of emptyrec, and if emptyrec 𝟘 is
--   disallowed, then Theorem 6.13 holds also for inconsistent
--   contexts.
--
-- * The target language now supports call-by-value, in addition to
--   call-by-name, and the extraction function has been changed in
--   several ways.
--
-- * Equality with the grade 𝟘 is now required to be decidable for all
--   modalities.
--
-- * The logical relations for reducibility and erasure have been
--   changed.

-- Another notable change is related to the natrec-star operators. The
-- paper does not focus on linearity, but some modalities for linear
-- and/or affine types are discussed. It was discovered that using
-- those modalities, and in particular the natrec-star operators of
-- those modalities, one can prove that a certain doubling function,
-- basically λ n. n + n, is linear (or affine). Furthermore one can
-- prove that a certain implementation of addition with a linear type
-- is not well-resourced, even though that would arguably make sense.

double-linear = Graded.Modality.Instances.Examples.⊢double
double-ok₁    = Graded.Modality.Instances.Linearity.Bad.▸double
double-ok₂    = Graded.Modality.Instances.Affine.Bad.▸double
double-ok₃    = Graded.Modality.Instances.Linear-or-affine.Bad.▸double

plus-linear  = Graded.Modality.Instances.Examples.⊢plus
plus-not-ok₁ = Graded.Modality.Instances.Linearity.Bad.¬▸plus
plus-not-ok₂ = Graded.Modality.Instances.Linear-or-affine.Bad.¬▸plus

-- In order to make the theory more flexible the natrec-star operator
-- in the main usage rule for natrec has been replaced by an "nr
-- function" (natrec usage function). Previously the usage rule had
--
--   (γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r
--
-- in the conclusion. Now the conclusion instead contains
--
--   nrᶜ p r γ δ η.

usage-relation = Graded.Usage._▸[_]_

-- The nr functions have to satisfy certain properties, and every
-- valid natrec-star operator gives rise to a valid nr function:
--
--   nr p r z s n = (z ∧ n) ⊛ s + p · n ▷ r

Has-nr          = Graded.Modality.Has-nr
Has-star→Has-nr = Graded.Modality.Properties.Star.has-nr

-- The definition of a modality has been changed to refer to nr
-- functions instead of natrec-star operators.

has-nr = Graded.Modality.Modality.has-nr

-- For the modalities discussed above custom nr functions have been
-- defined (there is one parametrised definition for the linear types
-- and affine types modalities, and one for the linear or affine types
-- modality).

zero-one-many-nr =
  Graded.Modality.Instances.Zero-one-many.zero-one-many-has-nr
linear-or-affine-nr =
  Graded.Modality.Instances.Linear-or-affine.linear-or-affine-has-nr

-- In the case of the linear types modality the custom nr function is
-- neither bounded from below nor from above by the nr function
-- obtained from the "bad" natrec-star operator. In the case of the
-- affine types modality the custom nr function is strictly smaller.

incomparable = Graded.Modality.Instances.Linearity.incomparable
smaller      = Graded.Modality.Instances.Affine.alternative-greater

-- The problems mentioned above do not affect the obtained modalities,
-- but (at the time of writing) there is no solid evidence showing
-- that these modalities are "correct".

double-not-ok₁ = Graded.Modality.Instances.Linearity.Good.¬▸double
double-not-ok₂ = Graded.Modality.Instances.Affine.Good.¬▸double
double-not-ok₃ =
  Graded.Modality.Instances.Linear-or-affine.Good.¬▸double

plus-ok₁ = Graded.Modality.Instances.Linearity.Good.▸plus
plus-ok₂ = Graded.Modality.Instances.Linear-or-affine.Good.▸plus

-- Section 7.1.4 in the paper briefly discusses an alternative usage
-- rule for natrec. This rule has been changed:
--
-- * The inequality χ ≤ γ ∧ η ∧ (δ + pη + rχ) was replaced by three
--   inequalities: χ ≤ γ, χ ≤ η and χ ≤ δ + pη + rχ.
--
-- * The inequality χ ≤ η is now only required to hold for modalities
--   with a well-behaved zero, because that suffices for the proofs in
--   the formalisation.
--
-- * A new inequality, χ ≤ δ, has been added. This inequality is only
--   required to hold if the mode 𝟘ᵐ is allowed. Footnote 10 in the
--   paper states that an extra assumption, p + q ≤ p, is used for the
--   system with two modes: now the inequality χ ≤ δ is used instead.
--
-- The problems discussed above also affect the alternative usage rule
-- for natrec:
--
-- * The linear/affine doubling function is well-resoured (for the
--   linear or affine types modality, and the linear types modality,
--   this is only the case if 𝟘ᵐ is not allowed).
--
-- * The linear addition function is not well-resourced.

double-ok₄ =
  Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr.▸double
double-ok₅ =
  Graded.Modality.Instances.Affine.Bad.No-dedicated-nr.▸double
double-ok₆ =
  Graded.Modality.Instances.Linear-or-affine.Bad.No-dedicated-nr.▸double

plus-not-ok₃ =
  Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr.¬▸plus
plus-not-ok₄ =
  Graded.Modality.Instances.Linear-or-affine.Bad.No-dedicated-nr.¬▸plus

-- Thus this rule should perhaps not be used for linear or affine
-- types.
--
-- For the linear or affine types modality, and the linear types
-- modality, one could ensure that the doubling function is never
-- well-resourced (irrespective of whether 𝟘ᵐ is allowed) by requiring
-- that the new inequality χ ≤ δ holds for modalities with
-- well-behaved zeros. However, the linear addition function would
-- still not be well-resourced, and the doubling function would still
-- be well-resourced for the affine types modality.

------------------------------------------------------------------------
-- Differences between the paper and the code
------------------------------------------------------------------------

-- The code does not follow the paper exactly. Notably, the
-- formalisation contains parameters that make it possible to control
-- whether certain features should be included or not (in addition to
-- the possibility to choose what modality to use):

-- * One can have a theory with a single mode, or two modes, and there
--   can be a (dedicated) nr function, or the alternative usage rule
--   for natrec from Section 7.1.4 can be used.
--
--   Two mutually exclusive types, Dedicated-nr and No-dedicated-nr,
--   are used to control which usage rules are available for natrec.
--   If Dedicated-nr is inhabited, then the rule with the nr function
--   is used, and if No-dedicated-nr is inhabited, then the other rule
--   is used.

Modality-variant  = Graded.Modality.Variant.Modality-variant
Dedicated-star    = Graded.Modality.Dedicated-nr.Dedicated-nr
No-dedicated-star = Graded.Modality.Dedicated-nr.No-dedicated-nr

-- * One can choose whether to allow the strong unit type. Furthermore
--   one can choose whether to allow binders of the form B_p^q, where
--   p and q are grades and B is "Π", "strong Σ" or "weak Σ":

types = Definition.Typed.Restrictions.Type-restrictions

--   This parameter does not affect the syntax, but if a term has a
--   certain type ("Unit" or "B_p^q C D"), then this type must be
--   allowed:

Unit-allowed =
  Definition.Typed.Consequences.Inversion.⊢∷Unit→Unit-allowed
ΠΣ-allowed =
  Definition.Typed.Consequences.Inversion.⊢∷ΠΣ→ΠΣ-allowed

-- * One can choose whether to allow the term prodrec_r,p^q (and one
--   can choose to only allow this term for the mode 𝟘ᵐ):

prodrec = Graded.Usage.Restrictions.Usage-restrictions

--   This only affects the usage relation. If prodrec_r,p^q A t u is
--   well-resourced (with respect to a given mode), then the term is
--   allowed (for that mode):

prodrec-allowed = Graded.Usage.Inversion.inv-usage-prodrec

--   One can use this parameter to rule out erased matches for weak
--   Σ-types:

no-erased-matches = Graded.Restrictions.no-erased-matches-UR

-- Note that some results have only been proved for certain variants
-- of the theory.

-- Some modules are parameterized by a collection of equality
-- relations and properties of those relations. The reducibility
-- logical relation and its fundamental lemmas are defined/proved for
-- any such collection, and can be instantiated for either the normal
-- type and term equality, or algorithmic equality relations.

-- There are also other differences between the paper and the
-- formalisation. Quite a few such differences are noted below.

------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

-- The remainder of this file contains pointers to results from the
-- paper.

------------------------------------------------------------------------
-- 2: Relation to the State of the Art

------------------------------------------------------------------------
-- 2.2: Usage Accounting Also in Types

-- A relation which can be used to force the two grade annotations on
-- Π- and Σ-types to be equal.

ΠΣ-allowed′ = Definition.Typed.Restrictions.Type-restrictions.ΠΣ-allowed

------------------------------------------------------------------------
-- 3: Modalities as Ordered Semirings

-- Definition 3.1: Modalities.
--
-- As discussed above the natrec-star operators from the paper have
-- been replaced by nr functions.
--
-- Modality records contain a field of type Modality-variant. For the
-- variant of the type theory in Sections 3-5 the mode 𝟘ᵐ should be
-- disallowed, i.e. the Modality-variant field 𝟘ᵐ-allowed should be
-- false. Furthermore there should be a dedicated nr function, i.e.
-- the Modality-variant field nr-available should be true (and to
-- match the paper the nr function should correspond to a natrec-star
-- operator).
--
-- Unlike in the paper equality is not required to be decidable (only
-- equality with the grade 𝟘). Instead this property is assumed where
-- it is used.

Modality = Graded.Modality.Modality

-- Addition, multiplication and natrec-star are monotone operations.

+-monotone = Graded.Modality.Properties.Addition.+-monotone
·-monotone = Graded.Modality.Properties.Multiplication.·-monotone
⊛-monotone = Graded.Modality.Properties.Star.⊛-monotone

-- Usage contexts.
--
-- The usage contexts are defined as (length-indexed) lists, not as
-- functions from variables.

Conₘ = Graded.Context.Conₘ

-- Lifted operators and a lifted ordering relation for usage contexts.

_+_   = Graded.Context._+ᶜ_
_·_   = Graded.Context._·ᶜ_
_∧_   = Graded.Context._∧ᶜ_
_⊛_▷_ = Graded.Context._⊛ᶜ_▷_
_≤_   = Graded.Context._≤ᶜ_

-- Usage contexts of a given size form a left semimodule.

left-semimodule = Graded.Context.Properties.Conₘ-semimodule

-- The trivial (one element) modality.

unitModality = Graded.Modality.Instances.Unit.UnitModality

-- With the given definitions of _∧_, _+_ and _·_ there is only one
-- lawful way to define the star operator (up to pointwise equality)
-- for the erasure modality.

⊛-unique = Graded.Modality.Instances.Erasure.Properties.⊛-unique

-- The erasure modality.
--
-- The definition takes an argument of type Modality-variant. For each
-- modality variant an erasure modality can be defined.

erasureModality =
  Graded.Modality.Instances.Erasure.Modality.ErasureModality

-- An "affine types" modality, along with the variant with a custom nr
-- function.

affineModality  = Graded.Modality.Instances.Affine.bad-affine-modality
affineModality′ = Graded.Modality.Instances.Affine.affineModality

-- A "linear types" modality, along with the variant with a custom nr
-- function.
--
-- The module has a parameter of type Modality-variant which is
-- required to satisfy a certain property. If this property holds,
-- then a "linear types" modality of the given kind can be defined.

linearityModality =
  Graded.Modality.Instances.Linearity.bad-linearity-modality
linearityModality′ =
  Graded.Modality.Instances.Linearity.linearityModality

-- The natrec-star operators of the "affine types" and "linear types"
-- modalities return results that are as large as possible (given the
-- definitions of the zero, the one, addition, multiplication and
-- meet).

⊛-greatest₁ = Graded.Modality.Instances.Zero-one-many.⊛-greatest

-- A "linear or affine types" modality, along with the variant with a
-- custom nr function.
--
-- The definition takes an argument of type Modality-variant which is
-- required to satisfy a certain property. If this property holds,
-- then a "linear or affine types" modality of the given kind can be
-- defined.
--
-- Note that the names of two of the grades differ from those used in
-- the paper. The formalization uses ≤ω for unrestricted usage and ≤𝟙
-- for affine usage.

linearOrAffineModality =
  Graded.Modality.Instances.Linear-or-affine.bad-linear-or-affine
linearOrAffineModality′ =
  Graded.Modality.Instances.Linear-or-affine.linear-or-affine

-- The natrec-star operator of the "linear or affine types" modality
-- returns results that are as large as possible (given the
-- definitions of the zero, the one, addition, multiplication and
-- meet).

⊛-greatest₂ = Graded.Modality.Instances.Linear-or-affine.⊛-greatest

------------------------------------------------------------------------
-- 4: Type Theory with Grades

-- The grammar of the language.
--
-- The syntax is not defined in the same way as in the paper:
--
-- * The syntax is well-scoped: the type of terms is indexed by the
--   number of variables in the context.
--
-- * Terms are either variables or applications of "kinds" to terms.
--
-- * The type Kind is indexed by a list of natural numbers. The length
--   of the list specifies the number of term arguments of the "kind",
--   and each natural number specifies how many extra variables each
--   term argument takes.
--
-- For instance, instead of three plain constructors for Π, Σ_& and
-- Σ_⊗ there is a kind constructor Binderkind of type
--
--   (b : BinderMode) (p q : M) → Kind (0 ∷ 1 ∷ []).
--
-- The type BinderMode represents "Π, Σ_& or Σ_⊗", and the two
-- arguments of type M are the two quantities of the binders. (The
-- syntax always allows the graded Σ-types from Section 8.) The list
-- 0 ∷ 1 ∷ [] means that the binders take two arguments, one with n
-- variables in the context (for some n), and one with 1 + n variables
-- in the context.
--
-- Pattern synonyms are used so that one can write code which is
-- closer to the notation from the paper.
--
-- The formalization includes a strong unit type which is discussed
-- mainly in Section 7.3. As discussed above use of this unit type can
-- be disallowed.

grammar = Definition.Untyped.Term

-- Weakenings.
--
-- Unlike in the paper the type of weakenings is well-scoped: it is
-- indexed by two natural numbers, the sizes of the target and source
-- contexts, respectively.
--
-- The lifting constructor ⇑ is called lift, and the shifting
-- constructor ↑ is called step.

Wk = Definition.Untyped.Wk

-- Application of a weakening to a de Bruijn index.

weakening-of-variable = Definition.Untyped.wkVar

-- Application of a weakening to a term.

weakening = Definition.Untyped.wk

-- Substitutions.
--
-- Unlike in the paper the type of substitutions is well-scoped: it is
-- indexed by two natural numbers, the sizes of the target and source
-- contexts, respectively.

Subst = Definition.Untyped.Subst

-- Application of a substitution to a term.

_[_] = Definition.Untyped._[_]

-- Some other substitution operations from the paper.

identity  = Definition.Untyped.idSubst
shifting  = Definition.Untyped.wk1Subst
lifting   = Definition.Untyped.liftSubst
extension = Definition.Untyped.consSubst
head      = Definition.Untyped.head
tail      = Definition.Untyped.tail

-- The typing relations.
--
-- These relations are parametrised by a value of type
-- Type-restrictions, which can be used to restrict certain types, as
-- discussed above.
--
-- Note also that some rules for Π and Σ have been merged.
--
-- In some rules fording (equality hypotheses) is used to equate
-- grades. In the paper such equated grades are simply shown as a
-- single grade.

⊢_      = Definition.Typed.⊢_
_⊢_     = Definition.Typed._⊢_
_⊢_∷_   = Definition.Typed._⊢_∷_
_⊢_≡_   = Definition.Typed._⊢_≡_
_⊢_≡_∷_ = Definition.Typed._⊢_≡_∷_
_∷_∈_   = Definition.Typed._∷_∈_

-- Typing contexts.

Con = Definition.Untyped.Con

-- A weakening lemma.

wkEq = Definition.Typed.Weakening.wkEq

-- A derived congruence rule for Π- and Σ-types with fewer
-- assumptions.

ΠΣ-cong′ = Definition.Typed.Consequences.DerivedRules.ΠΣ-cong′

-- One can define something like prodrec for the strong Σ-types.

prodrec-for-Σₚ              = Definition.Untyped.Sigma.prodrecˢ
prodrec-for-Σₚ-type-correct =
  Definition.Typed.Consequences.DerivedRules.Sigma.prodrecˢⱼ

-- However, our definition does not in general satisfy the usage rule
-- for prodrec.

prodrec-for-Σₚ-usage = Graded.Derived.Sigma.¬prodrecₘ

-- One can also define projections for weak Σ-types by using prodrec.

fst-for-Σᵣ = Definition.Untyped.Sigma.Fstʷ-sndʷ.fstʷ
snd-for-Σᵣ = Definition.Untyped.Sigma.Fstʷ-sndʷ.sndʷ

-- However, η-equality does not hold in general for our definitions.

no-η-equality-Σᵣ =
  Definition.Typed.Consequences.DerivedRules.Sigma.¬-Σʷ-η-prodʷ-fstʷ-sndʷ

-- Reduction relations

_⊢_⇒_    = Definition.Typed._⊢_⇒_
_⊢_⇒_∷_  = Definition.Typed._⊢_⇒_∷_
_⊢_⇒*_   = Definition.Typed._⊢_⇒*_
_⊢_⇒*_∷_ = Definition.Typed._⊢_⇒*_∷_

-- Theorem 4.3.

Theorem-4-3a = Definition.Typed.Properties.whnfRed*Term
Theorem-4-3b = Definition.Typed.Properties.whnfRed*

-- Theorem 4.4.

Theorem-4-4a = Definition.Typed.Properties.whrDet*Term
Theorem-4-4b = Definition.Typed.Properties.whrDet*

-- Some properties that are proved via a reducibility logical
-- relation:

-- * Admissibility of substitution.

substitutionAdmissible =
  Definition.Typed.Consequences.Substitution.substitution
substitutionAdmissibleEq =
  Definition.Typed.Consequences.Substitution.substitutionEq
substitutionAdmissibleTerm =
  Definition.Typed.Consequences.Substitution.substitutionTerm
substitutionAdmissibleEqTerm =
  Definition.Typed.Consequences.Substitution.substitutionEqTerm

-- * Subject reduction.

subjectReduction =
  Definition.Typed.Consequences.Syntactic.syntacticRed
subjectReductionTerm =
  Definition.Typed.Consequences.Syntactic.syntacticRedTerm

-- * Normalization.

normalization     = Definition.Typed.Consequences.Reduction.whNorm
normalizationTerm = Definition.Typed.Consequences.Reduction.whNormTerm

-- * Decidability of equality.

decEq     = Definition.Typed.Decidable.Equality.decEq
decEqTerm = Definition.Typed.Decidable.Equality.decEqTerm

-- * Decidability of type-checking for some terms and types.

decTypeCheck      = Definition.Typed.Decidable.decConTermTypeᶜ
decTypeCheck′     = Definition.Typed.Decidable.decTermᶜ
decTypeCheckType  = Definition.Typed.Decidable.decConTypeᶜ
decTypeCheckType′ = Definition.Typed.Decidable.dec

------------------------------------------------------------------------
-- 5: Assigning Grades

-- Definition 5.1: The usage relation.
--
-- The usage relation is indexed by a mode, and one can choose to have
-- only one mode (𝟙ᵐ). In this case the mode 𝟘ᵐ? is equal to 𝟙ᵐ,
-- m ᵐ· p is equal to 𝟙ᵐ, and ⌜ m ⌝ is equal to the modality's one.
--
-- The usage rule for prodrec in the paper contains the side condition
-- "Prodrec r". This condition has been replaced by
-- "Prodrec-allowed m r p q".
--
-- There are two alternative usage rules for natrec. One is the one
-- from Section 5, but with an nr function instead of a natrec-star
-- operator. This one is used if there is a dedicated nr function. If
-- there is no such function, then the rule from Section 7.1.4 is
-- used.

_▸_ = Graded.Usage._▸[_]_

-- A safe head function for lists

safe-head = Graded.Erasure.Examples.head

-- A decision procedure for usage.
--
-- The decision procedure for usage takes an argument of type
-- Dedicated-star: this procedure is not available if the alternative
-- usage rule for natrec from Section 7.1.4 is used.

decision-procedure-for-usage = Graded.Usage.Decidable.▸[_]?_

-- Substitution matrices.

subst-matrix = Graded.Substitution.Substₘ

-- Multiplication of usage contexts and substitution matrices.

_<*_ = Graded.Substitution._<*_

-- Definition 5.2.
--
-- This predicate has been generalised to account for modes.

_▶_ = Graded.Substitution._▶[_]_

-- Theorem 5.3: A substitution lemma for usage.

Theorem-5-3 = Graded.Substitution.Properties.substₘ-lemma₁

-- The previous theorem is restricted to a setting with only one mode.
-- There is also a more general substitution lemma.

main-substitution-lemma = Graded.Substitution.Properties.substₘ-lemma

-- Theorem 5.4: Subject reduction for the usage relation.

Theorem-5-4 = Graded.Reduction.usagePresTerm

------------------------------------------------------------------------
-- 6: Erasure Case Study

-- Definition 6.1: Well-behaved zeros.

Has-well-behaved-zero = Graded.Modality.Has-well-behaved-zero

-- Four modality instances from the paper have well-behaved zeros.

erasure-has-well-behaved-zero =
  Graded.Modality.Instances.Erasure.Modality.erasure-has-well-behaved-zero
linearity-has-well-behaved-zero =
  Graded.Modality.Instances.Linearity.linearity-has-well-behaved-zero
affine-has-well-behaved-zero =
  Graded.Modality.Instances.Affine.affine-has-well-behaved-zero
linear-or-affine-has-well-behaved-zero =
  Graded.Modality.Instances.Linear-or-affine.linear-or-affine-has-well-behaved-zero

-- Theorem 6.2.

Theorem-6-2 =
  Graded.Usage.Properties.Has-well-behaved-zero.valid-var-usage

-- An example: The polymorphic identity function.

id = Graded.Erasure.Examples.id

-- The identity function is well-typed.

⊢id = Graded.Erasure.Examples.⊢id

-- The identity function is well-resourced.

▸id = Graded.Erasure.Examples.▸id

-- The identity function applied to two free variables.

id-x1-x0 = Graded.Erasure.Examples.id-x1-x0

-- The term id-x1-x0 is well-typed.

⊢id-x1-x0 = Graded.Erasure.Examples.⊢id-x1-x0

-- The term id-x1-x0 is well-resourced.

▸id-x1-x0 = Graded.Erasure.Examples.▸id-x1-x0

-- The grammar of the untyped target language.
--
-- The syntax is well-scoped.

target = Graded.Erasure.Target.Term

-- The reduction relation of the target language.

_⇒_  = Graded.Erasure.Target._⇒_
_⇒*_ = Graded.Erasure.Target._⇒*_

-- Definition 6.3: The extraction function.
--
-- The definition is actually the one given in Section 8.

_• = Graded.Erasure.Extraction.erase

-- An example: The identity function applied to ℕ and zero.

id-ℕ-zero = Graded.Erasure.Examples.id-ℕ-zero

-- The term id-ℕ-zero is well-typed.

⊢id-ℕ-zero = Graded.Erasure.Examples.⊢id-ℕ-zero

-- The term id-ℕ-zero is well-resourced.

▸id-ℕ-zero = Graded.Erasure.Examples.▸id-ℕ-zero

-- One of the arguments gets erased by the extraction function.
--
-- The current version of the code includes one extraction function
-- that uses strict applications, and one that uses non-strict
-- applications. In the strict case the extraction of id-ℕ-zero
-- includes ↯, and in the non-strict case that argument is removed
-- entirely, along with one lambda.

erase-strict-id-ℕ-zero =
  Graded.Erasure.Examples.erase-strict-id-ℕ-zero
erase-non-strict-id-ℕ-zero =
  Graded.Erasure.Examples.erase-non-strict-id-ℕ-zero

-- Theorem 6.4.

Theorem-6-4 = Graded.Erasure.Extraction.Properties.hasX.erased-hasX

-- The term id-ℕ-zero reduces to zero.

id-ℕ-zero⇒*zero = Graded.Erasure.Examples.id-ℕ-zero⇒*zero

-- The erasure of id-ℕ-zero reduces to zero.

erase-id-ℕ-zero⇒*zero = Graded.Erasure.Examples.erase-id-ℕ-zero⇒*zero

-- The reducibility logical relation for types.
--
-- In the paper the type level is written as a subscript instead of
-- within brackets.

_⊩′⟨_⟩_ = Definition.LogicalRelation._⊩⟨_⟩_

-- The reducibility logical relation for terms.
--
-- In the paper the type level is written as a subscript instead of
-- within brackets.

_⊩′⟨_⟩_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_∷_/_

-- Some fundamental lemmas for the reducibility relation.

fundamentalReducibleType =
  Definition.LogicalRelation.Fundamental.Reducibility.reducible-⊩
fundamentalReducibleTerm =
  Definition.LogicalRelation.Fundamental.Reducibility.reducible-⊩∷

-- Definition 6.5: The logical relation for erasure.
--
-- In the paper the type level is written as a subscript instead of
-- within brackets.
--
-- For the Π and Σ cases some weakenings are applied to the types of
-- the domain and codomain (or first and second component). The reason
-- for this is that the reducibility relation inductively gives a
-- proof that these types are reducible under any weakenings. We do
-- not need to make use of this extra information, so we apply
-- identity weakenings.
--
-- For Σ-types the presentation is different from that in the paper to
-- account for the possibility to erase the first component, which is
-- added in Section 8. For the language treated in Section 6 one can
-- restrict attention to Σ-types of the form Σ_k,1^q A B.
--
-- In the paper we fix a well-formed, consistent context Δ₀. In the
-- formalization this is partly implemented through module parameters.

_®⟨_⟩_∷_/_ = Graded.Erasure.LogicalRelation._®⟨_⟩_∷_/_

-- The logical relation for natural numbers.
--
-- In the paper this is written with ℕ as a subscript.

_®ℕ_ = Graded.Erasure.LogicalRelation._®_∷ℕ

-- Valid substitutions.
--
-- The current definition does not take the same arguments as the
-- definition in the paper: the context well-formedness and validity
-- proofs have been omitted.

_⊩′ˢ_∷_ = Definition.LogicalRelation.Substitution._⊩ˢ_∷_

-- Valid contexts.

⊩′ᵛ_ = Definition.LogicalRelation.Substitution.⊩ᵛ_

-- Valid types.
--
-- The current definition does not take the same arguments as the
-- definition in the paper: the context validity proof has been
-- omitted.

_⊩′ᵛ⟨_⟩_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_

-- Definition 6.6: The logical relation for substitutions.
--
-- The current definition does not take the same arguments as the
-- definition in the paper: an unused type level has been omitted, as
-- well as the context and substitution validity proofs, but a mode
-- has been added.

_®_∷[_]_◂_ = Graded.Erasure.LogicalRelation.Hidden._®_∷[_]_◂_

-- Definition 6.7: Erasure validity.
--
-- In the paper the type level is written as a subscript instead of
-- within brackets.
--
-- The current definition does not take the same arguments as the
-- definition in the paper: the context and type validity proofs have
-- been omitted, but a mode has been added.

_▸_⊩ʳ⟨_⟩_∷[_]_ = Graded.Erasure.LogicalRelation.Hidden._▸_⊩ʳ⟨_⟩_∷[_]_

-- Theorem 6.8: Backwards closure of the logical relation under
-- reduction.

Theorem-6-8 = Graded.Erasure.LogicalRelation.Reduction.redSubstTerm*

-- Theorem 6.9: Subsumption for the logical relation.

Theorem-6-9a =
  Graded.Erasure.LogicalRelation.Hidden.subsumption-®∷[]◂
Theorem-6-9b =
  Graded.Erasure.LogicalRelation.Hidden.subsumption-▸⊩ʳ∷[]

-- Theorem 6.10: The fundamental lemma.

fundamental =
  Graded.Erasure.LogicalRelation.Fundamental.Fundamental.fundamental

-- Theorem 6.11: Every valid source substitution from an erasable
-- context is related to every matching target substitution.

Theorem-6-11 = Graded.Erasure.LogicalRelation.Hidden.®∷[]◂𝟘ᶜ

-- Theorem 6.12: The fundamental lemma for open terms in erased
-- contexts.

Theorem-6-12 =
  Graded.Erasure.LogicalRelation.Fundamental.Fundamental.fundamentalErased

-- Extended reduction relations.
--
-- Note that the extended relation for the target language is used in
-- the statement of soundness of extraction when terms are extracted
-- to terms with non-strict applications, but not when terms are
-- extracted to terms with strict applications.

_⊢_⇒ˢ_∷ℕ  = Graded.Erasure.SucRed._⊢_⇒ˢ_∷ℕ
_⊢_⇒ˢ*_∷ℕ = Graded.Erasure.SucRed._⊢_⇒ˢ*_∷ℕ
_⇒ˢ_      = Graded.Erasure.SucRed._⇒ˢ_
_⇒ˢ*_     = Graded.Erasure.SucRed._⇒ˢ*_

-- Theorem 6.13: Soundness of the extraction function.
--
-- The assumption that erased matches are not allowed for weak Σ-types
-- (unless the context is empty) is expressed in a different way:
-- erased matches are actually allowed if 1 = 0. However, another
-- assumption is that the modality has a well-behaved zero, which
-- implies that 1 ≠ 0.
--
-- If emptyrec 𝟘 is disallowed when the mode is 𝟙ᵐ, then the context
-- does not need to be consistent.

soundness = Graded.Erasure.Consequences.Soundness.Soundness.soundness-ℕ

------------------------------------------------------------------------
-- 7: Discussion

------------------------------------------------------------------------
-- 7.1: Natrec-Star

-- A lawful definition of natrec-star for lower-bounded structures.

⊛ᵣ-lower-bounded = Graded.Modality.Instances.LowerBounded._⊛_▷_

-- This definition does not give the greatest solution for the affine
-- or linear types modalities (which are defined as different
-- instances of the modality zero-one-many-greatest in
-- Graded.Modality.Instances.Zero-one-many).

not-greatest =
  Graded.Modality.Instances.Zero-one-many.¬-lower-bounded-greatest

-- A lawful definition of natrec-star defined recursively.

⊛ᵣ-recursive = Graded.Modality.Instances.Recursive._⊛_▷_

-- The family of sequences discussed in Section 7.1.2 does not have
-- the required fixpoints for a certain modality for the natural
-- numbers extended with infinity.

¬-fixpoints =
  Graded.Modality.Instances.Nat-plus-infinity.¬-Has-fixpoints-nr

-- A lawful definition of natrec-star for bounded star-semirings.

⊛ᵣ-star-semiring = Graded.Modality.Instances.BoundedStar._⊛_▷_

-- The definition of natrec-star for bounded star-semirings is greater
-- than or equal to the one presented for lower-bounded instances.

⊛ᵣ-lower-bounded≤⊛ᵣ-star-semiring =
  Graded.Modality.Instances.BoundedStar.LowerBounded.⊛′≤⊛

-- The usage rule for natrec without the natrec-star operator/nr
-- function is called natrec-no-nrₘ, and is part of the definition of
-- _▸[_]_.

▸-with-alternative-usage-rule-for-natrec = Graded.Usage._▸[_]_

------------------------------------------------------------------------
-- 7.2: Erased Matches

-- Theorem 7.1.
--
-- Instead of the assumption "erased matches are not allowed for weak
-- Σ-types" the theorem uses the assumption "either (the modality is
-- non-trivial implies that erased matches are not allowed for weak
-- Σ-types, weak unit types, and identity types) or the context is
-- empty". However, note that another assumption is that the modality
-- has a well-behaved zero, which implies that 1 ≠ 0.

Theorem-7-1 =
  Graded.Erasure.Consequences.Soundness.Soundness.soundness-ℕ-only-source

-- If (certain kinds of) erased matches are allowed for weak Σ-types,
-- and additionally some Σ-types are allowed, then there is a
-- counterexample to Theorem 7.1 without the assumption "erased
-- matches are not allowed unless the context is empty".

counterexample₁ =
  Graded.Erasure.Consequences.Soundness.soundness-ℕ-only-source-counterexample₁

-- The above counterexample is not a counterexample to canonicity for
-- the target language.

not-counterexample =
  Graded.Erasure.Consequences.Soundness.soundness-ℕ-only-target-not-counterexample₁

-- If (certain kinds of) erased matches are allowed for weak Σ-types,
-- and additionally some Σ-types are allowed, then one cannot prove a
-- variant of the fundamental lemma (Theorem 6.12) without the
-- assumption "erased matches are not allowed or the context is empty"
-- (assuming that Agda is consistent).

counterexample₂ =
  Graded.Erasure.LogicalRelation.Fundamental.Counterexample.negation-of-fundamental-lemma-with-erased-matches₁

------------------------------------------------------------------------
-- 7.3: Unit Type

-- A type- and resource-preserving procedure that takes a well-typed,
-- well-resourced term to one of its η-long normal forms.
--
-- The procedure makes certain assumptions about types with
-- η-equality.

η-long-normal-forms = Graded.FullReduction.fullRedTerm

------------------------------------------------------------------------
-- 7.4: Information Flow Interpretation

-- A non-interference result.

non-interference =
  Graded.Erasure.Consequences.Non-interference.non-interference

-- If division by q is supported, then p / q is the least r such that
-- p ≤ q · r, and _/ q is monotone.

/-least    = Graded.Modality.Properties.Division./-least-≤·
/-monotone = Graded.Modality.Properties.Division./-monotoneˡ′

-- The total order L ≤ M ≤ H.

L≤M≤H = Graded.Modality.Instances.Information-flow.L≤M≤H

-- Division laws.

/𝟙≡  = Graded.Modality.Properties.Division./𝟙≡′
/𝟘≡𝟙 = Graded.Modality.Properties.Division./𝟘≡𝟙′
/≡𝟙  = Graded.Modality.Properties.Division./≡𝟙′
𝟙/≡𝟙 = Graded.Modality.Properties.Division.𝟙/≡𝟙′
𝟘/≡𝟘 = Graded.Modality.Properties.Division.𝟘/≡𝟘′

------------------------------------------------------------------------
-- 8: Extension: Modes and Graded Σ-types

-- Modes.
--
-- The mode 1_M is denoted by 𝟙ᵐ. One can choose whether to allow or
-- disallow 0_M. If 0_M is allowed, then it is represented by
-- applications of the constructor 𝟘ᵐ: this constructor takes an
-- argument which indicates that 0_M is allowed.
--
-- Note that for the definitions and theorems in Section 8 a modality
-- for which 0_M is allowed should be used.

Mode = Graded.Mode.Mode

-- Translating modes to grades.
--
-- In the paper this function is denoted by an overline.

⌜_⌝ = Graded.Mode.⌜_⌝

-- Translating grades to modes.
--
-- In the paper this function is denoted by an underline.

⌞_⌟ = Graded.Mode.⌞_⌟

-- Scaling modes by grades.

_⊙_ = Graded.Mode._ᵐ·_

-- The syntax, the type system, and the reduction relations.

grammar′  = Definition.Untyped.Term
⊢′_       = Definition.Typed.⊢_
_⊢′_      = Definition.Typed._⊢_
_⊢′_∷_    = Definition.Typed._⊢_∷_
_⊢′_≡_    = Definition.Typed._⊢_≡_
_⊢′_≡_∷_  = Definition.Typed._⊢_≡_∷_
_∷_∈′_    = Definition.Typed._∷_∈_
_⊢′_⇒_    = Definition.Typed._⊢_⇒_
_⊢′_⇒_∷_  = Definition.Typed._⊢_⇒_∷_
_⊢′_⇒*_   = Definition.Typed._⊢_⇒*_
_⊢′_⇒*_∷_ = Definition.Typed._⊢_⇒*_∷_

-- Definition 8.1: The usage relation with modes.
--
-- In the paper the mode is written as a superscript instead of within
-- brackets.

_▸[_]_ = Graded.Usage._▸[_]_

-- A term t is well-resourced with respect to the zero usage context
-- and the zero mode exactly when all subterms of the form
-- prodrec_r,p^q A u v in t are allowed (and some other conditions,
-- related to term formers added after the paper was written, hold).

𝟘ᶜ▸[𝟘ᵐ]⇔ = Graded.Usage.Restrictions.Satisfied.𝟘ᶜ▸[𝟘ᵐ]⇔

-- Theorem 8.2: Subject reduction for the usage relation with modes.

Theorem-8-2 = Graded.Reduction.usagePresTerm

-- The extraction function.

_•′ = Graded.Erasure.Extraction.erase

-- Theorem 8.3: Soundness of the extraction function.
--
-- The assumption that erased matches are not allowed for weak Σ-types
-- (unless the context is empty) is expressed in a different way:
-- erased matches are actually allowed if 1 = 0. However, another
-- assumption is that the modality has a well-behaved zero, which
-- implies that 1 ≠ 0.

Theorem-8-3 =
  Graded.Erasure.Consequences.Soundness.Soundness.soundness-ℕ

-- A definition of η-long normal forms.

_⊢nf_∷_ = Definition.Typed.Eta-long-normal-form._⊢nf_∷_

-- If "Π 𝟙 , r" and "Σₚ p , q" are allowed, then the identity function
-- lam 𝟙 (var x0) has type
-- Π 𝟙 , r ▷ Σₚ p , q ▷ ℕ ▹ ℕ ▹ Σₚ p , q ▷ ℕ ▹ ℕ, is well-resourced in
-- the empty context, and is definitionally equal to the η-long normal
-- form lam 𝟙 (prodₚ p (fst p (var x0)) (snd p (var x0))). However,
-- this η-long normal form is well-resourced in the empty context if
-- and only if either p is 𝟙, or p is 𝟘, 𝟘ᵐ is allowed, and 𝟙 ≤ 𝟘.

η-long-nf-for-id⇔≡𝟙⊎≡𝟘 = Graded.Reduction.η-long-nf-for-id⇔≡𝟙⊎≡𝟘

-- A type- and resource-preserving procedure that takes a well-typed,
-- well-resourced term to one of its η-long normal forms.
--
-- The procedure makes certain assumptions about types with
-- η-equality.

η-long-normal-forms′ = Graded.FullReduction.fullRedTerm

-- The conditions for existence of η-long normal forms are satisfied
-- for the unit modality (which is defined under the assumption that
-- 0_M is not allowed).

unit = Graded.Modality.Instances.Unit.full-reduction-assumptions

-- The conditions are satisfied for the erasure modality if "Σ_&,0^q
-- is allowed" implies that 0_M is allowed.

erasure =
  Graded.Modality.Instances.Erasure.Properties.full-reduction-assumptions

-- The conditions are satisfied for the affine types modality if
-- "Σ_&,0^q is allowed" implies that 0_M is allowed, and Σ_&,ω^q is
-- not allowed.

affine = Graded.Modality.Instances.Affine.full-reduction-assumptions

-- The conditions are satisfied for the linear types modality if the
-- strong unit type is not allowed (or can be used as a sink), the
-- weak unit type does not come with η-equality, Σ_&,0^q is not
-- allowed, and Σ_&,ω^q is not allowed.

linear = Graded.Modality.Instances.Linearity.full-reduction-assumptions

-- The conditions are satisfied for the linear or affine types
-- modality if the strong unit type is not allowed (or can be used as
-- a sink), the weak unit type does not come with η-equality, Σ_&,0^q
-- is not allowed, Σ_&,01^q is not allowed, and Σ_&,ω^q is not
-- allowed.

linear-or-affine =
  Graded.Modality.Instances.Linear-or-affine.full-reduction-assumptions

------------------------------------------------------------------------
-- A: A Logical Relation for Reducibility

-- Combined reduction and typing relations.

_⊢_:⇒*:_∷_ = Definition.Typed._⊢_:⇒*:_∷_
_⊢_:⇒*:_   = Definition.Typed._⊢_:⇒*:_

-- The relation _:_⊇_.

_∷_⊇_ = Definition.Typed.Weakening._∷_⊇_

-- Definition A.1: Reducibility of types.
--
-- In the paper the type level is written as a subscript instead of
-- within brackets.

_⊩⟨_⟩_ = Definition.LogicalRelation._⊩⟨_⟩_

-- Definition A.2: Reducibility of terms.
--
-- In the paper the type level is written as a subscript instead of
-- within brackets.

_⊩⟨_⟩_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_∷_/_

-- Reducibility of natural numbers.
--
-- In the paper ℕ is written as a subscript.

_⊩ℕ_ = Definition.LogicalRelation._⊩ℕ_∷ℕ

-- Definition A.3: Equality of reducible types.
--
-- In the paper the type level is written as a subscript instead of
-- within brackets.

_⊩⟨_⟩_≡_/_ = Definition.LogicalRelation._⊩⟨_⟩_≡_/_

-- Definition A.4: Equality of reducible terms.
--
-- In the paper the type level is written as a subscript instead of
-- within brackets.

_⊩⟨_⟩_≡_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_≡_∷_/_

-- Equality of reducible natural numbers.
--
-- In the paper ℕ is written as a subscript.

_⊩ℕ_≡_ = Definition.LogicalRelation._⊩ℕ_≡_∷ℕ

-- Definition A.6: Validity of contexts.

⊩ᵛ_ = Definition.LogicalRelation.Substitution.⊩ᵛ_

-- Definition A.7: Validity of substitutions and equality of valid
-- substitutions.
--
-- Note that the current definitions do not take the same arguments as
-- the definitions in the paper.

_⊩ˢ_∷_   = Definition.LogicalRelation.Substitution._⊩ˢ_∷_
_⊩ˢ_≡_∷_ = Definition.LogicalRelation.Substitution._⊩ˢ_≡_∷_

-- Definition A.8: Validity of types and terms and equality of valid
-- types and terms.
--
-- Note that the current definitions do not take the same arguments as
-- the definitions in the paper.

_⊩ᵛ⟨_⟩_     = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_
_⊩ᵛ⟨_⟩_∷_   = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_∷_
_⊩ᵛ⟨_⟩_≡_   = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_≡_
_⊩ᵛ⟨_⟩_≡_∷_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_≡_∷_

-- Theorem A.9: The fundamental lemma.

fundamentalType =
  Definition.LogicalRelation.Fundamental.Reducibility.reducible-⊩
fundamentalTerm =
  Definition.LogicalRelation.Fundamental.Reducibility.reducible-⊩∷
fundamentalTypeEq =
  Definition.LogicalRelation.Fundamental.Reducibility.reducible-⊩≡
fundamentalTermEq =
  Definition.LogicalRelation.Fundamental.Reducibility.reducible-⊩≡∷

------------------------------------------------------------------------
-- B: Usage Inference

-- Definition B.1: Usage inference.

∣_∣ = Graded.Usage.⌈_⌉

-- Theorem B.2.

Theorem-B-2a = Graded.Usage.Properties.usage-inf
Theorem-B-2b = Graded.Usage.Properties.usage-upper-bound

-- Theorem B.3: Decidability of the usage relation.

Theorem-B-3a = Graded.Usage.Decidable.⌈⌉▸[_]?′_
Theorem-B-3b = Graded.Usage.Decidable._▸[_]?_

-- Definition B.4: Substitution matrix inference.

∥_∥ = Graded.Substitution.∥_∥

-- Theorem B.5.

Theorem-B-5 = Graded.Substitution.Properties.subst-calc-correct′
