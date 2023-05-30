--------------------------------------------------------------------------
-- Code related to the paper "A Graded Modal Dependent Type Theory with a
-- Universe and Erasure, Formalized"
--------------------------------------------------------------------------

module README where

import Graded.Modality
import Graded.Context
import Graded.FullReduction
import Graded.Modality.Instances.Unit
import Graded.Modality.Instances.Erasure.Modality
import Graded.Modality.Instances.Erasure.Properties
import Graded.Modality.Instances.Affine
import Graded.Modality.Instances.Linearity
import Graded.Modality.Instances.Zero-one-many
import Graded.Modality.Instances.Linear-or-affine
import Graded.Modality.Instances.LowerBounded
import Graded.Modality.Instances.Recursive
import Graded.Modality.Instances.BoundedStar
import Graded.Usage
import Graded.Usage.Decidable
import Graded.Usage.Inversion
import Graded.Usage.Properties
import Graded.Usage.Restrictions
import Graded.Reduction
import Graded.Restrictions
import Graded.Substitution
import Graded.Substitution.Properties

import Definition.Untyped
import Definition.Untyped.Properties
import Definition.Typed
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Eta-long-normal-form
import Definition.Typed.Properties
import Definition.Typed.Restrictions
import Definition.Sigma
import Definition.LogicalRelation
import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility
import Definition.LogicalRelation.Substitution
import Graded.Mode
import Graded.Mode.Restrictions

import Graded.Erasure.Target
import Graded.Erasure.Extraction
import Graded.Erasure.Extraction.Properties
import Graded.Erasure.LogicalRelation
import Graded.Erasure.LogicalRelation.Reduction
import Graded.Erasure.LogicalRelation.Subsumption
import Graded.Erasure.LogicalRelation.Fundamental
import Graded.Erasure.LogicalRelation.Fundamental.Counterexample
import Graded.Erasure.SucRed
import Graded.Erasure.Consequences.Soundness

import Application.NegativeOrErasedAxioms.Canonicity.Erased
import Application.NegativeOrErasedAxioms.Canonicity.ErasedMatches

-- The code does not follow the paper exactly. Notably, the
-- formalisation contains parameters that make it possible to control
-- whether certain features should be included or not (in addition to
-- the possibility to choose what modality to use):

-- * One can have a theory with a single mode, or two modes:

modes = Graded.Mode.Restrictions.Mode-restrictions

-- * One can choose whether to allow use of the unit type with
--   η-equality. Furthermore one can choose whether to allow binders
--   of the form B_p^q, where p and q are grades and B is "Π", "Σ
--   without η-equality" or "Σ with η-equality":

types = Definition.Typed.Restrictions.Type-restrictions

--   This parameter does not affect the syntax, but if a term has a
--   certain type ("Unit" or "B_p^q A B"), then this type must be
--   allowed:

Unit-allowed =
  Definition.Typed.Consequences.Inversion.⊢∷Unit→Unit-restriction
ΠΣ-allowed =
  Definition.Typed.Consequences.Inversion.⊢∷ΠΣ→ΠΣ-restriction

-- * One can choose whether to allow the term prodrec_r,p^q:

prodrec = Graded.Usage.Restrictions.Usage-restrictions

--   This only affects the usage relation. If prodrec_r,p^q A t u is
--   well-resourced (under any mode), then the term is allowed:

prodrec-allowed = Graded.Usage.Inversion.inv-usage-prodrec

--   One can use this parameter to rule out erased matches:

no-erased-matches = Graded.Restrictions.no-erased-matches

-- Note that some results have only been proved for certain variants
-- of the theory.

-- There are also other differences between the paper and the
-- formalisation. Quite a few such differences are noted below.

------------------------------------------------------------------------
-- 3: Modalities as grades in an ordered semiring

-- Definition 3.1: The modality semiring.
--
-- For the variant of the type theory in Section 3 the mode 𝟘ᵐ should
-- be disallowed, i.e. 𝟘ᵐ-allowed should be false.
--
-- Unlike in the paper equality is not required to be decidable.
-- Instead this property is assumed where it is used.

Modality = Graded.Modality.Modality

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

-- The trivial (one element) modality.

unitModality = Graded.Modality.Instances.Unit.UnitModality

-- With the given definitions of _∧_, _+_ and _·_ there is only one
-- lawful way to define the star operator (up to pointwise equality).

⊛-unique = Graded.Modality.Instances.Erasure.Properties.⊛-unique

-- An erasure modality.

erasureModality =
  Graded.Modality.Instances.Erasure.Modality.ErasureModality

-- An "affine types" modality.

affineModality = Graded.Modality.Instances.Affine.affineModality

-- A "linear types" modality.

linearityModality =
  Graded.Modality.Instances.Linearity.linearityModality

-- The star operations of the "affine types" and "linear types"
-- modalities return results that are as large as possible (given the
-- definitions of the zero, the one, addition, multiplication and
-- meet).

⊛-greatest₁ = Graded.Modality.Instances.Zero-one-many.⊛-greatest

-- A "linear or affine types" modality.

linearOrAffineModality =
  Graded.Modality.Instances.Linear-or-affine.linear-or-affine

-- The star operation of the "linear or affine types" modality returns
-- results that are as large as possible (given the definitions of the
-- zero, the one, addition, multiplication and meet).

⊛-greatest₂ = Graded.Modality.Instances.Linear-or-affine.⊛-greatest

------------------------------------------------------------------------
-- 4: Type theory with grades

-- The grammar of the language.
--
-- The syntax is not defined in the same way as in the paper:
--
-- * The syntax is well-scoped: the type of terms is indexed by the
--   number of variables in the context.
--
-- * Terms are either variables or applications of "kinds" to terms.
--
-- * The type Kind specifies the arities of constructors, how many
--   extra variables the different term arguments take, as well as any
--   constructor arguments that are not terms.
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
-- closer to the notation in the paper.

grammar = Definition.Untyped.Term

-- Weakenings.
--
-- Unlike in the paper the type of weakenings is well-scoped: it is
-- indexed by two natural numbers, the sizes of the target and source
-- contexts, respectively.

Wk = Definition.Untyped.Wk

-- Application of a weakening to a de Bruijn index.
--
-- The definition of this operation is similar to the text's
-- presentation of applications of weakenings to variables, but not
-- quite idential: it is structurally recursive, and arguably less
-- complicated.

weakening-of-variable = Definition.Untyped.wkVar

-- Application of a weakening to a term.

weakening = Definition.Untyped.wk

-- Substitutions.
--
-- The type of substitutions is not defined in the same way as in the
-- paper. It is well-scoped, and instead of a data type with four
-- constructors the type Subst m n is the type of functions taking
-- variables with indices less than n to terms in contexts of size m.

Subst = Definition.Untyped.Subst

-- The main substitution constructors from the paper.

identity  = Definition.Untyped.idSubst
shifting  = Definition.Untyped.wk1Subst
lifting   = Definition.Untyped.liftSubst
extension = Definition.Untyped.consSubst

-- Application of a substitution to a term.

substitution = Definition.Untyped.subst

-- The head and tail of a substitution.

head = Definition.Untyped.head
tail = Definition.Untyped.tail

-- The typing relations.
--
-- These relations are parametrised by a value of type
-- Type-restrictions, which can be used to restrict certain types, as
-- discussed above.
--
-- Note also that some rules for Π and Σ have been merged.
--
-- The rules for natrec use types of the form
-- wk1 (A [ suc (var x0) ]↑). However, the paper uses types of the
-- form A [ suc (var x1) ]↑². These two types are equal.

⊢_                  = Definition.Typed.⊢_
_⊢_                 = Definition.Typed._⊢_
_⊢_∷_               = Definition.Typed._⊢_∷_
_⊢_≡_               = Definition.Typed._⊢_≡_
_⊢_≡_∷_             = Definition.Typed._⊢_≡_∷_
_∷_∈_               = Definition.Typed._∷_∈_
natrec-type-correct = Definition.Untyped.Properties.natrec-type-correct

-- Typing contexts.

Con = Definition.Untyped.Con

-- One can define something like prodrec for the Σ-types with
-- η-equality.

prodrec-for-Σₚ              = Definition.Sigma.prodrecₚ
prodrec-for-Σₚ-type-correct = Definition.Sigma.prodrecₚⱼ

-- Reduction relations

_⊢_⇒_    = Definition.Typed._⊢_⇒_
_⊢_⇒_∷_  = Definition.Typed._⊢_⇒_∷_
_⊢_⇒*_   = Definition.Typed._⊢_⇒*_
_⊢_⇒*_∷_ = Definition.Typed._⊢_⇒*_∷_

-- Theorem 4.3

Theorem-4-3a = Definition.Typed.Properties.whnfRed*Term
Theorem-4-3b = Definition.Typed.Properties.whnfRed*

-- Theorem 4.4

Theorem-4-4a = Definition.Typed.Properties.whrDet*Term
Theorem-4-4b = Definition.Typed.Properties.whrDet*

------------------------------------------------------------------------
-- 5: Assigning grades

-- Definition 5.1: The usage relation.
--
-- The usage relation is indexed by a mode, and one can choose to have
-- only one mode (𝟙ᵐ). In this case the mode 𝟘ᵐ? is equal to 𝟙ᵐ,
-- m ᵐ· p is equal to 𝟙ᵐ, and ⌜ m ⌝ is equal to the one of the
-- modality.
--
-- The usage rule for prodrec in the paper contains the side condition
-- "Prodrec r". This condition has been replaced by
-- "Prodrec-restriction r p q".

_▹_ = Graded.Usage._▸[_]_

-- Definition 5.2.
--
-- This predicate has been generalised to account for modes.

_▶_ = Graded.Substitution._▶[_]_

-- Theorem 5.3: A substitution lemma for usage.

Theorem-5-3 = Graded.Substitution.Properties.substₘ-lemma₁

-- The previous theorem is restricted to a setting with only one mode.
-- There is also a more general substitution lemma.

main-substitution-lemma = Graded.Substitution.Properties.substₘ-lemma

-- Theorem 5.4: Subject reduction for the usage relation.

Theorem-5-4 = Graded.Reduction.usagePresTerm

------------------------------------------------------------------------
-- 6: Erasure case study

-- Definition 6.1: Well-behaved zeros.
--
-- This definition includes one requirement that is not part of the
-- definition in the paper: equality with zero must be decidable.
-- However, the paper's definition of a modality semiring includes the
-- requirement that equality is decidable for all elements.

Has-well-behaved-zero = Graded.Modality.Has-well-behaved-zero

-- Four modality instances from the paper have well-behaved zeros.

erasure-has-well-behaved-zero =
  Graded.Modality.Instances.Erasure.Modality.erasure-has-well-behaved-zero
linearity-has-well-behaved-zero =
  Graded.Modality.Instances.Linearity.zero-one-many-has-well-behaved-zero
affine-has-well-behaved-zero =
  Graded.Modality.Instances.Affine.zero-one-many-has-well-behaved-zero
linear-or-affine-has-well-behaved-zero =
  Graded.Modality.Instances.Linear-or-affine.linear-or-affine-has-well-behaved-zero

-- Theorem 6.2.

Theorem-6-2 = Graded.Usage.Properties.valid-var-usage

-- The grammar of the untyped target language
--
-- The syntax is well-scoped.

target = Graded.Erasure.Target.Term

-- The reduction relation of the target language.

_⇒_  = Graded.Erasure.Target._⇒_
_⇒*_ = Graded.Erasure.Target._⇒*_

-- Definition 6.3: The extraction function.

_• = Graded.Erasure.Extraction.erase

-- Theorem 6.4.

Theorem-6-4 = Graded.Erasure.Extraction.Properties.erased-hasX

-- Reducibility logical relation for types.
--
-- In the paper the type level is written as a subscript instead of
-- within braces.

_⊩′⟨_⟩_ = Definition.LogicalRelation._⊩⟨_⟩_

-- Some cases of the relation.
--
-- The case for Π is common with the cases for the two kinds of
-- Σ-types.
--
-- For the case called ⟨emb/⟩, see
-- Definition.LogicalRelation.LogRel._⊩¹_.emb.

⟨ℕ⟩   = Definition.LogicalRelation._⊩ℕ_
⟨Π//⟩ = Definition.LogicalRelation.LogRel._⊩¹B⟨_⟩_

-- Reducibility logical relation for terms.
--
-- In the paper the type level is written as a subscript instead of
-- within braces.

_⊩′⟨_⟩_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_∷_/_

-- The fundamental lemma of the reducibility relation.

fundamentalReducibleType = Definition.LogicalRelation.Fundamental.Reducibility.reducible
fundamentalReducibleTerm = Definition.LogicalRelation.Fundamental.Reducibility.reducibleTerm

-- Definition 6.5: The logical relation for erasure.
--
-- In the paper the logical relation is defined specifically for the
-- erasure modality, but here it has been generalised to hold for
-- arbitrary modalities with well-behaved zeros.
--
-- In the paper the type level is written as a subscript instead of
-- within braces.

_®⟨_⟩_∷_/_ = Graded.Erasure.LogicalRelation._®⟨_⟩_∷_/_

-- Valid substitutions.
--
-- The argument for the target context being well-formed is not
-- included in the paper because the context is fixed and assumed to
-- be well-formed.

_⊩ˢ_∷_/_ = Definition.LogicalRelation.Substitution._⊩ˢ_∷_/_/_

-- Definition 6.6: The logical relation for substitutions.
--
-- In the paper the type level is written as a subscript instead of
-- within braces.

_®⟨_⟩_∷_◂_/_/_ = Graded.Erasure.LogicalRelation._®⟨_⟩_∷[_]_◂_/_/_

-- Definition 6.7: Erasure validity
--
-- In the paper the type level is written as a subscript instead of
-- within braces.

_▸_⊩ʳ⟨_⟩_∷_/_/_ = Graded.Erasure.LogicalRelation._▸_⊩ʳ⟨_⟩_∷[_]_/_/_

-- Theorem 6.8: Backwards closure of logical relation under reduction.

Theorem-6-8 = Graded.Erasure.LogicalRelation.Reduction.redSubstTerm*

-- Theorem 6.9: Subsumption of the logical relation.

Theorem-6-9a =
  Graded.Erasure.LogicalRelation.Subsumption.subsumptionSubst
Theorem-6-9b =
  Graded.Erasure.LogicalRelation.Subsumption.subsumption

-- Theorem 6.10: The fundamental lemma.

fundamental = Graded.Erasure.LogicalRelation.Fundamental.fundamental

-- Theorem 6.11: All substitutions are related under erased contexts.

Theorem-6-11 = Graded.Erasure.LogicalRelation.Subsumption.erasedSubst

-- Theorem 6.12: The fundamental lemma for fully erased terms.

Theorem-6-12 =
  Graded.Erasure.LogicalRelation.Fundamental.fundamentalErased

-- Extended reduction relations.

_⊢_⇒ˢ_∷ℕ  = Graded.Erasure.SucRed._⊢_⇒ˢ_∷ℕ
_⊢_⇒ˢ*_∷ℕ = Graded.Erasure.SucRed._⊢_⇒ˢ*_∷ℕ
_⇒ˢ_      = Graded.Erasure.SucRed._⇒ˢ_
_⇒ˢ*_     = Graded.Erasure.SucRed._⇒ˢ*_

-- Theorem 6.13: Soundness of the extraction function.

soundness = Graded.Erasure.Consequences.Soundness.soundness-ℕ

------------------------------------------------------------------------
-- 7: Discussion

------------------------------------------------------------------------
-- 7.1: Modalities for the recursor

-- A lawful definition of ⊛ᵣ for lower bounded structures.

⊛ᵣ-lower-bounded = Graded.Modality.Instances.LowerBounded._⊛_▷_

-- A lawful definition of ⊛ᵣ defined recursively.

⊛ᵣ-recursive = Graded.Modality.Instances.Recursive._⊛_▷_

-- A lawful definition of ⊛ᵣ for bounded star-semirings.

⊛ᵣ-star-semiring = Graded.Modality.Instances.BoundedStar._⊛_▷_

------------------------------------------------------------------------
-- 7.2: Erased matches

-- Theorem 7.1.

theorem-7-1 =
  Application.NegativeOrErasedAxioms.Canonicity.Erased.canonicityRed

-- A counteraxample to Theorem 7.1 if erased matches are allowed.

counterexample₁ =
  Application.NegativeOrErasedAxioms.Canonicity.ErasedMatches.Counterexample.cEx

-- A counterexample to the fundamental lemma if erased matches are
-- allowed.

counterexample₂ =
  Graded.Erasure.LogicalRelation.Fundamental.Counterexample.cEx

------------------------------------------------------------------------
-- 7.3: Unit type

-- A type- and resource-preserving procedure that takes a well-typed,
-- well-resourced term to one of its η-long normal forms.
--
-- The procedure makes certain assumptions about types with
-- η-equality.

η-long-normal-forms = Graded.FullReduction.fullRedTerm

------------------------------------------------------------------------
-- 8: Extension: modes and graded Σ-types

-- Note that for the definitions and theorems in this section,
-- a modality with the zero mode allowed should be used.

-- Modes.
--
-- The definition is parametric: one can disallow the mode 𝟘ᵐ.

Mode = Graded.Mode.Mode

-- Translating grades to modes.
--
-- In the paper this function is denoted by an underline.

⌞_⌟ = Graded.Mode.⌞_⌟

-- Translating modes to grades.
--
-- In the paper this function is denoted by an overline.

⌜_⌝ = Graded.Mode.⌜_⌝

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

-- The usage relation with modes.
--
-- In the paper the mode is written as a superscript instead of within
-- braces.

_▸[_]_ = Graded.Usage._▸[_]_

-- Theorem 8.2: Subject reduction for the usage relation with modes.

Theorem-8-2 = Graded.Reduction.usagePresTerm

-- The extraction function.

_•′ = Graded.Erasure.Extraction.erase

-- Theorem 8.3: Soundness of the extraction function.

Theorem-8-3 = Graded.Erasure.Consequences.Soundness.soundness-ℕ

-- A definition of η-long normal forms.

_⊢nf_∷_ = Definition.Typed.Eta-long-normal-form._⊢nf_∷_

-- A type- and resource-preserving procedure that takes a well-typed,
-- well-resourced term to one of its η-long normal forms.
--
-- The procedure makes certain assumptions about types with
-- η-equality.

η-long-normal-forms′ = Graded.FullReduction.fullRedTerm

-- The assumptions are satisfied for the unit modality.

unit = Graded.Modality.Instances.Unit.full-reduction-assumptions

-- The assumptions are satisfied for the erasure modality if Σ_&,0^q
-- is only allowed when 𝟘ᵐ is allowed.

erasure =
  Graded.Modality.Instances.Erasure.Properties.full-reduction-assumptions

-- The assumptions are satisfied for the affine types modality if
-- Σ_&,0^q is only allowed when 𝟘ᵐ is allowed, and Σ_&,ω^q is not
-- allowed.

affine = Graded.Modality.Instances.Affine.full-reduction-assumptions

-- The assumptions are satisfied for the linear types modality if the
-- unit type with η-equality is not allowed, Σ_&,0^q is not allowed,
-- and Σ_&,ω^q is not allowed.

linear = Graded.Modality.Instances.Linearity.full-reduction-assumptions

-- The assumptions are satisfied for the linear or affine types
-- modality if the unit type with η-equality is not allowed, Σ_&,0^q
-- is not allowed, Σ_&,≤1^q is not allowed, and Σ_&,≤ω^q is not
-- allowed.

linear-or-affine =
  Graded.Modality.Instances.Linear-or-affine.full-reduction-assumptions

------------------------------------------------------------------------
-- A: Logical relation for reducibility

-- Combined reduction and typing relations

_⊢_:⇒*:_∷_ = Definition.Typed._⊢_:⇒*:_∷_
_⊢_:⇒*:_ = Definition.Typed._⊢_:⇒*:_

-- Definition A.1: Reducibility of types
-- In the paper, the type level is denoted with a subscript instead of within braces.

_⊩⟨_⟩_ = Definition.LogicalRelation._⊩⟨_⟩_

-- Definition A.2: Reducibility of terms
-- In the paper, the type level is denoted with a subscript instead of within braces.

_⊩⟨_⟩_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_∷_/_

-- Definition A.3: Equality of reducible types
-- In the paper, the type level is denoted with a subscript instead of within braces.

_⊩⟨_⟩_≡_/_ = Definition.LogicalRelation._⊩⟨_⟩_≡_/_

-- Definition A.4: Equality of reducible terms
-- In the paper, the type level is denoted with a subscript instead of within braces.

_⊩⟨_⟩_≡_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_≡_∷_/_

-- Definition A.6: Validity of contexts

⊩ᵛ_ = Definition.LogicalRelation.Substitution.⊩ᵛ_

-- Definition A.7: Validity of substitutions and equality of
-- valid substitutions

_⊩ˢ_∷_/_/_ = Definition.LogicalRelation.Substitution._⊩ˢ_∷_/_/_

-- Definition A.8: Validity of types, terms and equality of
-- valid types and terms
-- In the paper, the type levels are denoted with a subscript instead of within braces.

_⊩ᵛ⟨_⟩_/_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_/_
_⊩ᵛ⟨_⟩_∷_/_/_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_∷_/_/_
_⊩ᵛ⟨_⟩_≡_/_/_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_≡_/_/_
_⊩ᵛ⟨_⟩_≡_∷_/_/_ = Definition.LogicalRelation.Substitution._⊩ᵛ⟨_⟩_≡_∷_/_/_

-- Theorem A.9: The fundamental lemma

fundamentalType = Definition.LogicalRelation.Fundamental.Reducibility.reducible
fundamentalTerm = Definition.LogicalRelation.Fundamental.Reducibility.reducibleTerm
fundamentalTypeEq = Definition.LogicalRelation.Fundamental.Reducibility.reducibleEq
fundamentalTermEq = Definition.LogicalRelation.Fundamental.Reducibility.reducibleEqTerm

------------------------------------------------------------------------
-- B: Usage inference

-- Definition B.1: Usage inference

∣_∣ = Graded.Usage.⌈_⌉

-- Theorem B.2

Theorem-B-2a = Graded.Usage.Properties.usage-inf
Theorem-B-2b = Graded.Usage.Properties.usage-upper-bound

-- Theorem B.3: Decidability of the usage relation

Theorem-B-3a = Graded.Usage.Decidable.⌈⌉▸[_]?_
Theorem-B-3b = Graded.Usage.Decidable._▸[_]?_

-- Definition B.4: Substitution matrix inference

∥_∥ = Graded.Substitution.∥_∥

-- Theorem B.5

Theorem-B-5 = Graded.Substitution.Properties.subst-calc-correct′
