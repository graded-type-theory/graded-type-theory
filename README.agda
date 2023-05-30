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
import Definition.Typed
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Properties
import Definition.Typed.Restrictions
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
-- formalisation. Such differences are noted below.

-- TODO: Note such differences below.

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

-- The grammar of the language

grammar = Definition.Untyped.Term

-- Weakenings

Wk = Definition.Untyped.Wk

-- Substitutions

Subst = Definition.Untyped.Subst

-- The typing relations

⊢_ = Definition.Typed.⊢_
_⊢_ = Definition.Typed._⊢_
_⊢_∷_ = Definition.Typed._⊢_∷_
_⊢_≡_ = Definition.Typed._⊢_≡_
_⊢_≡_∷_ = Definition.Typed._⊢_≡_∷_

-- Typing contexts

Con = Definition.Untyped.Con

-- Reduction relations

_⊢_⇒_ = Definition.Typed._⊢_⇒_
_⊢_⇒_∷_ = Definition.Typed._⊢_⇒_∷_
_⊢_⇒*_ = Definition.Typed._⊢_⇒*_
_⊢_⇒*_∷_ = Definition.Typed._⊢_⇒*_∷_

-- Theorem 4.3

Theorem-4-3a = Definition.Typed.Properties.whnfRed*Term
Theorem-4-3b = Definition.Typed.Properties.whnfRed*

-- Theorem 4.4

Theorem-4-4a = Definition.Typed.Properties.whrDet*Term
Theorem-4-4b = Definition.Typed.Properties.whrDet*

------------------------------------------------------------------------
-- 5: Assigning grades

-- Note that for the definitions and theorems in this section,
-- a modality with the zero mode disallowed should be used and the
-- extra annotation on Σ-types should be 𝟙

-- Definition 5.1: The usage relation

_▹_ = Graded.Usage._▸[_]_

-- Definition 5.2

_▶_ = Graded.Substitution._▶[_]_

-- Theorem 5.3: Substitution lemma for grade usage

Theorem-5-3 = Graded.Substitution.Properties.substₘ-lemma₁

-- Theorem 5.4: Subject reduction for grade usage

Theorem-5-4 = Graded.Reduction.usagePresTerm

------------------------------------------------------------------------
-- 6: Erasure case study

-- Note that for the definitions and theorems in this section,
-- the modality has the zero mode disallowed and the extra annotation
-- on Σ-types is required to be 𝟙

-- Definition 6.1

Has-well-behaved-zero = Graded.Modality.Has-well-behaved-zero

erasure-has-well-behaved-zero =
  Graded.Modality.Instances.Erasure.Modality.erasure-has-well-behaved-zero
linearity-has-well-behaved-zero =
  Graded.Modality.Instances.Linearity.zero-one-many-has-well-behaved-zero
affine-has-well-behaved-zero =
  Graded.Modality.Instances.Affine.zero-one-many-has-well-behaved-zero
linear-or-affine-has-well-behaved-zero =
  Graded.Modality.Instances.Linear-or-affine.linear-or-affine-has-well-behaved-zero

-- Theorem 6.2

Theorem-62 = Graded.Usage.Properties.valid-var-usage

-- The grammar of the untyped target language

target = Graded.Erasure.Target.Term

-- The reduction relation of the target language

_⇒_ = Graded.Erasure.Target._⇒_
_⇒*_ = Graded.Erasure.Target._⇒*_

-- Definition 6.3: The extraction function

_• = Graded.Erasure.Extraction.erase

-- Theorem 6.4

Theorem-64 = Graded.Erasure.Extraction.Properties.erased-hasX

-- Reducibility logical relation for types
-- In the paper, the type level is denoted with a subscript instead of within braces.

_⊩′⟨_⟩_ = Definition.LogicalRelation._⊩⟨_⟩_

-- Reducibility logical relation for terms
-- In the paper, the type level is denoted with a subscript instead of within braces.

_⊩′⟨_⟩_∷_/_ = Definition.LogicalRelation._⊩⟨_⟩_∷_/_

-- The fundamental lemma of the reducibility relation

fundamentalReducibleType = Definition.LogicalRelation.Fundamental.Reducibility.reducible
fundamentalReducibleTerm = Definition.LogicalRelation.Fundamental.Reducibility.reducibleTerm

-- Definition 6.5: The logical relation for erasure
-- In the paper, the logical relation is defined specifically for the
-- erasure modality but is here generalized to hold in more general
-- cases, assuming that the zero of the semiring is sufficiently
-- well behaved.

_®⟨_⟩_∷_/_ = Graded.Erasure.LogicalRelation._®⟨_⟩_∷_/_
-- In the paper, the type level is denoted with a subscript instead of within braces.

-- Valid substitutions
-- The argument for the target context being well-formed is not included in the
-- paper since the context is fixed and assumed to be well-formed.

_⊩ˢ_∷_/_ = Definition.LogicalRelation.Substitution._⊩ˢ_∷_/_/_

-- Definition 6.6: The logical relation for substitutions
-- In the paper, the type level is denoted with a subscript instead of within braces.

_®⟨_⟩_∷_◂_/_/_ = Graded.Erasure.LogicalRelation._®⟨_⟩_∷[_]_◂_/_/_


-- Definition 6.7: Erasure validity
-- In the paper, the type level is denoted with a subscript instead of within braces.

_▸_⊩ʳ⟨_⟩_∷_/_/_ = Graded.Erasure.LogicalRelation._▸_⊩ʳ⟨_⟩_∷[_]_/_/_

-- Theorem 6.8: Backwards closure of logical relation under reduction

Theorem-68 = Graded.Erasure.LogicalRelation.Reduction.redSubstTerm*

-- Theorem 6.9: Subsumption of the logical relation

Theorem-69a = Graded.Erasure.LogicalRelation.Subsumption.subsumptionSubst
Theorem-69b = Graded.Erasure.LogicalRelation.Subsumption.subsumption

-- Theorem 6.10: The fundamental lemma

fundamental = Graded.Erasure.LogicalRelation.Fundamental.fundamental

-- Theorem 6.11: All substitutions are related under erased contexts

Theorem-611 = Graded.Erasure.LogicalRelation.Subsumption.erasedSubst

-- Theorem 6.12: The fundamental lemma for fully erased terms

Theorem-612 = Graded.Erasure.LogicalRelation.Fundamental.fundamentalErased

-- Extended reduction relations

_⊢_⇒ˢ_∷ℕ = Graded.Erasure.SucRed._⊢_⇒ˢ_∷ℕ
_⊢_⇒ˢ*_∷ℕ = Graded.Erasure.SucRed._⊢_⇒ˢ*_∷ℕ
_⇒ˢ_ = Graded.Erasure.SucRed._⇒ˢ_
_⇒ˢ*_ = Graded.Erasure.SucRed._⇒ˢ*_

-- Theorem 6.13: Soundness of the extraction function

soundness = Graded.Erasure.Consequences.Soundness.soundness-ℕ

------------------------------------------------------------------------
-- 7: Discussion

-- A lawful definition of ⊛ᵣ for lower bounded structures

⊛ᵣ-lower-bounded = Graded.Modality.Instances.LowerBounded._⊛_▷_

-- A lawful definition of ⊛ᵣ defined recursively

⊛ᵣ-recursive = Graded.Modality.Instances.Recursive._⊛_▷_

-- A lawful definition of ⊛ᵣ for bounded star-semirings

⊛ᵣ-star-semiring = Graded.Modality.Instances.BoundedStar._⊛_▷_

-- Theorem 7.1

theorem-71 = Application.NegativeOrErasedAxioms.Canonicity.Erased.canonicityRed

-- A counteraxample to theorem 7.1 if erased matches are allowed

counterexample₁ =
  Application.NegativeOrErasedAxioms.Canonicity.ErasedMatches.Counterexample.cEx

-- A counterexample to the fundamental lemma if erased matches are allowed

counterexample₂ = Graded.Erasure.LogicalRelation.Fundamental.Counterexample.cEx

-- The existence of η-long normal forms

η-long-normal-forms = Graded.FullReduction.fullRedTerm

------------------------------------------------------------------------
-- 8: Extension: modes and graded Σ-types

-- Note that for the definitions and theorems in this section,
-- a modality with the zero mode allowed should be used.

-- Modes

Mode = Graded.Mode.Mode

-- Definition 8.1: The extended modality structure

ExtendedModality = Graded.Modality.Modality

-- The modality structures for erasure, affine and linear types
-- satisfy the conditions of the extended modality definition

erasureModalityₑ = Graded.Modality.Instances.Erasure.Modality.ErasureModality
affineModalityₑ = Graded.Modality.Instances.Affine.affineModality
linearityModalityₑ = Graded.Modality.Instances.Linearity.linearityModality

-- Subject reduction for the extended grade usage relation

subjectReduction = Graded.Reduction.usagePresTerm

-- Translating modes into grades
-- In the paper, this function is denoted by an overbar.

⌜_⌝ = Graded.Mode.⌜_⌝

-- Translating grades into modes
-- In the paper, this function is denoted by an underline.

⌞_⌟ = Graded.Mode.⌞_⌟

-- Scaling modes by grades

_⊙_ = Graded.Mode._ᵐ·_

-- The usage relation with modes
-- In the paper, the mode is denoted with a superscript instead of within braces.

_▸[_]_ = Graded.Usage._▸[_]_

-- Theorem 8.3: Subject reduction for the usage relation with modes

Theorem-83 = Graded.Reduction.usagePresTerm

-- The extraction function
-- Note that this has been updated to no longer use substitutions

_◦ = Graded.Erasure.Extraction.erase

-- Theorem 8.4: Soundness of the extraction function

Theorem-84 = Graded.Erasure.Consequences.Soundness.soundness-ℕ

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

Theorem-B2a = Graded.Usage.Properties.usage-inf
Theorem-B2b = Graded.Usage.Properties.usage-upper-bound

-- Theorem B.3: Decidability of the usage relation

Theorem-B3a = Graded.Usage.Decidable.⌈⌉▸[_]?_
Theorem-B3b = Graded.Usage.Decidable._▸[_]?_

-- Definition B.4: Substitution matrix inference

∥_∥ = Graded.Substitution.∥_∥

-- Theorem B.5

Theorem-B5 = Graded.Substitution.Properties.subst-calc-correct′
