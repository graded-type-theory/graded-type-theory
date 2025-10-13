module README where

------------------------------------------------------------------------
-- Code related to the paper "Normalisation for First-Class Universe
-- Levels" by Nils Anders Danielsson, Naïm Camille Favier and Ondřej Kubánek
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
--   by Nils Anders Danielsson, Naïm Camille Favier and Ondřej Kubánek
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

-- Some typing rules have slightly different names from those in the paper.

import Definition.Typed using (⊢_; _⊢_; _⊢_≡_; _⊢_∷_; _⊢_≡_∷_; _⊢_≤_∷Level)
import Definition.Typed.Properties.Admissible.Level
  using (⊢≤-refl; ⊢≤-trans; ⊢≤-antisymmetric)
import Definition.Typed.Properties.Admissible.Lift using (Liftⱼ≤)

-- Admissible heterogeneous Π- and Σ-types.

import Definition.Typed.Properties.Admissible.Pi-Sigma using (ΠΣʰⱼ)
import Definition.Typed.Properties.Admissible.Pi using (lamʰⱼ; ∘ʰⱼ)
import Definition.Typed.Properties.Admissible.Sigma using (prodʰⱼ; fstʰⱼ; sndʰⱼ)

-- Well-formedness and subject reduction are only mentioned in the
-- Contributions section; we plan to revise the paper to include these
-- results in this section.

import Definition.Typed.Syntactic using (syntacticTerm; syntacticRedTerm)

------------------------------------------------------------------------
-- 2.3: Reduction rules

import Definition.Typed using (_⊢_⇒_∷_)

-- Compared to the paper, we use Neutral instead of Neutralᵃ for
-- atomic neutrals and Neutralˡ instead of Neutral for neutrals
-- possibly including _supᵘ_.

import Definition.Untyped.Neutral using (Neutral; Neutralˡ; Whnf)

------------------------------------------------------------------------
-- 3: A logical relation

-- The external universe level hierarchy ω + 1.
import Definition.Untyped.NotParametrised using (Universe-level)

-- The generic equality relations.
import Definition.Typed.EqualityRelation

-- The equality relation instance for judgemental equality.
import Definition.Typed.EqRelInstance

------------------------------------------------------------------------
-- 3.1: Reducible levels and neutrals

-- We write Γ ⊩Level t ∷Level instead of Γ ⊩Lvl t, Level-prop Γ t instead
-- of Γ ⊩Lvl_w t, and neLevel-prop Γ t instead of Γ ⊩Lvlₙ t, and
-- similarly for equalities.

import Definition.LogicalRelation
  using (_⊩neNf_≡_∷_; _⊩Level_∷Level; Level-prop; neLevel-prop)

-- Unary versions of the logical relations.
import Definition.LogicalRelation.Unary using (_⊩neNf_∷_)

-- The realiser of a reducible level t is written ↑ᵘ [t], where [t] is
-- a witness that t is reducible.

import Definition.LogicalRelation using (↑ᵘ_)

-- Irrelevance for ↑ᵘ; ↑ᵘ respects equality and ordering.
import Definition.LogicalRelation.Properties.Primitive
  using (↑ᵘ-irrelevance; ↑ᵘ-cong; ↑ᵘ-cong-≤)

-- supᵘ respects equality in its first argument.
import Definition.LogicalRelation.Properties.Primitive using (⊩supᵘ-congˡ)

-- Lemma 3.1: The typing rule for supᵘ is reducible.
import Definition.LogicalRelation.Properties.Primitive using (⊩supᵘ)

-- Lemma 3.2: The judgemental equality supᵘ-idem is reducible.
import Definition.LogicalRelation.Properties.Primitive using (⊩supᵘ-idem)

------------------------------------------------------------------------
-- 3.2: Reducibility

-- The main reducibility judgements are written Γ ⊩⟨ ℓ ⟩ 𝒥, where 𝒥 is
-- one of the four forms of judgement.

import Definition.LogicalRelation
  using (_⊩⟨_⟩_; _⊩⟨_⟩_≡_/_; _⊩⟨_⟩_∷_/_; _⊩⟨_⟩_≡_∷_/_)

-- The logical relation is cumulative.
import Definition.LogicalRelation.Properties.Embedding

-- Versions of reducibility judgements with hidden reducibility arguments.
import Definition.LogicalRelation.Hidden
  using (_⊩⟨_⟩_≡_; _⊩⟨_⟩_∷_; _⊩⟨_⟩_≡_∷_)

-- Irrelevance for reducibility judgements, justifying the hidden versions
-- above.
import Definition.LogicalRelation.Irrelevance

------------------------------------------------------------------------
-- 3.3 Validity and the fundamental lemma

-- Γ ⊩⟨ ℓ ⟩ 𝒥 implies Γ ⊢ 𝒥.
import Definition.LogicalRelation.Properties.Escape

-- Validity judgements.
import Definition.LogicalRelation.Substitution
  using (⊩ᵛ_; _⊩ᵛ⟨_⟩_; _⊩ᵛ⟨_⟩_≡_; _⊩ˢ_≡_∷_; _⊩ˢ_∷_; _⊩ᵛ⟨_⟩_≡_∷_; _⊩ᵛ⟨_⟩_∷_)

-- Lemma 3.3: Fundamental lemma.
import Definition.LogicalRelation.Fundamental

-- Lemma 3.4: The term typing rule for U is valid.
import Definition.LogicalRelation.Substitution.Introductions.Universe using (⊩ᵛU∷U)

-- Lemma 3.5: The typing rule univ is valid.
import Definition.LogicalRelation.Substitution.Introductions.Universe using (⊩ᵛ∷U→⊩ᵛ)

-- Lemma 3.6: The term typing rule for Lift is valid.
import Definition.LogicalRelation.Substitution.Introductions.Lift using (Liftᵗᵛ)

-- Corollary 3.8: Well-typed objects are reducible.
import Definition.LogicalRelation.Fundamental.Reducibility

-- Atomic neutrals are reducible.
import Definition.LogicalRelation.Properties.Neutral

-- Corollary 3.9: Consistency.
import Definition.Typed.Consequences.Canonicity using (¬Empty)

-- Corollary 3.10: Canonicity.
import Definition.Typed.Consequences.Canonicity using (canonicity)

-- Corollary 3.11: Weak head normalisation.
import Definition.Typed.Consequences.Reduction using (whNorm; whNormTerm)

-- Corollary 3.12: Injectivity of type formers.
import Definition.Typed.Consequences.Injectivity

------------------------------------------------------------------------
-- 4: Decidability of equality

-- Algorithmic equality.

-- The conversion relations are denoted as follows:
-- * Γ ⊢ A [conv↑] B and Γ ⊢ A [conv↓] B for arbitrary types and types
--   in WHNF respectively,
-- * Γ ⊢ t [conv↑] u ∷ A and Γ ⊢ t [conv↓] u ∷ B for arbitrary terms and terms
--   in WHNF with types in WHNF respectively, and
-- * Γ ⊢ t ~ u ↑ A and Γ ⊢ t ~ u ↓ A for atomic neutral terms and atomic
--   neutral terms with types in WHNF respectively.

import Definition.Conversion
  using (_⊢_[conv↑]_; _⊢_[conv↓]_; _⊢_[conv↑]_∷_; _⊢_[conv↓]_∷_; _⊢_~_↑_; _⊢_~_↓_)

-- Level atoms and views.
import Definition.Conversion using (LevelAtom; Level⁺; Levelᵛ)

-- Level view comparison.
import Definition.Conversion using (_≡ᵛ_; ≤ᵛ)

-- Operations on level views.
import Definition.Conversion using (sucᵛ; supᵛ)

-- Normalising levels into level views.
import Definition.Conversion using (_⊢_↑ᵛ_; _⊢_↓ᵛ_; _⊢_~ᵛ_)

-- Algorithmic equality is sound.
import Definition.Conversion.Soundness

-- Algorithmic equality is stable under weakening.
import Definition.Conversion.Weakening

-- Algorithmic equality is decidable.
import Definition.Conversion.Decidable

-- Level normalisation is deterministic.
import Definition.Conversion.Level using (deterministic-↑ᵛ)

-- Lemma 4.1.
import Definition.Conversion.EqRelInstance -- supᵘ-↑ᵛ

-- Lemma 4.2: Algorithmic equality is complete for judgemental equality.
import Definition.Conversion.Consequences.Completeness

-- Corollary 4.3: Judgemental equality of well-formed types and terms is decidable.
import Definition.Typed.Decidable.Equality

-- Corollary 4.4: Typing is decidable for a certain subset of Checkable
-- types and terms.
import Definition.Typechecking using (Checkable)
import Definition.Typed.Decidable

-- Corollary 4.5: Deep normalisation.
import Definition.Typed.Eta-long-normal-form
import Definition.Conversion.FullReduction using (fullRed)

------------------------------------------------------------------------
-- 5: Erasing levels is safe

-- The usage relation.
import Graded.Usage using (_▸[_]_)

-- The erasure modality.
import Graded.Modality.Instances.Erasure using (𝟘; ω)
import Graded.Modality.Instances.Erasure.Modality

-- The target language.
import Graded.Erasure.Target

-- Theorem 5.1: Soundness of erasure.
import Graded.Erasure.Consequences.Soundness

-- Some examples, including a universe-polymorphic identity function.
import Graded.Erasure.Examples using (⊢id)

------------------------------------------------------------------------
-- Additional results

-- Some features were added to the formalisation after the paper was submitted.

-- There is now a Level-is-small parameter that controls whether Level
-- belongs to the first universe. If this is disabled, then Level is
-- only a type, not an element of any universe. Disabling this parameter
-- is similar to *enabling* Agda's --level-universe flag, which makes
-- Level an element of a separate universe LevelUniv instead of Set.
-- A notable difference is that Agda disallows forming identity
-- types of types in LevelUniv, whereas our type theory has identity
-- type formation rules for every type.

open import Definition.Typed.Restrictions using (module Type-restrictions)
open Type-restrictions using (Level-is-small)

-- Canonicity is proved for natural number terms in contexts consisting
-- only of Level variables.

import Definition.Typed.Consequences.Canonicity
  using (canonicity-with-level-assumptions)
