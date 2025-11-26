```agda
module README where
```

# An Agda Formalization of a Graded Modal Type Theory with First-Class Universe Levels and Erasure

This code is related to the POPL 2026 paper "Normalisation for First-Class
Universe Levels" by Nils Anders Danielsson, Naïm Camille Favier and
Ondřej Kubánek. It builds on an existing formalisation, see "Project
history" below.

## Dependencies and licences

The code depends on some libraries:

* Agda's standard library, version 2.3.
* The builtin modules that are shipped with Agda 2.8.0.

When HTML code is generated from this file code is also generated
for the two libraries above, so URLs for their licences are
included here. At the time of writing the licence texts can be
found at the following URLs:

* https://github.com/agda/agda-stdlib/blob/v2.3/LICENCE
* https://github.com/agda/agda/blob/v2.8.0/LICENSE

The licence for this project can be found in the file LICENSE.

## Project history

This formalization originated as a fork of
[logrel-mltt](https://github.com/mr-ohman/logrel-mltt). That work
consisted of the following contributions:

* "A Logical Relation for Martin-Löf Type Theory in Agda", code
  mostly written by Joakim Öhman in 2016 as part of a master's
  thesis supervised by Andrea Vezzosi and Andreas Abel.

  That development is described in the article "Decidability of
  Conversion for Type Theory in Type Theory", Andreas Abel, Joakim
  Öhman and Andrea Vezzosi, Proceedings of the ACM on Programming
  Languages, Volume 2, Issue POPL, 2017
  ([doi:10.1145/3158111](https://doi.org/10.1145/3158111)).

* The empty type was added by Gaëtan Gilbert (2018).

* A unit type and Σ-types were added by Wojciech Nawrocki (2021).

* The code was refactored to use well-scoped syntax by Oskar
  Eriksson (2021).

The formalization was lifted to graded modal type theory: this is the
basis of the paper "A Graded Modal Type Theory with a Universe and
Erasure, Formalized", Andreas Abel, Nils Anders Danielsson and Oskar
Eriksson, Proceedings of the ACM on Programming Languages, Volume 7,
Issue ICFP, 2023
([doi.org/10.1145/3607862](https://doi.org/10.1145/3607862)).

Later other additions were made:

* Identity types were added by Nils Anders Danielsson (2023).

* A weak unit type was added by Oskar Eriksson (2023).

* A universe hierarchy with first-class universe levels was added
  by Nils Anders Danielsson, Naïm Camille Favier and Ondřej Kubánek
  (2024-2025): this is the focus of the discussion below.

Note also that some changes to the code were made after feedback from
anonymous reviewers.

## Pointers to code for specific definitions, theorems etc. in the paper

Below pointers to code are included for all the main definitions,
theorems, etc. in the paper, along with some discussion of
differences between the paper and the code.

### 2: A type theory with first-class universe levels

#### 2.1: Syntax

Note that large parts of the development are parametrised by a grade
type or a modality. Grades and modalities are to a large part ignored
in the paper. If one does not care about grades, then one can use a
unit type or a trivial modality:
```agda
import Graded.Modality.Instances.Unit using (UnitModality)
```

Terms. The notation does not match the paper exactly. The notation
`zeroᵘ` is used for 0, `sucᵘ` for \_⁺, and `_supᵘ_` for \_⊔\_. Instead
of a constructor Π for Π-types there is a constructor `ΠΣ⟨_⟩_,_▷_▹_`
for *graded* Π- and Σ-types, and the constructors for lambdas and
applications also take grades. The derived notation k + t is denoted
by `sucᵘᵏ k t`, and ↓ k is denoted by `↓ᵘ k`.
```agda
import Definition.Untyped using (Term; sucᵘᵏ; ↓ᵘ_)
```

Contexts. The type is more general than in the paper: the
instantiation `Con Term` corresponds to what is called Con in the
paper. Furthermore the notation does not match that used in the paper:
the notation `ε` is used for ·, and `_∙_` is used instead of \_,\_.
```agda
import Definition.Untyped using (Con)
```

Substitution.
```agda
import Definition.Untyped using (_[_])
```

Weakening. The notation `wk ρ t` is used instead of t[ρ], and the
notation `ρ ∷ʷ Δ ⊇ Γ` means that ρ is a well-formed weakening from Γ
to Δ (Δ ⊢ ρ : Γ in the paper). The single-step weakening p is written
`step id`: in the code this weakening is often used via
`wk1` = `wk (step id)`, and the lemmas `wk₁` and `wkTerm₁` show that
this operation is type-preserving.
```agda
import Definition.Untyped using (wk; step; id; wk1)
import Definition.Typed.Weakening using (_∷ʷ_⊇_; wk₁; wkTerm₁)
```

#### 2.2: Typing rules

Unlike in the paper the type system is parametrised by a value of type
`Type-restrictions` that makes it possible to disallow certain things,
like certain (graded) Π- or Σ-types, the K rule or equality
reflection. For instance, the two typing rules for Π and Σ include the
assumption `ΠΣ-allowed b p q`. It is also possible to restrict the
`Level` type so that it is not an element of a universe, or not
allowed at all (see further discussion of this below).
```agda
import Definition.Typed.Restrictions using (Type-restrictions)
```

The type system. Some typing rules have names that differ from those
in the paper. The definitions use the relations `_⊢_∷Level` and
`_⊢_≡_∷Level` to support disallowing `Level` entirely: in the case
where `Level` is allowed `Γ ⊢ t ∷Level` is equivalent to
`Γ ⊢ t ∷ Level`, and similarly for `_⊢_≡_∷Level`.
```agda
import Definition.Typed
  using
    (⊢_; _⊢_; _⊢_≡_; _⊢_∷_; _⊢_≡_∷_; _⊢_≤_∷Level;
     _⊢_∷Level; _⊢_≡_∷Level)
```

The ordering of levels induced by `_supᵘ_` is reflexive, transitive and
antisymmetric.
```agda
import Definition.Typed.Properties.Admissible.Level
  using (⊢≤-refl; ⊢≤-trans; ⊢≤-antisymmetric)
```

The typing rule for `Lift` that uses the ordering of levels is admissible.
```agda
import Definition.Typed.Properties.Admissible.Lift
  using (Liftⱼ≤)
```

Admissible heterogeneous Π- and Σ-types.
```agda
import Definition.Typed.Properties.Admissible.Pi-Sigma
  using (⊢ΠΣʰ; ΠΣʰ-cong-⊢; ⊢ΠΣʰ∷; ΠΣʰ-cong-⊢∷)
import Definition.Typed.Properties.Admissible.Pi
  using (⊢lamʰ; ⊢∘ʰ; app-congʰ; β-redʰ; η-eqʰ)
import Definition.Typed.Properties.Admissible.Sigma using
  (⊢prodʰ; prodʰ-cong;
   ⊢fstʰ; ⊢sndʰ; fstʰ-cong; sndʰ-cong; Σʰ-β₁; Σʰ-β₂; Σʰ-η;
   ⊢prodrecʰ⟨⟩; prodrecʰ⟨⟩-cong; prodrecʰ⟨⟩-β)
```

Lemma 2.1: well-formedness and subject reduction.
```agda
import Definition.Typed.Syntactic
  using (syntacticTerm; syntacticRedTerm)
```

#### 2.3: Reduction rules

```agda
import Definition.Typed using (_⊢_⇒_∷_; _⊢_⇒*_∷_)
```

Compared to the paper, we use `Neutral` instead of Neutralᵃ for
atomic neutrals and `Neutralˡ` instead of Neutral for neutrals
possibly including `_supᵘ_`.
```agda
import Definition.Untyped.Neutral using (Neutral; Neutralˡ; Whnf)
```

### 3: A logical relation

The external universe level hierarchy ω + 1.
```agda
import Definition.Untyped.NotParametrised using (Universe-level)
```

The generic equality relations.
```agda
import Definition.Typed.EqualityRelation
```

The equality relation instance for judgemental equality.
```agda
import Definition.Typed.EqRelInstance
```

#### 3.1: Reducible levels and neutrals

We write `Γ ⊩Level t ∷Level` instead of Γ ⊩Lvl t, `Level-prop Γ t`
instead of Γ ⊩Lvl_w t, `neLevel-prop Γ t` instead of Γ ⊩Lvlₙ t, and
similarly for equalities.
```agda
import Definition.LogicalRelation
  using (_⊩neNf_≡_∷_; _⊩Level_∷Level; Level-prop; neLevel-prop)
```

Unary versions of the logical relations.
```agda
import Definition.LogicalRelation.Unary using (_⊩neNf_∷_)
```

The realiser of a reducible level t is written `↑ᵘ [t]`, where `[t]` is
a witness that t is reducible.
```agda
import Definition.LogicalRelation using (↑ᵘ_)
```

Irrelevance for `↑ᵘ_`; `↑ᵘ_` respects equality and ordering.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (↑ᵘ-irrelevance; ↑ᵘ-cong; ↑ᵘ-cong-≤)
```

The function `_supᵘ_` respects equality in its first argument.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (⊩supᵘ-congˡ)
```

Lemma 3.1: The typing rule for `_supᵘ_` is reducible.
```agda
import Definition.LogicalRelation.Properties.Primitive using (⊩supᵘ)
```

Lemma 3.2: The judgemental equality supᵘ-idem is reducible.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (⊩supᵘ-idem)
```

#### 3.2: Reducibility

The main reducibility judgements are written `Γ ⊩⟨ ℓ ⟩ 𝒥`, where `𝒥` is
one of the four forms of judgement.
```agda
import Definition.LogicalRelation
  using (_⊩⟨_⟩_; _⊩⟨_⟩_≡_/_; _⊩⟨_⟩_∷_/_; _⊩⟨_⟩_≡_∷_/_)
```

The logical relation is cumulative.
```agda
import Definition.LogicalRelation.Properties.Embedding
```

Versions of reducibility judgements with hidden reducibility arguments.
```agda
import Definition.LogicalRelation.Hidden
  using (_⊩⟨_⟩_≡_; _⊩⟨_⟩_∷_; _⊩⟨_⟩_≡_∷_)
```

Irrelevance for reducibility judgements, justifying the hidden versions
above.
```agda
import Definition.LogicalRelation.Irrelevance
```

#### 3.3 Validity and the fundamental lemma

`Γ ⊩⟨ ℓ ⟩ 𝒥` implies `Γ ⊢ 𝒥`.
```agda
import Definition.LogicalRelation.Properties.Escape
```

Validity judgements.
```agda
import Definition.LogicalRelation.Substitution using
  (⊩ᵛ_; _⊩ᵛ⟨_⟩_; _⊩ᵛ⟨_⟩_≡_; _⊩ˢ_≡_∷_; _⊩ˢ_∷_; _⊩ᵛ⟨_⟩_≡_∷_; _⊩ᵛ⟨_⟩_∷_)
```

Lemma 3.3: Fundamental lemma.
```agda
import Definition.LogicalRelation.Fundamental
```

Lemma 3.4: The term typing rule for U is valid.
```agda
import Definition.LogicalRelation.Substitution.Introductions.Universe
  using (⊩ᵛU∷U)
```

Lemma 3.5: The typing rule univ is valid.
```agda
import Definition.LogicalRelation.Substitution.Introductions.Universe
  using (⊩ᵛ∷U→⊩ᵛ)
```

Lemma 3.6: The term typing rule for Lift is valid.
```agda
import Definition.LogicalRelation.Substitution.Introductions.Lift
  using (Liftᵗᵛ)
```

Lemma 3.7: The term typing rule for Π is valid.
```agda
import Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma
  using (ΠΣᵗᵛ)
```

Corollary 3.8: Well-typed objects are reducible.
```agda
import Definition.LogicalRelation.Fundamental.Reducibility
```

Atomic neutrals are reducible.
```agda
import Definition.LogicalRelation.Properties.Neutral
```

Corollary 3.9: Consistency.
```agda
import Definition.Typed.Consequences.Canonicity using (¬Empty)
```

Corollary 3.10: Canonicity.
```agda
import Definition.Typed.Consequences.Canonicity using (canonicity)
```

Corollary 3.11: Weak head normalisation.
```agda
import Definition.Typed.Consequences.Reduction
  using (whNorm; whNormTerm)
```

Corollary 3.12: Injectivity of type formers.
```agda
import Definition.Typed.Consequences.Injectivity
```

### 4: Decidability of equality

Algorithmic equality. The conversion relations are denoted as follows:
* `Γ ⊢ A [conv↑] B` and `Γ ⊢ A [conv↓] B` for arbitrary types and
  types in WHNF, respectively,
* `Γ ⊢ t [conv↑] u ∷ A` and `Γ ⊢ t [conv↓] u ∷ B` for arbitrary terms with arbitrary types,
  and terms in WHNF with types in WHNF, respectively, and
* `Γ ⊢ t ~ u ↑ A` and `Γ ⊢ t ~ u ↓ A` for atomic neutral terms and
  atomic neutral terms with types in WHNF, respectively.
```agda
import Definition.Conversion using
  (_⊢_[conv↑]_; _⊢_[conv↓]_; _⊢_[conv↑]_∷_; _⊢_[conv↓]_∷_;
   _⊢_~_↑_; _⊢_~_↓_)
```

Level atoms and views.
```agda
import Definition.Conversion using (LevelAtom; Level⁺; Levelᵛ)
```

Level view comparison.
```agda
import Definition.Conversion using (_≡ᵛ_; ≤ᵛ)
```

Operations on level views.
```agda
import Definition.Conversion using (sucᵛ; supᵛ)
```

Normalising levels into level views.
```agda
import Definition.Conversion using (_⊢_↑ᵛ_; _⊢_↓ᵛ_; _⊢_~ᵛ_)
```

Algorithmic equality is sound.
```agda
import Definition.Conversion.Soundness
```

Algorithmic equality is stable under weakening.
```agda
import Definition.Conversion.Weakening
```

Algorithmic equality is decidable.
```agda
import Definition.Conversion.Decidable
```

Level normalisation is deterministic.
```agda
import Definition.Conversion.Level using (deterministic-↑ᵛ)
```

Lemma 4.1.
```agda
open import Definition.Conversion.EqRelInstance using (module Lemmas)
open Lemmas using (supᵘ-↑ᵛ)
```

Lemma 4.2: Algorithmic equality is complete for judgemental equality.
```agda
import Definition.Conversion.Consequences.Completeness
```

Corollary 4.3: Judgemental equality of well-formed types and terms is
decidable.
```agda
import Definition.Typed.Decidable.Equality
```

Corollary 4.4: Typing is decidable for a certain subset of Checkable
types and terms.
```agda
import Definition.Typechecking using (Checkable)
import Definition.Typed.Decidable
```

Corollary 4.5: Deep normalisation.
```agda
import Definition.Typed.Eta-long-normal-form
import Definition.Conversion.FullReduction using (fullRed)
```

### 5: Erasing levels is safe

The usage relation.
```agda
import Graded.Usage using (_▸[_]_)
```

Usage contexts.
```agda
import Graded.Context using (Conₘ)
```

Modes. The development supports modalities with or without the zero
mode.
```agda
import Graded.Mode using (Mode)
```

The erasure modality. The development supports two variants of the
erasure modality: with or without support for the zero mode. When the
paper refers to "the erasure modality" it is the one with support for
the zero mode that is meant.

```agda
import Graded.Modality.Instances.Erasure using (𝟘; ω)
import Graded.Modality.Instances.Erasure.Modality
  using (ErasureModality)
```

The target language. The predicate Valueˢ is called `Value⟨ s ⟩`, sucˢ
is called `suc⟨ s ⟩`, ↯ˢ is called `loop? s`, ⇒ˢᵘᶜ is called `_⇒ˢ_`,
_⊢_⟶ˢᵘᶜ_:ℕ is called `_⊢_⇒ˢ_∷ℕ`, _⊢_⟶ˢᵘᶜ*_:ℕ is called `_⊢_⇒ˢ*_∷ℕ`,
⇒*ₛ is called `_⇒ˢ⟨_⟩*_`, and n̲ is called `sucᵏ n`. The term loop
corresponds to `loop non-strict`.
```agda
import Graded.Erasure.Target
  using (Term; Strictness; Value; Value⟨_⟩; _⇒_; suc⟨_⟩; sucᵏ)
import Definition.Untyped using (sucᵏ)
import Graded.Erasure.Target.Non-terminating using (loop)
import Graded.Erasure.Extraction using (loop?; erase)
import Graded.Erasure.SucRed using (_⇒ˢ_; _⊢_⇒ˢ_∷ℕ; _⊢_⇒ˢ*_∷ℕ; _⇒ˢ⟨_⟩*_)
```

Complete removal of all arguments can, in the strict setting, lead to
non-termination for the extracted program.
```agda
import Graded.Erasure.Extraction.Non-terminating
```

Theorem 5.1: Soundness of erasure. The paper uses the formulation
"erased matches are disallowed for weak Σ and unit types", but the
code uses the formulation "if the modality is non-trivial, then erased
matches are disallowed for weak Σ and unit types as well as the
identity type": the paper focuses on the erasure modality, which is
non-trivial, and identity types are mostly ignored in the text. The
statement in the code also has the condition "equality reflection is
disallowed or the context is empty".
```agda
import Graded.Erasure.Consequences.Soundness
theorem-5-1 =
  Graded.Erasure.Consequences.Soundness.Soundness.soundness-ℕ
```

Corollary 5.2: Soundness of erasure for closed terms.
```agda
corollary-5-2 =
  Graded.Erasure.Consequences.Soundness.Soundness₀.soundness-ℕ
```

Some counterexamples to variants of Theorem 5.1, one for the case
where erased matches are allowed for weak Σ-types, and one for the
case where erased matches are allowed for the empty type and the
context is allowed to be inconsistent.
```agda
import Graded.Erasure.Consequences.Soundness using
  (soundness-ℕ-only-source-counterexample₁; soundness-ℕ-counterexample₆)
```

Some examples, including a universe-polymorphic identity function.
```agda
import Graded.Erasure.Examples using (⊢id)
```

## Additional results

Some features were added to the formalisation after the paper was
submitted.

There is now a parameter `level-support` that can take one of the
following three values:

* `only-literals`: The `Level` type is disallowed, and only level
  literals are allowed.

* `level-type small`: The `Level` type is allowed and has type
  `U zeroᵘ`. If this setting is used, then the type `Level-is-small`
  is inhabited.

* `level-type not-small`: The `Level` type is allowed, but does not
  belong to the first (or any) universe. If this setting is used, then
  the type `Level-is-not-small` is inhabited.

  Using this setting is similar to enabling Agda's `--level-universe`
  flag, which makes `Level` an element of a separate universe
  `LevelUniv` instead of `Set`. A notable difference is that Agda
  disallows forming identity types of types in `LevelUniv`, whereas
  our type theory has identity type formation rules for every type.

If either of the two last settings are used, then the type
`Level-allowed` is inhabited. The results in the paper do not depend
on whether `Level` is small or not.
```agda
open Definition.Typed.Restrictions.Type-restrictions
  using
    (level-support; Level-is-small; Level-is-not-small; Level-allowed)

import Definition.Typed.Properties.Admissible.Level
  using (¬Level-is-small→¬Level∷U)
```

Canonicity is proved for natural number terms in contexts where the
type of every variable is either `Level` or `U t` for some `t`.
```agda
import Definition.Typed.Consequences.Canonicity
  using (canonicity-Only-Level-or-U)
```
