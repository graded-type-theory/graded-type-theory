# An Agda Formalisation of a Graded Modal Type Theory with First-Class Universe Levels and Erasure

This code is related to the paper "Normalisation for First-Class
Universe Levels", Nils Anders Danielsson, Naïm Camille Favier and
Ondřej Kubánek, Proceedings of the ACM on Programming Languages,
Volume 10, Issue POPL, 2026
([doi:10.1145/3776645](https://doi.org/10.1145/3776645)). It builds on
an existing formalisation, see "Project history" below.

## Dependencies and licences

The code depends on some libraries:

* Agda's standard library, version 2.3
  ([licence](https://github.com/agda/agda-stdlib/blob/v2.3/LICENCE)).
* The builtin modules that are shipped with Agda 2.8.0
  ([licence](https://github.com/agda/agda/blob/v2.8.0/LICENSE)).

When HTML code is generated from this file code is also generated for
the two libraries above, so links (which are up-to-date at the time of
writing) to their licences are included above.

The licence for this project can be found in the file `LICENSE`.

## Type-checking

To type-check everything in the formalisation, including this file,
you can run the following command (assuming that `agda` refers to a
suitable version of Agda set up with a suitable version of its
standard library):
```sh
agda Everything.agda
```
The file `graded-type-theory.agda-lib` includes the flag `--safe`,
which disallows things like postulates, turning off the termination
checker, and so on.

## Project history

This formalisation originated as a fork of
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

The formalisation was lifted to graded modal type theory: this is the
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

```agda
module README where
```

Below pointers to code are included for all the main definitions,
theorems, etc. in the paper, along with some discussion of
differences between the paper and the code.

### 2: A Type Theory with First-Class Universe Levels

#### 2.1: Syntax

Note that large parts of the development are parametrised by a grade
type or a modality. Grades and modalities are to a large part ignored
in the paper. If one does not care about grades, then one can use a
unit type or a trivial modality:
```agda
import Graded.Modality.Instances.Unit
  using (UnitModality)
```

Terms. The notation does not match the paper exactly. The notation
`zeroᵘ` is used for 0, `sucᵘ` for \_⁺, and `_supᵘ_` for \_⊔\_. Instead
of a constructor Π for Π-types there is a constructor `ΠΣ⟨_⟩_,_▷_▹_`
for *graded* Π- and Σ-types, and the constructors for lambdas and
applications also take grades. The derived notation k + t is denoted
by `sucᵘᵏ k t`, and ↓ k is denoted by `↓ᵘ k`.
```agda
import Definition.Untyped
  using (Term; sucᵘᵏ; ↓ᵘ_)
```

Contexts. The type is more general than in the paper: the
instantiation `Con Term` corresponds to what is called Con in the
paper. Furthermore the notation does not match that used in the paper:
the notation `ε` is used for ·, and `_∙_` is used instead of \_,\_.
```agda
import Definition.Untyped
  using (Con)
```

Substitution.
```agda
import Definition.Untyped
  using (_[_])
```

Weakening. The notation `wk ρ t` is used instead of t[ρ], and the
notation `ρ ∷ʷ Δ ⊇ Γ` means that ρ is a well-formed weakening from Γ
to Δ (Δ ⊢ ρ : Γ in the paper). The single-step weakening p is written
`step id`: in the code this weakening is often used via
`wk1` = `wk (step id)`, and the lemmas `wk₁` and `wkTerm₁` show that
this operation is type-preserving.
```agda
import Definition.Untyped
  using (wk; step; id; wk1)
import Definition.Typed.Weakening
  using (_∷ʷ_⊇_; wk₁; wkTerm₁)
```

#### 2.2: Typing Rules

Unlike in the paper the type system is parametrised by a value of type
`Type-restrictions` that makes it possible to disallow certain things,
like certain (graded) Π- or Σ-types, the K rule or equality
reflection. For instance, the two typing rules for Π and Σ include the
assumption `ΠΣ-allowed b p q`.
```agda
import Definition.Typed.Restrictions
  using (Type-restrictions)
```

It is also possible to restrict the `Level` type so that it is not an
element of a universe, or not allowed at all. There is a parameter
`level-support` that can take one of the following three values:

* `only-literals`: The `Level` type is disallowed, and only level
  literals are allowed.

* `level-type small`: The `Level` type is allowed and has type
  `U zeroᵘ`. If this setting is used, then the type `Level-is-small`
  is inhabited.

* `level-type not-small`: The `Level` type is allowed, but does not
  belong to the first (or any) universe. If this setting is used, then
  the type `Level-is-not-small` is inhabited.

If either of the two last settings are used, then the type
`Level-allowed` is inhabited.
```agda
open Definition.Typed.Restrictions.Type-restrictions
  using
    (level-support; Level-is-small; Level-is-not-small; Level-allowed)
```

The variant of the type theory in which `Level` is allowed but not
small is similar to what one gets by enabling Agda's
`--level-universe` flag, which makes `Level` an element of a separate
universe `LevelUniv` instead of `Set`. A notable difference is that
Agda disallows forming identity types of types in `LevelUniv`, whereas
our type theory has identity type formation rules for every type. If
`Level` is allowed, then `Id Level t u` is a well-formed type when `t`
and `u` are well-typed levels, whether `Level` is small or not. No
result in the paper depends on whether `Level` is small or not, except
for the following one: if `Level` is not small, then `Id Level t u`
does not live in a universe.
```agda
import Definition.Typed.Properties.Admissible.Level
  using (⊢Id-Level; ¬Level-is-small→¬Level∷U)
```

The type system. Some typing rules have names that differ from those
in the paper. Γ ∋ x : A is denoted by `x ∷ A ∈ Γ`. The definitions use
the relations `_⊢_∷Level` and `_⊢_≡_∷Level` to support disallowing
`Level` entirely: in the case where `Level` is allowed `Γ ⊢ t ∷Level`
is logically equivalent to `Γ ⊢ t ∷ Level`, and similarly for
`_⊢_≡_∷Level`.
```agda
import Definition.Typed
  using
    (⊢_; _⊢_; _⊢_≡_; _⊢_∷_; _⊢_≡_∷_; _∷_∈_; _⊢_≤_∷Level;
     _⊢_∷Level; _⊢_≡_∷Level)
```

The ordering of levels induced by `_supᵘ_` is reflexive, transitive and
antisymmetric, and the right identity rule can be derived.
```agda
import Definition.Typed.Properties.Admissible.Level
  using (⊢≤-refl; ⊢≤-trans; ⊢≤-antisymmetric; supᵘ-zeroʳⱼ)
```

The typing rule for `Lift` that uses the ordering of levels is
admissible.
```agda
import Definition.Typed.Properties.Admissible.Lift
  using (Liftⱼ≤)
```

The type of the universe-polymorphic identity function does not live
in any universe, and "Π U₀ U₁" does not have a type.
```agda
import Definition.Typed.Consequences.Universe
  using (the-type-of-id-does-not-have-a-type; type-without-type)
```

Admissible typing rules for heterogeneous Π- and Σ-types.
```agda
import Definition.Typed.Properties.Admissible.Pi-Sigma
  using (⊢ΠΣʰ; ΠΣʰ-cong-⊢; ⊢ΠΣʰ∷; ΠΣʰ-cong-⊢∷)
import Definition.Typed.Properties.Admissible.Pi
  using (⊢lamʰ; ⊢∘ʰ; app-congʰ; β-redʰ; η-eqʰ)
import Definition.Typed.Properties.Admissible.Sigma
  using
    (⊢prodʰ; prodʰ-cong;
     ⊢fstʰ; ⊢sndʰ; fstʰ-cong; sndʰ-cong; Σʰ-β₁; Σʰ-β₂; Σʰ-η;
     ⊢prodrecʰ⟨⟩; prodrecʰ⟨⟩-cong; prodrecʰ⟨⟩-β)
```

The type of natural numbers does not have type `U (sucᵘ l)`.
```agda
import Definition.Typed.Consequences.Inequality
  using (¬ℕ∷U-sucᵘ)
```

#### 2.3: Reduction Rules

Single-step reduction and reduction for terms and types.
```agda
import Definition.Typed
  using (_⊢_⇒_∷_; _⊢_⇒*_∷_; _⊢_⇒_; _⊢_⇒*_)
```

Neutral terms and WHNFs. Compared to the paper, we use `Neutral`
instead of Neutralᵃ for atomic neutrals and `Neutralˡ` instead of
Neutral.
```agda
import Definition.Untyped.Neutral
  using (Neutral; Neutralˡ; Whnf)
```

Lemma 2.1: Well-formedness.
```agda
import Definition.Typed.Properties
  using (wf; wfEq; wfTerm; wfEqTerm)
import Definition.Typed.Well-formed
  using (wf-⊢≡; wf-⊢∷; wf-⊢≡∷)
import Definition.Typed.Syntactic
  using (syntacticRed; syntacticRedTerm)
```

### 3: A Logical Relation

External universe levels (natural numbers or ω).
```agda
import Definition.Untyped.NotParametrised
  using (Universe-level)
```

The generic equality relations. Compared to the paper we include an
extra relation for levels, to support disallowing `Level` entirely. We
also include the type `Neutrals-included`, which is used to handle
equality reflection: in the absence of equality reflection one can
instantiate this type with something inhabited.
```agda
open import Definition.Typed.EqualityRelation
  using (EqRelSet)
open EqRelSet
  using (Neutrals-included)
```

The generic equality relation instance for judgemental equality. Note
that `Neutrals-included` is instantiated to `No-equality-reflection`.
```agda
import Definition.Typed.EqRelInstance
  using (eqRelInstance)
```

#### 3.1: Reducible Levels and Neutrals

We use the notations `Γ ⊩neNf t ∷ A` and `Γ ⊩neNf t ≡ u ∷ A` instead
of Γ ⊩neNf t : A and Γ ⊩neNf t = u : A, `Γ ⊩Level t ∷Level` and
`Γ ⊩Level t ≡ u ∷Level` instead of Γ ⊩Lvl t and Γ ⊩Lvl t = u,
`Level-prop Γ t` and `[Level]-prop Γ t u` instead of Γ ⊩Lvl\_w t and
Γ ⊩Lvl\_w t = u, and `neLevel-prop Γ t` and `[neLevel]-prop Γ t u`
instead of Γ ⊩Lvlₙ t and Γ ⊩Lvlₙ t = u. The code sometimes uses
`Γ ⊩neNf t ≡ t ∷ A` instead of `Γ ⊩neNf t ∷ A`: these definitions are
logically equivalent.
```agda
import Definition.LogicalRelation.Unary
  using (_⊩neNf_∷_; ⊩neNf∷⇔⊩neNf≡∷)
import Definition.LogicalRelation
  using
    (_⊩neNf_≡_∷_;
     _⊩Level_∷Level; _⊩Level_≡_∷Level;
     Level-prop; [Level]-prop;
     neLevel-prop; [neLevel]-prop)
```

If `Level-prop Γ t` holds, then `t` is in WHNF, if `neLevel-prop Γ t`
holds, then `t` is neutral, and similarly for the corresponding binary
predicates.
```agda
import Definition.LogicalRelation.Properties.Whnf
  using (level; nelevel; lsplit; nelsplit)
```

The natural number realising a reducible level t is written `↑ⁿ [t]`,
where `[t]` is a witness that t is reducible. The corresponding
external level is written `↑ᵘ [t]`.
```agda
import Definition.LogicalRelation
  using (↑ⁿ_; ↑ᵘ_)
```

The natural number realiser satisfies the specification given in the
paper, and any function that satisfies the specification is pointwise
equal to the realiser.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (↑ⁿ-respects-⇒*; ↑ⁿ-zeroᵘ; ↑ⁿ-sucᵘ; ↑ⁿ-supᵘ′; ↑ⁿ-ne; ↑ⁿ-unique)
```

Irrelevance for `↑ⁿ_` and `↑ᵘ_`; `↑ⁿ_` and `↑ᵘ_` respect equality and
ordering.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using
    (↑ⁿ-irrelevance; ↑ᵘ-irrelevance;
     ↑ⁿ-cong; ↑ᵘ-cong;
     ↑ⁿ-cong-≤; ↑ᵘ-cong-≤)
```

The function `_supᵘ_` respects equality in its first argument.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (⊩supᵘ-congˡ)
```

Lemma 3.1: Reducibility for the typing rule for `_supᵘ_`.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (⊩supᵘ)
```

Lemma 3.2: Reducibility for the judgemental equality rule supᵘ-idem.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (⊩supᵘ-idem)
```

Two weak head expansion lemmas used in Lemmas 3.1 and 3.2.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (⊩Level-⇒*; redLevel′)
```

#### 3.2: Reducibility

The main reducibility judgements.
```agda
import Definition.LogicalRelation
  using (_⊩⟨_⟩_; _⊩⟨_⟩_≡_/_; _⊩⟨_⟩_≡_∷_/_; _⊩⟨_⟩_∷_/_)
```

The logical relation is cumulative.
```agda
import Definition.LogicalRelation.Properties.Embedding
  using (emb-≤-⊩; emb-≤-⊩≡; emb-≤-⊩≡∷; emb-≤-⊩∷)
```

Reducibility for neutrals.
```agda
import Definition.LogicalRelation
  using (_⊩ne_; _⊩ne_≡_/_; _⊩ne_≡_∷_/_)
```

Reducibility for levels.
```agda
import Definition.LogicalRelation
  using (_⊩Level_; _⊩Level_≡_; _⊩Level_≡_∷Level)
```

Level reflexivity and well-formedness.
```agda
import Definition.LogicalRelation.Properties.Primitive
  using (reflLevel; wf-Level-eq)
```

Reducibility for universes.
```agda
open import Definition.LogicalRelation
  using (module LogRel)
open LogRel
  using (_⊩₁U_; _⊩₁U≡_/_; _⊩₁U_≡_∷U/_)
```

Types in WHNF.
```agda
import Definition.Untyped.Neutral
  using (Type)
```

Reducibility for lift types.
```agda
open LogRel
  using (_⊩ₗLift_; _⊩ₗLift_≡_/_; _⊩ₗLift_≡_∷_/_)
```

Reducibility for Π-types (the first two definitions are used also for
Σ-types).
```agda
open LogRel
  using (_⊩ₗB⟨_⟩_; _⊩ₗB⟨_⟩_≡_/_; _⊩ₗΠ_≡_∷_/_)
```

Well-formed weakenings were introduced above. The definition of the
logical relation uses a variant of this definition which is logically
equivalent if `Neutrals-included` is inhabited.
```agda
import Definition.LogicalRelation.Weakening.Restricted
  using (_∷ʷʳ_⊇_; ∷ʷ⊇→∷ʷʳ⊇; ∷ʷʳ⊇→∷ʷ⊇)
```

Lifting of weakenings is denoted by `lift` rather than \_⇑ (which is
used for substitutions).
```agda
import Definition.Untyped.NotParametrised
  using (lift)
import Definition.Typed.Weakening
  using (liftʷ)
```

Irrelevance for reducibility judgements.
```agda
import Definition.LogicalRelation.Irrelevance
  using (irrelevanceEq; irrelevanceEqTerm; irrelevanceTerm)
```

Reducibility judgements with hidden reducibility arguments.
```agda
import Definition.LogicalRelation.Hidden
  using (_⊩⟨_⟩_∷_; _⊩⟨_⟩_≡_∷_; _⊩⟨_⟩_≡_)
```

#### 3.3 Validity and the Fundamental Lemma

`Γ ⊩⟨ ℓ ⟩ 𝒥` implies `Γ ⊢ 𝒥`.
```agda
import Definition.LogicalRelation.Properties.Escape
  using (escape; escapeEq; escapeTerm; escapeTermEq)
```

Validity judgements. In addition to the ones in the paper we also use
`Γ ⊩ᵛ⟨ ℓ ⟩ t ∷Level` and `Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷Level`, which are logically
equivalent to `Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level` and `Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ Level`,
respectively, when the `Level` type is allowed.
```agda
import Definition.LogicalRelation.Substitution
  using
    (⊩ᵛ_; _⊩ᵛ⟨_⟩_; _⊩ᵛ⟨_⟩_≡_; _⊩ˢ_∷_; _⊩ˢ_≡_∷_; _⊩ᵛ⟨_⟩_∷_; _⊩ᵛ⟨_⟩_≡_∷_;
     _⊩ᵛ⟨_⟩_∷Level; _⊩ᵛ⟨_⟩_≡_∷Level; ⊩ᵛ∷L⇔; ⊩ᵛ≡∷L⇔)
```

Lemma 3.3: Fundamental lemma.
```agda
import Definition.LogicalRelation.Fundamental
  using
    (valid;
     fundamental-⊩ᵛ; fundamental-⊩ᵛ≡; fundamental-⊩ᵛ∷; fundamental-⊩ᵛ≡∷)
```

Lemma 3.4: Validity for the term typing rule for U. The proof sketch
given in the paper does not quite match the proof used here: this
proof goes via a corresponding proof for binary validity. Similar
comments apply to Lemmas 3.5 and 3.6 below.
```agda
import Definition.LogicalRelation.Substitution.Introductions.Universe
  using (⊩ᵛU∷U)
```

Lemma 3.5: Validity for the typing rule univ.
```agda
import Definition.LogicalRelation.Substitution.Introductions.Universe
  using (⊩ᵛ∷U→⊩ᵛ)
```

Lemma 3.6: Validity for the term typing rule for Lift.
```agda
import Definition.LogicalRelation.Substitution.Introductions.Lift
  using (Liftᵗᵛ)
```

Lemma 3.7: Validity for the term typing rule for Π.
```agda
import Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma
  using (ΠΣᵗᵛ)
```

Level realisers are stable under weakening.
```agda
import Definition.LogicalRelation.Weakening
  using (wk-↑ⁿ; wk-↑ᵘ)
```

Corollary 3.8: Well-typed objects are reducible.
```agda
import Definition.LogicalRelation.Fundamental.Reducibility
  using (reducible-⊩; reducible-⊩≡; reducible-⊩∷; reducible-⊩≡∷)
```

The identity substitution is reducible.
```agda
import Definition.LogicalRelation.Substitution
  using (⊩ˢ∷-idSubst)
```

Atomic neutrals are reducible.
```agda
import Definition.LogicalRelation.Properties.Neutral
```

Corollary 3.9: Consistency.
```agda
import Definition.Typed.Consequences.Canonicity
  using (¬Empty)
```

Corollary 3.10: Canonicity.
```agda
import Definition.Typed.Consequences.Canonicity
  using (canonicity)
```

Corollary 3.11: Weak head normalisation.
```agda
import Definition.Typed.Consequences.Reduction
  using (whNorm; whNormTerm)
```

Corollary 3.12: Injectivity of and non-confusion for type formers.
More lemmas of this kind can be found in the given modules. Statements
of the form "`A` is not derivable" are interpreted as `¬ A`; note that
if Agda is inconsistent, then `¬ A` and `A` might both be inhabited.
```agda
import Definition.Typed.Consequences.Injectivity
  using
    (U-injectivity; Lift-injectivity;
     ΠΣ-injectivity-no-equality-reflection)
import Definition.Typed.Consequences.Inequality
  using (Level≢ℕ; U≢ℕ)
```

Corollary 3.13: Canonicity for contexts that only contain level and
type variables.
```agda
import Definition.Typed.Consequences.Canonicity
  using (canonicity-Only-Level-or-U)
```

### 4: Decidability of Equality

Algorithmic equality. The conversion relations are denoted as follows:
* `Γ ⊢ A [conv↑] B` and `Γ ⊢ A [conv↓] B` for arbitrary types and
  types in WHNF, respectively,
* `Γ ⊢ t [conv↑] u ∷ A` and `Γ ⊢ t [conv↓] u ∷ B` for arbitrary terms
  with arbitrary types, and terms in WHNF with types in WHNF,
  respectively, and
* `Γ ⊢ t ~ u ↑ A` and `Γ ⊢ t ~ u ↓ A` for atomic neutral terms and
  atomic neutral terms with types in WHNF, respectively.
```agda
import Definition.Conversion
  using
    (_⊢_[conv↑]_; _⊢_[conv↓]_; _⊢_[conv↑]_∷_; _⊢_[conv↓]_∷_;
     _⊢_~_↑_; _⊢_~_↓_)
```

Level atoms, `Level⁺` and level views.
```agda
import Definition.Conversion
  using (LevelAtom; Level⁺; Levelᵛ)
```

Level view comparison.
```agda
import Definition.Conversion
  using (_≡ᵛ_; ≤ᵛ; ≤⁺ᵛ; ≤⁺; ≤ᵃ)
```

Operations on level views.
```agda
import Definition.Conversion
  using (sucᵛ; supᵛ)
```

Normalising levels into level views.
```agda
import Definition.Conversion
  using (_⊢_↑ᵛ_; _⊢_↓ᵛ_; _⊢_~ᵛ_)
```

Algorithmic equality is sound.
```agda
import Definition.Conversion.Soundness
  using
    (soundnessConv↑; soundnessConv↓;
     soundnessConv↑Term; soundnessConv↓Term;
     soundness~↑; soundness~↓)
```

Algorithmic equality is stable under weakening.
```agda
import Definition.Conversion.Weakening
  using (wkConv↑; wkConv↓; wkConv↑Term; wkConv↓Term; wk~↑; wk~↓)
```

Algorithmic equality is decidable.
```agda
import Definition.Conversion.Decidable
  using (decConv↑; decConv↓; decConv↑Term; decConv↓Term; dec~↑; dec~↓)
```

Level normalisation is deterministic.
```agda
import Definition.Conversion.Level
  using (deterministic-↑ᵛ)
```

Lemma 4.1.
```agda
open import Definition.Conversion.EqRelInstance
  using (module Lemmas)
open Lemmas
  using (supᵘ-↑ᵛ)
```

The generic equality relation instance for algorithmic equality.
```agda
import Definition.Conversion.EqRelInstance
  using (eqRelInstance)
```

Theorem 4.2: Algorithmic equality is complete with respect to
judgemental equality.
```agda
import Definition.Conversion.Consequences.Completeness
  using (completeEq; completeEqTerm)
```

Corollary 4.3: Judgemental equality of well-formed types and terms is
decidable.
```agda
import Definition.Typed.Decidable.Equality
  using (decEq; decEqTerm)
```

Corollary 4.4: Deep normalisation.
```agda
import Definition.Conversion.FullReduction
  using (fullRed; fullRedTerm)
```

Checkable types, checkable terms and inferable terms. The code also
makes use of `Checkable-level`. If `Level` is allowed, then
`Checkable-level t` is logically equivalent to `Checkable t`.
```agda
import Definition.Typechecking
  using (Checkable-type; Checkable; Inferable; Checkable-level)
```

The term Π (λ x₀) x₀ is a checkable type but not a checkable term.
Every well-formed, checkable type is inferable.
```agda
import Definition.Typechecking
  using (Checkable-type×¬Checkable; ⊢→Checkable-type→Inferable)
```

Theorem 4.5: Decidability of type checking/type inference for certain
classes of terms, types and contexts.
```agda
import Definition.Typed.Decidable
  using (decWfCon; decConTypeᶜ; decConTermTypeᶜ; decConTermᵢ)
```

### 5: Erasing Levels Is Safe

The usage relation. This relation is parametrised by a value of type
`Usage-restrictions`, which for instance makes it possible to disallow
several forms of erased matches.
```agda
import Graded.Usage
  using (_▸[_]_)
import Graded.Usage.Restrictions
  using (Usage-restrictions)
```

Usage contexts.
```agda
import Graded.Context
  using (Conₘ)
```

Modes. The development supports modalities with or without the zero
mode.
```agda
import Graded.Mode
  using (Mode)
```

The erasure modality. The development supports two variants of the
erasure modality: with or without support for the zero mode. When the
paper refers to "the erasure modality" it is the one with support for
the zero mode that is meant.
```agda
import Graded.Modality.Instances.Erasure
  using (𝟘; ω)
import Graded.Modality.Instances.Erasure.Modality
  using (ErasureModality)
```

The target language. The term appˢ t u is denoted by `t ∘⟨ s ⟩ u`, the
predicate Valueˢ is called `Value⟨ s ⟩`, sucˢ is called `suc⟨ s ⟩`, ↯ˢ
is called `loop? s`, ⇒ˢᵘᶜ is called `_⇒ˢ_`, \_⊢\_⟶ˢᵘᶜ\_:ℕ is called
`_⊢_⇒ˢ_∷ℕ`, \_⊢\_⟶ˢᵘᶜ\*\_:ℕ is called `_⊢_⇒ˢ*_∷ℕ`, ⇒\*ₛ is called
`_⇒ˢ⟨_⟩*_`, and n̲ is called `sucᵏ n`. The term loop corresponds to
`loop non-strict`.
```agda
import Graded.Erasure.Target
  using (Term; Strictness; Value; Value⟨_⟩; _⇒_; suc⟨_⟩; sucᵏ)
import Definition.Untyped
  using (sucᵏ)
import Graded.Erasure.Target.Non-terminating
  using (loop)
import Graded.Erasure.Extraction
  using (loop?)
import Graded.Erasure.SucRed
  using (_⇒ˢ_; _⊢_⇒ˢ_∷ℕ; _⊢_⇒ˢ*_∷ℕ; _⇒ˢ⟨_⟩*_)
```

The extraction function.
```agda
import Graded.Erasure.Extraction
  using (erase)
```

Complete removal of all arguments can, in the strict setting, lead to
non-termination for the extracted program.
```agda
import Graded.Erasure.Extraction.Non-terminating
  using (loops-reduces-forever; ⊢loops; ▸loops)
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
open import Graded.Erasure.Consequences.Soundness
open Soundness
  using (soundness-ℕ)
```

Corollary 5.2: Soundness of erasure for closed terms.
```agda
open Soundness₀
  using (soundness-ℕ)
```

Some counterexamples to variants of Theorem 5.1, one for the case
where erased matches are allowed for weak Σ-types, and one for the
case where erased matches are allowed for the empty type and the
context is allowed to be inconsistent.
```agda
import Graded.Erasure.Consequences.Soundness using
  (soundness-ℕ-only-source-counterexample₁; soundness-ℕ-counterexample₆)
```

### 6: Discussion and Future Work

The algorithmic η-equality rule for Lift, stability of algorithmic
equality under conversion, and lifting of algorithmic equality of
atomic neutrals with types in WHNF (`Γ ⊢ t ~ u ↓ A`) to algorithmic
equality of terms in WHNF (`Γ ⊢ t [conv↓] u ∷ A`).
```agda
open import Definition.Conversion
  using (module _⊢_[conv↓]_∷_)
open _⊢_[conv↓]_∷_
  using (Lift-η)
import Definition.Conversion.Conversion
  using (convConv↑Term; convConv↓Term)
import Definition.Conversion.Lift
  using (lift~toConv↓)
```

## More pointers to code

Some examples, including a universe-polymorphic identity function and
a universe-polymorphic encoding of vectors (lists of a given length).
```agda
import Graded.Erasure.Examples
  using (⊢id; ⊢Vec; ⊢head)
```
