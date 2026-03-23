```
{-# OPTIONS --infer-absurd-clauses #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module README.Opaque-definitions where

module ExampleLib where -- Utilities for the example code snippets
  open import Tools.Level renaming (_⊔_ to _⊔ₗ_)
  open import Tools.Nat renaming (Nat to ℕ; 1+ to suc) hiding (pred) public
  open import Tools.Product renaming (proj₁ to fst; proj₂ to snd) public
  open import Tools.PropositionalEquality public
  open import Tools.Relation using (¬_) public

  Σ-syntax : ∀ {ℓ ℓ′} (A : Set ℓ) (B : A → Set ℓ′) → Set (ℓ ⊔ₗ ℓ′)
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∷ A ] B
  infix 2 Σ-syntax

  data _>_ : ℕ → ℕ → Set where
    >zero : ∀ {n}           → suc n > 0
    >suc  : ∀ {m n} → m > n → suc m > suc n
```

# A Formalization of Opaque Definitions for a Dependent Type Theory

This document serves as a companion to the paper of the same name, linking the definitions and theorems used in the
paper to the relevant parts of the actual formalization codebase. Each entity listed here is accompanied by an Agda
snippet containing either relevant example code or a reference to the theorem in the main formalization. Any differences
between the formalism given in the paper and the actual formalization will also be mentioned.

Note that the listings in the paper reference previous snapshots of the formalization, whereas this document is intended
to live in the most up-to-date version. As such, some of the references below do not refer to the same code as is
referenced by the corresponding entity in the paper; instead, they'll refer to the code as it appears in this version.
This also means that there is some duplication below, since an entity referenced in two different snapshots by the paper
will both redirect to the same entity in this version.

Note also that this version of the code is not identical to the code that accompanies the paper
(doi:10.5281/zenodo.16906631). Some differences are mentioned below. One addition is a discussion of consistency in the
presence of opaque definitions:
```
import Definition.Typed.Consequences.Consistency
```

This document is a literate Agda document, which means it's also valid Agda source code! Try loading it in an editor
with good support for Agda to make navigating the references a bit easier.

## 1 Introduction

The first code snippet from the introduction, demonstrating definitions:
```
module DefinitionDemo where
  open ExampleLib

  double : ℕ → ℕ -- Doubles a natural
  double n = n + n

  quadruple : ℕ → ℕ -- Quadruples a natural
  quadruple n = double (double n)

  ℕ>0 : Set -- Positive naturals
  ℕ>0 = Σ[ n ∷ ℕ ] n > 0

  pred : ℕ>0 → ℕ -- Predecessor
  pred (suc n , >zero) = n
```

The "complex" example from the introduction, first without opaque definitions:
```
module IntroExample1 where
  open ExampleLib

  ℤ : Set -- Integers as differences of naturals
  ℤ = ℕ × ℕ

  _≡ℤ_ : ℤ → ℤ → Set -- Equality on integers
  x ≡ℤ y = fst x + snd y ≡ fst y + snd x

  _*ℤ_ : ℤ → ℤ → ℤ -- Integer multiplication
  x *ℤ y  = fst x * fst y + snd x * snd y
          , fst x * snd y + fst y * snd x

  infix 5 _≡ℤ_
  infixl 30 _*ℤ_

  0ℤ : ℤ -- Integer zero
  0ℤ = 0 , 0

  ℤ≠0 : Set -- Nonzero integers
  ℤ≠0 = Σ[ x ∷ ℤ ] ¬ x ≡ℤ 0ℤ

  ℚ : Set -- Rationals as the field of fractions
  ℚ = ℤ × ℤ≠0

  _≡ℚ_ : ℚ → ℚ → Set -- Equality on rationals
  x ≡ℚ y = fst x *ℤ fst (snd y) ≡ℤ fst y *ℤ fst (snd x)

  infix 5 _≡ℚ_

--  sym-ℚ : ∀ {x y} → x ≡ℚ y → y ≡ℚ x
--  sym-ℚ p = {! insert proof here !}
```

The "complex" example again, now with opaque definitions:
```
module IntroExample2 where
  open ExampleLib

  opaque
    ℤ : Set -- Integers as differences of naturals
    ℤ = ℕ × ℕ

  opaque
    unfolding ℤ
    _≡ℤ_ : ℤ → ℤ → Set -- Equality on integers
    x ≡ℤ y = fst x + snd y ≡ fst y + snd x

  opaque
    unfolding ℤ
    _*ℤ_ : ℤ → ℤ → ℤ -- Integer multiplication
    x *ℤ y  = fst x * fst y + snd x * snd y
            , fst x * snd y + fst y * snd x

  infix 5 _≡ℤ_
  infixl 30 _*ℤ_

  opaque
    unfolding ℤ
    0ℤ : ℤ -- Integer zero
    0ℤ = 0 , 0

  opaque
    ℤ≠0 : Set -- Nonzero integers
    ℤ≠0 = Σ[ x ∷ ℤ ] ¬ x ≡ℤ 0ℤ

  opaque
    ℚ : Set -- Rationals as the field of fractions
    ℚ = ℤ × ℤ≠0

  opaque
    unfolding ℚ ℤ≠0
    _≡ℚ_ : ℚ → ℚ → Set -- Equality on rationals
    x ≡ℚ y = fst x *ℤ fst (snd y) ≡ℤ fst y *ℤ fst (snd x)

  infix 5 _≡ℚ_

--  opaque
--    unfolding _≡ℚ_
--    sym-ℚ : ∀ {x y} → x ≡ℚ y → y ≡ℚ x
--    sym-ℚ p = {! insert proof here !}
```

## 3 Background

### 3.1 The Type Theory

Definition 3.1 refers to terms, which are defined here:
```
import Definition.Untyped using (Term)
```
Note that the formalization uses well-scoped terms (this is mostly ignored in the paper): `Term n` stands for terms with
at most `n` distinct free variables. Note how the `var` constructor takes an index from `Fin n`, and so it is not
possible to reference an out-of-scope variable.

The formalization includes support for modalities, and some terms are annotated with "grades". Such annotations are not
included in the paper. However, some results related to the grades have been extended to also work in the presence of
definitions. For instance, soundness of erasure holds for transparent definition contexts:
```
import Graded.Erasure.Consequences.Soundness
_ = Graded.Erasure.Consequences.Soundness.Soundness.soundness-ℕ
```

Definitions 3.2, 3.3, and 3.4 refer to typing contexts, weakenings, and substitutions, which are defined here (all
well-scoped):
```
import Definition.Untyped.NotParametrised using
  ( Con -- Typing contexts
  ; Wk  -- Weakenings
  )
import Definition.Untyped using
  ( wk    -- Weakening operation
  ; Subst -- Substitutions
  ; _[_]  -- Substitution operation
  )
```
Note that the `Con` type former is more general than in the paper.

Definition 3.5 refers to the typing judgements, which are defined here (albeit with accommodation for definition
contexts, which are discussed further down in Section 4):
```
import Definition.Typed using
  ( _»⊢_    -- Well-formed typing contexts
  ; _⊢_     -- Well-formed types
  ; _⊢_∷_   -- Well-typed terms
  ; _⊢_≡_   -- Equality of types
  ; _⊢_≡_∷_ -- Equality of terms
  ; _⊢_⇒_   -- Single-step weak head reduction of types
  ; _⊢_⇒_∷_ -- Single-step weak head reduction of terms
  )
import Definition.Typed.Weakening using
  ( _»_∷ʷ_⊇_ -- Well-formed weakenings
  )
import Definition.Typed.Substitution using
  ( _⊢ˢʷ_∷_ -- Well-formed substitutions
  )
```
Note that well-formedness of weakenings and substitutions as defined for the above relations includes well-formedness of
the target context (the one on the left).

The type system is parametrised by a record type that makes it possible to include or exclude certain features:
```
import Definition.Typed.Restrictions using (Type-restrictions)
```
For instance, one can choose whether or not to include equality reflection.

The following variants of the reduction relations, allowing for zero or more steps, are also used:
```
import Definition.Typed using
  ( _⊢_⇒*_   -- Many-step weak head reduction for types
  ; _⊢_⇒*_∷_ -- Many-step weak head reduction for terms
  )
```
These are left implicit in the paper, but are used in some of the theorem statements here.

Lemma 3.6 states that typing judgements are preserved under weakening:
```
import Definition.Typed.Weakening using
  ( wk        -- Seven basic typing judgements are preserved under weakening
  ; wkRed     -- Weak head reduction is preserved under weakening
  ; wkRedTerm -- Weak head reduction of terms is preserved under weakening
  )
```

Lemma 3.7 states that typing judgements are preserved under substitution:
```
import Definition.Typed.Substitution using
  ( subst-⊢   -- Seven basic typing judgements are preserved under substitution
  ; subst-⊢⇒  -- Weak head reduction is preserved under substitution
  ; subst-⊢⇒∷ -- Weak head reduction of terms is preserved under substitution
  )
```
Some of these lemmas are stated a little differently than in the paper. For instance, `subst-⊢≡` involves equality of
substitutions.

Lemma 3.8 states that constituents of valid typing judgements are well-formed:
```
import Definition.Typed.Properties.Well-formed using
  ( wf -- Γ ⊢ A implies ⊢ Γ
  )
import Definition.Typed.Well-formed using
  ( wf-⊢∷  -- Γ ⊢ t ∷ A implies Γ ⊢ A
  ; wf-⊢≡  -- Γ ⊢ A ≡ B implies Γ ⊢ A and Γ ⊢ B
  ; wf-⊢≡∷ -- Γ ⊢ t ≡ u ∷ A implies Γ ⊢ t ∷ A and Γ ⊢ u ∷ A
  )
import Definition.Typed.Syntactic using
  ( syntacticRed     -- Γ ⊢ A ⇒* B implies Γ ⊢ A and Γ ⊢ B
  ; syntacticRedTerm -- Γ ⊢ t ⇒* u ∷ A implies Γ ⊢ t ∷ A and Γ ⊢ u ∷ A
  )
```
The formalization does not contain lemmas like `syntacticRed` and `syntacticRedTerm` for the non-starred reduction
relations: those variants follow from `redMany-⊢` and `redMany`:
```
import Definition.Typed.Properties.Reduction using
  ( redMany-⊢ -- Γ ⊢ A ⇒ B implies Γ ⊢ A ⇒* B
  ; redMany   -- Γ ⊢ t ⇒ u ∷ A implies Γ ⊢ t ⇒* u ∷ A
  )
```

Theorem 3.9 states that the term reduction relation enjoys subject reduction. The statement as it appears in the paper
follows directly from the above:
```
module SubjectReduction {a} {M : Set a} {𝕄 : Modality M} (R : Type-restrictions 𝕄) where
  open import Tools.Product
  open import Definition.Untyped M
  open import Definition.Typed R
  open import Definition.Typed.Properties.Reduction R
  open import Definition.Typed.Syntactic R

  subject-reduction :
    ∀ {m n} {Γ : Cons m n} {t u A : Term n} →
    Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A
  subject-reduction t⇒u ⊢t = syntacticRedTerm (redMany t⇒u) .proj₂ .proj₂
```
Note that the parameter `⊢t : Γ ⊢ t ∷ A` is unused; in fact, it can be obtained from `syntacticRedTerm`.

### 3.2 The Logical Relation

Definition 3.10 refers to neutrals, which are defined by a predicate on terms here:
```
import Definition.Untyped.Neutral using (Neutral)
```
The predicate in the formalization includes some extra parameters.

Definition 3.11 refers to weak head normal forms, which are similarly defined by a predicate here:
```
import Definition.Untyped.Whnf using (Whnf)
```
The predicate in the formalization includes an extra parameter.

Definition 3.12 refers to the logical relation for reducibility, which is defined here:
```
import Definition.LogicalRelation using
  ( _⊩⟨_⟩_       -- Reducible types
  ; _⊩⟨_⟩_∷_/_   -- Reducible terms
  ; _⊩⟨_⟩_≡_/_   -- Reducibly equal types
  ; _⊩⟨_⟩_≡_∷_/_ -- Reducibly equal terms
  )
```
Note the two extra parameters compared to the presentation in the paper, one in brackets (`⟨_⟩`) and the other under a
slash (`/_`). The bracketed parameter is a universe level and the other parameter is a type reducibility proof. Both are
elided in the paper for brevity.

Note also that the notion of judgemental equality used in the logical relation is not the usual judgemental equality
`_⊢_≡_`, but is given by the `EqRelSet` data structure, which contains three operators `_⊢_≅_`, `_⊢_≅_∷_`, and
`_⊢_~_∷_`:
```
import Definition.Typed.EqualityRelation using (EqRelSet)
```
Additionally, there is a `Var-included` flag used to control how terms stuck on free variables are treated in the
logical relation:
```
_ = Definition.Typed.EqualityRelation.EqRelSet.Var-included
```
This flag is present because the formalization has optional support for equality reflection: in the presence of equality
reflection, normalization does not necessarily hold for open terms.

The `EqRelSet` parameter allows for different instantiations of the logical relation (and, by extension, of the
fundamental theorem) which can be used in different situations to prove different properties of the type system. In the
formalization, the "standard" instantiation uses `_⊢_≡_` and `_⊢_≡_∷_`, while a specialized instantiation is given in
`Definition.Conversion` to show decidability of conversion:
```
import Definition.Typed.EqRelInstance using (eqRelInstance)
import Definition.Conversion.EqRelInstance using (eqRelInstance)
```

Lemma 3.13 states that reducibility is preserved under weakening:
```
import Definition.LogicalRelation.Weakening using
  ( wk       -- Weakening for reducible types
  ; wkTerm   -- Weakening for reducible terms
  ; wkEq     -- Weakening for reducible equality of types
  ; wkEqTerm -- Weakening for reducible equality of terms
  )
```
Note that the well-formedness relation for weakening is the "restricted" variant `_»_∷ʷʳ_⊇_`, which requires the
weakening to be trivial if `Var-included` does not hold.

Lemma 3.14 states that the reducibility judgements can be "escaped" to recover the normal typing judgements:
```
import Definition.LogicalRelation.Properties.Escape using
  ( escape       -- Escape for reducible types
  ; escapeTerm   -- Escape for reducible terms
  ; escapeEq     -- Escape for reducible equality of types
  ; escapeTermEq -- Escape for reducible equality of terms
  )
```

Definition 3.15 refers to the validity judgements, which are defined here (again, with accommodation for definition
contexts):
```
import Definition.LogicalRelation.Substitution using
  ( _»⊩ᵛ_       -- Valid typing contexts
  ; _⊩ᵛ⟨_⟩_     -- Valid types
  ; _⊩ᵛ⟨_⟩_∷_   -- Valid terms
  ; _⊩ᵛ⟨_⟩_≡_   -- Valid equality of types
  ; _⊩ᵛ⟨_⟩_≡_∷_ -- Valid equality of terms
  ; _⊩ˢ_∷_      -- Valid substitutions
  ; _⊩ˢ_≡_∷_    -- Valid equality of substitutions
  )
```
Note that the substitution validity operators are tagged with a superscript `ˢ` in the Agda code, rather than with a `ᵛ`
as in the paper.

As with reducibility above, the bracketed universe level parameter is elided in the paper, but note that the other
parameter (the type reducibility proof) has vanished; this is accomplished by existential quantification in the "hidden"
variant of reducibility introduced here:
```
import Definition.LogicalRelation.Hidden using
  ( _⊩⟨_⟩_∷_   -- "Hidden" reducibility for terms
  ; _⊩⟨_⟩_≡_   -- "Hidden" reducible equality for types
  ; _⊩⟨_⟩_≡_∷_ -- "Hidden" reducible equality for terms
  )
```
No hidden variant of type reducibility is necessary, since there is no parameter to hide.

Additionally, the validity judgements operate on a "restricted" variant of reducibility that is only required to hold
when either the context is empty or `Var-included` does not hold; this is introduced here:
```
import Definition.LogicalRelation.Hidden.Restricted using
  ( _⊩⟨_⟩_     -- "Restricted" reducibility for types
  ; _⊩⟨_⟩_∷_   -- "Restricted" reducibility for terms
  ; _⊩⟨_⟩_≡_   -- "Restricted" reducible equality for types
  ; _⊩⟨_⟩_≡_∷_ -- "Restricted" reducible equality for terms
  )
```
This restricted notion of reducibility is used to enable the validity argument for equality reflection.

Lemma 3.16 states that the validity judgements can be "escaped" to recover reducibility (and, by extension, the normal
typing judgements):
```
import Definition.LogicalRelation.Substitution using
  ( escape-⊩ᵛ′  -- Escape for valid typing contexts
  ; ⊩ᵛ→⊩        -- Escape for valid types
  ; ⊩ᵛ∷→⊩∷      -- Escape for valid terms
  ; ⊩ᵛ≡→⊩≡      -- Escape for valid equality of types
  ; ⊩ᵛ≡∷→⊩≡∷    -- Escape for valid equality of terms
  ; escape-⊩ˢ∷  -- Escape for valid substitutions
  ; escape-⊩ˢ≡∷ -- Escape for valid equality of substitutions
  )
```
In the formalization, these lemmas include an assumption related to `Var-included`. Note that the escape lemmas for
valid contexts, substitutions, and substitution equality all go directly to the normal typing judgements, since there is
no notion of reducibility for these entities.

Theorem 3.17, the fundamental theorem, states that the normal typing judgements can be strengthened to validity:
```
import Definition.LogicalRelation.Fundamental using
  ( fundamental-⊩ᵛ   -- Fundamental theorem for seven basic typing judgements
  ; fundamental-⊩ˢ∷  -- Fundamental theorem for well-formedness of substitutions
  ; fundamental-⊩ˢ≡∷ -- Fundamental theorem for equality of well-formed substitutions
  )
```

Theorem 3.18 states that all well-typed terms normalize to a WHNF; the same is true of well-formed types:
```
import Definition.Typed.Consequences.Reduction using
  ( whNorm     -- Well-formed types normalize to WHNF
  ; whNormTerm -- Well-typed terms normalize to WHNF
  )
```
Note that these results require either that the context is empty or that equality reflection is disallowed; otherwise,
equality reflection can contradict normalization:
```
import Definition.Typed.Consequences.Reduction using
  ( type-without-WHNF -- A well-formed type that fails to normalize in the presence of equality reflection
  ; term-without-WHNF -- A well-typed term that fails to normalize in the presence of equality reflection
  )
```

Theorem 3.19 states that if `ε ⊢ t ∷ ℕ`, then `t` is judgementally equal to a canonical form of `ℕ`, i.e. a numeral:
```
import Definition.Typed.Consequences.Canonicity using (canonicity)
```

Theorem 3.20 states that the empty type is uninhabited in the empty context---that is, that the theory is consistent;
this is the special case of canonicity for the empty type:
```
import Definition.Typed.Consequences.Canonicity using (¬Empty)
```

Theorem 3.21 states that conversion is decidable (in the absence of equality reflection):
```
import Definition.Typed.Decidable.Equality using
  ( decEq     -- Equality of types is decidable
  ; decEqTerm -- Equality of terms is decidable
  )
```
As mentioned above, this is shown through a specialized instantiation of the logical relation.

## 4 Formalizing Top-level Definitions

### 4.1 The Formalism

Definition 4.1 refers to the terms updated with a definition constructor, which are defined here:
```
import Definition.Untyped using
  ( Term -- Term data type
  ; defn -- Definition constructor
  )
```

Definition 4.2 refers to definition contexts, which are defined here (the definition includes an extra parameter, and
one of the constructors takes an extra opacity argument, which is discussed later):
```
import Definition.Untyped using (DCon)
```
As with typing contexts, definition contexts are also length-indexed.

Definition 4.3 refers to the maps-to relations, which are defined here:
```
import Definition.Untyped using
  ( _↦_∷_∈_ -- A name refers to a definition with a given definiens and annotated with a given type
  ; _↦∷_∈_  -- A name refers to a definition annotated with a given type
  )
```
Since the code here accounts for opacity, `_↦_∷_∈_` has the additional stipulation that the definition is transparent,
as mentioned later in the paper.

Definition 4.4 refers to well-formedness for definition contexts, which is defined here:
```
import Definition.Typed using (»_)
```
The constructors here similarly account for opacity, and so the "extend" case is split into two separate constructors
which are also discussed later in the paper.

Definition 4.5 refers to well-formedness for typing contexts, which is defined here:
```
import Definition.Typed using (_»⊢_)
```

The typing rules are augmented with definition contexts, but instead of prepending a parameter for it as in the paper
(e.g. `_»_⊢_`), the formalization here just changes the parameter on the left of the turnstile to a pair of a definition
context and a typing context. By naming the pairing operator `_»_`, we can recover the syntax from the paper by
expanding the pair. These pairs are defined here:
```
import Definition.Untyped using
  ( Cons -- Context pair type
  ; _»_  -- Pairing operator
  )
```

The typing rules for definitions are given here:
```
import Definition.Typed using
  ( defn  -- Well-typedness rule
  ; δ-red -- Equality (and reduction) rule
  )
```
Note the extra weakenings, which are necessary because the definientia are closed terms (defined in the empty context)
which must be lifted to the ambient context for the rule. Since these weakenings are necessarily trivial, they are
elided in the paper for brevity.

Definition 4.6 refers to definition context extensions, which are defined here:
```
import Definition.Untyped using
  ( DExt -- Definition context extensions
  )
```
The code no longer contains the definition `_»_⊇_`, but instead uses a definition that does not refer to `DExt`, `»_⊇_`:
```
import Definition.Typed.Weakening.Definition using
  ( »_⊇_ -- Well-formed definition context extensions
  )
```

Lemma 4.7 states that typing judgements are preserved under weakening of the definition context ("definitional
weakening"):
```
import Definition.Typed.Weakening.Definition using
  ( defn-wk        -- Preservation under definitional weakening for seven basic typing judgements
  ; defn-wkRed     -- Weak head reduction is preserved under definitional weakening
  ; defn-wkRedTerm -- Weak head reduction of terms is preserved under definitional weakening
  )
```

Lemma 4.8 states that if `» ∇` and `α ↦ t ∷ A ∈ ∇`, then `∇ » ε ⊢ t ∷ A`; a similar result holds for `α ↦∷ A ∈ ∇`:
```
import Definition.Typed.Well-formed using
  ( wf-↦∈  -- Well-formedness of the type annotation for `α ↦∷ A ∈ ∇`
  ; wf-↦∷∈ -- Well-typedness of the definiens for `α ↦ t ∷ A ∈ ∇`
  )
```

Lemma 4.9 extends the well-formedness lemma with definition contexts and an additional case for well-formedness of the
definition context:
```
import Definition.Typed.Well-formed using
  ( wf-⊢ -- The first five cases (and more)
  )
import Definition.Typed.Syntactic using
  ( syntacticRed     -- ∇ » Γ ⊢ A ⇒ B implies ∇ » Γ ⊢ A and ∇ » Γ ⊢ B
  ; syntacticRedTerm -- ∇ » Γ ⊢ t ⇒ u ∷ A implies ∇ » Γ ⊢ t ∷ A and ∇ » Γ ⊢ u ∷ A
  )
```

### 4.2 Updating the Logical Relation

Definition 4.10 extends the logical relation for reducibility with defintion contexts (this snippet is identical to the
one above for Definition 3.12):

```
import Definition.LogicalRelation using
  ( _⊩⟨_⟩_       -- Reducible types
  ; _⊩⟨_⟩_∷_/_   -- Reducible terms
  ; _⊩⟨_⟩_≡_/_   -- Reducibly equal types
  ; _⊩⟨_⟩_≡_∷_/_ -- Reducibly equal terms
  )
```
As with the normal typing judgements, the parameter to the left of the turnstile is a context pair.

Definition 4.11 similarly extends the validity judgements with definition contexts (this snippet is identical to the one
above for Definition 3.15):
```
import Definition.LogicalRelation.Substitution using
  ( _»⊩ᵛ_       -- Valid typing contexts
  ; _⊩ᵛ⟨_⟩_     -- Valid types
  ; _⊩ᵛ⟨_⟩_∷_   -- Valid terms
  ; _⊩ᵛ⟨_⟩_≡_   -- Valid equality of types
  ; _⊩ᵛ⟨_⟩_≡_∷_ -- Valid equality of terms
  ; _⊩ˢ_∷_      -- Valid substitutions
  ; _⊩ˢ_≡_∷_    -- Valid equality of substitutions
  )
```

Definition 4.12 refers to validity for definition contexts, which is defined here:
```
import Definition.LogicalRelation.Substitution.Introductions.Definition using (»ᵛ_)
```

Theorem 4.13 updates the fundamental theorem, adding a case for definition contexts:
```
import Definition.LogicalRelation.Fundamental using
  ( defn-valid       -- Fundamental theorem for well-formedness of definition contexts
  ; fundamental-⊩ᵛ   -- Fundamental theorem for seven basic typing judgements
  ; fundamental-⊩ˢ∷  -- Fundamental theorem for well-formedness of substitutions
  ; fundamental-⊩ˢ≡∷ -- Fundamental theorem for equality of well-formed substitutions
  )
```

Lemma 4.14 establishes validity for δ-reduction (with two weakenings which are elided in the paper):
```
import Definition.LogicalRelation.Substitution.Introductions.Definition using (δ-redᵛ)
```

Lemma 4.15 establishes validity variants of the well-formedness results from Lemma 4.8:
```
import Definition.LogicalRelation.Substitution.Introductions.Definition using
  ( wf-↦∈ᵛ  -- Validity of the type annotation for `α ↦∷ A ∈ ∇`
  ; wf-↦∷∈ᵛ -- Validity of the definiens for `α ↦ t ∷ A ∈ ∇`
  )
```

Lemma 4.16 states that validity is preserved under definitional weakening:
```
import Definition.LogicalRelation.Substitution using
  ( defn-wk-⊩ᵛ   -- Validity of types is preserved under definitional weakening
  ; defn-wk-⊩ᵛ∷  -- Validity of terms is preserved under definitional weakening
  ; defn-wk-⊩ᵛ≡  -- Valid equality of types is preserved under definitional weakening
  ; defn-wk-⊩ᵛ≡∷ -- Valid equality of terms is preserved under definitional weakening
  )
```

Lemma 4.17 states that validity is preserved under weak head expansion (the formalized statement is a little different
from the one in the paper if `Var-included` does not hold):
```
import Definition.LogicalRelation.Substitution using
  ( ⊩ᵛ∷-⇐ -- Weak head expansion for validity
  )
```
This is proved using `redSubst*Term`:
```
import Definition.LogicalRelation.Properties.Reduction using
  ( redSubst*Term -- Weak head expansion for reducibility
  )
```

Lemma 4.18 establishes validity for the definition typing rule (with a weakening which is elided in the paper):
```
import Definition.LogicalRelation.Substitution.Introductions.Definition using (defnᵛ)
```
Note that the argument here accounts for opacity, and so it differs somewhat from the one given in this section of the
paper.

## 5 Formalizing Opacity

### 5.1 The Formalism, Take Two

Definition 5.1 refers to opacities and unfolding vectors:

```
import Definition.Untyped using
  ( Opacity   -- Opacities
  ; Unfolding -- Unfolding vectors
  )
```
Note that opacities and unfolding vectors are indexed by the length of the definition contexts they act on, which is how
the side condition on the length of `φ` in `opa(φ)` is enforced.

Definition 5.2 extends definition contexts with opacities (this snippet is identical to the one above for
Definition 4.2):
```
import Definition.Untyped using (DCon)
```

Definition 5.3 extends the maps-to relations with an additional case for opaque definitions, and refines the `_↦_∷_∈_`
relation to require that the definition is transparent:
```
import Definition.Untyped using
  ( _↦_∷_∈_ -- A name refers to a transparent definition with a given definiens and annotated with a given type
  ; _↦⊘∷_∈_ -- A name refers to an opaque definition annotated with a given type
  ; _↦∷_∈_  -- A name refers to a definition annotated with a given type
  )
```

Lemma 5.4 states that any definition (`_↦∷_∈_`) must be either opaque (`_↦⊘∷_∈_`) or transparent (`_↦_∷_∈_`):
```
import Definition.Untyped.Properties using (dichotomy-↦∈)
```

Definition 5.5 refers to the glassification operation, which is defined here:
```
import Definition.Untyped using (glassify)
```

Lemma 5.6 states that glassification makes any definition transparent:
```
import Definition.Untyped.Properties using (glassify-↦∈′)
```

Definition 5.7 refers to a transparentization relation. This relation has been replaced by a function:
```
import Definition.Typed using
  ( Trans -- The transparentization function
  )
```

In the paper, the "⊔" operator refers exclusively to bitwise disjunction, whereas the formalization offers the choice of
an alternative operator that always returns the left unfolding vector and discards the right one. A consequence of the
use of this operator is shown later in Counterexample 5.13. The operators are defined here:
```
import Definition.Typed.Variant using
  ( UnfoldingMode  -- The enumeration of available unfolding operators
  )
import Definition.Typed using
  ( _⊔ᵒᵗ_ -- The parametric unfolding operator
  )
```

Definition 5.8 extends well-formedness for definition contexts with opacity:
```
import Definition.Typed using
  ( »_         -- Well-formedness relation
  ; ε          -- Empty case
  ; ∙ᵒ⟨_⟩[_∷_] -- Extend case for an opaque definition
  ; ∙ᵗ[_]      -- Extend case for a transparent definition
  )
```
Note the `Opacity-allowed` parameter to the opaque case: this is a type system parameter that specifies whether opaque
definitions are allowed at all:
```
_ = Definition.Typed.Restrictions.Type-restrictions.Opacity-allowed
```
If this is set to the empty type, then the `∙ᵒ⟨_,_⟩[_∷_]` constructor becomes unusable, meaning that contexts with
opaque definitions cannot be well-formed. In particular, we use this to prohibit opaque definitions in the presence of
equality reflection:
```
_ = Definition.Typed.Restrictions.Type-restrictions.no-opaque-equality-reflection
```
This is used in the proof of validity for equality reflection: if all definitions are transparent, then any closed
term of an identity type must reduce to reflexivity.

Lemma 5.9 states that typing judgements are preserved under definitional weakening (this snippet is identical to the one
above for Lemma 4.7):
```
import Definition.Typed.Weakening.Definition using
  ( defn-wk        -- Preservation under definitional weakening for seven basic typing judgements
  ; defn-wkRed     -- Weak head reduction is preserved under definitional weakening
  ; defn-wkRedTerm -- Weak head reduction of terms is preserved under definitional weakening
  )
```

Lemma 5.10 states that typing judgements are preserved under glassification of the definition context:
```
import Definition.Typed.Properties.Definition using
  ( glassify-»  -- Glassification for well-formedness of definition contexts
  ; glassify-⊢  -- Glassification for seven basic typing judgements
  ; glassify-⇒  -- Glassification for weak head reduction of types
  ; glassify-⇒∷ -- Glassification for weak head reduction of terms
  )
```

Theorem 5.11 re-establishes subject reduction:
```
_ = SubjectReduction.subject-reduction
```

Theorem 5.12 states that with transitive unfolding (using the bitwise disjunction operator), well-formedness of
definition contexts (among other things) is preserved under transparentization by any unfolding vector:
```
import Definition.Typed.Properties.Transparentisation
_ = Definition.Typed.Properties.Transparentisation.Transitive.unfold-»
_ = Definition.Typed.Properties.Transparentisation.Transitive.unfold-⊢′
_ = Definition.Typed.Properties.Transparentisation.Transitive.unfold-⊢
_ = Definition.Typed.Properties.Transparentisation.Transitive.unfold-⊢∷
_ = Definition.Typed.Properties.Transparentisation.Transitive.unfold-⊢≡
_ = Definition.Typed.Properties.Transparentisation.Transitive.unfold-⊢≡∷
_ = Definition.Typed.Properties.Transparentisation.Transitive.unfold-⇒∷
_ = Definition.Typed.Properties.Transparentisation.Transitive.unfold-⇒
```
(The last seven definitions above are given in a module with an extra assumption that is instantiated in the module
`Transitive`; see `open Unconditional`.)

Counterexample 5.13 demonstrates that the same is not necessarily true of the alternative operator:
```
import Definition.Typed.Consequences.Transparentisation
_ = Definition.Typed.Consequences.Transparentisation.no-unfold-»
```

The text discusses efficiency of type-checking. Our implementation of `decWfDCon`, a type-checker for definition
contexts, uses an extra recursive call in one of the branches if transitive unfolding is not used:
```
open import Definition.Typed.Decidable using (decWfDCon)
```

### 5.2 Updating the Logical Relation, Take Two

Definitions 5.14 and 5.15 extend neutrality and WHNFs to include opaque definitions:
```
import Definition.Untyped.Neutral using (Neutral)
import Definition.Untyped.Whnf using (Whnf)
```
The definition of neutrality includes an extra parameter that is used to handle equality reflection.

Lemma 5.16 re-establishes validity for the definition typing rule (this snippet is identical to the one above for
Lemma 4.18):
```
import Definition.LogicalRelation.Substitution.Introductions.Definition using (defnᵛ)
```

Lemma 5.17 states that neutral terms of reducible types are reducible:
```
import Definition.LogicalRelation.Properties.Neutral using
  ( neuTerm -- Neutral term reducibility for basic reducibility
  )
import Definition.LogicalRelation.Hidden.Restricted using
  ( neutral-⊩∷ -- Neutral term reducibility for the restricted variant of reducibility used to define validity
  )
```

Lemma 5.18 extends the well-formedness results for definitions from Lemma 4.15 to handle opacity (this snippet is
identical to the one above for Lemma 4.15):
```
import Definition.LogicalRelation.Substitution.Introductions.Definition using
  ( wf-↦∈ᵛ  -- Validity of the type annotation for `α ↦∷ A ∈ ∇`
  ; wf-↦∷∈ᵛ -- Validity of the definiens for `α ↦ t ∷ A ∈ ∇`
  )
```

### 5.3 Consequences of the Fundamental Theorem

Theorem 5.19 re-establishes canonicity for natural numbers with appropriate glassification of definition contexts (this
snippet is identical to the one above for Theorem 3.19):
```
import Definition.Typed.Consequences.Canonicity using (canonicity)
```

Theorem 5.20 states that in glass definition contexts, terms of identity types may be lifted to judgemental equalities:
```
import Definition.Typed.Consequences.Canonicity using (ε⊢∷Id→ε⊢≡∷)
```

Counterexample 5.21 demonstrates that this can fail in non-glass contexts:
```
import Definition.Typed.Consequences.Canonicity using (ε⊢∷Id↛ε⊢≡∷)
```

Theorem 5.22 re-establishes consistency (this snippet is identical to the one above for Theorem 3.20):
```
import Definition.Typed.Consequences.Canonicity using (¬Empty)
```

Theorem 5.23 states that no definition in a well-formed definition context has the empty type, a property that might be
called "definition consistency":
```
import Definition.Typed.Consequences.Canonicity using (¬defn-Empty′)
```

Theorems 5.24 and 5.25 re-establish normalization (this snippet is identical to the one above for Theorem 3.18):
```
import Definition.Typed.Consequences.Reduction using
  ( whNorm     -- Well-formed types normalize to a WHNF
  ; whNormTerm -- Well-typed terms normalize to a WHNF
  )
```

Theorem 5.26 re-establishes decidability of conversion (this snippet is identical to the one above for Theorem 3.21):
```
import Definition.Typed.Decidable.Equality using
  ( decEq     -- Equality of types is decidable
  ; decEqTerm -- Equality of terms is decidable
  )
```

Theorem 5.27 states that type-checking is decidable for a "checkable" fragment of the language:
```
import Definition.Typechecking using
  ( Checkable-type -- Checkability predicate for types
  ; Checkable      -- Checkability predicate for terms
  ; Inferable      -- Inferability predicate
  )
import Definition.Typed.Decidable using
  ( decWfDCon -- Check whether a definition context of checkable definitions is well-formed
  ; decWfCon  -- Check whether a typing context of checkable types is well-formed
  ; dec       -- Check whether a checkable type is well-formed
  ; decTermᶜ  -- Check whether a checkable term is well-typed for a given type
  ; decTermᵢ  -- Infer a type for an inferable term, if possible
  )
```
