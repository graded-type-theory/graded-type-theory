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

<pre class="Agda"><a id="3159" class="Keyword">module</a> <a id="3166" href="README.html" class="Module">README</a> <a id="3173" class="Keyword">where</a>
</pre>
Below pointers to code are included for all the main definitions,
theorems, etc. in the paper, along with some discussion of
differences between the paper and the code.

Note that if HTML has been generated from this file in a suitable way
using @agda --html@, then names in import statements below should be
linked to the corresponding definitions.

### 2: A Type Theory with First-Class Universe Levels

#### 2.1: Syntax

Note that large parts of the development are parametrised by a grade
type or a modality. Grades and modalities are to a large part ignored
in the paper. If one does not care about grades, then one can use a
unit type or a trivial modality:
<pre class="Agda"><a id="3856" class="Keyword">import</a> <a id="3863" href="Graded.Modality.Instances.Unit.html" class="Module">Graded.Modality.Instances.Unit</a>
  <a id="3896" class="Keyword">using</a> <a id="3902" class="Symbol">(</a><a id="3903" href="Graded.Modality.Instances.Unit.html#5376" class="Function">UnitModality</a><a id="3915" class="Symbol">)</a>
</pre>
Terms. The notation does not match the paper exactly. The notation
`zeroᵘ` is used for 0, `sucᵘ` for \_⁺, and `_supᵘ_` for \_⊔\_. Instead
of a constructor Π for Π-types there is a constructor `ΠΣ⟨_⟩_,_▷_▹_`
for *graded* Π- and Σ-types, and the constructors for lambdas and
applications also take grades. The derived notation k + t is denoted
by `sucᵘᵏ k t`, and ↓ k is denoted by `↓ᵘ k`.
<pre class="Agda"><a id="4318" class="Keyword">import</a> <a id="4325" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4346" class="Keyword">using</a> <a id="4352" class="Symbol">(</a><a id="4353" href="Definition.Untyped.html#1241" class="Datatype">Term</a><a id="4357" class="Symbol">;</a> <a id="4359" href="Definition.Untyped.html#5692" class="Function">sucᵘᵏ</a><a id="4364" class="Symbol">;</a> <a id="4366" href="Definition.Untyped.html#5848" class="Function Operator">↓ᵘ_</a><a id="4369" class="Symbol">)</a>
</pre>
Contexts. The type is more general than in the paper: the
instantiation `Con Term` corresponds to what is called Con in the
paper. Furthermore the notation does not match that used in the paper:
the notation `ε` is used for ·, and `_∙_` is used instead of \_,\_.
<pre class="Agda"><a id="4647" class="Keyword">import</a> <a id="4654" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4675" class="Keyword">using</a> <a id="4681" class="Symbol">(</a><a id="4682" href="Definition.Untyped.NotParametrised.html#882" class="Datatype">Con</a><a id="4685" class="Symbol">)</a>
</pre>
Substitution.
<pre class="Agda"><a id="4714" class="Keyword">import</a> <a id="4721" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4742" class="Keyword">using</a> <a id="4748" class="Symbol">(</a><a id="4749" href="Definition.Untyped.html#17311" class="Function Operator">_[_]</a><a id="4753" class="Symbol">)</a>
</pre>
Weakening. The notation `wk ρ t` is used instead of t[ρ], and the
notation `ρ ∷ʷ Δ ⊇ Γ` means that ρ is a well-formed weakening from Γ
to Δ (Δ ⊢ ρ : Γ in the paper). The single-step weakening p is written
`step id`: in the code this weakening is often used via
`wk1` = `wk (step id)`, and the lemmas `wk₁` and `wkTerm₁` show that
this operation is type-preserving.
<pre class="Agda"><a id="5133" class="Keyword">import</a> <a id="5140" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="5161" class="Keyword">using</a> <a id="5167" class="Symbol">(</a><a id="5168" href="Definition.Untyped.html#12636" class="Function">wk</a><a id="5170" class="Symbol">;</a> <a id="5172" href="Definition.Untyped.NotParametrised.html#3041" class="InductiveConstructor">step</a><a id="5176" class="Symbol">;</a> <a id="5178" href="Definition.Untyped.NotParametrised.html#2977" class="InductiveConstructor">id</a><a id="5180" class="Symbol">;</a> <a id="5182" href="Definition.Untyped.html#14452" class="Function">wk1</a><a id="5185" class="Symbol">)</a>
<a id="5187" class="Keyword">import</a> <a id="5194" href="Definition.Typed.Weakening.html" class="Module">Definition.Typed.Weakening</a>
  <a id="5223" class="Keyword">using</a> <a id="5229" class="Symbol">(</a><a id="5230" href="Definition.Typed.Weakening.html#2544" class="Function Operator">_∷ʷ_⊇_</a><a id="5236" class="Symbol">;</a> <a id="5238" href="Definition.Typed.Weakening.html#32758" class="Function">wk₁</a><a id="5241" class="Symbol">;</a> <a id="5243" href="Definition.Typed.Weakening.html#33002" class="Function">wkTerm₁</a><a id="5250" class="Symbol">)</a>
</pre>
#### 2.2: Typing Rules

Unlike in the paper the type system is parametrised by a value of type
`Type-restrictions` that makes it possible to disallow certain things,
like certain (graded) Π- or Σ-types, the K rule or equality
reflection. For instance, the two typing rules for Π and Σ include the
assumption `ΠΣ-allowed b p q`.
<pre class="Agda"><a id="5593" class="Keyword">import</a> <a id="5600" href="Definition.Typed.Restrictions.html" class="Module">Definition.Typed.Restrictions</a>
  <a id="5632" class="Keyword">using</a> <a id="5638" class="Symbol">(</a><a id="5639" href="Definition.Typed.Restrictions.html#927" class="Record">Type-restrictions</a><a id="5656" class="Symbol">)</a>
</pre>
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
<pre class="Agda"><a id="6389" class="Keyword">open</a> <a id="6394" href="Definition.Typed.Restrictions.html#927" class="Module">Definition.Typed.Restrictions.Type-restrictions</a>
  <a id="6444" class="Keyword">using</a>
    <a id="6454" class="Symbol">(</a><a id="6455" href="Definition.Typed.Restrictions.html#1193" class="Field">level-support</a><a id="6468" class="Symbol">;</a> <a id="6470" href="Definition.Typed.Restrictions.html#5583" class="Function">Level-is-small</a><a id="6484" class="Symbol">;</a> <a id="6486" href="Definition.Typed.Restrictions.html#6073" class="Function">Level-is-not-small</a><a id="6504" class="Symbol">;</a> <a id="6506" href="Definition.Typed.Restrictions.html#4738" class="Function">Level-allowed</a><a id="6519" class="Symbol">)</a>
</pre>
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
<pre class="Agda"><a id="7238" class="Keyword">import</a> <a id="7245" href="Definition.Typed.Properties.Admissible.Level.html" class="Module">Definition.Typed.Properties.Admissible.Level</a>
  <a id="7292" class="Keyword">using</a> <a id="7298" class="Symbol">(</a><a id="7299" href="Definition.Typed.Properties.Admissible.Level.html#2222" class="Function">⊢Id-Level</a><a id="7308" class="Symbol">;</a> <a id="7310" href="Definition.Typed.Properties.Admissible.Level.html#1636" class="Function">¬Level-is-small→¬Level∷U</a><a id="7334" class="Symbol">)</a>
</pre>
The type system. Some typing rules have names that differ from those
in the paper. Γ ∋ x : A is denoted by `x ∷ A ∈ Γ`. The definitions use
the relations `_⊢_∷Level` and `_⊢_≡_∷Level` to support disallowing
`Level` entirely: in the case where `Level` is allowed `Γ ⊢ t ∷Level`
is logically equivalent to `Γ ⊢ t ∷ Level`, and similarly for
`_⊢_≡_∷Level`.
<pre class="Agda"><a id="7703" class="Keyword">import</a> <a id="7710" href="Definition.Typed.html" class="Module">Definition.Typed</a>
  <a id="7729" class="Keyword">using</a>
    <a id="7739" class="Symbol">(</a><a id="7740" href="Definition.Typed.html#1476" class="Datatype Operator">⊢_</a><a id="7742" class="Symbol">;</a> <a id="7744" href="Definition.Typed.html#1574" class="Datatype Operator">_⊢_</a><a id="7747" class="Symbol">;</a> <a id="7749" href="Definition.Typed.html#5996" class="Datatype Operator">_⊢_≡_</a><a id="7754" class="Symbol">;</a> <a id="7756" href="Definition.Typed.html#2034" class="Datatype Operator">_⊢_∷_</a><a id="7761" class="Symbol">;</a> <a id="7763" href="Definition.Typed.html#6762" class="Datatype Operator">_⊢_≡_∷_</a><a id="7770" class="Symbol">;</a> <a id="7772" href="Definition.Typed.html#1282" class="Datatype Operator">_∷_∈_</a><a id="7777" class="Symbol">;</a> <a id="7779" href="Definition.Typed.html#23266" class="Function Operator">_⊢_≤_∷Level</a><a id="7790" class="Symbol">;</a>
     <a id="7797" href="Definition.Typed.html#5731" class="Datatype Operator">_⊢_∷Level</a><a id="7806" class="Symbol">;</a> <a id="7808" href="Definition.Typed.html#16211" class="Datatype Operator">_⊢_≡_∷Level</a><a id="7819" class="Symbol">)</a>
</pre>
The ordering of levels induced by `_supᵘ_` is reflexive, transitive and
antisymmetric, and the right identity rule can be derived.
<pre class="Agda"><a id="7965" class="Keyword">import</a> <a id="7972" href="Definition.Typed.Properties.Admissible.Level.html" class="Module">Definition.Typed.Properties.Admissible.Level</a>
  <a id="8019" class="Keyword">using</a> <a id="8025" class="Symbol">(</a><a id="8026" href="Definition.Typed.Properties.Admissible.Level.html#2682" class="Function">⊢≤-refl</a><a id="8033" class="Symbol">;</a> <a id="8035" href="Definition.Typed.Properties.Admissible.Level.html#2883" class="Function">⊢≤-trans</a><a id="8043" class="Symbol">;</a> <a id="8045" href="Definition.Typed.Properties.Admissible.Level.html#3300" class="Function">⊢≤-antisymmetric</a><a id="8061" class="Symbol">;</a> <a id="8063" href="Definition.Typed.Properties.Admissible.Level.html#6733" class="Function">supᵘ-zeroʳⱼ</a><a id="8074" class="Symbol">)</a>
</pre>
The typing rule for `Lift` that uses the ordering of levels is
admissible.
<pre class="Agda"><a id="8164" class="Keyword">import</a> <a id="8171" href="Definition.Typed.Properties.Admissible.Lift.html" class="Module">Definition.Typed.Properties.Admissible.Lift</a>
  <a id="8217" class="Keyword">using</a> <a id="8223" class="Symbol">(</a><a id="8224" href="Definition.Typed.Properties.Admissible.Lift.html#1785" class="Function">Liftⱼ≤</a><a id="8230" class="Symbol">)</a>
</pre>
The type of the universe-polymorphic identity function does not live
in any universe, and "Π U₀ U₁" does not have a type.
<pre class="Agda"><a id="8367" class="Keyword">import</a> <a id="8374" href="Definition.Typed.Consequences.Universe.html" class="Module">Definition.Typed.Consequences.Universe</a>
  <a id="8415" class="Keyword">using</a> <a id="8421" class="Symbol">(</a><a id="8422" href="Definition.Typed.Consequences.Universe.html#2287" class="Function">the-type-of-id-does-not-have-a-type</a><a id="8457" class="Symbol">;</a> <a id="8459" href="Definition.Typed.Consequences.Universe.html#4067" class="Function">type-without-type</a><a id="8476" class="Symbol">)</a>
</pre>
Admissible typing rules for heterogeneous Π- and Σ-types.
<pre class="Agda"><a id="8549" class="Keyword">import</a> <a id="8556" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html" class="Module">Definition.Typed.Properties.Admissible.Pi-Sigma</a>
  <a id="8606" class="Keyword">using</a> <a id="8612" class="Symbol">(</a><a id="8613" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#3505" class="Function">⊢ΠΣʰ</a><a id="8617" class="Symbol">;</a> <a id="8619" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#2693" class="Function">ΠΣʰ-cong-⊢</a><a id="8629" class="Symbol">;</a> <a id="8631" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#4976" class="Function">⊢ΠΣʰ∷</a><a id="8636" class="Symbol">;</a> <a id="8638" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#4480" class="Function">ΠΣʰ-cong-⊢∷</a><a id="8649" class="Symbol">)</a>
<a id="8651" class="Keyword">import</a> <a id="8658" href="Definition.Typed.Properties.Admissible.Pi.html" class="Module">Definition.Typed.Properties.Admissible.Pi</a>
  <a id="8702" class="Keyword">using</a> <a id="8708" class="Symbol">(</a><a id="8709" href="Definition.Typed.Properties.Admissible.Pi.html#9455" class="Function">⊢lamʰ</a><a id="8714" class="Symbol">;</a> <a id="8716" href="Definition.Typed.Properties.Admissible.Pi.html#10166" class="Function">⊢∘ʰ</a><a id="8719" class="Symbol">;</a> <a id="8721" href="Definition.Typed.Properties.Admissible.Pi.html#9769" class="Function">app-congʰ</a><a id="8730" class="Symbol">;</a> <a id="8732" href="Definition.Typed.Properties.Admissible.Pi.html#10403" class="Function">β-redʰ</a><a id="8738" class="Symbol">;</a> <a id="8740" href="Definition.Typed.Properties.Admissible.Pi.html#11364" class="Function">η-eqʰ</a><a id="8745" class="Symbol">)</a>
<a id="8747" class="Keyword">import</a> <a id="8754" href="Definition.Typed.Properties.Admissible.Sigma.html" class="Module">Definition.Typed.Properties.Admissible.Sigma</a>
  <a id="8801" class="Keyword">using</a>
    <a id="8811" class="Symbol">(</a><a id="8812" href="Definition.Typed.Properties.Admissible.Sigma.html#45137" class="Function">⊢prodʰ</a><a id="8818" class="Symbol">;</a> <a id="8820" href="Definition.Typed.Properties.Admissible.Sigma.html#44525" class="Function">prodʰ-cong</a><a id="8830" class="Symbol">;</a>
     <a id="8837" href="Definition.Typed.Properties.Admissible.Sigma.html#45651" class="Function">⊢fstʰ</a><a id="8842" class="Symbol">;</a> <a id="8844" href="Definition.Typed.Properties.Admissible.Sigma.html#46085" class="Function">⊢sndʰ</a><a id="8849" class="Symbol">;</a> <a id="8851" href="Definition.Typed.Properties.Admissible.Sigma.html#45477" class="Function">fstʰ-cong</a><a id="8860" class="Symbol">;</a> <a id="8862" href="Definition.Typed.Properties.Admissible.Sigma.html#45845" class="Function">sndʰ-cong</a><a id="8871" class="Symbol">;</a> <a id="8873" href="Definition.Typed.Properties.Admissible.Sigma.html#46275" class="Function">Σʰ-β₁</a><a id="8878" class="Symbol">;</a> <a id="8880" href="Definition.Typed.Properties.Admissible.Sigma.html#47102" class="Function">Σʰ-β₂</a><a id="8885" class="Symbol">;</a> <a id="8887" href="Definition.Typed.Properties.Admissible.Sigma.html#48091" class="Function">Σʰ-η</a><a id="8891" class="Symbol">;</a>
     <a id="8898" href="Definition.Typed.Properties.Admissible.Sigma.html#55691" class="Function">⊢prodrecʰ⟨⟩</a><a id="8909" class="Symbol">;</a> <a id="8911" href="Definition.Typed.Properties.Admissible.Sigma.html#54814" class="Function">prodrecʰ⟨⟩-cong</a><a id="8926" class="Symbol">;</a> <a id="8928" href="Definition.Typed.Properties.Admissible.Sigma.html#56057" class="Function">prodrecʰ⟨⟩-β</a><a id="8940" class="Symbol">)</a>
</pre>
The type of natural numbers does not have type `U (sucᵘ l)`.
<pre class="Agda"><a id="9016" class="Keyword">import</a> <a id="9023" href="Definition.Typed.Consequences.Inequality.html" class="Module">Definition.Typed.Consequences.Inequality</a>
  <a id="9066" class="Keyword">using</a> <a id="9072" class="Symbol">(</a><a id="9073" href="Definition.Typed.Consequences.Inequality.html#24981" class="Function">¬ℕ∷U-sucᵘ</a><a id="9082" class="Symbol">)</a>
</pre>
#### 2.3: Reduction Rules

Single-step reduction and reduction for terms and types.
<pre class="Agda"><a id="9181" class="Keyword">import</a> <a id="9188" href="Definition.Typed.html" class="Module">Definition.Typed</a>
  <a id="9207" class="Keyword">using</a> <a id="9213" class="Symbol">(</a><a id="9214" href="Definition.Typed.html#16495" class="Datatype Operator">_⊢_⇒_∷_</a><a id="9221" class="Symbol">;</a> <a id="9223" href="Definition.Typed.html#22629" class="Datatype Operator">_⊢_⇒*_∷_</a><a id="9231" class="Symbol">;</a> <a id="9233" href="Definition.Typed.html#22498" class="Datatype Operator">_⊢_⇒_</a><a id="9238" class="Symbol">;</a> <a id="9240" href="Definition.Typed.html#22844" class="Datatype Operator">_⊢_⇒*_</a><a id="9246" class="Symbol">)</a>
</pre>
Neutral terms and WHNFs. Compared to the paper, we use `Neutral`
instead of Neutralᵃ for atomic neutrals and `Neutralˡ` instead of
Neutral.
<pre class="Agda"><a id="9401" class="Keyword">import</a> <a id="9408" href="Definition.Untyped.Neutral.html" class="Module">Definition.Untyped.Neutral</a>
  <a id="9437" class="Keyword">using</a> <a id="9443" class="Symbol">(</a><a id="9444" href="Definition.Untyped.Neutral.html#1014" class="Datatype">Neutral</a><a id="9451" class="Symbol">;</a> <a id="9453" href="Definition.Untyped.Neutral.html#2517" class="Datatype">Neutralˡ</a><a id="9461" class="Symbol">;</a> <a id="9463" href="Definition.Untyped.Neutral.html#3086" class="Datatype">Whnf</a><a id="9467" class="Symbol">)</a>
</pre>
Lemma 2.1: Well-formedness.
<pre class="Agda"><a id="9510" class="Keyword">import</a> <a id="9517" href="Definition.Typed.Properties.html" class="Module">Definition.Typed.Properties</a>
  <a id="9547" class="Keyword">using</a> <a id="9553" class="Symbol">(</a><a id="9554" href="Definition.Typed.Properties.Well-formed.html#13908" class="Function">wf</a><a id="9556" class="Symbol">;</a> <a id="9558" href="Definition.Typed.Properties.Well-formed.html#14328" class="Function">wfEq</a><a id="9562" class="Symbol">;</a> <a id="9564" href="Definition.Typed.Properties.Well-formed.html#14030" class="Function">wfTerm</a><a id="9570" class="Symbol">;</a> <a id="9572" href="Definition.Typed.Properties.Well-formed.html#14475" class="Function">wfEqTerm</a><a id="9580" class="Symbol">)</a>
<a id="9582" class="Keyword">import</a> <a id="9589" href="Definition.Typed.Well-formed.html" class="Module">Definition.Typed.Well-formed</a>
  <a id="9620" class="Keyword">using</a> <a id="9626" class="Symbol">(</a><a id="9627" href="Definition.Typed.Well-formed.html#3434" class="Function">wf-⊢≡</a><a id="9632" class="Symbol">;</a> <a id="9634" href="Definition.Typed.Well-formed.html#1659" class="Function">wf-⊢∷</a><a id="9639" class="Symbol">;</a> <a id="9641" href="Definition.Typed.Well-formed.html#4503" class="Function">wf-⊢≡∷</a><a id="9647" class="Symbol">)</a>
<a id="9649" class="Keyword">import</a> <a id="9656" href="Definition.Typed.Syntactic.html" class="Module">Definition.Typed.Syntactic</a>
  <a id="9685" class="Keyword">using</a> <a id="9691" class="Symbol">(</a><a id="9692" href="Definition.Typed.Syntactic.html#870" class="Function">syntacticRed</a><a id="9704" class="Symbol">;</a> <a id="9706" href="Definition.Typed.Syntactic.html#1007" class="Function">syntacticRedTerm</a><a id="9722" class="Symbol">)</a>
</pre>
### 3: A Logical Relation

External universe levels (natural numbers or ω).
<pre class="Agda"><a id="9813" class="Keyword">import</a> <a id="9820" href="Definition.Untyped.NotParametrised.html" class="Module">Definition.Untyped.NotParametrised</a>
  <a id="9857" class="Keyword">using</a> <a id="9863" class="Symbol">(</a><a id="9864" href="Definition.Untyped.NotParametrised.html#4249" class="Datatype">Universe-level</a><a id="9878" class="Symbol">)</a>
</pre>
The generic equality relations. Compared to the paper we include an
extra relation for levels, to support disallowing `Level` entirely. We
also include the type `Neutrals-included`, which is used to handle
equality reflection: in the absence of equality reflection one can
instantiate this type with something inhabited.
<pre class="Agda"><a id="10214" class="Keyword">open</a> <a id="10219" class="Keyword">import</a> <a id="10226" href="Definition.Typed.EqualityRelation.html" class="Module">Definition.Typed.EqualityRelation</a>
  <a id="10262" class="Keyword">using</a> <a id="10268" class="Symbol">(</a><a id="10269" href="Definition.Typed.EqualityRelation.html#15512" class="Record">EqRelSet</a><a id="10277" class="Symbol">)</a>
<a id="10279" class="Keyword">open</a> <a id="10284" href="Definition.Typed.EqualityRelation.html#15512" class="Module">EqRelSet</a>
  <a id="10295" class="Keyword">using</a> <a id="10301" class="Symbol">(</a><a id="10302" href="Definition.Typed.EqualityRelation.html#16024" class="Field">Neutrals-included</a><a id="10319" class="Symbol">)</a>
</pre>
The generic equality relation instance for judgemental equality. Note
that `Neutrals-included` is instantiated to `No-equality-reflection`.
<pre class="Agda"><a id="10474" class="Keyword">import</a> <a id="10481" href="Definition.Typed.EqRelInstance.html" class="Module">Definition.Typed.EqRelInstance</a>
  <a id="10514" class="Keyword">using</a> <a id="10520" class="Symbol">(</a><a id="10521" href="Definition.Typed.EqRelInstance.html#4004" class="Function">eqRelInstance</a><a id="10534" class="Symbol">)</a>
</pre>
#### 3.1: Reducible Levels and Neutrals

We use the notations `Γ ⊩neNf t ∷ A` and `Γ ⊩neNf t ≡ u ∷ A` instead
of Γ ⊩neNf t : A and Γ ⊩neNf t = u : A, `Γ ⊩Level t ∷Level` and
`Γ ⊩Level t ≡ u ∷Level` instead of Γ ⊩Lvl t and Γ ⊩Lvl t = u,
`Level-prop Γ t` and `[Level]-prop Γ t u` instead of Γ ⊩Lvl\_w t and
Γ ⊩Lvl\_w t = u, and `neLevel-prop Γ t` and `[neLevel]-prop Γ t u`
instead of Γ ⊩Lvlₙ t and Γ ⊩Lvlₙ t = u. The code sometimes uses
`Γ ⊩neNf t ≡ t ∷ A` instead of `Γ ⊩neNf t ∷ A`: these definitions are
logically equivalent.
<pre class="Agda"><a id="11077" class="Keyword">import</a> <a id="11084" href="Definition.LogicalRelation.Unary.html" class="Module">Definition.LogicalRelation.Unary</a>
  <a id="11119" class="Keyword">using</a> <a id="11125" class="Symbol">(</a><a id="11126" href="Definition.LogicalRelation.Unary.html#1626" class="Record Operator">_⊩neNf_∷_</a><a id="11135" class="Symbol">;</a> <a id="11137" href="Definition.LogicalRelation.Unary.html#1960" class="Function">⊩neNf∷⇔⊩neNf≡∷</a><a id="11151" class="Symbol">)</a>
<a id="11153" class="Keyword">import</a> <a id="11160" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="11189" class="Keyword">using</a>
    <a id="11199" class="Symbol">(</a><a id="11200" href="Definition.LogicalRelation.html#2491" class="Record Operator">_⊩neNf_≡_∷_</a><a id="11211" class="Symbol">;</a>
     <a id="11218" href="Definition.LogicalRelation.html#3305" class="Datatype Operator">_⊩Level_∷Level</a><a id="11232" class="Symbol">;</a> <a id="11234" href="Definition.LogicalRelation.html#4348" class="Datatype Operator">_⊩Level_≡_∷Level</a><a id="11250" class="Symbol">;</a>
     <a id="11257" href="Definition.LogicalRelation.html#3654" class="Datatype">Level-prop</a><a id="11267" class="Symbol">;</a> <a id="11269" href="Definition.LogicalRelation.html#4798" class="Datatype">[Level]-prop</a><a id="11281" class="Symbol">;</a>
     <a id="11288" href="Definition.LogicalRelation.html#3950" class="Datatype">neLevel-prop</a><a id="11300" class="Symbol">;</a> <a id="11302" href="Definition.LogicalRelation.html#5529" class="Datatype">[neLevel]-prop</a><a id="11316" class="Symbol">)</a>
</pre>
If `Level-prop Γ t` holds, then `t` is in WHNF, if `neLevel-prop Γ t`
holds, then `t` is neutral, and similarly for the corresponding binary
predicates.
<pre class="Agda"><a id="11484" class="Keyword">import</a> <a id="11491" href="Definition.LogicalRelation.Properties.Whnf.html" class="Module">Definition.LogicalRelation.Properties.Whnf</a>
  <a id="11536" class="Keyword">using</a> <a id="11542" class="Symbol">(</a><a id="11543" href="Definition.LogicalRelation.Properties.Whnf.html#1131" class="Function">level</a><a id="11548" class="Symbol">;</a> <a id="11550" href="Definition.LogicalRelation.Properties.Whnf.html#896" class="Function">nelevel</a><a id="11557" class="Symbol">;</a> <a id="11559" href="Definition.LogicalRelation.Properties.Whnf.html#2214" class="Function">lsplit</a><a id="11565" class="Symbol">;</a> <a id="11567" href="Definition.LogicalRelation.Properties.Whnf.html#1342" class="Function">nelsplit</a><a id="11575" class="Symbol">)</a>
</pre>
The natural number realising a reducible level t is written `↑ⁿ [t]`,
where `[t]` is a witness that t is reducible. The corresponding
external level is written `↑ᵘ [t]`.
<pre class="Agda"><a id="11760" class="Keyword">import</a> <a id="11767" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="11796" class="Keyword">using</a> <a id="11802" class="Symbol">(</a><a id="11803" href="Definition.LogicalRelation.html#7414" class="Function Operator">↑ⁿ_</a><a id="11806" class="Symbol">;</a> <a id="11808" href="Definition.LogicalRelation.html#7844" class="Function Operator">↑ᵘ_</a><a id="11811" class="Symbol">)</a>
</pre>
The natural number realiser satisfies the specification given in the
paper, and any function that satisfies the specification is pointwise
equal to the realiser.
<pre class="Agda"><a id="11988" class="Keyword">import</a> <a id="11995" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12045" class="Keyword">using</a> <a id="12051" class="Symbol">(</a><a id="12052" href="Definition.LogicalRelation.Properties.Primitive.html#51372" class="Function">↑ⁿ-respects-⇒*</a><a id="12066" class="Symbol">;</a> <a id="12068" href="Definition.LogicalRelation.Properties.Primitive.html#38030" class="Function">↑ⁿ-zeroᵘ</a><a id="12076" class="Symbol">;</a> <a id="12078" href="Definition.LogicalRelation.Properties.Primitive.html#38648" class="Function">↑ⁿ-sucᵘ</a><a id="12085" class="Symbol">;</a> <a id="12087" href="Definition.LogicalRelation.Properties.Primitive.html#39550" class="Function">↑ⁿ-supᵘ′</a><a id="12095" class="Symbol">;</a> <a id="12097" href="Definition.LogicalRelation.Properties.Primitive.html#37255" class="Function">↑ⁿ-ne</a><a id="12102" class="Symbol">;</a> <a id="12104" href="Definition.LogicalRelation.Properties.Primitive.html#52424" class="Function">↑ⁿ-unique</a><a id="12113" class="Symbol">)</a>
</pre>
Irrelevance for `↑ⁿ_` and `↑ᵘ_`; `↑ⁿ_` and `↑ᵘ_` respect equality and
ordering.
<pre class="Agda"><a id="12208" class="Keyword">import</a> <a id="12215" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12265" class="Keyword">using</a>
    <a id="12275" class="Symbol">(</a><a id="12276" href="Definition.LogicalRelation.Properties.Primitive.html#34372" class="Function">↑ⁿ-irrelevance</a><a id="12290" class="Symbol">;</a> <a id="12292" href="Definition.LogicalRelation.Properties.Primitive.html#36591" class="Function">↑ᵘ-irrelevance</a><a id="12306" class="Symbol">;</a>
     <a id="12313" href="Definition.LogicalRelation.Properties.Primitive.html#42288" class="Function">↑ⁿ-cong</a><a id="12320" class="Symbol">;</a> <a id="12322" href="Definition.LogicalRelation.Properties.Primitive.html#51135" class="Function">↑ᵘ-cong</a><a id="12329" class="Symbol">;</a>
     <a id="12336" href="Definition.LogicalRelation.Properties.Primitive.html#51834" class="Function">↑ⁿ-cong-≤</a><a id="12345" class="Symbol">;</a> <a id="12347" href="Definition.LogicalRelation.Properties.Primitive.html#52089" class="Function">↑ᵘ-cong-≤</a><a id="12356" class="Symbol">)</a>
</pre>
The function `_supᵘ_` respects equality in its first argument.
<pre class="Agda"><a id="12434" class="Keyword">import</a> <a id="12441" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12491" class="Keyword">using</a> <a id="12497" class="Symbol">(</a><a id="12498" href="Definition.LogicalRelation.Properties.Primitive.html#32200" class="Function">⊩supᵘ-congˡ</a><a id="12509" class="Symbol">)</a>
</pre>
Lemma 3.1: Reducibility for the typing rule for `_supᵘ_`.
<pre class="Agda"><a id="12582" class="Keyword">import</a> <a id="12589" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12639" class="Keyword">using</a> <a id="12645" class="Symbol">(</a><a id="12646" href="Definition.LogicalRelation.Properties.Primitive.html#13358" class="Function">⊩supᵘ</a><a id="12651" class="Symbol">)</a>
</pre>
Lemma 3.2: Reducibility for the judgemental equality rule supᵘ-idem.
<pre class="Agda"><a id="12735" class="Keyword">import</a> <a id="12742" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12792" class="Keyword">using</a> <a id="12798" class="Symbol">(</a><a id="12799" href="Definition.LogicalRelation.Properties.Primitive.html#22294" class="Function">⊩supᵘ-idem</a><a id="12809" class="Symbol">)</a>
</pre>
Two weak head expansion lemmas used in Lemmas 3.1 and 3.2.
<pre class="Agda"><a id="12883" class="Keyword">import</a> <a id="12890" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12940" class="Keyword">using</a> <a id="12946" class="Symbol">(</a><a id="12947" href="Definition.LogicalRelation.Properties.Primitive.html#4277" class="Function">⊩Level-⇒*</a><a id="12956" class="Symbol">;</a> <a id="12958" href="Definition.LogicalRelation.Properties.Primitive.html#3975" class="Function">redLevel′</a><a id="12967" class="Symbol">)</a>
</pre>
#### 3.2: Reducibility

The main reducibility judgements.
<pre class="Agda"><a id="13040" class="Keyword">import</a> <a id="13047" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13076" class="Keyword">using</a> <a id="13082" class="Symbol">(</a><a id="13083" href="Definition.LogicalRelation.html#23465" class="Function Operator">_⊩⟨_⟩_</a><a id="13089" class="Symbol">;</a> <a id="13091" href="Definition.LogicalRelation.html#23600" class="Function Operator">_⊩⟨_⟩_≡_/_</a><a id="13101" class="Symbol">;</a> <a id="13103" href="Definition.LogicalRelation.html#23978" class="Function Operator">_⊩⟨_⟩_≡_∷_/_</a><a id="13115" class="Symbol">;</a> <a id="13117" href="Definition.LogicalRelation.html#23786" class="Function Operator">_⊩⟨_⟩_∷_/_</a><a id="13127" class="Symbol">)</a>
</pre>
The logical relation is cumulative.
<pre class="Agda"><a id="13178" class="Keyword">import</a> <a id="13185" href="Definition.LogicalRelation.Properties.Embedding.html" class="Module">Definition.LogicalRelation.Properties.Embedding</a>
  <a id="13235" class="Keyword">using</a> <a id="13241" class="Symbol">(</a><a id="13242" href="Definition.LogicalRelation.Properties.Embedding.html#945" class="Function">emb-≤-⊩</a><a id="13249" class="Symbol">;</a> <a id="13251" href="Definition.LogicalRelation.Properties.Embedding.html#2186" class="Function">emb-≤-⊩≡</a><a id="13259" class="Symbol">;</a> <a id="13261" href="Definition.LogicalRelation.Properties.Embedding.html#2403" class="Function">emb-≤-⊩≡∷</a><a id="13270" class="Symbol">;</a> <a id="13272" href="Definition.LogicalRelation.Properties.Embedding.html#1048" class="Function">emb-≤-⊩∷</a><a id="13280" class="Symbol">)</a>
</pre>
Reducibility for neutrals.
<pre class="Agda"><a id="13322" class="Keyword">import</a> <a id="13329" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13358" class="Keyword">using</a> <a id="13364" class="Symbol">(</a><a id="13365" href="Definition.LogicalRelation.html#1812" class="Record Operator">_⊩ne_</a><a id="13370" class="Symbol">;</a> <a id="13372" href="Definition.LogicalRelation.html#2131" class="Record Operator">_⊩ne_≡_/_</a><a id="13381" class="Symbol">;</a> <a id="13383" href="Definition.LogicalRelation.html#2801" class="Record Operator">_⊩ne_≡_∷_/_</a><a id="13394" class="Symbol">)</a>
</pre>
Reducibility for levels.
<pre class="Agda"><a id="13434" class="Keyword">import</a> <a id="13441" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13470" class="Keyword">using</a> <a id="13476" class="Symbol">(</a><a id="13477" href="Definition.LogicalRelation.html#3087" class="Function Operator">_⊩Level_</a><a id="13485" class="Symbol">;</a> <a id="13487" href="Definition.LogicalRelation.html#3188" class="Function Operator">_⊩Level_≡_</a><a id="13497" class="Symbol">;</a> <a id="13499" href="Definition.LogicalRelation.html#4348" class="Datatype Operator">_⊩Level_≡_∷Level</a><a id="13515" class="Symbol">)</a>
</pre>
Level reflexivity and well-formedness.
<pre class="Agda"><a id="13569" class="Keyword">import</a> <a id="13576" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="13626" class="Keyword">using</a> <a id="13632" class="Symbol">(</a><a id="13633" href="Definition.LogicalRelation.Properties.Primitive.html#1444" class="Function">reflLevel</a><a id="13642" class="Symbol">;</a> <a id="13644" href="Definition.LogicalRelation.Properties.Primitive.html#25302" class="Function">wf-Level-eq</a><a id="13655" class="Symbol">)</a>
</pre>
Reducibility for universes.
<pre class="Agda"><a id="13698" class="Keyword">open</a> <a id="13703" class="Keyword">import</a> <a id="13710" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13739" class="Keyword">using</a> <a id="13745" class="Symbol">(</a><a id="13746" class="Keyword">module</a> <a id="13753" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a><a id="13759" class="Symbol">)</a>
<a id="13761" class="Keyword">open</a> <a id="13766" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="13775" class="Keyword">using</a> <a id="13781" class="Symbol">(</a><a id="13782" href="Definition.LogicalRelation.html#11413" class="Record Operator">_⊩₁U_</a><a id="13787" class="Symbol">;</a> <a id="13789" href="Definition.LogicalRelation.html#11660" class="Record Operator">_⊩₁U≡_/_</a><a id="13797" class="Symbol">;</a> <a id="13799" href="Definition.LogicalRelation.html#11908" class="Record Operator">_⊩₁U_≡_∷U/_</a><a id="13810" class="Symbol">)</a>
</pre>
Types in WHNF.
<pre class="Agda"><a id="13840" class="Keyword">import</a> <a id="13847" href="Definition.Untyped.Neutral.html" class="Module">Definition.Untyped.Neutral</a>
  <a id="13876" class="Keyword">using</a> <a id="13882" class="Symbol">(</a><a id="13883" href="Definition.Untyped.Neutral.html#7007" class="Datatype">Type</a><a id="13887" class="Symbol">)</a>
</pre>
Reducibility for lift types.
<pre class="Agda"><a id="13931" class="Keyword">open</a> <a id="13936" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="13945" class="Keyword">using</a> <a id="13951" class="Symbol">(</a><a id="13952" href="Definition.LogicalRelation.html#12411" class="Record Operator">_⊩ₗLift_</a><a id="13960" class="Symbol">;</a> <a id="13962" href="Definition.LogicalRelation.html#12713" class="Record Operator">_⊩ₗLift_≡_/_</a><a id="13974" class="Symbol">;</a> <a id="13976" href="Definition.LogicalRelation.html#13074" class="Function Operator">_⊩ₗLift_≡_∷_/_</a><a id="13990" class="Symbol">)</a>
</pre>
Reducibility for Π-types (the first two definitions are used also for
Σ-types).
<pre class="Agda"><a id="14085" class="Keyword">open</a> <a id="14090" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="14099" class="Keyword">using</a> <a id="14105" class="Symbol">(</a><a id="14106" href="Definition.LogicalRelation.html#13448" class="Record Operator">_⊩ₗB⟨_⟩_</a><a id="14114" class="Symbol">;</a> <a id="14116" href="Definition.LogicalRelation.html#14403" class="Record Operator">_⊩ₗB⟨_⟩_≡_/_</a><a id="14128" class="Symbol">;</a> <a id="14130" href="Definition.LogicalRelation.html#15186" class="Function Operator">_⊩ₗΠ_≡_∷_/_</a><a id="14141" class="Symbol">)</a>
</pre>
Well-formed weakenings were introduced above. The definition of the
logical relation uses a variant of this definition which is logically
equivalent if `Neutrals-included` is inhabited.
<pre class="Agda"><a id="14342" class="Keyword">import</a> <a id="14349" href="Definition.LogicalRelation.Weakening.Restricted.html" class="Module">Definition.LogicalRelation.Weakening.Restricted</a>
  <a id="14399" class="Keyword">using</a> <a id="14405" class="Symbol">(</a><a id="14406" href="Definition.LogicalRelation.Weakening.Restricted.html#844" class="Datatype Operator">_∷ʷʳ_⊇_</a><a id="14413" class="Symbol">;</a> <a id="14415" href="Definition.LogicalRelation.Weakening.Restricted.html#1055" class="Function">∷ʷ⊇→∷ʷʳ⊇</a><a id="14423" class="Symbol">;</a> <a id="14425" href="Definition.LogicalRelation.Weakening.Restricted.html#1342" class="Function">∷ʷʳ⊇→∷ʷ⊇</a><a id="14433" class="Symbol">)</a>
</pre>
Lifting of weakenings is denoted by `lift` rather than \_⇑ (which is
used for substitutions).
<pre class="Agda"><a id="14542" class="Keyword">import</a> <a id="14549" href="Definition.Untyped.NotParametrised.html" class="Module">Definition.Untyped.NotParametrised</a>
  <a id="14586" class="Keyword">using</a> <a id="14592" class="Symbol">(</a><a id="14593" href="Definition.Untyped.NotParametrised.html#3130" class="InductiveConstructor">lift</a><a id="14597" class="Symbol">)</a>
<a id="14599" class="Keyword">import</a> <a id="14606" href="Definition.Typed.Weakening.html" class="Module">Definition.Typed.Weakening</a>
  <a id="14635" class="Keyword">using</a> <a id="14641" class="Symbol">(</a><a id="14642" href="Definition.Typed.Weakening.html#3469" class="Function">liftʷ</a><a id="14647" class="Symbol">)</a>
</pre>
Irrelevance for reducibility judgements.
<pre class="Agda"><a id="14703" class="Keyword">import</a> <a id="14710" href="Definition.LogicalRelation.Irrelevance.html" class="Module">Definition.LogicalRelation.Irrelevance</a>
  <a id="14751" class="Keyword">using</a> <a id="14757" class="Symbol">(</a><a id="14758" href="Definition.LogicalRelation.Irrelevance.html#1944" class="Function">irrelevanceEq</a><a id="14771" class="Symbol">;</a> <a id="14773" href="Definition.LogicalRelation.Irrelevance.html#7487" class="Function">irrelevanceEqTerm</a><a id="14790" class="Symbol">;</a> <a id="14792" href="Definition.LogicalRelation.Irrelevance.html#6045" class="Function">irrelevanceTerm</a><a id="14807" class="Symbol">)</a>
</pre>
Reducibility judgements with hidden reducibility arguments.
<pre class="Agda"><a id="14882" class="Keyword">import</a> <a id="14889" href="Definition.LogicalRelation.Hidden.html" class="Module">Definition.LogicalRelation.Hidden</a>
  <a id="14925" class="Keyword">using</a> <a id="14931" class="Symbol">(</a><a id="14932" href="Definition.LogicalRelation.Hidden.html#1616" class="Function Operator">_⊩⟨_⟩_∷_</a><a id="14940" class="Symbol">;</a> <a id="14942" href="Definition.LogicalRelation.Hidden.html#2021" class="Function Operator">_⊩⟨_⟩_≡_∷_</a><a id="14952" class="Symbol">;</a> <a id="14954" href="Definition.LogicalRelation.Hidden.html#1810" class="Function Operator">_⊩⟨_⟩_≡_</a><a id="14962" class="Symbol">)</a>
</pre>
#### 3.3 Validity and the Fundamental Lemma

`Γ ⊩⟨ ℓ ⟩ 𝒥` implies `Γ ⊢ 𝒥`.
<pre class="Agda"><a id="15052" class="Keyword">import</a> <a id="15059" href="Definition.LogicalRelation.Properties.Escape.html" class="Module">Definition.LogicalRelation.Properties.Escape</a>
  <a id="15106" class="Keyword">using</a> <a id="15112" class="Symbol">(</a><a id="15113" href="Definition.LogicalRelation.Properties.Escape.html#1299" class="Function">escape</a><a id="15119" class="Symbol">;</a> <a id="15121" href="Definition.LogicalRelation.Properties.Escape.html#1728" class="Function">escapeEq</a><a id="15129" class="Symbol">;</a> <a id="15131" href="Definition.LogicalRelation.Properties.Escape.html#1982" class="Function">escapeTerm</a><a id="15141" class="Symbol">;</a> <a id="15143" href="Definition.LogicalRelation.Properties.Escape.html#1864" class="Function">escapeTermEq</a><a id="15155" class="Symbol">)</a>
</pre>
Validity judgements. In addition to the ones in the paper we also use
`Γ ⊩ᵛ⟨ ℓ ⟩ t ∷Level` and `Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷Level`, which are logically
equivalent to `Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level` and `Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ Level`,
respectively, when the `Level` type is allowed.
<pre class="Agda"><a id="15426" class="Keyword">import</a> <a id="15433" href="Definition.LogicalRelation.Substitution.html" class="Module">Definition.LogicalRelation.Substitution</a>
  <a id="15475" class="Keyword">using</a>
    <a id="15485" class="Symbol">(</a><a id="15486" href="Definition.LogicalRelation.Substitution.html#1823" class="Function Operator">⊩ᵛ_</a><a id="15489" class="Symbol">;</a> <a id="15491" href="Definition.LogicalRelation.Substitution.html#1950" class="Function Operator">_⊩ᵛ⟨_⟩_</a><a id="15498" class="Symbol">;</a> <a id="15500" href="Definition.LogicalRelation.Substitution.html#2088" class="Function Operator">_⊩ᵛ⟨_⟩_≡_</a><a id="15509" class="Symbol">;</a> <a id="15511" href="Definition.LogicalRelation.Substitution.html#2677" class="Function Operator">_⊩ˢ_∷_</a><a id="15517" class="Symbol">;</a> <a id="15519" href="Definition.LogicalRelation.Substitution.html#2343" class="Function Operator">_⊩ˢ_≡_∷_</a><a id="15527" class="Symbol">;</a> <a id="15529" href="Definition.LogicalRelation.Substitution.html#3101" class="Function Operator">_⊩ᵛ⟨_⟩_∷_</a><a id="15538" class="Symbol">;</a> <a id="15540" href="Definition.LogicalRelation.Substitution.html#2821" class="Function Operator">_⊩ᵛ⟨_⟩_≡_∷_</a><a id="15551" class="Symbol">;</a>
     <a id="15558" href="Definition.LogicalRelation.Substitution.html#3660" class="Function Operator">_⊩ᵛ⟨_⟩_∷Level</a><a id="15571" class="Symbol">;</a> <a id="15573" href="Definition.LogicalRelation.Substitution.html#3264" class="Datatype Operator">_⊩ᵛ⟨_⟩_≡_∷Level</a><a id="15588" class="Symbol">;</a> <a id="15590" href="Definition.LogicalRelation.Substitution.html#11459" class="Function">⊩ᵛ∷L⇔</a><a id="15595" class="Symbol">;</a> <a id="15597" href="Definition.LogicalRelation.Substitution.html#11187" class="Function">⊩ᵛ≡∷L⇔</a><a id="15603" class="Symbol">)</a>
</pre>
Lemma 3.3: Fundamental lemma.
<pre class="Agda"><a id="15648" class="Keyword">import</a> <a id="15655" href="Definition.LogicalRelation.Fundamental.html" class="Module">Definition.LogicalRelation.Fundamental</a>
  <a id="15696" class="Keyword">using</a>
    <a id="15706" class="Symbol">(</a><a id="15707" href="Definition.LogicalRelation.Fundamental.html#1309" class="Function">valid</a><a id="15712" class="Symbol">;</a>
     <a id="15719" href="Definition.LogicalRelation.Fundamental.html#1454" class="Function">fundamental-⊩ᵛ</a><a id="15733" class="Symbol">;</a> <a id="15735" href="Definition.LogicalRelation.Fundamental.html#2075" class="Function">fundamental-⊩ᵛ≡</a><a id="15750" class="Symbol">;</a> <a id="15752" href="Definition.LogicalRelation.Fundamental.html#3351" class="Function">fundamental-⊩ᵛ∷</a><a id="15767" class="Symbol">;</a> <a id="15769" href="Definition.LogicalRelation.Fundamental.html#7267" class="Function">fundamental-⊩ᵛ≡∷</a><a id="15785" class="Symbol">)</a>
</pre>
Lemma 3.4: Validity for the term typing rule for U. The proof sketch
given in the paper does not quite match the proof used here: this
proof goes via a corresponding proof for binary validity. Similar
comments apply to Lemmas 3.5 and 3.6 below.
<pre class="Agda"><a id="16045" class="Keyword">import</a> <a id="16052" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Universe</a>
  <a id="16117" class="Keyword">using</a> <a id="16123" class="Symbol">(</a><a id="16124" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html#11289" class="Function">⊩ᵛU∷U</a><a id="16129" class="Symbol">)</a>
</pre>
Lemma 3.5: Validity for the typing rule univ.
<pre class="Agda"><a id="16190" class="Keyword">import</a> <a id="16197" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Universe</a>
  <a id="16262" class="Keyword">using</a> <a id="16268" class="Symbol">(</a><a id="16269" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html#11753" class="Function">⊩ᵛ∷U→⊩ᵛ</a><a id="16276" class="Symbol">)</a>
</pre>
Lemma 3.6: Validity for the term typing rule for Lift.
<pre class="Agda"><a id="16346" class="Keyword">import</a> <a id="16353" href="Definition.LogicalRelation.Substitution.Introductions.Lift.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Lift</a>
  <a id="16414" class="Keyword">using</a> <a id="16420" class="Symbol">(</a><a id="16421" href="Definition.LogicalRelation.Substitution.Introductions.Lift.html#7140" class="Function">Liftᵗᵛ</a><a id="16427" class="Symbol">)</a>
</pre>
Lemma 3.7: Validity for the term typing rule for Π.
<pre class="Agda"><a id="16494" class="Keyword">import</a> <a id="16501" href="Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma</a>
  <a id="16566" class="Keyword">using</a> <a id="16572" class="Symbol">(</a><a id="16573" href="Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma.html#23518" class="Function">ΠΣᵗᵛ</a><a id="16577" class="Symbol">)</a>
</pre>
Level realisers are stable under weakening.
<pre class="Agda"><a id="16636" class="Keyword">import</a> <a id="16643" href="Definition.LogicalRelation.Weakening.html" class="Module">Definition.LogicalRelation.Weakening</a>
  <a id="16682" class="Keyword">using</a> <a id="16688" class="Symbol">(</a><a id="16689" href="Definition.LogicalRelation.Weakening.html#4888" class="Function">wk-↑ⁿ</a><a id="16694" class="Symbol">;</a> <a id="16696" href="Definition.LogicalRelation.Weakening.html#7971" class="Function">wk-↑ᵘ</a><a id="16701" class="Symbol">)</a>
</pre>
Corollary 3.8: Well-typed objects are reducible.
<pre class="Agda"><a id="16765" class="Keyword">import</a> <a id="16772" href="Definition.LogicalRelation.Fundamental.Reducibility.html" class="Module">Definition.LogicalRelation.Fundamental.Reducibility</a>
  <a id="16826" class="Keyword">using</a> <a id="16832" class="Symbol">(</a><a id="16833" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1081" class="Function">reducible-⊩</a><a id="16844" class="Symbol">;</a> <a id="16846" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1299" class="Function">reducible-⊩≡</a><a id="16858" class="Symbol">;</a> <a id="16860" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1451" class="Function">reducible-⊩∷</a><a id="16872" class="Symbol">;</a> <a id="16874" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1691" class="Function">reducible-⊩≡∷</a><a id="16887" class="Symbol">)</a>
</pre>
The identity substitution is reducible.
<pre class="Agda"><a id="16942" class="Keyword">import</a> <a id="16949" href="Definition.LogicalRelation.Substitution.html" class="Module">Definition.LogicalRelation.Substitution</a>
  <a id="16991" class="Keyword">using</a> <a id="16997" class="Symbol">(</a><a id="16998" href="Definition.LogicalRelation.Substitution.html#38328" class="Function">⊩ˢ∷-idSubst</a><a id="17009" class="Symbol">)</a>
</pre>
Atomic neutrals are reducible.
<pre class="Agda"><a id="17055" class="Keyword">import</a> <a id="17062" href="Definition.LogicalRelation.Properties.Neutral.html" class="Module">Definition.LogicalRelation.Properties.Neutral</a>
</pre>
Corollary 3.9: Consistency.
<pre class="Agda"><a id="17149" class="Keyword">import</a> <a id="17156" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="17199" class="Keyword">using</a> <a id="17205" class="Symbol">(</a><a id="17206" href="Definition.Typed.Consequences.Canonicity.html#9637" class="Function">¬Empty</a><a id="17212" class="Symbol">)</a>
</pre>
Corollary 3.10: Canonicity.
<pre class="Agda"><a id="17255" class="Keyword">import</a> <a id="17262" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="17305" class="Keyword">using</a> <a id="17311" class="Symbol">(</a><a id="17312" href="Definition.Typed.Consequences.Canonicity.html#1463" class="Function">canonicity</a><a id="17322" class="Symbol">)</a>
</pre>
Corollary 3.11: Weak head normalisation.
<pre class="Agda"><a id="17378" class="Keyword">import</a> <a id="17385" href="Definition.Typed.Consequences.Reduction.html" class="Module">Definition.Typed.Consequences.Reduction</a>
  <a id="17427" class="Keyword">using</a> <a id="17433" class="Symbol">(</a><a id="17434" href="Definition.Typed.Consequences.Reduction.html#6345" class="Function">whNorm</a><a id="17440" class="Symbol">;</a> <a id="17442" href="Definition.Typed.Consequences.Reduction.html#13640" class="Function">whNormTerm</a><a id="17452" class="Symbol">)</a>
</pre>
Corollary 3.12: Injectivity of and non-confusion for type formers.
More lemmas of this kind can be found in the given modules. Statements
of the form "`A` is not derivable" are interpreted as `¬ A`; note that
if Agda is inconsistent, then `¬ A` and `A` might both be inhabited.
<pre class="Agda"><a id="17745" class="Keyword">import</a> <a id="17752" href="Definition.Typed.Consequences.Injectivity.html" class="Module">Definition.Typed.Consequences.Injectivity</a>
  <a id="17796" class="Keyword">using</a>
    <a id="17806" class="Symbol">(</a><a id="17807" href="Definition.Typed.Consequences.Injectivity.html#1286" class="Function">U-injectivity</a><a id="17820" class="Symbol">;</a> <a id="17822" href="Definition.Typed.Consequences.Injectivity.html#1560" class="Function">Lift-injectivity</a><a id="17838" class="Symbol">;</a>
     <a id="17845" href="Definition.Typed.Consequences.Injectivity.html#3097" class="Function">ΠΣ-injectivity-no-equality-reflection</a><a id="17882" class="Symbol">)</a>
<a id="17884" class="Keyword">import</a> <a id="17891" href="Definition.Typed.Consequences.Inequality.html" class="Module">Definition.Typed.Consequences.Inequality</a>
  <a id="17934" class="Keyword">using</a> <a id="17940" class="Symbol">(</a><a id="17941" href="Definition.Typed.Consequences.Inequality.html#7808" class="Function">Level≢ℕ</a><a id="17948" class="Symbol">;</a> <a id="17950" href="Definition.Typed.Consequences.Inequality.html#2857" class="Function">U≢ℕ</a><a id="17953" class="Symbol">)</a>
</pre>
Corollary 3.13: Canonicity for contexts that only contain level and
type variables.
<pre class="Agda"><a id="18052" class="Keyword">import</a> <a id="18059" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="18102" class="Keyword">using</a> <a id="18108" class="Symbol">(</a><a id="18109" href="Definition.Typed.Consequences.Canonicity.html#8636" class="Function">canonicity-Only-Level-or-U</a><a id="18135" class="Symbol">)</a>
</pre>
### 4: Decidability of Equality

Algorithmic equality. The conversion relations are denoted as follows:

* `Γ ⊢ A [conv↑] B` and `Γ ⊢ A [conv↓] B` for arbitrary types and
  types in WHNF, respectively,

* `Γ ⊢ t [conv↑] u ∷ A` and `Γ ⊢ t [conv↓] u ∷ B` for arbitrary terms
  with arbitrary types, and terms in WHNF with types in WHNF,
  respectively, and

* `Γ ⊢ t ~ u ↑ A` and `Γ ⊢ t ~ u ↓ A` for atomic neutral terms and
  atomic neutral terms with types in WHNF, respectively.

<pre class="Agda"><a id="18631" class="Keyword">import</a> <a id="18638" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18662" class="Keyword">using</a>
    <a id="18672" class="Symbol">(</a><a id="18673" href="Definition.Conversion.html#5092" class="Record Operator">_⊢_[conv↑]_</a><a id="18684" class="Symbol">;</a> <a id="18686" href="Definition.Conversion.html#5380" class="Datatype Operator">_⊢_[conv↓]_</a><a id="18697" class="Symbol">;</a> <a id="18699" href="Definition.Conversion.html#6398" class="Record Operator">_⊢_[conv↑]_∷_</a><a id="18712" class="Symbol">;</a> <a id="18714" href="Definition.Conversion.html#6743" class="Datatype Operator">_⊢_[conv↓]_∷_</a><a id="18727" class="Symbol">;</a>
     <a id="18734" href="Definition.Conversion.html#1461" class="Datatype Operator">_⊢_~_↑_</a><a id="18741" class="Symbol">;</a> <a id="18743" href="Definition.Conversion.html#4591" class="Record Operator">_⊢_~_↓_</a><a id="18750" class="Symbol">)</a>
</pre>
Level atoms, `Level⁺` and level views.
<pre class="Agda"><a id="18804" class="Keyword">import</a> <a id="18811" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18835" class="Keyword">using</a> <a id="18841" class="Symbol">(</a><a id="18842" href="Definition.Conversion.html#9587" class="Datatype">LevelAtom</a><a id="18851" class="Symbol">;</a> <a id="18853" href="Definition.Conversion.html#9713" class="Function">Level⁺</a><a id="18859" class="Symbol">;</a> <a id="18861" href="Definition.Conversion.html#9775" class="Function">Levelᵛ</a><a id="18867" class="Symbol">)</a>
</pre>
Level view comparison.
<pre class="Agda"><a id="18905" class="Keyword">import</a> <a id="18912" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18936" class="Keyword">using</a> <a id="18942" class="Symbol">(</a><a id="18943" href="Definition.Conversion.html#9866" class="Function Operator">_≡ᵛ_</a><a id="18947" class="Symbol">;</a> <a id="18949" href="Definition.Conversion.html#10186" class="Function">≤ᵛ</a><a id="18951" class="Symbol">;</a> <a id="18953" href="Definition.Conversion.html#10272" class="Function">≤⁺ᵛ</a><a id="18956" class="Symbol">;</a> <a id="18958" href="Definition.Conversion.html#10351" class="Function">≤⁺</a><a id="18960" class="Symbol">;</a> <a id="18962" href="Definition.Conversion.html#10441" class="Datatype">≤ᵃ</a><a id="18964" class="Symbol">)</a>
</pre>
Operations on level views.
<pre class="Agda"><a id="19006" class="Keyword">import</a> <a id="19013" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="19037" class="Keyword">using</a> <a id="19043" class="Symbol">(</a><a id="19044" href="Definition.Conversion.html#11231" class="Function">sucᵛ</a><a id="19048" class="Symbol">;</a> <a id="19050" href="Definition.Conversion.html#11299" class="Function">supᵛ</a><a id="19054" class="Symbol">)</a>
</pre>
Normalising levels into level views.
<pre class="Agda"><a id="19106" class="Keyword">import</a> <a id="19113" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="19137" class="Keyword">using</a> <a id="19143" class="Symbol">(</a><a id="19144" href="Definition.Conversion.html#12274" class="Record Operator">_⊢_↑ᵛ_</a><a id="19150" class="Symbol">;</a> <a id="19152" href="Definition.Conversion.html#11466" class="Datatype Operator">_⊢_↓ᵛ_</a><a id="19158" class="Symbol">;</a> <a id="19160" href="Definition.Conversion.html#11798" class="Datatype Operator">_⊢_~ᵛ_</a><a id="19166" class="Symbol">)</a>
</pre>
Algorithmic equality is sound.
<pre class="Agda"><a id="19212" class="Keyword">import</a> <a id="19219" href="Definition.Conversion.Soundness.html" class="Module">Definition.Conversion.Soundness</a>
  <a id="19253" class="Keyword">using</a>
    <a id="19263" class="Symbol">(</a><a id="19264" href="Definition.Conversion.Soundness.html#4201" class="Function">soundnessConv↑</a><a id="19278" class="Symbol">;</a> <a id="19280" href="Definition.Conversion.Soundness.html#4444" class="Function">soundnessConv↓</a><a id="19294" class="Symbol">;</a>
     <a id="19301" href="Definition.Conversion.Soundness.html#5238" class="Function">soundnessConv↑Term</a><a id="19319" class="Symbol">;</a> <a id="19321" href="Definition.Conversion.Soundness.html#5861" class="Function">soundnessConv↓Term</a><a id="19339" class="Symbol">;</a>
     <a id="19346" href="Definition.Conversion.Soundness.html#1675" class="Function">soundness~↑</a><a id="19357" class="Symbol">;</a> <a id="19359" href="Definition.Conversion.Soundness.html#3899" class="Function">soundness~↓</a><a id="19370" class="Symbol">)</a>
</pre>
Algorithmic equality is stable under weakening.
<pre class="Agda"><a id="19433" class="Keyword">import</a> <a id="19440" href="Definition.Conversion.Weakening.html" class="Module">Definition.Conversion.Weakening</a>
  <a id="19474" class="Keyword">using</a> <a id="19480" class="Symbol">(</a><a id="19481" href="Definition.Conversion.Weakening.html#6221" class="Function">wkConv↑</a><a id="19488" class="Symbol">;</a> <a id="19490" href="Definition.Conversion.Weakening.html#6526" class="Function">wkConv↓</a><a id="19497" class="Symbol">;</a> <a id="19499" href="Definition.Conversion.Weakening.html#7364" class="Function">wkConv↑Term</a><a id="19510" class="Symbol">;</a> <a id="19512" href="Definition.Conversion.Weakening.html#8078" class="Function">wkConv↓Term</a><a id="19523" class="Symbol">;</a> <a id="19525" href="Definition.Conversion.Weakening.html#1589" class="Function">wk~↑</a><a id="19529" class="Symbol">;</a> <a id="19531" href="Definition.Conversion.Weakening.html#5817" class="Function">wk~↓</a><a id="19535" class="Symbol">)</a>
</pre>
Algorithmic equality is decidable.
<pre class="Agda"><a id="19585" class="Keyword">import</a> <a id="19592" href="Definition.Conversion.Decidable.html" class="Module">Definition.Conversion.Decidable</a>
  <a id="19626" class="Keyword">using</a> <a id="19632" class="Symbol">(</a><a id="19633" href="Definition.Conversion.Decidable.html#29697" class="Function">decConv↑</a><a id="19641" class="Symbol">;</a> <a id="19643" href="Definition.Conversion.Decidable.html#30565" class="Function">decConv↓</a><a id="19651" class="Symbol">;</a> <a id="19653" href="Definition.Conversion.Decidable.html#34356" class="Function">decConv↑Term</a><a id="19665" class="Symbol">;</a> <a id="19667" href="Definition.Conversion.Decidable.html#36438" class="Function">decConv↓Term</a><a id="19679" class="Symbol">;</a> <a id="19681" href="Definition.Conversion.Decidable.html#22940" class="Function">dec~↑</a><a id="19686" class="Symbol">;</a> <a id="19688" href="Definition.Conversion.Decidable.html#28901" class="Function">dec~↓</a><a id="19693" class="Symbol">)</a>
</pre>
Level normalisation is deterministic.
<pre class="Agda"><a id="19746" class="Keyword">import</a> <a id="19753" href="Definition.Conversion.Level.html" class="Module">Definition.Conversion.Level</a>
  <a id="19783" class="Keyword">using</a> <a id="19789" class="Symbol">(</a><a id="19790" href="Definition.Conversion.Level.html#5741" class="Function">deterministic-↑ᵛ</a><a id="19806" class="Symbol">)</a>
</pre>
Lemma 4.1.
<pre class="Agda"><a id="19832" class="Keyword">open</a> <a id="19837" class="Keyword">import</a> <a id="19844" href="Definition.Conversion.EqRelInstance.html" class="Module">Definition.Conversion.EqRelInstance</a>
  <a id="19882" class="Keyword">using</a> <a id="19888" class="Symbol">(</a><a id="19889" class="Keyword">module</a> <a id="19896" href="Definition.Conversion.EqRelInstance.html#2997" class="Module">Lemmas</a><a id="19902" class="Symbol">)</a>
<a id="19904" class="Keyword">open</a> <a id="19909" href="Definition.Conversion.EqRelInstance.html#2997" class="Module">Lemmas</a>
  <a id="19918" class="Keyword">using</a> <a id="19924" class="Symbol">(</a><a id="19925" href="Definition.Conversion.EqRelInstance.html#12091" class="Function">supᵘ-↑ᵛ</a><a id="19932" class="Symbol">)</a>
</pre>
The generic equality relation instance for algorithmic equality.
<pre class="Agda"><a id="20012" class="Keyword">import</a> <a id="20019" href="Definition.Conversion.EqRelInstance.html" class="Module">Definition.Conversion.EqRelInstance</a>
  <a id="20057" class="Keyword">using</a> <a id="20063" class="Symbol">(</a><a id="20064" href="Definition.Conversion.EqRelInstance.html#23156" class="Function">eqRelInstance</a><a id="20077" class="Symbol">)</a>
</pre>
Theorem 4.2: Algorithmic equality is complete with respect to
judgemental equality.
<pre class="Agda"><a id="20176" class="Keyword">import</a> <a id="20183" href="Definition.Conversion.Consequences.Completeness.html" class="Module">Definition.Conversion.Consequences.Completeness</a>
  <a id="20233" class="Keyword">using</a> <a id="20239" class="Symbol">(</a><a id="20240" href="Definition.Conversion.Consequences.Completeness.html#1034" class="Function">completeEq</a><a id="20250" class="Symbol">;</a> <a id="20252" href="Definition.Conversion.Consequences.Completeness.html#1327" class="Function">completeEqTerm</a><a id="20266" class="Symbol">)</a>
</pre>
Corollary 4.3: Judgemental equality of well-formed types and terms is
decidable.
<pre class="Agda"><a id="20362" class="Keyword">import</a> <a id="20369" href="Definition.Typed.Decidable.Equality.html" class="Module">Definition.Typed.Decidable.Equality</a>
  <a id="20407" class="Keyword">using</a> <a id="20413" class="Symbol">(</a><a id="20414" href="Definition.Typed.Decidable.Equality.html#958" class="Function">decEq</a><a id="20419" class="Symbol">;</a> <a id="20421" href="Definition.Typed.Decidable.Equality.html#1207" class="Function">decEqTerm</a><a id="20430" class="Symbol">)</a>
</pre>
Corollary 4.4: Deep normalisation.
<pre class="Agda"><a id="20480" class="Keyword">import</a> <a id="20487" href="Definition.Conversion.FullReduction.html" class="Module">Definition.Conversion.FullReduction</a>
  <a id="20525" class="Keyword">using</a> <a id="20531" class="Symbol">(</a><a id="20532" href="Definition.Conversion.FullReduction.html#19328" class="Function">fullRed</a><a id="20539" class="Symbol">;</a> <a id="20541" href="Definition.Conversion.FullReduction.html#19522" class="Function">fullRedTerm</a><a id="20552" class="Symbol">)</a>
</pre>
Checkable types, checkable terms and inferable terms. The code also
makes use of `Checkable-level`. If `Level` is allowed, then
`Checkable-level t` is logically equivalent to `Checkable t`.
<pre class="Agda"><a id="20757" class="Keyword">import</a> <a id="20764" href="Definition.Typechecking.html" class="Module">Definition.Typechecking</a>
  <a id="20790" class="Keyword">using</a> <a id="20796" class="Symbol">(</a><a id="20797" href="Definition.Typechecking.html#5795" class="Datatype">Checkable-type</a><a id="20811" class="Symbol">;</a> <a id="20813" href="Definition.Typechecking.html#8000" class="Datatype">Checkable</a><a id="20822" class="Symbol">;</a> <a id="20824" href="Definition.Typechecking.html#6224" class="Datatype">Inferable</a><a id="20833" class="Symbol">;</a> <a id="20835" href="Definition.Typechecking.html#8300" class="Datatype">Checkable-level</a><a id="20850" class="Symbol">)</a>
</pre>
The term Π (λ x₀) x₀ is a checkable type but not a checkable term.
Every well-formed, checkable type is inferable.
<pre class="Agda"><a id="20980" class="Keyword">import</a> <a id="20987" href="Definition.Typechecking.html" class="Module">Definition.Typechecking</a>
  <a id="21013" class="Keyword">using</a> <a id="21019" class="Symbol">(</a><a id="21020" href="Definition.Typechecking.html#9153" class="Function">Checkable-type×¬Checkable</a><a id="21045" class="Symbol">;</a> <a id="21047" href="Definition.Typechecking.html#10689" class="Function">⊢→Checkable-type→Inferable</a><a id="21073" class="Symbol">)</a>
</pre>
Theorem 4.5: Decidability of type checking/type inference for certain
classes of terms, types and contexts.
<pre class="Agda"><a id="21196" class="Keyword">import</a> <a id="21203" href="Definition.Typed.Decidable.html" class="Module">Definition.Typed.Decidable</a>
  <a id="21232" class="Keyword">using</a> <a id="21238" class="Symbol">(</a><a id="21239" href="Definition.Typed.Decidable.html#2185" class="Function">decWfCon</a><a id="21247" class="Symbol">;</a> <a id="21249" href="Definition.Typed.Decidable.html#2501" class="Function">decConTypeᶜ</a><a id="21260" class="Symbol">;</a> <a id="21262" href="Definition.Typed.Decidable.html#2788" class="Function">decConTermTypeᶜ</a><a id="21277" class="Symbol">;</a> <a id="21279" href="Definition.Typed.Decidable.html#3128" class="Function">decConTermᵢ</a><a id="21290" class="Symbol">)</a>
</pre>
### 5: Erasing Levels Is Safe

The usage relation. This relation is parametrised by a value of type
`Usage-restrictions`, which for instance makes it possible to disallow
several forms of erased matches.
<pre class="Agda"><a id="21509" class="Keyword">import</a> <a id="21516" href="Graded.Usage.html" class="Module">Graded.Usage</a>
  <a id="21531" class="Keyword">using</a> <a id="21537" class="Symbol">(</a><a id="21538" href="Graded.Usage.html#8746" class="Datatype Operator">_▸[_]_</a><a id="21544" class="Symbol">)</a>
<a id="21546" class="Keyword">import</a> <a id="21553" href="Graded.Usage.Restrictions.html" class="Module">Graded.Usage.Restrictions</a>
  <a id="21581" class="Keyword">using</a> <a id="21587" class="Symbol">(</a><a id="21588" href="Graded.Usage.Restrictions.html#812" class="Record">Usage-restrictions</a><a id="21606" class="Symbol">)</a>
</pre>
Usage contexts.
<pre class="Agda"><a id="21637" class="Keyword">import</a> <a id="21644" href="Graded.Context.html" class="Module">Graded.Context</a>
  <a id="21661" class="Keyword">using</a> <a id="21667" class="Symbol">(</a><a id="21668" href="Graded.Context.html#729" class="Datatype">Conₘ</a><a id="21672" class="Symbol">)</a>
</pre>
Modes. The development supports modalities with or without the zero
mode.
<pre class="Agda"><a id="21761" class="Keyword">import</a> <a id="21768" href="Graded.Mode.html" class="Module">Graded.Mode</a>
  <a id="21782" class="Keyword">using</a> <a id="21788" class="Symbol">(</a><a id="21789" href="Graded.Mode.html#1039" class="Datatype">Mode</a><a id="21793" class="Symbol">)</a>
</pre>
The erasure modality. The development supports two variants of the
erasure modality: with or without support for the zero mode. When the
paper refers to "the erasure modality" it is the one with support for
the zero mode that is meant.
<pre class="Agda"><a id="22044" class="Keyword">import</a> <a id="22051" href="Graded.Modality.Instances.Erasure.html" class="Module">Graded.Modality.Instances.Erasure</a>
  <a id="22087" class="Keyword">using</a> <a id="22093" class="Symbol">(</a><a id="22094" href="Graded.Modality.Instances.Erasure.html#442" class="InductiveConstructor">𝟘</a><a id="22095" class="Symbol">;</a> <a id="22097" href="Graded.Modality.Instances.Erasure.html#444" class="InductiveConstructor">ω</a><a id="22098" class="Symbol">)</a>
<a id="22100" class="Keyword">import</a> <a id="22107" href="Graded.Modality.Instances.Erasure.Modality.html" class="Module">Graded.Modality.Instances.Erasure.Modality</a>
  <a id="22152" class="Keyword">using</a> <a id="22158" class="Symbol">(</a><a id="22159" href="Graded.Modality.Instances.Erasure.Modality.html#2775" class="Function">ErasureModality</a><a id="22174" class="Symbol">)</a>
</pre>
The target language. The term appˢ t u is denoted by `t ∘⟨ s ⟩ u`, the
predicate Valueˢ is called `Value⟨ s ⟩`, sucˢ is called `suc⟨ s ⟩`, ↯ˢ
is called `loop? s`, ⇒ˢᵘᶜ is called `_⇒ˢ_`, \_⊢\_⟶ˢᵘᶜ\_:ℕ is called
`_⊢_⇒ˢ_∷ℕ`, \_⊢\_⟶ˢᵘᶜ\*\_:ℕ is called `_⊢_⇒ˢ*_∷ℕ`, ⇒\*ₛ is called
`_⇒ˢ⟨_⟩*_`, and n̲ is called `sucᵏ n`. The term loop corresponds to
`loop non-strict`.
<pre class="Agda"><a id="22552" class="Keyword">import</a> <a id="22559" href="Graded.Erasure.Target.html" class="Module">Graded.Erasure.Target</a>
  <a id="22583" class="Keyword">using</a> <a id="22589" class="Symbol">(</a><a id="22590" href="Graded.Erasure.Target.html#1253" class="Datatype">Term</a><a id="22594" class="Symbol">;</a> <a id="22596" href="Graded.Erasure.Target.html#673" class="Datatype">Strictness</a><a id="22606" class="Symbol">;</a> <a id="22608" href="Graded.Erasure.Target.html#6149" class="Datatype">Value</a><a id="22613" class="Symbol">;</a> <a id="22615" href="Graded.Erasure.Target.html#6393" class="Function Operator">Value⟨_⟩</a><a id="22623" class="Symbol">;</a> <a id="22625" href="Graded.Erasure.Target.html#7040" class="Datatype Operator">_⇒_</a><a id="22628" class="Symbol">;</a> <a id="22630" href="Graded.Erasure.Target.html#1847" class="Function Operator">suc⟨_⟩</a><a id="22636" class="Symbol">;</a> <a id="22638" href="Graded.Erasure.Target.html#6927" class="Function">sucᵏ</a><a id="22642" class="Symbol">)</a>
<a id="22644" class="Keyword">import</a> <a id="22651" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="22672" class="Keyword">using</a> <a id="22678" class="Symbol">(</a><a id="22679" href="Definition.Untyped.html#3842" class="Function">sucᵏ</a><a id="22683" class="Symbol">)</a>
<a id="22685" class="Keyword">import</a> <a id="22692" href="Graded.Erasure.Target.Non-terminating.html" class="Module">Graded.Erasure.Target.Non-terminating</a>
  <a id="22732" class="Keyword">using</a> <a id="22738" class="Symbol">(</a><a id="22739" href="Graded.Erasure.Target.Non-terminating.html#751" class="Function">loop</a><a id="22743" class="Symbol">)</a>
<a id="22745" class="Keyword">import</a> <a id="22752" href="Graded.Erasure.Extraction.html" class="Module">Graded.Erasure.Extraction</a>
  <a id="22780" class="Keyword">using</a> <a id="22786" class="Symbol">(</a><a id="22787" href="Graded.Erasure.Extraction.html#854" class="Function">loop?</a><a id="22792" class="Symbol">)</a>
<a id="22794" class="Keyword">import</a> <a id="22801" href="Graded.Erasure.SucRed.html" class="Module">Graded.Erasure.SucRed</a>
  <a id="22825" class="Keyword">using</a> <a id="22831" class="Symbol">(</a><a id="22832" href="Graded.Erasure.SucRed.html#5300" class="Datatype Operator">_⇒ˢ_</a><a id="22836" class="Symbol">;</a> <a id="22838" href="Graded.Erasure.SucRed.html#1292" class="Datatype Operator">_⊢_⇒ˢ_∷ℕ</a><a id="22846" class="Symbol">;</a> <a id="22848" href="Graded.Erasure.SucRed.html#1535" class="Datatype Operator">_⊢_⇒ˢ*_∷ℕ</a><a id="22857" class="Symbol">;</a> <a id="22859" href="Graded.Erasure.SucRed.html#8981" class="Function Operator">_⇒ˢ⟨_⟩*_</a><a id="22867" class="Symbol">)</a>
</pre>
The extraction function.
<pre class="Agda"><a id="22907" class="Keyword">import</a> <a id="22914" href="Graded.Erasure.Extraction.html" class="Module">Graded.Erasure.Extraction</a>
  <a id="22942" class="Keyword">using</a> <a id="22948" class="Symbol">(</a><a id="22949" href="Graded.Erasure.Extraction.html#2119" class="Function">erase</a><a id="22954" class="Symbol">)</a>
</pre>
Complete removal of all arguments can, in the strict setting, lead to
non-termination for the extracted program.
<pre class="Agda"><a id="23082" class="Keyword">import</a> <a id="23089" href="Graded.Erasure.Extraction.Non-terminating.html" class="Module">Graded.Erasure.Extraction.Non-terminating</a>
  <a id="23133" class="Keyword">using</a> <a id="23139" class="Symbol">(</a><a id="23140" href="Graded.Erasure.Extraction.Non-terminating.html#12385" class="Function">loops-reduces-forever</a><a id="23161" class="Symbol">;</a> <a id="23163" href="Graded.Erasure.Extraction.Non-terminating.html#13408" class="Function">⊢loops</a><a id="23169" class="Symbol">;</a> <a id="23171" href="Graded.Erasure.Extraction.Non-terminating.html#13721" class="Function">▸loops</a><a id="23177" class="Symbol">)</a>
</pre>
Theorem 5.1: Soundness of erasure. The paper uses the formulation
"erased matches are disallowed for weak Σ and unit types", but the
code uses the formulation "if the modality is non-trivial, then erased
matches are disallowed for weak Σ and unit types as well as the
identity type": the paper focuses on the erasure modality, which is
non-trivial, and identity types are mostly ignored in the text. The
statement in the code also has the condition "equality reflection is
disallowed or the context is empty".
<pre class="Agda"><a id="23702" class="Keyword">open</a> <a id="23707" class="Keyword">import</a> <a id="23714" href="Graded.Erasure.Consequences.Soundness.html" class="Module">Graded.Erasure.Consequences.Soundness</a>
<a id="23752" class="Keyword">open</a> <a id="23757" href="Graded.Erasure.Consequences.Soundness.html#6156" class="Module">Soundness</a>
  <a id="23769" class="Keyword">using</a> <a id="23775" class="Symbol">(</a><a id="23776" href="Graded.Erasure.Consequences.Soundness.html#7745" class="Function">soundness-ℕ</a><a id="23787" class="Symbol">)</a>
</pre>
Corollary 5.2: Soundness of erasure for closed terms.
<pre class="Agda"><a id="23856" class="Keyword">open</a> <a id="23861" href="Graded.Erasure.Consequences.Soundness.html#9809" class="Module">Soundness₀</a>
  <a id="23874" class="Keyword">using</a> <a id="23880" class="Symbol">(</a><a id="23881" href="Graded.Erasure.Consequences.Soundness.html#9966" class="Function">soundness-ℕ</a><a id="23892" class="Symbol">)</a>
</pre>
Some counterexamples to variants of Theorem 5.1, one for the case
where erased matches are allowed for weak Σ-types, and one for the
case where erased matches are allowed for the empty type and the
context is allowed to be inconsistent.
<pre class="Agda"><a id="24144" class="Keyword">import</a> <a id="24151" href="Graded.Erasure.Consequences.Soundness.html" class="Module">Graded.Erasure.Consequences.Soundness</a> <a id="24189" class="Keyword">using</a>
  <a id="24197" class="Symbol">(</a><a id="24198" href="Graded.Erasure.Consequences.Soundness.html#10926" class="Function">soundness-ℕ-only-source-counterexample₁</a><a id="24237" class="Symbol">;</a> <a id="24239" href="Graded.Erasure.Consequences.Soundness.html#18647" class="Function">soundness-ℕ-counterexample₆</a><a id="24266" class="Symbol">)</a>
</pre>
### 6: Discussion and Future Work

The algorithmic η-equality rule for Lift, stability of algorithmic
equality under conversion, and lifting of algorithmic equality of
atomic neutrals with types in WHNF (`Γ ⊢ t ~ u ↓ A`) to algorithmic
equality of terms in WHNF (`Γ ⊢ t [conv↓] u ∷ A`).
<pre class="Agda"><a id="24568" class="Keyword">open</a> <a id="24573" class="Keyword">import</a> <a id="24580" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="24604" class="Keyword">using</a> <a id="24610" class="Symbol">(</a><a id="24611" class="Keyword">module</a> <a id="24618" href="Definition.Conversion.html#6743" class="Module Operator">_⊢_[conv↓]_∷_</a><a id="24631" class="Symbol">)</a>
<a id="24633" class="Keyword">open</a> <a id="24638" href="Definition.Conversion.html#6743" class="Module Operator">_⊢_[conv↓]_∷_</a>
  <a id="24654" class="Keyword">using</a> <a id="24660" class="Symbol">(</a><a id="24661" href="Definition.Conversion.html#7698" class="InductiveConstructor">Lift-η</a><a id="24667" class="Symbol">)</a>
<a id="24669" class="Keyword">import</a> <a id="24676" href="Definition.Conversion.Conversion.html" class="Module">Definition.Conversion.Conversion</a>
  <a id="24711" class="Keyword">using</a> <a id="24717" class="Symbol">(</a><a id="24718" href="Definition.Conversion.Conversion.html#6364" class="Function">convConv↑Term</a><a id="24731" class="Symbol">;</a> <a id="24733" href="Definition.Conversion.Conversion.html#6549" class="Function">convConv↓Term</a><a id="24746" class="Symbol">)</a>
<a id="24748" class="Keyword">import</a> <a id="24755" href="Definition.Conversion.Lift.html" class="Module">Definition.Conversion.Lift</a>
  <a id="24784" class="Keyword">using</a> <a id="24790" class="Symbol">(</a><a id="24791" href="Definition.Conversion.Lift.html#8441" class="Function">lift~toConv↓</a><a id="24803" class="Symbol">)</a>
</pre>
## More pointers to code

Some examples, including a universe-polymorphic identity function and
a universe-polymorphic encoding of vectors (lists of a given length).
<pre class="Agda"><a id="24984" class="Keyword">import</a> <a id="24991" href="Graded.Erasure.Examples.html" class="Module">Graded.Erasure.Examples</a>
  <a id="25017" class="Keyword">using</a> <a id="25023" class="Symbol">(</a><a id="25024" href="Graded.Erasure.Examples.html#4802" class="Function">⊢id</a><a id="25027" class="Symbol">;</a> <a id="25029" href="Graded.Erasure.Examples.html#12777" class="Function">⊢Vec</a><a id="25033" class="Symbol">;</a> <a id="25035" href="Graded.Erasure.Examples.html#23317" class="Function">⊢head</a><a id="25040" class="Symbol">)</a>
</pre>