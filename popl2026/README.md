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

### 2: A Type Theory with First-Class Universe Levels

#### 2.1: Syntax

Note that large parts of the development are parametrised by a grade
type or a modality. Grades and modalities are to a large part ignored
in the paper. If one does not care about grades, then one can use a
unit type or a trivial modality:
<pre class="Agda"><a id="3675" class="Keyword">import</a> <a id="3682" href="Graded.Modality.Instances.Unit.html" class="Module">Graded.Modality.Instances.Unit</a>
  <a id="3715" class="Keyword">using</a> <a id="3721" class="Symbol">(</a><a id="3722" href="Graded.Modality.Instances.Unit.html#5376" class="Function">UnitModality</a><a id="3734" class="Symbol">)</a>
</pre>
Terms. The notation does not match the paper exactly. The notation
`zeroᵘ` is used for 0, `sucᵘ` for \_⁺, and `_supᵘ_` for \_⊔\_. Instead
of a constructor Π for Π-types there is a constructor `ΠΣ⟨_⟩_,_▷_▹_`
for *graded* Π- and Σ-types, and the constructors for lambdas and
applications also take grades. The derived notation k + t is denoted
by `sucᵘᵏ k t`, and ↓ k is denoted by `↓ᵘ k`.
<pre class="Agda"><a id="4137" class="Keyword">import</a> <a id="4144" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4165" class="Keyword">using</a> <a id="4171" class="Symbol">(</a><a id="4172" href="Definition.Untyped.html#1241" class="Datatype">Term</a><a id="4176" class="Symbol">;</a> <a id="4178" href="Definition.Untyped.html#5692" class="Function">sucᵘᵏ</a><a id="4183" class="Symbol">;</a> <a id="4185" href="Definition.Untyped.html#5848" class="Function Operator">↓ᵘ_</a><a id="4188" class="Symbol">)</a>
</pre>
Contexts. The type is more general than in the paper: the
instantiation `Con Term` corresponds to what is called Con in the
paper. Furthermore the notation does not match that used in the paper:
the notation `ε` is used for ·, and `_∙_` is used instead of \_,\_.
<pre class="Agda"><a id="4466" class="Keyword">import</a> <a id="4473" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4494" class="Keyword">using</a> <a id="4500" class="Symbol">(</a><a id="4501" href="Definition.Untyped.NotParametrised.html#882" class="Datatype">Con</a><a id="4504" class="Symbol">)</a>
</pre>
Substitution.
<pre class="Agda"><a id="4533" class="Keyword">import</a> <a id="4540" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4561" class="Keyword">using</a> <a id="4567" class="Symbol">(</a><a id="4568" href="Definition.Untyped.html#17311" class="Function Operator">_[_]</a><a id="4572" class="Symbol">)</a>
</pre>
Weakening. The notation `wk ρ t` is used instead of t[ρ], and the
notation `ρ ∷ʷ Δ ⊇ Γ` means that ρ is a well-formed weakening from Γ
to Δ (Δ ⊢ ρ : Γ in the paper). The single-step weakening p is written
`step id`: in the code this weakening is often used via
`wk1` = `wk (step id)`, and the lemmas `wk₁` and `wkTerm₁` show that
this operation is type-preserving.
<pre class="Agda"><a id="4952" class="Keyword">import</a> <a id="4959" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4980" class="Keyword">using</a> <a id="4986" class="Symbol">(</a><a id="4987" href="Definition.Untyped.html#12636" class="Function">wk</a><a id="4989" class="Symbol">;</a> <a id="4991" href="Definition.Untyped.NotParametrised.html#3041" class="InductiveConstructor">step</a><a id="4995" class="Symbol">;</a> <a id="4997" href="Definition.Untyped.NotParametrised.html#2977" class="InductiveConstructor">id</a><a id="4999" class="Symbol">;</a> <a id="5001" href="Definition.Untyped.html#14452" class="Function">wk1</a><a id="5004" class="Symbol">)</a>
<a id="5006" class="Keyword">import</a> <a id="5013" href="Definition.Typed.Weakening.html" class="Module">Definition.Typed.Weakening</a>
  <a id="5042" class="Keyword">using</a> <a id="5048" class="Symbol">(</a><a id="5049" href="Definition.Typed.Weakening.html#2544" class="Function Operator">_∷ʷ_⊇_</a><a id="5055" class="Symbol">;</a> <a id="5057" href="Definition.Typed.Weakening.html#32758" class="Function">wk₁</a><a id="5060" class="Symbol">;</a> <a id="5062" href="Definition.Typed.Weakening.html#33002" class="Function">wkTerm₁</a><a id="5069" class="Symbol">)</a>
</pre>
#### 2.2: Typing Rules

Unlike in the paper the type system is parametrised by a value of type
`Type-restrictions` that makes it possible to disallow certain things,
like certain (graded) Π- or Σ-types, the K rule or equality
reflection. For instance, the two typing rules for Π and Σ include the
assumption `ΠΣ-allowed b p q`.
<pre class="Agda"><a id="5412" class="Keyword">import</a> <a id="5419" href="Definition.Typed.Restrictions.html" class="Module">Definition.Typed.Restrictions</a>
  <a id="5451" class="Keyword">using</a> <a id="5457" class="Symbol">(</a><a id="5458" href="Definition.Typed.Restrictions.html#927" class="Record">Type-restrictions</a><a id="5475" class="Symbol">)</a>
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
<pre class="Agda"><a id="6208" class="Keyword">open</a> <a id="6213" href="Definition.Typed.Restrictions.html#927" class="Module">Definition.Typed.Restrictions.Type-restrictions</a>
  <a id="6263" class="Keyword">using</a>
    <a id="6273" class="Symbol">(</a><a id="6274" href="Definition.Typed.Restrictions.html#1193" class="Field">level-support</a><a id="6287" class="Symbol">;</a> <a id="6289" href="Definition.Typed.Restrictions.html#5583" class="Function">Level-is-small</a><a id="6303" class="Symbol">;</a> <a id="6305" href="Definition.Typed.Restrictions.html#6073" class="Function">Level-is-not-small</a><a id="6323" class="Symbol">;</a> <a id="6325" href="Definition.Typed.Restrictions.html#4738" class="Function">Level-allowed</a><a id="6338" class="Symbol">)</a>
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
<pre class="Agda"><a id="7057" class="Keyword">import</a> <a id="7064" href="Definition.Typed.Properties.Admissible.Level.html" class="Module">Definition.Typed.Properties.Admissible.Level</a>
  <a id="7111" class="Keyword">using</a> <a id="7117" class="Symbol">(</a><a id="7118" href="Definition.Typed.Properties.Admissible.Level.html#2222" class="Function">⊢Id-Level</a><a id="7127" class="Symbol">;</a> <a id="7129" href="Definition.Typed.Properties.Admissible.Level.html#1636" class="Function">¬Level-is-small→¬Level∷U</a><a id="7153" class="Symbol">)</a>
</pre>
The type system. Some typing rules have names that differ from those
in the paper. Γ ∋ x : A is denoted by `x ∷ A ∈ Γ`. The definitions use
the relations `_⊢_∷Level` and `_⊢_≡_∷Level` to support disallowing
`Level` entirely: in the case where `Level` is allowed `Γ ⊢ t ∷Level`
is logically equivalent to `Γ ⊢ t ∷ Level`, and similarly for
`_⊢_≡_∷Level`.
<pre class="Agda"><a id="7522" class="Keyword">import</a> <a id="7529" href="Definition.Typed.html" class="Module">Definition.Typed</a>
  <a id="7548" class="Keyword">using</a>
    <a id="7558" class="Symbol">(</a><a id="7559" href="Definition.Typed.html#1476" class="Datatype Operator">⊢_</a><a id="7561" class="Symbol">;</a> <a id="7563" href="Definition.Typed.html#1574" class="Datatype Operator">_⊢_</a><a id="7566" class="Symbol">;</a> <a id="7568" href="Definition.Typed.html#5996" class="Datatype Operator">_⊢_≡_</a><a id="7573" class="Symbol">;</a> <a id="7575" href="Definition.Typed.html#2034" class="Datatype Operator">_⊢_∷_</a><a id="7580" class="Symbol">;</a> <a id="7582" href="Definition.Typed.html#6762" class="Datatype Operator">_⊢_≡_∷_</a><a id="7589" class="Symbol">;</a> <a id="7591" href="Definition.Typed.html#1282" class="Datatype Operator">_∷_∈_</a><a id="7596" class="Symbol">;</a> <a id="7598" href="Definition.Typed.html#23266" class="Function Operator">_⊢_≤_∷Level</a><a id="7609" class="Symbol">;</a>
     <a id="7616" href="Definition.Typed.html#5731" class="Datatype Operator">_⊢_∷Level</a><a id="7625" class="Symbol">;</a> <a id="7627" href="Definition.Typed.html#16211" class="Datatype Operator">_⊢_≡_∷Level</a><a id="7638" class="Symbol">)</a>
</pre>
The ordering of levels induced by `_supᵘ_` is reflexive, transitive and
antisymmetric, and the right identity rule can be derived.
<pre class="Agda"><a id="7784" class="Keyword">import</a> <a id="7791" href="Definition.Typed.Properties.Admissible.Level.html" class="Module">Definition.Typed.Properties.Admissible.Level</a>
  <a id="7838" class="Keyword">using</a> <a id="7844" class="Symbol">(</a><a id="7845" href="Definition.Typed.Properties.Admissible.Level.html#2682" class="Function">⊢≤-refl</a><a id="7852" class="Symbol">;</a> <a id="7854" href="Definition.Typed.Properties.Admissible.Level.html#2883" class="Function">⊢≤-trans</a><a id="7862" class="Symbol">;</a> <a id="7864" href="Definition.Typed.Properties.Admissible.Level.html#3300" class="Function">⊢≤-antisymmetric</a><a id="7880" class="Symbol">;</a> <a id="7882" href="Definition.Typed.Properties.Admissible.Level.html#6733" class="Function">supᵘ-zeroʳⱼ</a><a id="7893" class="Symbol">)</a>
</pre>
The typing rule for `Lift` that uses the ordering of levels is
admissible.
<pre class="Agda"><a id="7983" class="Keyword">import</a> <a id="7990" href="Definition.Typed.Properties.Admissible.Lift.html" class="Module">Definition.Typed.Properties.Admissible.Lift</a>
  <a id="8036" class="Keyword">using</a> <a id="8042" class="Symbol">(</a><a id="8043" href="Definition.Typed.Properties.Admissible.Lift.html#1785" class="Function">Liftⱼ≤</a><a id="8049" class="Symbol">)</a>
</pre>
The type of the universe-polymorphic identity function does not live
in any universe, and "Π U₀ U₁" does not have a type.
<pre class="Agda"><a id="8186" class="Keyword">import</a> <a id="8193" href="Definition.Typed.Consequences.Universe.html" class="Module">Definition.Typed.Consequences.Universe</a>
  <a id="8234" class="Keyword">using</a> <a id="8240" class="Symbol">(</a><a id="8241" href="Definition.Typed.Consequences.Universe.html#2287" class="Function">the-type-of-id-does-not-have-a-type</a><a id="8276" class="Symbol">;</a> <a id="8278" href="Definition.Typed.Consequences.Universe.html#4067" class="Function">type-without-type</a><a id="8295" class="Symbol">)</a>
</pre>
Admissible typing rules for heterogeneous Π- and Σ-types.
<pre class="Agda"><a id="8368" class="Keyword">import</a> <a id="8375" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html" class="Module">Definition.Typed.Properties.Admissible.Pi-Sigma</a>
  <a id="8425" class="Keyword">using</a> <a id="8431" class="Symbol">(</a><a id="8432" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#3505" class="Function">⊢ΠΣʰ</a><a id="8436" class="Symbol">;</a> <a id="8438" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#2693" class="Function">ΠΣʰ-cong-⊢</a><a id="8448" class="Symbol">;</a> <a id="8450" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#4976" class="Function">⊢ΠΣʰ∷</a><a id="8455" class="Symbol">;</a> <a id="8457" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#4480" class="Function">ΠΣʰ-cong-⊢∷</a><a id="8468" class="Symbol">)</a>
<a id="8470" class="Keyword">import</a> <a id="8477" href="Definition.Typed.Properties.Admissible.Pi.html" class="Module">Definition.Typed.Properties.Admissible.Pi</a>
  <a id="8521" class="Keyword">using</a> <a id="8527" class="Symbol">(</a><a id="8528" href="Definition.Typed.Properties.Admissible.Pi.html#9455" class="Function">⊢lamʰ</a><a id="8533" class="Symbol">;</a> <a id="8535" href="Definition.Typed.Properties.Admissible.Pi.html#10166" class="Function">⊢∘ʰ</a><a id="8538" class="Symbol">;</a> <a id="8540" href="Definition.Typed.Properties.Admissible.Pi.html#9769" class="Function">app-congʰ</a><a id="8549" class="Symbol">;</a> <a id="8551" href="Definition.Typed.Properties.Admissible.Pi.html#10403" class="Function">β-redʰ</a><a id="8557" class="Symbol">;</a> <a id="8559" href="Definition.Typed.Properties.Admissible.Pi.html#11364" class="Function">η-eqʰ</a><a id="8564" class="Symbol">)</a>
<a id="8566" class="Keyword">import</a> <a id="8573" href="Definition.Typed.Properties.Admissible.Sigma.html" class="Module">Definition.Typed.Properties.Admissible.Sigma</a>
  <a id="8620" class="Keyword">using</a>
    <a id="8630" class="Symbol">(</a><a id="8631" href="Definition.Typed.Properties.Admissible.Sigma.html#45137" class="Function">⊢prodʰ</a><a id="8637" class="Symbol">;</a> <a id="8639" href="Definition.Typed.Properties.Admissible.Sigma.html#44525" class="Function">prodʰ-cong</a><a id="8649" class="Symbol">;</a>
     <a id="8656" href="Definition.Typed.Properties.Admissible.Sigma.html#45651" class="Function">⊢fstʰ</a><a id="8661" class="Symbol">;</a> <a id="8663" href="Definition.Typed.Properties.Admissible.Sigma.html#46085" class="Function">⊢sndʰ</a><a id="8668" class="Symbol">;</a> <a id="8670" href="Definition.Typed.Properties.Admissible.Sigma.html#45477" class="Function">fstʰ-cong</a><a id="8679" class="Symbol">;</a> <a id="8681" href="Definition.Typed.Properties.Admissible.Sigma.html#45845" class="Function">sndʰ-cong</a><a id="8690" class="Symbol">;</a> <a id="8692" href="Definition.Typed.Properties.Admissible.Sigma.html#46275" class="Function">Σʰ-β₁</a><a id="8697" class="Symbol">;</a> <a id="8699" href="Definition.Typed.Properties.Admissible.Sigma.html#47102" class="Function">Σʰ-β₂</a><a id="8704" class="Symbol">;</a> <a id="8706" href="Definition.Typed.Properties.Admissible.Sigma.html#48091" class="Function">Σʰ-η</a><a id="8710" class="Symbol">;</a>
     <a id="8717" href="Definition.Typed.Properties.Admissible.Sigma.html#55691" class="Function">⊢prodrecʰ⟨⟩</a><a id="8728" class="Symbol">;</a> <a id="8730" href="Definition.Typed.Properties.Admissible.Sigma.html#54814" class="Function">prodrecʰ⟨⟩-cong</a><a id="8745" class="Symbol">;</a> <a id="8747" href="Definition.Typed.Properties.Admissible.Sigma.html#56057" class="Function">prodrecʰ⟨⟩-β</a><a id="8759" class="Symbol">)</a>
</pre>
The type of natural numbers does not have type `U (sucᵘ l)`.
<pre class="Agda"><a id="8835" class="Keyword">import</a> <a id="8842" href="Definition.Typed.Consequences.Inequality.html" class="Module">Definition.Typed.Consequences.Inequality</a>
  <a id="8885" class="Keyword">using</a> <a id="8891" class="Symbol">(</a><a id="8892" href="Definition.Typed.Consequences.Inequality.html#24981" class="Function">¬ℕ∷U-sucᵘ</a><a id="8901" class="Symbol">)</a>
</pre>
#### 2.3: Reduction Rules

Single-step reduction and reduction for terms and types.
<pre class="Agda"><a id="9000" class="Keyword">import</a> <a id="9007" href="Definition.Typed.html" class="Module">Definition.Typed</a>
  <a id="9026" class="Keyword">using</a> <a id="9032" class="Symbol">(</a><a id="9033" href="Definition.Typed.html#16495" class="Datatype Operator">_⊢_⇒_∷_</a><a id="9040" class="Symbol">;</a> <a id="9042" href="Definition.Typed.html#22629" class="Datatype Operator">_⊢_⇒*_∷_</a><a id="9050" class="Symbol">;</a> <a id="9052" href="Definition.Typed.html#22498" class="Datatype Operator">_⊢_⇒_</a><a id="9057" class="Symbol">;</a> <a id="9059" href="Definition.Typed.html#22844" class="Datatype Operator">_⊢_⇒*_</a><a id="9065" class="Symbol">)</a>
</pre>
Neutral terms and WHNFs. Compared to the paper, we use `Neutral`
instead of Neutralᵃ for atomic neutrals and `Neutralˡ` instead of
Neutral.
<pre class="Agda"><a id="9220" class="Keyword">import</a> <a id="9227" href="Definition.Untyped.Neutral.html" class="Module">Definition.Untyped.Neutral</a>
  <a id="9256" class="Keyword">using</a> <a id="9262" class="Symbol">(</a><a id="9263" href="Definition.Untyped.Neutral.html#1014" class="Datatype">Neutral</a><a id="9270" class="Symbol">;</a> <a id="9272" href="Definition.Untyped.Neutral.html#2517" class="Datatype">Neutralˡ</a><a id="9280" class="Symbol">;</a> <a id="9282" href="Definition.Untyped.Neutral.html#3086" class="Datatype">Whnf</a><a id="9286" class="Symbol">)</a>
</pre>
Lemma 2.1: Well-formedness.
<pre class="Agda"><a id="9329" class="Keyword">import</a> <a id="9336" href="Definition.Typed.Properties.html" class="Module">Definition.Typed.Properties</a>
  <a id="9366" class="Keyword">using</a> <a id="9372" class="Symbol">(</a><a id="9373" href="Definition.Typed.Properties.Well-formed.html#13908" class="Function">wf</a><a id="9375" class="Symbol">;</a> <a id="9377" href="Definition.Typed.Properties.Well-formed.html#14328" class="Function">wfEq</a><a id="9381" class="Symbol">;</a> <a id="9383" href="Definition.Typed.Properties.Well-formed.html#14030" class="Function">wfTerm</a><a id="9389" class="Symbol">;</a> <a id="9391" href="Definition.Typed.Properties.Well-formed.html#14475" class="Function">wfEqTerm</a><a id="9399" class="Symbol">)</a>
<a id="9401" class="Keyword">import</a> <a id="9408" href="Definition.Typed.Well-formed.html" class="Module">Definition.Typed.Well-formed</a>
  <a id="9439" class="Keyword">using</a> <a id="9445" class="Symbol">(</a><a id="9446" href="Definition.Typed.Well-formed.html#3434" class="Function">wf-⊢≡</a><a id="9451" class="Symbol">;</a> <a id="9453" href="Definition.Typed.Well-formed.html#1659" class="Function">wf-⊢∷</a><a id="9458" class="Symbol">;</a> <a id="9460" href="Definition.Typed.Well-formed.html#4503" class="Function">wf-⊢≡∷</a><a id="9466" class="Symbol">)</a>
<a id="9468" class="Keyword">import</a> <a id="9475" href="Definition.Typed.Syntactic.html" class="Module">Definition.Typed.Syntactic</a>
  <a id="9504" class="Keyword">using</a> <a id="9510" class="Symbol">(</a><a id="9511" href="Definition.Typed.Syntactic.html#870" class="Function">syntacticRed</a><a id="9523" class="Symbol">;</a> <a id="9525" href="Definition.Typed.Syntactic.html#1007" class="Function">syntacticRedTerm</a><a id="9541" class="Symbol">)</a>
</pre>
### 3: A Logical Relation

External universe levels (natural numbers or ω).
<pre class="Agda"><a id="9632" class="Keyword">import</a> <a id="9639" href="Definition.Untyped.NotParametrised.html" class="Module">Definition.Untyped.NotParametrised</a>
  <a id="9676" class="Keyword">using</a> <a id="9682" class="Symbol">(</a><a id="9683" href="Definition.Untyped.NotParametrised.html#4249" class="Datatype">Universe-level</a><a id="9697" class="Symbol">)</a>
</pre>
The generic equality relations. Compared to the paper we include an
extra relation for levels, to support disallowing `Level` entirely. We
also include the type `Neutrals-included`, which is used to handle
equality reflection: in the absence of equality reflection one can
instantiate this type with something inhabited.
<pre class="Agda"><a id="10033" class="Keyword">open</a> <a id="10038" class="Keyword">import</a> <a id="10045" href="Definition.Typed.EqualityRelation.html" class="Module">Definition.Typed.EqualityRelation</a>
  <a id="10081" class="Keyword">using</a> <a id="10087" class="Symbol">(</a><a id="10088" href="Definition.Typed.EqualityRelation.html#15512" class="Record">EqRelSet</a><a id="10096" class="Symbol">)</a>
<a id="10098" class="Keyword">open</a> <a id="10103" href="Definition.Typed.EqualityRelation.html#15512" class="Module">EqRelSet</a>
  <a id="10114" class="Keyword">using</a> <a id="10120" class="Symbol">(</a><a id="10121" href="Definition.Typed.EqualityRelation.html#16024" class="Field">Neutrals-included</a><a id="10138" class="Symbol">)</a>
</pre>
The generic equality relation instance for judgemental equality. Note
that `Neutrals-included` is instantiated to `No-equality-reflection`.
<pre class="Agda"><a id="10293" class="Keyword">import</a> <a id="10300" href="Definition.Typed.EqRelInstance.html" class="Module">Definition.Typed.EqRelInstance</a>
  <a id="10333" class="Keyword">using</a> <a id="10339" class="Symbol">(</a><a id="10340" href="Definition.Typed.EqRelInstance.html#4004" class="Function">eqRelInstance</a><a id="10353" class="Symbol">)</a>
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
<pre class="Agda"><a id="10896" class="Keyword">import</a> <a id="10903" href="Definition.LogicalRelation.Unary.html" class="Module">Definition.LogicalRelation.Unary</a>
  <a id="10938" class="Keyword">using</a> <a id="10944" class="Symbol">(</a><a id="10945" href="Definition.LogicalRelation.Unary.html#1626" class="Record Operator">_⊩neNf_∷_</a><a id="10954" class="Symbol">;</a> <a id="10956" href="Definition.LogicalRelation.Unary.html#1960" class="Function">⊩neNf∷⇔⊩neNf≡∷</a><a id="10970" class="Symbol">)</a>
<a id="10972" class="Keyword">import</a> <a id="10979" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="11008" class="Keyword">using</a>
    <a id="11018" class="Symbol">(</a><a id="11019" href="Definition.LogicalRelation.html#2491" class="Record Operator">_⊩neNf_≡_∷_</a><a id="11030" class="Symbol">;</a>
     <a id="11037" href="Definition.LogicalRelation.html#3305" class="Datatype Operator">_⊩Level_∷Level</a><a id="11051" class="Symbol">;</a> <a id="11053" href="Definition.LogicalRelation.html#4348" class="Datatype Operator">_⊩Level_≡_∷Level</a><a id="11069" class="Symbol">;</a>
     <a id="11076" href="Definition.LogicalRelation.html#3654" class="Datatype">Level-prop</a><a id="11086" class="Symbol">;</a> <a id="11088" href="Definition.LogicalRelation.html#4798" class="Datatype">[Level]-prop</a><a id="11100" class="Symbol">;</a>
     <a id="11107" href="Definition.LogicalRelation.html#3950" class="Datatype">neLevel-prop</a><a id="11119" class="Symbol">;</a> <a id="11121" href="Definition.LogicalRelation.html#5529" class="Datatype">[neLevel]-prop</a><a id="11135" class="Symbol">)</a>
</pre>
If `Level-prop Γ t` holds, then `t` is in WHNF, if `neLevel-prop Γ t`
holds, then `t` is neutral, and similarly for the corresponding binary
predicates.
<pre class="Agda"><a id="11303" class="Keyword">import</a> <a id="11310" href="Definition.LogicalRelation.Properties.Whnf.html" class="Module">Definition.LogicalRelation.Properties.Whnf</a>
  <a id="11355" class="Keyword">using</a> <a id="11361" class="Symbol">(</a><a id="11362" href="Definition.LogicalRelation.Properties.Whnf.html#1131" class="Function">level</a><a id="11367" class="Symbol">;</a> <a id="11369" href="Definition.LogicalRelation.Properties.Whnf.html#896" class="Function">nelevel</a><a id="11376" class="Symbol">;</a> <a id="11378" href="Definition.LogicalRelation.Properties.Whnf.html#2214" class="Function">lsplit</a><a id="11384" class="Symbol">;</a> <a id="11386" href="Definition.LogicalRelation.Properties.Whnf.html#1342" class="Function">nelsplit</a><a id="11394" class="Symbol">)</a>
</pre>
The natural number realising a reducible level t is written `↑ⁿ [t]`,
where `[t]` is a witness that t is reducible. The corresponding
external level is written `↑ᵘ [t]`.
<pre class="Agda"><a id="11579" class="Keyword">import</a> <a id="11586" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="11615" class="Keyword">using</a> <a id="11621" class="Symbol">(</a><a id="11622" href="Definition.LogicalRelation.html#7414" class="Function Operator">↑ⁿ_</a><a id="11625" class="Symbol">;</a> <a id="11627" href="Definition.LogicalRelation.html#7844" class="Function Operator">↑ᵘ_</a><a id="11630" class="Symbol">)</a>
</pre>
The natural number realiser satisfies the specification given in the
paper, and any function that satisfies the specification is pointwise
equal to the realiser.
<pre class="Agda"><a id="11807" class="Keyword">import</a> <a id="11814" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="11864" class="Keyword">using</a> <a id="11870" class="Symbol">(</a><a id="11871" href="Definition.LogicalRelation.Properties.Primitive.html#51372" class="Function">↑ⁿ-respects-⇒*</a><a id="11885" class="Symbol">;</a> <a id="11887" href="Definition.LogicalRelation.Properties.Primitive.html#38030" class="Function">↑ⁿ-zeroᵘ</a><a id="11895" class="Symbol">;</a> <a id="11897" href="Definition.LogicalRelation.Properties.Primitive.html#38648" class="Function">↑ⁿ-sucᵘ</a><a id="11904" class="Symbol">;</a> <a id="11906" href="Definition.LogicalRelation.Properties.Primitive.html#39550" class="Function">↑ⁿ-supᵘ′</a><a id="11914" class="Symbol">;</a> <a id="11916" href="Definition.LogicalRelation.Properties.Primitive.html#37255" class="Function">↑ⁿ-ne</a><a id="11921" class="Symbol">;</a> <a id="11923" href="Definition.LogicalRelation.Properties.Primitive.html#52424" class="Function">↑ⁿ-unique</a><a id="11932" class="Symbol">)</a>
</pre>
Irrelevance for `↑ⁿ_` and `↑ᵘ_`; `↑ⁿ_` and `↑ᵘ_` respect equality and
ordering.
<pre class="Agda"><a id="12027" class="Keyword">import</a> <a id="12034" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12084" class="Keyword">using</a>
    <a id="12094" class="Symbol">(</a><a id="12095" href="Definition.LogicalRelation.Properties.Primitive.html#34372" class="Function">↑ⁿ-irrelevance</a><a id="12109" class="Symbol">;</a> <a id="12111" href="Definition.LogicalRelation.Properties.Primitive.html#36591" class="Function">↑ᵘ-irrelevance</a><a id="12125" class="Symbol">;</a>
     <a id="12132" href="Definition.LogicalRelation.Properties.Primitive.html#42288" class="Function">↑ⁿ-cong</a><a id="12139" class="Symbol">;</a> <a id="12141" href="Definition.LogicalRelation.Properties.Primitive.html#51135" class="Function">↑ᵘ-cong</a><a id="12148" class="Symbol">;</a>
     <a id="12155" href="Definition.LogicalRelation.Properties.Primitive.html#51834" class="Function">↑ⁿ-cong-≤</a><a id="12164" class="Symbol">;</a> <a id="12166" href="Definition.LogicalRelation.Properties.Primitive.html#52089" class="Function">↑ᵘ-cong-≤</a><a id="12175" class="Symbol">)</a>
</pre>
The function `_supᵘ_` respects equality in its first argument.
<pre class="Agda"><a id="12253" class="Keyword">import</a> <a id="12260" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12310" class="Keyword">using</a> <a id="12316" class="Symbol">(</a><a id="12317" href="Definition.LogicalRelation.Properties.Primitive.html#32200" class="Function">⊩supᵘ-congˡ</a><a id="12328" class="Symbol">)</a>
</pre>
Lemma 3.1: Reducibility for the typing rule for `_supᵘ_`.
<pre class="Agda"><a id="12401" class="Keyword">import</a> <a id="12408" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12458" class="Keyword">using</a> <a id="12464" class="Symbol">(</a><a id="12465" href="Definition.LogicalRelation.Properties.Primitive.html#13358" class="Function">⊩supᵘ</a><a id="12470" class="Symbol">)</a>
</pre>
Lemma 3.2: Reducibility for the judgemental equality rule supᵘ-idem.
<pre class="Agda"><a id="12554" class="Keyword">import</a> <a id="12561" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12611" class="Keyword">using</a> <a id="12617" class="Symbol">(</a><a id="12618" href="Definition.LogicalRelation.Properties.Primitive.html#22294" class="Function">⊩supᵘ-idem</a><a id="12628" class="Symbol">)</a>
</pre>
Two weak head expansion lemmas used in Lemmas 3.1 and 3.2.
<pre class="Agda"><a id="12702" class="Keyword">import</a> <a id="12709" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12759" class="Keyword">using</a> <a id="12765" class="Symbol">(</a><a id="12766" href="Definition.LogicalRelation.Properties.Primitive.html#4277" class="Function">⊩Level-⇒*</a><a id="12775" class="Symbol">;</a> <a id="12777" href="Definition.LogicalRelation.Properties.Primitive.html#3975" class="Function">redLevel′</a><a id="12786" class="Symbol">)</a>
</pre>
#### 3.2: Reducibility

The main reducibility judgements.
<pre class="Agda"><a id="12859" class="Keyword">import</a> <a id="12866" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="12895" class="Keyword">using</a> <a id="12901" class="Symbol">(</a><a id="12902" href="Definition.LogicalRelation.html#23465" class="Function Operator">_⊩⟨_⟩_</a><a id="12908" class="Symbol">;</a> <a id="12910" href="Definition.LogicalRelation.html#23600" class="Function Operator">_⊩⟨_⟩_≡_/_</a><a id="12920" class="Symbol">;</a> <a id="12922" href="Definition.LogicalRelation.html#23978" class="Function Operator">_⊩⟨_⟩_≡_∷_/_</a><a id="12934" class="Symbol">;</a> <a id="12936" href="Definition.LogicalRelation.html#23786" class="Function Operator">_⊩⟨_⟩_∷_/_</a><a id="12946" class="Symbol">)</a>
</pre>
The logical relation is cumulative.
<pre class="Agda"><a id="12997" class="Keyword">import</a> <a id="13004" href="Definition.LogicalRelation.Properties.Embedding.html" class="Module">Definition.LogicalRelation.Properties.Embedding</a>
  <a id="13054" class="Keyword">using</a> <a id="13060" class="Symbol">(</a><a id="13061" href="Definition.LogicalRelation.Properties.Embedding.html#945" class="Function">emb-≤-⊩</a><a id="13068" class="Symbol">;</a> <a id="13070" href="Definition.LogicalRelation.Properties.Embedding.html#2186" class="Function">emb-≤-⊩≡</a><a id="13078" class="Symbol">;</a> <a id="13080" href="Definition.LogicalRelation.Properties.Embedding.html#2403" class="Function">emb-≤-⊩≡∷</a><a id="13089" class="Symbol">;</a> <a id="13091" href="Definition.LogicalRelation.Properties.Embedding.html#1048" class="Function">emb-≤-⊩∷</a><a id="13099" class="Symbol">)</a>
</pre>
Reducibility for neutrals.
<pre class="Agda"><a id="13141" class="Keyword">import</a> <a id="13148" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13177" class="Keyword">using</a> <a id="13183" class="Symbol">(</a><a id="13184" href="Definition.LogicalRelation.html#1812" class="Record Operator">_⊩ne_</a><a id="13189" class="Symbol">;</a> <a id="13191" href="Definition.LogicalRelation.html#2131" class="Record Operator">_⊩ne_≡_/_</a><a id="13200" class="Symbol">;</a> <a id="13202" href="Definition.LogicalRelation.html#2801" class="Record Operator">_⊩ne_≡_∷_/_</a><a id="13213" class="Symbol">)</a>
</pre>
Reducibility for levels.
<pre class="Agda"><a id="13253" class="Keyword">import</a> <a id="13260" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13289" class="Keyword">using</a> <a id="13295" class="Symbol">(</a><a id="13296" href="Definition.LogicalRelation.html#3087" class="Function Operator">_⊩Level_</a><a id="13304" class="Symbol">;</a> <a id="13306" href="Definition.LogicalRelation.html#3188" class="Function Operator">_⊩Level_≡_</a><a id="13316" class="Symbol">;</a> <a id="13318" href="Definition.LogicalRelation.html#4348" class="Datatype Operator">_⊩Level_≡_∷Level</a><a id="13334" class="Symbol">)</a>
</pre>
Level reflexivity and well-formedness.
<pre class="Agda"><a id="13388" class="Keyword">import</a> <a id="13395" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="13445" class="Keyword">using</a> <a id="13451" class="Symbol">(</a><a id="13452" href="Definition.LogicalRelation.Properties.Primitive.html#1444" class="Function">reflLevel</a><a id="13461" class="Symbol">;</a> <a id="13463" href="Definition.LogicalRelation.Properties.Primitive.html#25302" class="Function">wf-Level-eq</a><a id="13474" class="Symbol">)</a>
</pre>
Reducibility for universes.
<pre class="Agda"><a id="13517" class="Keyword">open</a> <a id="13522" class="Keyword">import</a> <a id="13529" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13558" class="Keyword">using</a> <a id="13564" class="Symbol">(</a><a id="13565" class="Keyword">module</a> <a id="13572" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a><a id="13578" class="Symbol">)</a>
<a id="13580" class="Keyword">open</a> <a id="13585" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="13594" class="Keyword">using</a> <a id="13600" class="Symbol">(</a><a id="13601" href="Definition.LogicalRelation.html#11413" class="Record Operator">_⊩₁U_</a><a id="13606" class="Symbol">;</a> <a id="13608" href="Definition.LogicalRelation.html#11660" class="Record Operator">_⊩₁U≡_/_</a><a id="13616" class="Symbol">;</a> <a id="13618" href="Definition.LogicalRelation.html#11908" class="Record Operator">_⊩₁U_≡_∷U/_</a><a id="13629" class="Symbol">)</a>
</pre>
Types in WHNF.
<pre class="Agda"><a id="13659" class="Keyword">import</a> <a id="13666" href="Definition.Untyped.Neutral.html" class="Module">Definition.Untyped.Neutral</a>
  <a id="13695" class="Keyword">using</a> <a id="13701" class="Symbol">(</a><a id="13702" href="Definition.Untyped.Neutral.html#7007" class="Datatype">Type</a><a id="13706" class="Symbol">)</a>
</pre>
Reducibility for lift types.
<pre class="Agda"><a id="13750" class="Keyword">open</a> <a id="13755" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="13764" class="Keyword">using</a> <a id="13770" class="Symbol">(</a><a id="13771" href="Definition.LogicalRelation.html#12411" class="Record Operator">_⊩ₗLift_</a><a id="13779" class="Symbol">;</a> <a id="13781" href="Definition.LogicalRelation.html#12713" class="Record Operator">_⊩ₗLift_≡_/_</a><a id="13793" class="Symbol">;</a> <a id="13795" href="Definition.LogicalRelation.html#13074" class="Function Operator">_⊩ₗLift_≡_∷_/_</a><a id="13809" class="Symbol">)</a>
</pre>
Reducibility for Π-types (the first two definitions are used also for
Σ-types).
<pre class="Agda"><a id="13904" class="Keyword">open</a> <a id="13909" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="13918" class="Keyword">using</a> <a id="13924" class="Symbol">(</a><a id="13925" href="Definition.LogicalRelation.html#13448" class="Record Operator">_⊩ₗB⟨_⟩_</a><a id="13933" class="Symbol">;</a> <a id="13935" href="Definition.LogicalRelation.html#14403" class="Record Operator">_⊩ₗB⟨_⟩_≡_/_</a><a id="13947" class="Symbol">;</a> <a id="13949" href="Definition.LogicalRelation.html#15186" class="Function Operator">_⊩ₗΠ_≡_∷_/_</a><a id="13960" class="Symbol">)</a>
</pre>
Well-formed weakenings were introduced above. The definition of the
logical relation uses a variant of this definition which is logically
equivalent if `Neutrals-included` is inhabited.
<pre class="Agda"><a id="14161" class="Keyword">import</a> <a id="14168" href="Definition.LogicalRelation.Weakening.Restricted.html" class="Module">Definition.LogicalRelation.Weakening.Restricted</a>
  <a id="14218" class="Keyword">using</a> <a id="14224" class="Symbol">(</a><a id="14225" href="Definition.LogicalRelation.Weakening.Restricted.html#844" class="Datatype Operator">_∷ʷʳ_⊇_</a><a id="14232" class="Symbol">;</a> <a id="14234" href="Definition.LogicalRelation.Weakening.Restricted.html#1055" class="Function">∷ʷ⊇→∷ʷʳ⊇</a><a id="14242" class="Symbol">;</a> <a id="14244" href="Definition.LogicalRelation.Weakening.Restricted.html#1342" class="Function">∷ʷʳ⊇→∷ʷ⊇</a><a id="14252" class="Symbol">)</a>
</pre>
Lifting of weakenings is denoted by `lift` rather than \_⇑ (which is
used for substitutions).
<pre class="Agda"><a id="14361" class="Keyword">import</a> <a id="14368" href="Definition.Untyped.NotParametrised.html" class="Module">Definition.Untyped.NotParametrised</a>
  <a id="14405" class="Keyword">using</a> <a id="14411" class="Symbol">(</a><a id="14412" href="Definition.Untyped.NotParametrised.html#3130" class="InductiveConstructor">lift</a><a id="14416" class="Symbol">)</a>
<a id="14418" class="Keyword">import</a> <a id="14425" href="Definition.Typed.Weakening.html" class="Module">Definition.Typed.Weakening</a>
  <a id="14454" class="Keyword">using</a> <a id="14460" class="Symbol">(</a><a id="14461" href="Definition.Typed.Weakening.html#3469" class="Function">liftʷ</a><a id="14466" class="Symbol">)</a>
</pre>
Irrelevance for reducibility judgements.
<pre class="Agda"><a id="14522" class="Keyword">import</a> <a id="14529" href="Definition.LogicalRelation.Irrelevance.html" class="Module">Definition.LogicalRelation.Irrelevance</a>
  <a id="14570" class="Keyword">using</a> <a id="14576" class="Symbol">(</a><a id="14577" href="Definition.LogicalRelation.Irrelevance.html#1944" class="Function">irrelevanceEq</a><a id="14590" class="Symbol">;</a> <a id="14592" href="Definition.LogicalRelation.Irrelevance.html#7487" class="Function">irrelevanceEqTerm</a><a id="14609" class="Symbol">;</a> <a id="14611" href="Definition.LogicalRelation.Irrelevance.html#6045" class="Function">irrelevanceTerm</a><a id="14626" class="Symbol">)</a>
</pre>
Reducibility judgements with hidden reducibility arguments.
<pre class="Agda"><a id="14701" class="Keyword">import</a> <a id="14708" href="Definition.LogicalRelation.Hidden.html" class="Module">Definition.LogicalRelation.Hidden</a>
  <a id="14744" class="Keyword">using</a> <a id="14750" class="Symbol">(</a><a id="14751" href="Definition.LogicalRelation.Hidden.html#1616" class="Function Operator">_⊩⟨_⟩_∷_</a><a id="14759" class="Symbol">;</a> <a id="14761" href="Definition.LogicalRelation.Hidden.html#2021" class="Function Operator">_⊩⟨_⟩_≡_∷_</a><a id="14771" class="Symbol">;</a> <a id="14773" href="Definition.LogicalRelation.Hidden.html#1810" class="Function Operator">_⊩⟨_⟩_≡_</a><a id="14781" class="Symbol">)</a>
</pre>
#### 3.3 Validity and the Fundamental Lemma

`Γ ⊩⟨ ℓ ⟩ 𝒥` implies `Γ ⊢ 𝒥`.
<pre class="Agda"><a id="14871" class="Keyword">import</a> <a id="14878" href="Definition.LogicalRelation.Properties.Escape.html" class="Module">Definition.LogicalRelation.Properties.Escape</a>
  <a id="14925" class="Keyword">using</a> <a id="14931" class="Symbol">(</a><a id="14932" href="Definition.LogicalRelation.Properties.Escape.html#1299" class="Function">escape</a><a id="14938" class="Symbol">;</a> <a id="14940" href="Definition.LogicalRelation.Properties.Escape.html#1728" class="Function">escapeEq</a><a id="14948" class="Symbol">;</a> <a id="14950" href="Definition.LogicalRelation.Properties.Escape.html#1982" class="Function">escapeTerm</a><a id="14960" class="Symbol">;</a> <a id="14962" href="Definition.LogicalRelation.Properties.Escape.html#1864" class="Function">escapeTermEq</a><a id="14974" class="Symbol">)</a>
</pre>
Validity judgements. In addition to the ones in the paper we also use
`Γ ⊩ᵛ⟨ ℓ ⟩ t ∷Level` and `Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷Level`, which are logically
equivalent to `Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level` and `Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ Level`,
respectively, when the `Level` type is allowed.
<pre class="Agda"><a id="15245" class="Keyword">import</a> <a id="15252" href="Definition.LogicalRelation.Substitution.html" class="Module">Definition.LogicalRelation.Substitution</a>
  <a id="15294" class="Keyword">using</a>
    <a id="15304" class="Symbol">(</a><a id="15305" href="Definition.LogicalRelation.Substitution.html#1823" class="Function Operator">⊩ᵛ_</a><a id="15308" class="Symbol">;</a> <a id="15310" href="Definition.LogicalRelation.Substitution.html#1950" class="Function Operator">_⊩ᵛ⟨_⟩_</a><a id="15317" class="Symbol">;</a> <a id="15319" href="Definition.LogicalRelation.Substitution.html#2088" class="Function Operator">_⊩ᵛ⟨_⟩_≡_</a><a id="15328" class="Symbol">;</a> <a id="15330" href="Definition.LogicalRelation.Substitution.html#2677" class="Function Operator">_⊩ˢ_∷_</a><a id="15336" class="Symbol">;</a> <a id="15338" href="Definition.LogicalRelation.Substitution.html#2343" class="Function Operator">_⊩ˢ_≡_∷_</a><a id="15346" class="Symbol">;</a> <a id="15348" href="Definition.LogicalRelation.Substitution.html#3101" class="Function Operator">_⊩ᵛ⟨_⟩_∷_</a><a id="15357" class="Symbol">;</a> <a id="15359" href="Definition.LogicalRelation.Substitution.html#2821" class="Function Operator">_⊩ᵛ⟨_⟩_≡_∷_</a><a id="15370" class="Symbol">;</a>
     <a id="15377" href="Definition.LogicalRelation.Substitution.html#3660" class="Function Operator">_⊩ᵛ⟨_⟩_∷Level</a><a id="15390" class="Symbol">;</a> <a id="15392" href="Definition.LogicalRelation.Substitution.html#3264" class="Datatype Operator">_⊩ᵛ⟨_⟩_≡_∷Level</a><a id="15407" class="Symbol">;</a> <a id="15409" href="Definition.LogicalRelation.Substitution.html#11459" class="Function">⊩ᵛ∷L⇔</a><a id="15414" class="Symbol">;</a> <a id="15416" href="Definition.LogicalRelation.Substitution.html#11187" class="Function">⊩ᵛ≡∷L⇔</a><a id="15422" class="Symbol">)</a>
</pre>
Lemma 3.3: Fundamental lemma.
<pre class="Agda"><a id="15467" class="Keyword">import</a> <a id="15474" href="Definition.LogicalRelation.Fundamental.html" class="Module">Definition.LogicalRelation.Fundamental</a>
  <a id="15515" class="Keyword">using</a>
    <a id="15525" class="Symbol">(</a><a id="15526" href="Definition.LogicalRelation.Fundamental.html#1309" class="Function">valid</a><a id="15531" class="Symbol">;</a>
     <a id="15538" href="Definition.LogicalRelation.Fundamental.html#1454" class="Function">fundamental-⊩ᵛ</a><a id="15552" class="Symbol">;</a> <a id="15554" href="Definition.LogicalRelation.Fundamental.html#2075" class="Function">fundamental-⊩ᵛ≡</a><a id="15569" class="Symbol">;</a> <a id="15571" href="Definition.LogicalRelation.Fundamental.html#3351" class="Function">fundamental-⊩ᵛ∷</a><a id="15586" class="Symbol">;</a> <a id="15588" href="Definition.LogicalRelation.Fundamental.html#7267" class="Function">fundamental-⊩ᵛ≡∷</a><a id="15604" class="Symbol">)</a>
</pre>
Lemma 3.4: Validity for the term typing rule for U. The proof sketch
given in the paper does not quite match the proof used here: this
proof goes via a corresponding proof for binary validity. Similar
comments apply to Lemmas 3.5 and 3.6 below.
<pre class="Agda"><a id="15864" class="Keyword">import</a> <a id="15871" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Universe</a>
  <a id="15936" class="Keyword">using</a> <a id="15942" class="Symbol">(</a><a id="15943" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html#11289" class="Function">⊩ᵛU∷U</a><a id="15948" class="Symbol">)</a>
</pre>
Lemma 3.5: Validity for the typing rule univ.
<pre class="Agda"><a id="16009" class="Keyword">import</a> <a id="16016" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Universe</a>
  <a id="16081" class="Keyword">using</a> <a id="16087" class="Symbol">(</a><a id="16088" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html#11753" class="Function">⊩ᵛ∷U→⊩ᵛ</a><a id="16095" class="Symbol">)</a>
</pre>
Lemma 3.6: Validity for the term typing rule for Lift.
<pre class="Agda"><a id="16165" class="Keyword">import</a> <a id="16172" href="Definition.LogicalRelation.Substitution.Introductions.Lift.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Lift</a>
  <a id="16233" class="Keyword">using</a> <a id="16239" class="Symbol">(</a><a id="16240" href="Definition.LogicalRelation.Substitution.Introductions.Lift.html#7140" class="Function">Liftᵗᵛ</a><a id="16246" class="Symbol">)</a>
</pre>
Lemma 3.7: Validity for the term typing rule for Π.
<pre class="Agda"><a id="16313" class="Keyword">import</a> <a id="16320" href="Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma</a>
  <a id="16385" class="Keyword">using</a> <a id="16391" class="Symbol">(</a><a id="16392" href="Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma.html#23518" class="Function">ΠΣᵗᵛ</a><a id="16396" class="Symbol">)</a>
</pre>
Level realisers are stable under weakening.
<pre class="Agda"><a id="16455" class="Keyword">import</a> <a id="16462" href="Definition.LogicalRelation.Weakening.html" class="Module">Definition.LogicalRelation.Weakening</a>
  <a id="16501" class="Keyword">using</a> <a id="16507" class="Symbol">(</a><a id="16508" href="Definition.LogicalRelation.Weakening.html#4888" class="Function">wk-↑ⁿ</a><a id="16513" class="Symbol">;</a> <a id="16515" href="Definition.LogicalRelation.Weakening.html#7971" class="Function">wk-↑ᵘ</a><a id="16520" class="Symbol">)</a>
</pre>
Corollary 3.8: Well-typed objects are reducible.
<pre class="Agda"><a id="16584" class="Keyword">import</a> <a id="16591" href="Definition.LogicalRelation.Fundamental.Reducibility.html" class="Module">Definition.LogicalRelation.Fundamental.Reducibility</a>
  <a id="16645" class="Keyword">using</a> <a id="16651" class="Symbol">(</a><a id="16652" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1081" class="Function">reducible-⊩</a><a id="16663" class="Symbol">;</a> <a id="16665" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1299" class="Function">reducible-⊩≡</a><a id="16677" class="Symbol">;</a> <a id="16679" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1451" class="Function">reducible-⊩∷</a><a id="16691" class="Symbol">;</a> <a id="16693" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1691" class="Function">reducible-⊩≡∷</a><a id="16706" class="Symbol">)</a>
</pre>
The identity substitution is reducible.
<pre class="Agda"><a id="16761" class="Keyword">import</a> <a id="16768" href="Definition.LogicalRelation.Substitution.html" class="Module">Definition.LogicalRelation.Substitution</a>
  <a id="16810" class="Keyword">using</a> <a id="16816" class="Symbol">(</a><a id="16817" href="Definition.LogicalRelation.Substitution.html#38328" class="Function">⊩ˢ∷-idSubst</a><a id="16828" class="Symbol">)</a>
</pre>
Atomic neutrals are reducible.
<pre class="Agda"><a id="16874" class="Keyword">import</a> <a id="16881" href="Definition.LogicalRelation.Properties.Neutral.html" class="Module">Definition.LogicalRelation.Properties.Neutral</a>
</pre>
Corollary 3.9: Consistency.
<pre class="Agda"><a id="16968" class="Keyword">import</a> <a id="16975" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="17018" class="Keyword">using</a> <a id="17024" class="Symbol">(</a><a id="17025" href="Definition.Typed.Consequences.Canonicity.html#9637" class="Function">¬Empty</a><a id="17031" class="Symbol">)</a>
</pre>
Corollary 3.10: Canonicity.
<pre class="Agda"><a id="17074" class="Keyword">import</a> <a id="17081" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="17124" class="Keyword">using</a> <a id="17130" class="Symbol">(</a><a id="17131" href="Definition.Typed.Consequences.Canonicity.html#1463" class="Function">canonicity</a><a id="17141" class="Symbol">)</a>
</pre>
Corollary 3.11: Weak head normalisation.
<pre class="Agda"><a id="17197" class="Keyword">import</a> <a id="17204" href="Definition.Typed.Consequences.Reduction.html" class="Module">Definition.Typed.Consequences.Reduction</a>
  <a id="17246" class="Keyword">using</a> <a id="17252" class="Symbol">(</a><a id="17253" href="Definition.Typed.Consequences.Reduction.html#6345" class="Function">whNorm</a><a id="17259" class="Symbol">;</a> <a id="17261" href="Definition.Typed.Consequences.Reduction.html#13640" class="Function">whNormTerm</a><a id="17271" class="Symbol">)</a>
</pre>
Corollary 3.12: Injectivity of and non-confusion for type formers.
More lemmas of this kind can be found in the given modules. Statements
of the form "`A` is not derivable" are interpreted as `¬ A`; note that
if Agda is inconsistent, then `¬ A` and `A` might both be inhabited.
<pre class="Agda"><a id="17564" class="Keyword">import</a> <a id="17571" href="Definition.Typed.Consequences.Injectivity.html" class="Module">Definition.Typed.Consequences.Injectivity</a>
  <a id="17615" class="Keyword">using</a>
    <a id="17625" class="Symbol">(</a><a id="17626" href="Definition.Typed.Consequences.Injectivity.html#1286" class="Function">U-injectivity</a><a id="17639" class="Symbol">;</a> <a id="17641" href="Definition.Typed.Consequences.Injectivity.html#1560" class="Function">Lift-injectivity</a><a id="17657" class="Symbol">;</a>
     <a id="17664" href="Definition.Typed.Consequences.Injectivity.html#3097" class="Function">ΠΣ-injectivity-no-equality-reflection</a><a id="17701" class="Symbol">)</a>
<a id="17703" class="Keyword">import</a> <a id="17710" href="Definition.Typed.Consequences.Inequality.html" class="Module">Definition.Typed.Consequences.Inequality</a>
  <a id="17753" class="Keyword">using</a> <a id="17759" class="Symbol">(</a><a id="17760" href="Definition.Typed.Consequences.Inequality.html#7808" class="Function">Level≢ℕ</a><a id="17767" class="Symbol">;</a> <a id="17769" href="Definition.Typed.Consequences.Inequality.html#2857" class="Function">U≢ℕ</a><a id="17772" class="Symbol">)</a>
</pre>
Corollary 3.13: Canonicity for contexts that only contain level and
type variables.
<pre class="Agda"><a id="17871" class="Keyword">import</a> <a id="17878" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="17921" class="Keyword">using</a> <a id="17927" class="Symbol">(</a><a id="17928" href="Definition.Typed.Consequences.Canonicity.html#8636" class="Function">canonicity-Only-Level-or-U</a><a id="17954" class="Symbol">)</a>
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
<pre class="Agda"><a id="18446" class="Keyword">import</a> <a id="18453" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18477" class="Keyword">using</a>
    <a id="18487" class="Symbol">(</a><a id="18488" href="Definition.Conversion.html#5092" class="Record Operator">_⊢_[conv↑]_</a><a id="18499" class="Symbol">;</a> <a id="18501" href="Definition.Conversion.html#5380" class="Datatype Operator">_⊢_[conv↓]_</a><a id="18512" class="Symbol">;</a> <a id="18514" href="Definition.Conversion.html#6398" class="Record Operator">_⊢_[conv↑]_∷_</a><a id="18527" class="Symbol">;</a> <a id="18529" href="Definition.Conversion.html#6743" class="Datatype Operator">_⊢_[conv↓]_∷_</a><a id="18542" class="Symbol">;</a>
     <a id="18549" href="Definition.Conversion.html#1461" class="Datatype Operator">_⊢_~_↑_</a><a id="18556" class="Symbol">;</a> <a id="18558" href="Definition.Conversion.html#4591" class="Record Operator">_⊢_~_↓_</a><a id="18565" class="Symbol">)</a>
</pre>
Level atoms, `Level⁺` and level views.
<pre class="Agda"><a id="18619" class="Keyword">import</a> <a id="18626" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18650" class="Keyword">using</a> <a id="18656" class="Symbol">(</a><a id="18657" href="Definition.Conversion.html#9587" class="Datatype">LevelAtom</a><a id="18666" class="Symbol">;</a> <a id="18668" href="Definition.Conversion.html#9713" class="Function">Level⁺</a><a id="18674" class="Symbol">;</a> <a id="18676" href="Definition.Conversion.html#9775" class="Function">Levelᵛ</a><a id="18682" class="Symbol">)</a>
</pre>
Level view comparison.
<pre class="Agda"><a id="18720" class="Keyword">import</a> <a id="18727" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18751" class="Keyword">using</a> <a id="18757" class="Symbol">(</a><a id="18758" href="Definition.Conversion.html#9866" class="Function Operator">_≡ᵛ_</a><a id="18762" class="Symbol">;</a> <a id="18764" href="Definition.Conversion.html#10186" class="Function">≤ᵛ</a><a id="18766" class="Symbol">;</a> <a id="18768" href="Definition.Conversion.html#10272" class="Function">≤⁺ᵛ</a><a id="18771" class="Symbol">;</a> <a id="18773" href="Definition.Conversion.html#10351" class="Function">≤⁺</a><a id="18775" class="Symbol">;</a> <a id="18777" href="Definition.Conversion.html#10441" class="Datatype">≤ᵃ</a><a id="18779" class="Symbol">)</a>
</pre>
Operations on level views.
<pre class="Agda"><a id="18821" class="Keyword">import</a> <a id="18828" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18852" class="Keyword">using</a> <a id="18858" class="Symbol">(</a><a id="18859" href="Definition.Conversion.html#11231" class="Function">sucᵛ</a><a id="18863" class="Symbol">;</a> <a id="18865" href="Definition.Conversion.html#11299" class="Function">supᵛ</a><a id="18869" class="Symbol">)</a>
</pre>
Normalising levels into level views.
<pre class="Agda"><a id="18921" class="Keyword">import</a> <a id="18928" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18952" class="Keyword">using</a> <a id="18958" class="Symbol">(</a><a id="18959" href="Definition.Conversion.html#12274" class="Record Operator">_⊢_↑ᵛ_</a><a id="18965" class="Symbol">;</a> <a id="18967" href="Definition.Conversion.html#11466" class="Datatype Operator">_⊢_↓ᵛ_</a><a id="18973" class="Symbol">;</a> <a id="18975" href="Definition.Conversion.html#11798" class="Datatype Operator">_⊢_~ᵛ_</a><a id="18981" class="Symbol">)</a>
</pre>
Algorithmic equality is sound.
<pre class="Agda"><a id="19027" class="Keyword">import</a> <a id="19034" href="Definition.Conversion.Soundness.html" class="Module">Definition.Conversion.Soundness</a>
  <a id="19068" class="Keyword">using</a>
    <a id="19078" class="Symbol">(</a><a id="19079" href="Definition.Conversion.Soundness.html#4201" class="Function">soundnessConv↑</a><a id="19093" class="Symbol">;</a> <a id="19095" href="Definition.Conversion.Soundness.html#4444" class="Function">soundnessConv↓</a><a id="19109" class="Symbol">;</a>
     <a id="19116" href="Definition.Conversion.Soundness.html#5238" class="Function">soundnessConv↑Term</a><a id="19134" class="Symbol">;</a> <a id="19136" href="Definition.Conversion.Soundness.html#5861" class="Function">soundnessConv↓Term</a><a id="19154" class="Symbol">;</a>
     <a id="19161" href="Definition.Conversion.Soundness.html#1675" class="Function">soundness~↑</a><a id="19172" class="Symbol">;</a> <a id="19174" href="Definition.Conversion.Soundness.html#3899" class="Function">soundness~↓</a><a id="19185" class="Symbol">)</a>
</pre>
Algorithmic equality is stable under weakening.
<pre class="Agda"><a id="19248" class="Keyword">import</a> <a id="19255" href="Definition.Conversion.Weakening.html" class="Module">Definition.Conversion.Weakening</a>
  <a id="19289" class="Keyword">using</a> <a id="19295" class="Symbol">(</a><a id="19296" href="Definition.Conversion.Weakening.html#6221" class="Function">wkConv↑</a><a id="19303" class="Symbol">;</a> <a id="19305" href="Definition.Conversion.Weakening.html#6526" class="Function">wkConv↓</a><a id="19312" class="Symbol">;</a> <a id="19314" href="Definition.Conversion.Weakening.html#7364" class="Function">wkConv↑Term</a><a id="19325" class="Symbol">;</a> <a id="19327" href="Definition.Conversion.Weakening.html#8078" class="Function">wkConv↓Term</a><a id="19338" class="Symbol">;</a> <a id="19340" href="Definition.Conversion.Weakening.html#1589" class="Function">wk~↑</a><a id="19344" class="Symbol">;</a> <a id="19346" href="Definition.Conversion.Weakening.html#5817" class="Function">wk~↓</a><a id="19350" class="Symbol">)</a>
</pre>
Algorithmic equality is decidable.
<pre class="Agda"><a id="19400" class="Keyword">import</a> <a id="19407" href="Definition.Conversion.Decidable.html" class="Module">Definition.Conversion.Decidable</a>
  <a id="19441" class="Keyword">using</a> <a id="19447" class="Symbol">(</a><a id="19448" href="Definition.Conversion.Decidable.html#29697" class="Function">decConv↑</a><a id="19456" class="Symbol">;</a> <a id="19458" href="Definition.Conversion.Decidable.html#30565" class="Function">decConv↓</a><a id="19466" class="Symbol">;</a> <a id="19468" href="Definition.Conversion.Decidable.html#34356" class="Function">decConv↑Term</a><a id="19480" class="Symbol">;</a> <a id="19482" href="Definition.Conversion.Decidable.html#36438" class="Function">decConv↓Term</a><a id="19494" class="Symbol">;</a> <a id="19496" href="Definition.Conversion.Decidable.html#22940" class="Function">dec~↑</a><a id="19501" class="Symbol">;</a> <a id="19503" href="Definition.Conversion.Decidable.html#28901" class="Function">dec~↓</a><a id="19508" class="Symbol">)</a>
</pre>
Level normalisation is deterministic.
<pre class="Agda"><a id="19561" class="Keyword">import</a> <a id="19568" href="Definition.Conversion.Level.html" class="Module">Definition.Conversion.Level</a>
  <a id="19598" class="Keyword">using</a> <a id="19604" class="Symbol">(</a><a id="19605" href="Definition.Conversion.Level.html#5741" class="Function">deterministic-↑ᵛ</a><a id="19621" class="Symbol">)</a>
</pre>
Lemma 4.1.
<pre class="Agda"><a id="19647" class="Keyword">open</a> <a id="19652" class="Keyword">import</a> <a id="19659" href="Definition.Conversion.EqRelInstance.html" class="Module">Definition.Conversion.EqRelInstance</a>
  <a id="19697" class="Keyword">using</a> <a id="19703" class="Symbol">(</a><a id="19704" class="Keyword">module</a> <a id="19711" href="Definition.Conversion.EqRelInstance.html#2997" class="Module">Lemmas</a><a id="19717" class="Symbol">)</a>
<a id="19719" class="Keyword">open</a> <a id="19724" href="Definition.Conversion.EqRelInstance.html#2997" class="Module">Lemmas</a>
  <a id="19733" class="Keyword">using</a> <a id="19739" class="Symbol">(</a><a id="19740" href="Definition.Conversion.EqRelInstance.html#12091" class="Function">supᵘ-↑ᵛ</a><a id="19747" class="Symbol">)</a>
</pre>
The generic equality relation instance for algorithmic equality.
<pre class="Agda"><a id="19827" class="Keyword">import</a> <a id="19834" href="Definition.Conversion.EqRelInstance.html" class="Module">Definition.Conversion.EqRelInstance</a>
  <a id="19872" class="Keyword">using</a> <a id="19878" class="Symbol">(</a><a id="19879" href="Definition.Conversion.EqRelInstance.html#23156" class="Function">eqRelInstance</a><a id="19892" class="Symbol">)</a>
</pre>
Theorem 4.2: Algorithmic equality is complete with respect to
judgemental equality.
<pre class="Agda"><a id="19991" class="Keyword">import</a> <a id="19998" href="Definition.Conversion.Consequences.Completeness.html" class="Module">Definition.Conversion.Consequences.Completeness</a>
  <a id="20048" class="Keyword">using</a> <a id="20054" class="Symbol">(</a><a id="20055" href="Definition.Conversion.Consequences.Completeness.html#1034" class="Function">completeEq</a><a id="20065" class="Symbol">;</a> <a id="20067" href="Definition.Conversion.Consequences.Completeness.html#1327" class="Function">completeEqTerm</a><a id="20081" class="Symbol">)</a>
</pre>
Corollary 4.3: Judgemental equality of well-formed types and terms is
decidable.
<pre class="Agda"><a id="20177" class="Keyword">import</a> <a id="20184" href="Definition.Typed.Decidable.Equality.html" class="Module">Definition.Typed.Decidable.Equality</a>
  <a id="20222" class="Keyword">using</a> <a id="20228" class="Symbol">(</a><a id="20229" href="Definition.Typed.Decidable.Equality.html#958" class="Function">decEq</a><a id="20234" class="Symbol">;</a> <a id="20236" href="Definition.Typed.Decidable.Equality.html#1207" class="Function">decEqTerm</a><a id="20245" class="Symbol">)</a>
</pre>
Corollary 4.4: Deep normalisation.
<pre class="Agda"><a id="20295" class="Keyword">import</a> <a id="20302" href="Definition.Conversion.FullReduction.html" class="Module">Definition.Conversion.FullReduction</a>
  <a id="20340" class="Keyword">using</a> <a id="20346" class="Symbol">(</a><a id="20347" href="Definition.Conversion.FullReduction.html#19328" class="Function">fullRed</a><a id="20354" class="Symbol">;</a> <a id="20356" href="Definition.Conversion.FullReduction.html#19522" class="Function">fullRedTerm</a><a id="20367" class="Symbol">)</a>
</pre>
Checkable types, checkable terms and inferable terms. The code also
makes use of `Checkable-level`. If `Level` is allowed, then
`Checkable-level t` is logically equivalent to `Checkable t`.
<pre class="Agda"><a id="20572" class="Keyword">import</a> <a id="20579" href="Definition.Typechecking.html" class="Module">Definition.Typechecking</a>
  <a id="20605" class="Keyword">using</a> <a id="20611" class="Symbol">(</a><a id="20612" href="Definition.Typechecking.html#5795" class="Datatype">Checkable-type</a><a id="20626" class="Symbol">;</a> <a id="20628" href="Definition.Typechecking.html#8000" class="Datatype">Checkable</a><a id="20637" class="Symbol">;</a> <a id="20639" href="Definition.Typechecking.html#6224" class="Datatype">Inferable</a><a id="20648" class="Symbol">;</a> <a id="20650" href="Definition.Typechecking.html#8300" class="Datatype">Checkable-level</a><a id="20665" class="Symbol">)</a>
</pre>
The term Π (λ x₀) x₀ is a checkable type but not a checkable term.
Every well-formed, checkable type is inferable.
<pre class="Agda"><a id="20795" class="Keyword">import</a> <a id="20802" href="Definition.Typechecking.html" class="Module">Definition.Typechecking</a>
  <a id="20828" class="Keyword">using</a> <a id="20834" class="Symbol">(</a><a id="20835" href="Definition.Typechecking.html#9153" class="Function">Checkable-type×¬Checkable</a><a id="20860" class="Symbol">;</a> <a id="20862" href="Definition.Typechecking.html#10689" class="Function">⊢→Checkable-type→Inferable</a><a id="20888" class="Symbol">)</a>
</pre>
Theorem 4.5: Decidability of type checking/type inference for certain
classes of terms, types and contexts.
<pre class="Agda"><a id="21011" class="Keyword">import</a> <a id="21018" href="Definition.Typed.Decidable.html" class="Module">Definition.Typed.Decidable</a>
  <a id="21047" class="Keyword">using</a> <a id="21053" class="Symbol">(</a><a id="21054" href="Definition.Typed.Decidable.html#2185" class="Function">decWfCon</a><a id="21062" class="Symbol">;</a> <a id="21064" href="Definition.Typed.Decidable.html#2501" class="Function">decConTypeᶜ</a><a id="21075" class="Symbol">;</a> <a id="21077" href="Definition.Typed.Decidable.html#2788" class="Function">decConTermTypeᶜ</a><a id="21092" class="Symbol">;</a> <a id="21094" href="Definition.Typed.Decidable.html#3128" class="Function">decConTermᵢ</a><a id="21105" class="Symbol">)</a>
</pre>
### 5: Erasing Levels Is Safe

The usage relation. This relation is parametrised by a value of type
`Usage-restrictions`, which for instance makes it possible to disallow
several forms of erased matches.
<pre class="Agda"><a id="21324" class="Keyword">import</a> <a id="21331" href="Graded.Usage.html" class="Module">Graded.Usage</a>
  <a id="21346" class="Keyword">using</a> <a id="21352" class="Symbol">(</a><a id="21353" href="Graded.Usage.html#8746" class="Datatype Operator">_▸[_]_</a><a id="21359" class="Symbol">)</a>
<a id="21361" class="Keyword">import</a> <a id="21368" href="Graded.Usage.Restrictions.html" class="Module">Graded.Usage.Restrictions</a>
  <a id="21396" class="Keyword">using</a> <a id="21402" class="Symbol">(</a><a id="21403" href="Graded.Usage.Restrictions.html#812" class="Record">Usage-restrictions</a><a id="21421" class="Symbol">)</a>
</pre>
Usage contexts.
<pre class="Agda"><a id="21452" class="Keyword">import</a> <a id="21459" href="Graded.Context.html" class="Module">Graded.Context</a>
  <a id="21476" class="Keyword">using</a> <a id="21482" class="Symbol">(</a><a id="21483" href="Graded.Context.html#729" class="Datatype">Conₘ</a><a id="21487" class="Symbol">)</a>
</pre>
Modes. The development supports modalities with or without the zero
mode.
<pre class="Agda"><a id="21576" class="Keyword">import</a> <a id="21583" href="Graded.Mode.html" class="Module">Graded.Mode</a>
  <a id="21597" class="Keyword">using</a> <a id="21603" class="Symbol">(</a><a id="21604" href="Graded.Mode.html#1039" class="Datatype">Mode</a><a id="21608" class="Symbol">)</a>
</pre>
The erasure modality. The development supports two variants of the
erasure modality: with or without support for the zero mode. When the
paper refers to "the erasure modality" it is the one with support for
the zero mode that is meant.
<pre class="Agda"><a id="21859" class="Keyword">import</a> <a id="21866" href="Graded.Modality.Instances.Erasure.html" class="Module">Graded.Modality.Instances.Erasure</a>
  <a id="21902" class="Keyword">using</a> <a id="21908" class="Symbol">(</a><a id="21909" href="Graded.Modality.Instances.Erasure.html#442" class="InductiveConstructor">𝟘</a><a id="21910" class="Symbol">;</a> <a id="21912" href="Graded.Modality.Instances.Erasure.html#444" class="InductiveConstructor">ω</a><a id="21913" class="Symbol">)</a>
<a id="21915" class="Keyword">import</a> <a id="21922" href="Graded.Modality.Instances.Erasure.Modality.html" class="Module">Graded.Modality.Instances.Erasure.Modality</a>
  <a id="21967" class="Keyword">using</a> <a id="21973" class="Symbol">(</a><a id="21974" href="Graded.Modality.Instances.Erasure.Modality.html#2775" class="Function">ErasureModality</a><a id="21989" class="Symbol">)</a>
</pre>
The target language. The term appˢ t u is denoted by `t ∘⟨ s ⟩ u`, the
predicate Valueˢ is called `Value⟨ s ⟩`, sucˢ is called `suc⟨ s ⟩`, ↯ˢ
is called `loop? s`, ⇒ˢᵘᶜ is called `_⇒ˢ_`, \_⊢\_⟶ˢᵘᶜ\_:ℕ is called
`_⊢_⇒ˢ_∷ℕ`, \_⊢\_⟶ˢᵘᶜ\*\_:ℕ is called `_⊢_⇒ˢ*_∷ℕ`, ⇒\*ₛ is called
`_⇒ˢ⟨_⟩*_`, and n̲ is called `sucᵏ n`. The term loop corresponds to
`loop non-strict`.
<pre class="Agda"><a id="22367" class="Keyword">import</a> <a id="22374" href="Graded.Erasure.Target.html" class="Module">Graded.Erasure.Target</a>
  <a id="22398" class="Keyword">using</a> <a id="22404" class="Symbol">(</a><a id="22405" href="Graded.Erasure.Target.html#1253" class="Datatype">Term</a><a id="22409" class="Symbol">;</a> <a id="22411" href="Graded.Erasure.Target.html#673" class="Datatype">Strictness</a><a id="22421" class="Symbol">;</a> <a id="22423" href="Graded.Erasure.Target.html#6149" class="Datatype">Value</a><a id="22428" class="Symbol">;</a> <a id="22430" href="Graded.Erasure.Target.html#6393" class="Function Operator">Value⟨_⟩</a><a id="22438" class="Symbol">;</a> <a id="22440" href="Graded.Erasure.Target.html#7040" class="Datatype Operator">_⇒_</a><a id="22443" class="Symbol">;</a> <a id="22445" href="Graded.Erasure.Target.html#1847" class="Function Operator">suc⟨_⟩</a><a id="22451" class="Symbol">;</a> <a id="22453" href="Graded.Erasure.Target.html#6927" class="Function">sucᵏ</a><a id="22457" class="Symbol">)</a>
<a id="22459" class="Keyword">import</a> <a id="22466" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="22487" class="Keyword">using</a> <a id="22493" class="Symbol">(</a><a id="22494" href="Definition.Untyped.html#3842" class="Function">sucᵏ</a><a id="22498" class="Symbol">)</a>
<a id="22500" class="Keyword">import</a> <a id="22507" href="Graded.Erasure.Target.Non-terminating.html" class="Module">Graded.Erasure.Target.Non-terminating</a>
  <a id="22547" class="Keyword">using</a> <a id="22553" class="Symbol">(</a><a id="22554" href="Graded.Erasure.Target.Non-terminating.html#751" class="Function">loop</a><a id="22558" class="Symbol">)</a>
<a id="22560" class="Keyword">import</a> <a id="22567" href="Graded.Erasure.Extraction.html" class="Module">Graded.Erasure.Extraction</a>
  <a id="22595" class="Keyword">using</a> <a id="22601" class="Symbol">(</a><a id="22602" href="Graded.Erasure.Extraction.html#854" class="Function">loop?</a><a id="22607" class="Symbol">)</a>
<a id="22609" class="Keyword">import</a> <a id="22616" href="Graded.Erasure.SucRed.html" class="Module">Graded.Erasure.SucRed</a>
  <a id="22640" class="Keyword">using</a> <a id="22646" class="Symbol">(</a><a id="22647" href="Graded.Erasure.SucRed.html#5300" class="Datatype Operator">_⇒ˢ_</a><a id="22651" class="Symbol">;</a> <a id="22653" href="Graded.Erasure.SucRed.html#1292" class="Datatype Operator">_⊢_⇒ˢ_∷ℕ</a><a id="22661" class="Symbol">;</a> <a id="22663" href="Graded.Erasure.SucRed.html#1535" class="Datatype Operator">_⊢_⇒ˢ*_∷ℕ</a><a id="22672" class="Symbol">;</a> <a id="22674" href="Graded.Erasure.SucRed.html#8981" class="Function Operator">_⇒ˢ⟨_⟩*_</a><a id="22682" class="Symbol">)</a>
</pre>
The extraction function.
<pre class="Agda"><a id="22722" class="Keyword">import</a> <a id="22729" href="Graded.Erasure.Extraction.html" class="Module">Graded.Erasure.Extraction</a>
  <a id="22757" class="Keyword">using</a> <a id="22763" class="Symbol">(</a><a id="22764" href="Graded.Erasure.Extraction.html#2119" class="Function">erase</a><a id="22769" class="Symbol">)</a>
</pre>
Complete removal of all arguments can, in the strict setting, lead to
non-termination for the extracted program.
<pre class="Agda"><a id="22897" class="Keyword">import</a> <a id="22904" href="Graded.Erasure.Extraction.Non-terminating.html" class="Module">Graded.Erasure.Extraction.Non-terminating</a>
  <a id="22948" class="Keyword">using</a> <a id="22954" class="Symbol">(</a><a id="22955" href="Graded.Erasure.Extraction.Non-terminating.html#12385" class="Function">loops-reduces-forever</a><a id="22976" class="Symbol">;</a> <a id="22978" href="Graded.Erasure.Extraction.Non-terminating.html#13408" class="Function">⊢loops</a><a id="22984" class="Symbol">;</a> <a id="22986" href="Graded.Erasure.Extraction.Non-terminating.html#13721" class="Function">▸loops</a><a id="22992" class="Symbol">)</a>
</pre>
Theorem 5.1: Soundness of erasure. The paper uses the formulation
"erased matches are disallowed for weak Σ and unit types", but the
code uses the formulation "if the modality is non-trivial, then erased
matches are disallowed for weak Σ and unit types as well as the
identity type": the paper focuses on the erasure modality, which is
non-trivial, and identity types are mostly ignored in the text. The
statement in the code also has the condition "equality reflection is
disallowed or the context is empty".
<pre class="Agda"><a id="23517" class="Keyword">open</a> <a id="23522" class="Keyword">import</a> <a id="23529" href="Graded.Erasure.Consequences.Soundness.html" class="Module">Graded.Erasure.Consequences.Soundness</a>
<a id="23567" class="Keyword">open</a> <a id="23572" href="Graded.Erasure.Consequences.Soundness.html#6156" class="Module">Soundness</a>
  <a id="23584" class="Keyword">using</a> <a id="23590" class="Symbol">(</a><a id="23591" href="Graded.Erasure.Consequences.Soundness.html#7745" class="Function">soundness-ℕ</a><a id="23602" class="Symbol">)</a>
</pre>
Corollary 5.2: Soundness of erasure for closed terms.
<pre class="Agda"><a id="23671" class="Keyword">open</a> <a id="23676" href="Graded.Erasure.Consequences.Soundness.html#9809" class="Module">Soundness₀</a>
  <a id="23689" class="Keyword">using</a> <a id="23695" class="Symbol">(</a><a id="23696" href="Graded.Erasure.Consequences.Soundness.html#9966" class="Function">soundness-ℕ</a><a id="23707" class="Symbol">)</a>
</pre>
Some counterexamples to variants of Theorem 5.1, one for the case
where erased matches are allowed for weak Σ-types, and one for the
case where erased matches are allowed for the empty type and the
context is allowed to be inconsistent.
<pre class="Agda"><a id="23959" class="Keyword">import</a> <a id="23966" href="Graded.Erasure.Consequences.Soundness.html" class="Module">Graded.Erasure.Consequences.Soundness</a> <a id="24004" class="Keyword">using</a>
  <a id="24012" class="Symbol">(</a><a id="24013" href="Graded.Erasure.Consequences.Soundness.html#10926" class="Function">soundness-ℕ-only-source-counterexample₁</a><a id="24052" class="Symbol">;</a> <a id="24054" href="Graded.Erasure.Consequences.Soundness.html#18647" class="Function">soundness-ℕ-counterexample₆</a><a id="24081" class="Symbol">)</a>
</pre>
### 6: Discussion and Future Work

The algorithmic η-equality rule for Lift, stability of algorithmic
equality under conversion, and lifting of algorithmic equality of
atomic neutrals with types in WHNF (`Γ ⊢ t ~ u ↓ A`) to algorithmic
equality of terms in WHNF (`Γ ⊢ t [conv↓] u ∷ A`).
<pre class="Agda"><a id="24383" class="Keyword">open</a> <a id="24388" class="Keyword">import</a> <a id="24395" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="24419" class="Keyword">using</a> <a id="24425" class="Symbol">(</a><a id="24426" class="Keyword">module</a> <a id="24433" href="Definition.Conversion.html#6743" class="Module Operator">_⊢_[conv↓]_∷_</a><a id="24446" class="Symbol">)</a>
<a id="24448" class="Keyword">open</a> <a id="24453" href="Definition.Conversion.html#6743" class="Module Operator">_⊢_[conv↓]_∷_</a>
  <a id="24469" class="Keyword">using</a> <a id="24475" class="Symbol">(</a><a id="24476" href="Definition.Conversion.html#7698" class="InductiveConstructor">Lift-η</a><a id="24482" class="Symbol">)</a>
<a id="24484" class="Keyword">import</a> <a id="24491" href="Definition.Conversion.Conversion.html" class="Module">Definition.Conversion.Conversion</a>
  <a id="24526" class="Keyword">using</a> <a id="24532" class="Symbol">(</a><a id="24533" href="Definition.Conversion.Conversion.html#6364" class="Function">convConv↑Term</a><a id="24546" class="Symbol">;</a> <a id="24548" href="Definition.Conversion.Conversion.html#6549" class="Function">convConv↓Term</a><a id="24561" class="Symbol">)</a>
<a id="24563" class="Keyword">import</a> <a id="24570" href="Definition.Conversion.Lift.html" class="Module">Definition.Conversion.Lift</a>
  <a id="24599" class="Keyword">using</a> <a id="24605" class="Symbol">(</a><a id="24606" href="Definition.Conversion.Lift.html#8441" class="Function">lift~toConv↓</a><a id="24618" class="Symbol">)</a>
</pre>
## More pointers to code

Some examples, including a universe-polymorphic identity function and
a universe-polymorphic encoding of vectors (lists of a given length).
<pre class="Agda"><a id="24799" class="Keyword">import</a> <a id="24806" href="Graded.Erasure.Examples.html" class="Module">Graded.Erasure.Examples</a>
  <a id="24832" class="Keyword">using</a> <a id="24838" class="Symbol">(</a><a id="24839" href="Graded.Erasure.Examples.html#4802" class="Function">⊢id</a><a id="24842" class="Symbol">;</a> <a id="24844" href="Graded.Erasure.Examples.html#12777" class="Function">⊢Vec</a><a id="24848" class="Symbol">;</a> <a id="24850" href="Graded.Erasure.Examples.html#23317" class="Function">⊢head</a><a id="24855" class="Symbol">)</a>
</pre>