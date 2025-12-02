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
([doi:10.1145/3607862](https://doi.org/10.1145/3607862)).

Later other additions were made:

* Identity types were added by Nils Anders Danielsson (2023).

* A weak unit type was added by Oskar Eriksson (2023).

* A universe hierarchy with first-class universe levels was added
  by Nils Anders Danielsson, Naïm Camille Favier and Ondřej Kubánek
  (2024-2025): this is the focus of the discussion below.

Note also that some changes to the code were made after feedback from
anonymous reviewers.

## Pointers to code for specific definitions, theorems etc. in the paper

<pre class="Agda"><a id="3155" class="Keyword">module</a> <a id="3162" href="README.html" class="Module">README</a> <a id="3169" class="Keyword">where</a>
</pre>
Below pointers to code are included for all the main definitions,
theorems, etc. in the paper, along with some discussion of
differences between the paper and the code.

Note that if HTML has been generated from this file in a suitable way
using `agda --html`, then names in import statements below should be
linked to the corresponding definitions.

### 2: A Type Theory with First-Class Universe Levels

#### 2.1: Syntax

Note that large parts of the development are parametrised by a grade
type or a modality. Grades and modalities are to a large part ignored
in the paper. If one does not care about grades, then one can use a
unit type or a trivial modality:
<pre class="Agda"><a id="3852" class="Keyword">import</a> <a id="3859" href="Graded.Modality.Instances.Unit.html" class="Module">Graded.Modality.Instances.Unit</a>
  <a id="3892" class="Keyword">using</a> <a id="3898" class="Symbol">(</a><a id="3899" href="Graded.Modality.Instances.Unit.html#5376" class="Function">UnitModality</a><a id="3911" class="Symbol">)</a>
</pre>
Terms. The notation does not match the paper exactly. The notation
`zeroᵘ` is used for 0, `sucᵘ` for \_⁺, and `_supᵘ_` for \_⊔\_. Instead
of a constructor Π for Π-types there is a constructor `ΠΣ⟨_⟩_,_▷_▹_`
for *graded* Π- and Σ-types, and the constructors for lambdas and
applications also take grades. The derived notation k + t is denoted
by `sucᵘᵏ k t`, and ↓ k is denoted by `↓ᵘ k`.
<pre class="Agda"><a id="4314" class="Keyword">import</a> <a id="4321" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4342" class="Keyword">using</a> <a id="4348" class="Symbol">(</a><a id="4349" href="Definition.Untyped.html#1241" class="Datatype">Term</a><a id="4353" class="Symbol">;</a> <a id="4355" href="Definition.Untyped.html#5692" class="Function">sucᵘᵏ</a><a id="4360" class="Symbol">;</a> <a id="4362" href="Definition.Untyped.html#5848" class="Function Operator">↓ᵘ_</a><a id="4365" class="Symbol">)</a>
</pre>
Contexts. The type is more general than in the paper: the
instantiation `Con Term` corresponds to what is called Con in the
paper. Furthermore the notation does not match that used in the paper:
the notation `ε` is used for ·, and `_∙_` is used instead of \_,\_.
<pre class="Agda"><a id="4643" class="Keyword">import</a> <a id="4650" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4671" class="Keyword">using</a> <a id="4677" class="Symbol">(</a><a id="4678" href="Definition.Untyped.NotParametrised.html#882" class="Datatype">Con</a><a id="4681" class="Symbol">)</a>
</pre>
Substitution.
<pre class="Agda"><a id="4710" class="Keyword">import</a> <a id="4717" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="4738" class="Keyword">using</a> <a id="4744" class="Symbol">(</a><a id="4745" href="Definition.Untyped.html#17311" class="Function Operator">_[_]</a><a id="4749" class="Symbol">)</a>
</pre>
Weakening. The notation `wk ρ t` is used instead of t[ρ], and the
notation `ρ ∷ʷ Δ ⊇ Γ` means that ρ is a well-formed weakening from Γ
to Δ (Δ ⊢ ρ : Γ in the paper). The single-step weakening p is written
`step id`: in the code this weakening is often used via
`wk1` = `wk (step id)`, and the lemmas `wk₁` and `wkTerm₁` show that
this operation is type-preserving.
<pre class="Agda"><a id="5129" class="Keyword">import</a> <a id="5136" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="5157" class="Keyword">using</a> <a id="5163" class="Symbol">(</a><a id="5164" href="Definition.Untyped.html#12636" class="Function">wk</a><a id="5166" class="Symbol">;</a> <a id="5168" href="Definition.Untyped.NotParametrised.html#3041" class="InductiveConstructor">step</a><a id="5172" class="Symbol">;</a> <a id="5174" href="Definition.Untyped.NotParametrised.html#2977" class="InductiveConstructor">id</a><a id="5176" class="Symbol">;</a> <a id="5178" href="Definition.Untyped.html#14452" class="Function">wk1</a><a id="5181" class="Symbol">)</a>
<a id="5183" class="Keyword">import</a> <a id="5190" href="Definition.Typed.Weakening.html" class="Module">Definition.Typed.Weakening</a>
  <a id="5219" class="Keyword">using</a> <a id="5225" class="Symbol">(</a><a id="5226" href="Definition.Typed.Weakening.html#2544" class="Function Operator">_∷ʷ_⊇_</a><a id="5232" class="Symbol">;</a> <a id="5234" href="Definition.Typed.Weakening.html#32758" class="Function">wk₁</a><a id="5237" class="Symbol">;</a> <a id="5239" href="Definition.Typed.Weakening.html#33002" class="Function">wkTerm₁</a><a id="5246" class="Symbol">)</a>
</pre>
#### 2.2: Typing Rules

Unlike in the paper the type system is parametrised by a value of type
`Type-restrictions` that makes it possible to disallow certain things,
like certain (graded) Π- or Σ-types, the K rule or equality
reflection. For instance, the two typing rules for Π and Σ include the
assumption `ΠΣ-allowed b p q`.
<pre class="Agda"><a id="5589" class="Keyword">import</a> <a id="5596" href="Definition.Typed.Restrictions.html" class="Module">Definition.Typed.Restrictions</a>
  <a id="5628" class="Keyword">using</a> <a id="5634" class="Symbol">(</a><a id="5635" href="Definition.Typed.Restrictions.html#927" class="Record">Type-restrictions</a><a id="5652" class="Symbol">)</a>
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
<pre class="Agda"><a id="6385" class="Keyword">open</a> <a id="6390" href="Definition.Typed.Restrictions.html#927" class="Module">Definition.Typed.Restrictions.Type-restrictions</a>
  <a id="6440" class="Keyword">using</a>
    <a id="6450" class="Symbol">(</a><a id="6451" href="Definition.Typed.Restrictions.html#1193" class="Field">level-support</a><a id="6464" class="Symbol">;</a> <a id="6466" href="Definition.Typed.Restrictions.html#5583" class="Function">Level-is-small</a><a id="6480" class="Symbol">;</a> <a id="6482" href="Definition.Typed.Restrictions.html#6073" class="Function">Level-is-not-small</a><a id="6500" class="Symbol">;</a> <a id="6502" href="Definition.Typed.Restrictions.html#4738" class="Function">Level-allowed</a><a id="6515" class="Symbol">)</a>
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
<pre class="Agda"><a id="7234" class="Keyword">import</a> <a id="7241" href="Definition.Typed.Properties.Admissible.Level.html" class="Module">Definition.Typed.Properties.Admissible.Level</a>
  <a id="7288" class="Keyword">using</a> <a id="7294" class="Symbol">(</a><a id="7295" href="Definition.Typed.Properties.Admissible.Level.html#2222" class="Function">⊢Id-Level</a><a id="7304" class="Symbol">;</a> <a id="7306" href="Definition.Typed.Properties.Admissible.Level.html#1636" class="Function">¬Level-is-small→¬Level∷U</a><a id="7330" class="Symbol">)</a>
</pre>
The type system. Some typing rules have names that differ from those
in the paper. Γ ∋ x : A is denoted by `x ∷ A ∈ Γ`. The definitions use
the relations `_⊢_∷Level` and `_⊢_≡_∷Level` to support disallowing
`Level` entirely: in the case where `Level` is allowed `Γ ⊢ t ∷Level`
is logically equivalent to `Γ ⊢ t ∷ Level`, and similarly for
`_⊢_≡_∷Level`.
<pre class="Agda"><a id="7699" class="Keyword">import</a> <a id="7706" href="Definition.Typed.html" class="Module">Definition.Typed</a>
  <a id="7725" class="Keyword">using</a>
    <a id="7735" class="Symbol">(</a><a id="7736" href="Definition.Typed.html#1476" class="Datatype Operator">⊢_</a><a id="7738" class="Symbol">;</a> <a id="7740" href="Definition.Typed.html#1574" class="Datatype Operator">_⊢_</a><a id="7743" class="Symbol">;</a> <a id="7745" href="Definition.Typed.html#5996" class="Datatype Operator">_⊢_≡_</a><a id="7750" class="Symbol">;</a> <a id="7752" href="Definition.Typed.html#2034" class="Datatype Operator">_⊢_∷_</a><a id="7757" class="Symbol">;</a> <a id="7759" href="Definition.Typed.html#6762" class="Datatype Operator">_⊢_≡_∷_</a><a id="7766" class="Symbol">;</a> <a id="7768" href="Definition.Typed.html#1282" class="Datatype Operator">_∷_∈_</a><a id="7773" class="Symbol">;</a> <a id="7775" href="Definition.Typed.html#23266" class="Function Operator">_⊢_≤_∷Level</a><a id="7786" class="Symbol">;</a>
     <a id="7793" href="Definition.Typed.html#5731" class="Datatype Operator">_⊢_∷Level</a><a id="7802" class="Symbol">;</a> <a id="7804" href="Definition.Typed.html#16211" class="Datatype Operator">_⊢_≡_∷Level</a><a id="7815" class="Symbol">)</a>
</pre>
The ordering of levels induced by `_supᵘ_` is reflexive, transitive and
antisymmetric, and the right identity rule can be derived.
<pre class="Agda"><a id="7961" class="Keyword">import</a> <a id="7968" href="Definition.Typed.Properties.Admissible.Level.html" class="Module">Definition.Typed.Properties.Admissible.Level</a>
  <a id="8015" class="Keyword">using</a> <a id="8021" class="Symbol">(</a><a id="8022" href="Definition.Typed.Properties.Admissible.Level.html#2682" class="Function">⊢≤-refl</a><a id="8029" class="Symbol">;</a> <a id="8031" href="Definition.Typed.Properties.Admissible.Level.html#2883" class="Function">⊢≤-trans</a><a id="8039" class="Symbol">;</a> <a id="8041" href="Definition.Typed.Properties.Admissible.Level.html#3300" class="Function">⊢≤-antisymmetric</a><a id="8057" class="Symbol">;</a> <a id="8059" href="Definition.Typed.Properties.Admissible.Level.html#6733" class="Function">supᵘ-zeroʳⱼ</a><a id="8070" class="Symbol">)</a>
</pre>
The typing rule for `Lift` that uses the ordering of levels is
admissible.
<pre class="Agda"><a id="8160" class="Keyword">import</a> <a id="8167" href="Definition.Typed.Properties.Admissible.Lift.html" class="Module">Definition.Typed.Properties.Admissible.Lift</a>
  <a id="8213" class="Keyword">using</a> <a id="8219" class="Symbol">(</a><a id="8220" href="Definition.Typed.Properties.Admissible.Lift.html#1785" class="Function">Liftⱼ≤</a><a id="8226" class="Symbol">)</a>
</pre>
The type of the universe-polymorphic identity function does not live
in any universe, and "Π U₀ U₁" does not have a type.
<pre class="Agda"><a id="8363" class="Keyword">import</a> <a id="8370" href="Definition.Typed.Consequences.Universe.html" class="Module">Definition.Typed.Consequences.Universe</a>
  <a id="8411" class="Keyword">using</a> <a id="8417" class="Symbol">(</a><a id="8418" href="Definition.Typed.Consequences.Universe.html#2287" class="Function">the-type-of-id-does-not-have-a-type</a><a id="8453" class="Symbol">;</a> <a id="8455" href="Definition.Typed.Consequences.Universe.html#4067" class="Function">type-without-type</a><a id="8472" class="Symbol">)</a>
</pre>
Admissible typing rules for heterogeneous Π- and Σ-types.
<pre class="Agda"><a id="8545" class="Keyword">import</a> <a id="8552" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html" class="Module">Definition.Typed.Properties.Admissible.Pi-Sigma</a>
  <a id="8602" class="Keyword">using</a> <a id="8608" class="Symbol">(</a><a id="8609" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#3505" class="Function">⊢ΠΣʰ</a><a id="8613" class="Symbol">;</a> <a id="8615" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#2693" class="Function">ΠΣʰ-cong-⊢</a><a id="8625" class="Symbol">;</a> <a id="8627" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#4976" class="Function">⊢ΠΣʰ∷</a><a id="8632" class="Symbol">;</a> <a id="8634" href="Definition.Typed.Properties.Admissible.Pi-Sigma.html#4480" class="Function">ΠΣʰ-cong-⊢∷</a><a id="8645" class="Symbol">)</a>
<a id="8647" class="Keyword">import</a> <a id="8654" href="Definition.Typed.Properties.Admissible.Pi.html" class="Module">Definition.Typed.Properties.Admissible.Pi</a>
  <a id="8698" class="Keyword">using</a> <a id="8704" class="Symbol">(</a><a id="8705" href="Definition.Typed.Properties.Admissible.Pi.html#9455" class="Function">⊢lamʰ</a><a id="8710" class="Symbol">;</a> <a id="8712" href="Definition.Typed.Properties.Admissible.Pi.html#10166" class="Function">⊢∘ʰ</a><a id="8715" class="Symbol">;</a> <a id="8717" href="Definition.Typed.Properties.Admissible.Pi.html#9769" class="Function">app-congʰ</a><a id="8726" class="Symbol">;</a> <a id="8728" href="Definition.Typed.Properties.Admissible.Pi.html#10403" class="Function">β-redʰ</a><a id="8734" class="Symbol">;</a> <a id="8736" href="Definition.Typed.Properties.Admissible.Pi.html#11364" class="Function">η-eqʰ</a><a id="8741" class="Symbol">)</a>
<a id="8743" class="Keyword">import</a> <a id="8750" href="Definition.Typed.Properties.Admissible.Sigma.html" class="Module">Definition.Typed.Properties.Admissible.Sigma</a>
  <a id="8797" class="Keyword">using</a>
    <a id="8807" class="Symbol">(</a><a id="8808" href="Definition.Typed.Properties.Admissible.Sigma.html#45137" class="Function">⊢prodʰ</a><a id="8814" class="Symbol">;</a> <a id="8816" href="Definition.Typed.Properties.Admissible.Sigma.html#44525" class="Function">prodʰ-cong</a><a id="8826" class="Symbol">;</a>
     <a id="8833" href="Definition.Typed.Properties.Admissible.Sigma.html#45651" class="Function">⊢fstʰ</a><a id="8838" class="Symbol">;</a> <a id="8840" href="Definition.Typed.Properties.Admissible.Sigma.html#46085" class="Function">⊢sndʰ</a><a id="8845" class="Symbol">;</a> <a id="8847" href="Definition.Typed.Properties.Admissible.Sigma.html#45477" class="Function">fstʰ-cong</a><a id="8856" class="Symbol">;</a> <a id="8858" href="Definition.Typed.Properties.Admissible.Sigma.html#45845" class="Function">sndʰ-cong</a><a id="8867" class="Symbol">;</a> <a id="8869" href="Definition.Typed.Properties.Admissible.Sigma.html#46275" class="Function">Σʰ-β₁</a><a id="8874" class="Symbol">;</a> <a id="8876" href="Definition.Typed.Properties.Admissible.Sigma.html#47102" class="Function">Σʰ-β₂</a><a id="8881" class="Symbol">;</a> <a id="8883" href="Definition.Typed.Properties.Admissible.Sigma.html#48091" class="Function">Σʰ-η</a><a id="8887" class="Symbol">;</a>
     <a id="8894" href="Definition.Typed.Properties.Admissible.Sigma.html#55691" class="Function">⊢prodrecʰ⟨⟩</a><a id="8905" class="Symbol">;</a> <a id="8907" href="Definition.Typed.Properties.Admissible.Sigma.html#54814" class="Function">prodrecʰ⟨⟩-cong</a><a id="8922" class="Symbol">;</a> <a id="8924" href="Definition.Typed.Properties.Admissible.Sigma.html#56057" class="Function">prodrecʰ⟨⟩-β</a><a id="8936" class="Symbol">)</a>
</pre>
The type of natural numbers does not have type `U (sucᵘ l)`.
<pre class="Agda"><a id="9012" class="Keyword">import</a> <a id="9019" href="Definition.Typed.Consequences.Inequality.html" class="Module">Definition.Typed.Consequences.Inequality</a>
  <a id="9062" class="Keyword">using</a> <a id="9068" class="Symbol">(</a><a id="9069" href="Definition.Typed.Consequences.Inequality.html#24981" class="Function">¬ℕ∷U-sucᵘ</a><a id="9078" class="Symbol">)</a>
</pre>
#### 2.3: Reduction Rules

Single-step reduction and reduction for terms and types.
<pre class="Agda"><a id="9177" class="Keyword">import</a> <a id="9184" href="Definition.Typed.html" class="Module">Definition.Typed</a>
  <a id="9203" class="Keyword">using</a> <a id="9209" class="Symbol">(</a><a id="9210" href="Definition.Typed.html#16495" class="Datatype Operator">_⊢_⇒_∷_</a><a id="9217" class="Symbol">;</a> <a id="9219" href="Definition.Typed.html#22629" class="Datatype Operator">_⊢_⇒*_∷_</a><a id="9227" class="Symbol">;</a> <a id="9229" href="Definition.Typed.html#22498" class="Datatype Operator">_⊢_⇒_</a><a id="9234" class="Symbol">;</a> <a id="9236" href="Definition.Typed.html#22844" class="Datatype Operator">_⊢_⇒*_</a><a id="9242" class="Symbol">)</a>
</pre>
Neutral terms and WHNFs. Compared to the paper, we use `Neutral`
instead of Neutralᵃ for atomic neutrals and `Neutralˡ` instead of
Neutral.
<pre class="Agda"><a id="9397" class="Keyword">import</a> <a id="9404" href="Definition.Untyped.Neutral.html" class="Module">Definition.Untyped.Neutral</a>
  <a id="9433" class="Keyword">using</a> <a id="9439" class="Symbol">(</a><a id="9440" href="Definition.Untyped.Neutral.html#1014" class="Datatype">Neutral</a><a id="9447" class="Symbol">;</a> <a id="9449" href="Definition.Untyped.Neutral.html#2517" class="Datatype">Neutralˡ</a><a id="9457" class="Symbol">;</a> <a id="9459" href="Definition.Untyped.Neutral.html#3086" class="Datatype">Whnf</a><a id="9463" class="Symbol">)</a>
</pre>
Lemma 2.1: Well-formedness.
<pre class="Agda"><a id="9506" class="Keyword">import</a> <a id="9513" href="Definition.Typed.Properties.html" class="Module">Definition.Typed.Properties</a>
  <a id="9543" class="Keyword">using</a> <a id="9549" class="Symbol">(</a><a id="9550" href="Definition.Typed.Properties.Well-formed.html#13908" class="Function">wf</a><a id="9552" class="Symbol">;</a> <a id="9554" href="Definition.Typed.Properties.Well-formed.html#14328" class="Function">wfEq</a><a id="9558" class="Symbol">;</a> <a id="9560" href="Definition.Typed.Properties.Well-formed.html#14030" class="Function">wfTerm</a><a id="9566" class="Symbol">;</a> <a id="9568" href="Definition.Typed.Properties.Well-formed.html#14475" class="Function">wfEqTerm</a><a id="9576" class="Symbol">)</a>
<a id="9578" class="Keyword">import</a> <a id="9585" href="Definition.Typed.Well-formed.html" class="Module">Definition.Typed.Well-formed</a>
  <a id="9616" class="Keyword">using</a> <a id="9622" class="Symbol">(</a><a id="9623" href="Definition.Typed.Well-formed.html#3434" class="Function">wf-⊢≡</a><a id="9628" class="Symbol">;</a> <a id="9630" href="Definition.Typed.Well-formed.html#1659" class="Function">wf-⊢∷</a><a id="9635" class="Symbol">;</a> <a id="9637" href="Definition.Typed.Well-formed.html#4503" class="Function">wf-⊢≡∷</a><a id="9643" class="Symbol">)</a>
<a id="9645" class="Keyword">import</a> <a id="9652" href="Definition.Typed.Syntactic.html" class="Module">Definition.Typed.Syntactic</a>
  <a id="9681" class="Keyword">using</a> <a id="9687" class="Symbol">(</a><a id="9688" href="Definition.Typed.Syntactic.html#870" class="Function">syntacticRed</a><a id="9700" class="Symbol">;</a> <a id="9702" href="Definition.Typed.Syntactic.html#1007" class="Function">syntacticRedTerm</a><a id="9718" class="Symbol">)</a>
</pre>
### 3: A Logical Relation

External universe levels (natural numbers or ω).
<pre class="Agda"><a id="9809" class="Keyword">import</a> <a id="9816" href="Definition.Untyped.NotParametrised.html" class="Module">Definition.Untyped.NotParametrised</a>
  <a id="9853" class="Keyword">using</a> <a id="9859" class="Symbol">(</a><a id="9860" href="Definition.Untyped.NotParametrised.html#4249" class="Datatype">Universe-level</a><a id="9874" class="Symbol">)</a>
</pre>
The generic equality relations. Compared to the paper we include an
extra relation for levels, to support disallowing `Level` entirely. We
also include the type `Neutrals-included`, which is used to handle
equality reflection: in the absence of equality reflection one can
instantiate this type with something inhabited.
<pre class="Agda"><a id="10210" class="Keyword">open</a> <a id="10215" class="Keyword">import</a> <a id="10222" href="Definition.Typed.EqualityRelation.html" class="Module">Definition.Typed.EqualityRelation</a>
  <a id="10258" class="Keyword">using</a> <a id="10264" class="Symbol">(</a><a id="10265" href="Definition.Typed.EqualityRelation.html#15512" class="Record">EqRelSet</a><a id="10273" class="Symbol">)</a>
<a id="10275" class="Keyword">open</a> <a id="10280" href="Definition.Typed.EqualityRelation.html#15512" class="Module">EqRelSet</a>
  <a id="10291" class="Keyword">using</a> <a id="10297" class="Symbol">(</a><a id="10298" href="Definition.Typed.EqualityRelation.html#16024" class="Field">Neutrals-included</a><a id="10315" class="Symbol">)</a>
</pre>
The generic equality relation instance for judgemental equality. Note
that `Neutrals-included` is instantiated to `No-equality-reflection`.
<pre class="Agda"><a id="10470" class="Keyword">import</a> <a id="10477" href="Definition.Typed.EqRelInstance.html" class="Module">Definition.Typed.EqRelInstance</a>
  <a id="10510" class="Keyword">using</a> <a id="10516" class="Symbol">(</a><a id="10517" href="Definition.Typed.EqRelInstance.html#4004" class="Function">eqRelInstance</a><a id="10530" class="Symbol">)</a>
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
<pre class="Agda"><a id="11073" class="Keyword">import</a> <a id="11080" href="Definition.LogicalRelation.Unary.html" class="Module">Definition.LogicalRelation.Unary</a>
  <a id="11115" class="Keyword">using</a> <a id="11121" class="Symbol">(</a><a id="11122" href="Definition.LogicalRelation.Unary.html#1626" class="Record Operator">_⊩neNf_∷_</a><a id="11131" class="Symbol">;</a> <a id="11133" href="Definition.LogicalRelation.Unary.html#1960" class="Function">⊩neNf∷⇔⊩neNf≡∷</a><a id="11147" class="Symbol">)</a>
<a id="11149" class="Keyword">import</a> <a id="11156" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="11185" class="Keyword">using</a>
    <a id="11195" class="Symbol">(</a><a id="11196" href="Definition.LogicalRelation.html#2491" class="Record Operator">_⊩neNf_≡_∷_</a><a id="11207" class="Symbol">;</a>
     <a id="11214" href="Definition.LogicalRelation.html#3305" class="Datatype Operator">_⊩Level_∷Level</a><a id="11228" class="Symbol">;</a> <a id="11230" href="Definition.LogicalRelation.html#4348" class="Datatype Operator">_⊩Level_≡_∷Level</a><a id="11246" class="Symbol">;</a>
     <a id="11253" href="Definition.LogicalRelation.html#3654" class="Datatype">Level-prop</a><a id="11263" class="Symbol">;</a> <a id="11265" href="Definition.LogicalRelation.html#4798" class="Datatype">[Level]-prop</a><a id="11277" class="Symbol">;</a>
     <a id="11284" href="Definition.LogicalRelation.html#3950" class="Datatype">neLevel-prop</a><a id="11296" class="Symbol">;</a> <a id="11298" href="Definition.LogicalRelation.html#5529" class="Datatype">[neLevel]-prop</a><a id="11312" class="Symbol">)</a>
</pre>
If `Level-prop Γ t` holds, then `t` is in WHNF, if `neLevel-prop Γ t`
holds, then `t` is neutral, and similarly for the corresponding binary
predicates.
<pre class="Agda"><a id="11480" class="Keyword">import</a> <a id="11487" href="Definition.LogicalRelation.Properties.Whnf.html" class="Module">Definition.LogicalRelation.Properties.Whnf</a>
  <a id="11532" class="Keyword">using</a> <a id="11538" class="Symbol">(</a><a id="11539" href="Definition.LogicalRelation.Properties.Whnf.html#1131" class="Function">level</a><a id="11544" class="Symbol">;</a> <a id="11546" href="Definition.LogicalRelation.Properties.Whnf.html#896" class="Function">nelevel</a><a id="11553" class="Symbol">;</a> <a id="11555" href="Definition.LogicalRelation.Properties.Whnf.html#2214" class="Function">lsplit</a><a id="11561" class="Symbol">;</a> <a id="11563" href="Definition.LogicalRelation.Properties.Whnf.html#1342" class="Function">nelsplit</a><a id="11571" class="Symbol">)</a>
</pre>
The natural number realising a reducible level t is written `↑ⁿ [t]`,
where `[t]` is a witness that t is reducible. The corresponding
external level is written `↑ᵘ [t]`.
<pre class="Agda"><a id="11756" class="Keyword">import</a> <a id="11763" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="11792" class="Keyword">using</a> <a id="11798" class="Symbol">(</a><a id="11799" href="Definition.LogicalRelation.html#7414" class="Function Operator">↑ⁿ_</a><a id="11802" class="Symbol">;</a> <a id="11804" href="Definition.LogicalRelation.html#7844" class="Function Operator">↑ᵘ_</a><a id="11807" class="Symbol">)</a>
</pre>
The natural number realiser satisfies the specification given in the
paper, and any function that satisfies the specification is pointwise
equal to the realiser.
<pre class="Agda"><a id="11984" class="Keyword">import</a> <a id="11991" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12041" class="Keyword">using</a> <a id="12047" class="Symbol">(</a><a id="12048" href="Definition.LogicalRelation.Properties.Primitive.html#51372" class="Function">↑ⁿ-respects-⇒*</a><a id="12062" class="Symbol">;</a> <a id="12064" href="Definition.LogicalRelation.Properties.Primitive.html#38030" class="Function">↑ⁿ-zeroᵘ</a><a id="12072" class="Symbol">;</a> <a id="12074" href="Definition.LogicalRelation.Properties.Primitive.html#38648" class="Function">↑ⁿ-sucᵘ</a><a id="12081" class="Symbol">;</a> <a id="12083" href="Definition.LogicalRelation.Properties.Primitive.html#39550" class="Function">↑ⁿ-supᵘ′</a><a id="12091" class="Symbol">;</a> <a id="12093" href="Definition.LogicalRelation.Properties.Primitive.html#37255" class="Function">↑ⁿ-ne</a><a id="12098" class="Symbol">;</a> <a id="12100" href="Definition.LogicalRelation.Properties.Primitive.html#52424" class="Function">↑ⁿ-unique</a><a id="12109" class="Symbol">)</a>
</pre>
Irrelevance for `↑ⁿ_` and `↑ᵘ_`; `↑ⁿ_` and `↑ᵘ_` respect equality and
ordering.
<pre class="Agda"><a id="12204" class="Keyword">import</a> <a id="12211" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12261" class="Keyword">using</a>
    <a id="12271" class="Symbol">(</a><a id="12272" href="Definition.LogicalRelation.Properties.Primitive.html#34372" class="Function">↑ⁿ-irrelevance</a><a id="12286" class="Symbol">;</a> <a id="12288" href="Definition.LogicalRelation.Properties.Primitive.html#36591" class="Function">↑ᵘ-irrelevance</a><a id="12302" class="Symbol">;</a>
     <a id="12309" href="Definition.LogicalRelation.Properties.Primitive.html#42288" class="Function">↑ⁿ-cong</a><a id="12316" class="Symbol">;</a> <a id="12318" href="Definition.LogicalRelation.Properties.Primitive.html#51135" class="Function">↑ᵘ-cong</a><a id="12325" class="Symbol">;</a>
     <a id="12332" href="Definition.LogicalRelation.Properties.Primitive.html#51834" class="Function">↑ⁿ-cong-≤</a><a id="12341" class="Symbol">;</a> <a id="12343" href="Definition.LogicalRelation.Properties.Primitive.html#52089" class="Function">↑ᵘ-cong-≤</a><a id="12352" class="Symbol">)</a>
</pre>
The function `_supᵘ_` respects equality in its first argument.
<pre class="Agda"><a id="12430" class="Keyword">import</a> <a id="12437" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12487" class="Keyword">using</a> <a id="12493" class="Symbol">(</a><a id="12494" href="Definition.LogicalRelation.Properties.Primitive.html#32200" class="Function">⊩supᵘ-congˡ</a><a id="12505" class="Symbol">)</a>
</pre>
Lemma 3.1: Reducibility for the typing rule for `_supᵘ_`.
<pre class="Agda"><a id="12578" class="Keyword">import</a> <a id="12585" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12635" class="Keyword">using</a> <a id="12641" class="Symbol">(</a><a id="12642" href="Definition.LogicalRelation.Properties.Primitive.html#13358" class="Function">⊩supᵘ</a><a id="12647" class="Symbol">)</a>
</pre>
Lemma 3.2: Reducibility for the judgemental equality rule supᵘ-idem.
<pre class="Agda"><a id="12731" class="Keyword">import</a> <a id="12738" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12788" class="Keyword">using</a> <a id="12794" class="Symbol">(</a><a id="12795" href="Definition.LogicalRelation.Properties.Primitive.html#22294" class="Function">⊩supᵘ-idem</a><a id="12805" class="Symbol">)</a>
</pre>
Two weak head expansion lemmas used in Lemmas 3.1 and 3.2.
<pre class="Agda"><a id="12879" class="Keyword">import</a> <a id="12886" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="12936" class="Keyword">using</a> <a id="12942" class="Symbol">(</a><a id="12943" href="Definition.LogicalRelation.Properties.Primitive.html#4277" class="Function">⊩Level-⇒*</a><a id="12952" class="Symbol">;</a> <a id="12954" href="Definition.LogicalRelation.Properties.Primitive.html#3975" class="Function">redLevel′</a><a id="12963" class="Symbol">)</a>
</pre>
#### 3.2: Reducibility

The main reducibility judgements.
<pre class="Agda"><a id="13036" class="Keyword">import</a> <a id="13043" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13072" class="Keyword">using</a> <a id="13078" class="Symbol">(</a><a id="13079" href="Definition.LogicalRelation.html#23465" class="Function Operator">_⊩⟨_⟩_</a><a id="13085" class="Symbol">;</a> <a id="13087" href="Definition.LogicalRelation.html#23600" class="Function Operator">_⊩⟨_⟩_≡_/_</a><a id="13097" class="Symbol">;</a> <a id="13099" href="Definition.LogicalRelation.html#23978" class="Function Operator">_⊩⟨_⟩_≡_∷_/_</a><a id="13111" class="Symbol">;</a> <a id="13113" href="Definition.LogicalRelation.html#23786" class="Function Operator">_⊩⟨_⟩_∷_/_</a><a id="13123" class="Symbol">)</a>
</pre>
The logical relation is cumulative.
<pre class="Agda"><a id="13174" class="Keyword">import</a> <a id="13181" href="Definition.LogicalRelation.Properties.Embedding.html" class="Module">Definition.LogicalRelation.Properties.Embedding</a>
  <a id="13231" class="Keyword">using</a> <a id="13237" class="Symbol">(</a><a id="13238" href="Definition.LogicalRelation.Properties.Embedding.html#945" class="Function">emb-≤-⊩</a><a id="13245" class="Symbol">;</a> <a id="13247" href="Definition.LogicalRelation.Properties.Embedding.html#2186" class="Function">emb-≤-⊩≡</a><a id="13255" class="Symbol">;</a> <a id="13257" href="Definition.LogicalRelation.Properties.Embedding.html#2403" class="Function">emb-≤-⊩≡∷</a><a id="13266" class="Symbol">;</a> <a id="13268" href="Definition.LogicalRelation.Properties.Embedding.html#1048" class="Function">emb-≤-⊩∷</a><a id="13276" class="Symbol">)</a>
</pre>
Reducibility for neutrals.
<pre class="Agda"><a id="13318" class="Keyword">import</a> <a id="13325" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13354" class="Keyword">using</a> <a id="13360" class="Symbol">(</a><a id="13361" href="Definition.LogicalRelation.html#1812" class="Record Operator">_⊩ne_</a><a id="13366" class="Symbol">;</a> <a id="13368" href="Definition.LogicalRelation.html#2131" class="Record Operator">_⊩ne_≡_/_</a><a id="13377" class="Symbol">;</a> <a id="13379" href="Definition.LogicalRelation.html#2801" class="Record Operator">_⊩ne_≡_∷_/_</a><a id="13390" class="Symbol">)</a>
</pre>
Reducibility for levels.
<pre class="Agda"><a id="13430" class="Keyword">import</a> <a id="13437" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13466" class="Keyword">using</a> <a id="13472" class="Symbol">(</a><a id="13473" href="Definition.LogicalRelation.html#3087" class="Function Operator">_⊩Level_</a><a id="13481" class="Symbol">;</a> <a id="13483" href="Definition.LogicalRelation.html#3188" class="Function Operator">_⊩Level_≡_</a><a id="13493" class="Symbol">;</a> <a id="13495" href="Definition.LogicalRelation.html#4348" class="Datatype Operator">_⊩Level_≡_∷Level</a><a id="13511" class="Symbol">)</a>
</pre>
Level reflexivity and well-formedness.
<pre class="Agda"><a id="13565" class="Keyword">import</a> <a id="13572" href="Definition.LogicalRelation.Properties.Primitive.html" class="Module">Definition.LogicalRelation.Properties.Primitive</a>
  <a id="13622" class="Keyword">using</a> <a id="13628" class="Symbol">(</a><a id="13629" href="Definition.LogicalRelation.Properties.Primitive.html#1444" class="Function">reflLevel</a><a id="13638" class="Symbol">;</a> <a id="13640" href="Definition.LogicalRelation.Properties.Primitive.html#25302" class="Function">wf-Level-eq</a><a id="13651" class="Symbol">)</a>
</pre>
Reducibility for universes.
<pre class="Agda"><a id="13694" class="Keyword">open</a> <a id="13699" class="Keyword">import</a> <a id="13706" href="Definition.LogicalRelation.html" class="Module">Definition.LogicalRelation</a>
  <a id="13735" class="Keyword">using</a> <a id="13741" class="Symbol">(</a><a id="13742" class="Keyword">module</a> <a id="13749" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a><a id="13755" class="Symbol">)</a>
<a id="13757" class="Keyword">open</a> <a id="13762" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="13771" class="Keyword">using</a> <a id="13777" class="Symbol">(</a><a id="13778" href="Definition.LogicalRelation.html#11413" class="Record Operator">_⊩₁U_</a><a id="13783" class="Symbol">;</a> <a id="13785" href="Definition.LogicalRelation.html#11660" class="Record Operator">_⊩₁U≡_/_</a><a id="13793" class="Symbol">;</a> <a id="13795" href="Definition.LogicalRelation.html#11908" class="Record Operator">_⊩₁U_≡_∷U/_</a><a id="13806" class="Symbol">)</a>
</pre>
Types in WHNF.
<pre class="Agda"><a id="13836" class="Keyword">import</a> <a id="13843" href="Definition.Untyped.Neutral.html" class="Module">Definition.Untyped.Neutral</a>
  <a id="13872" class="Keyword">using</a> <a id="13878" class="Symbol">(</a><a id="13879" href="Definition.Untyped.Neutral.html#7007" class="Datatype">Type</a><a id="13883" class="Symbol">)</a>
</pre>
Reducibility for lift types.
<pre class="Agda"><a id="13927" class="Keyword">open</a> <a id="13932" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="13941" class="Keyword">using</a> <a id="13947" class="Symbol">(</a><a id="13948" href="Definition.LogicalRelation.html#12411" class="Record Operator">_⊩ₗLift_</a><a id="13956" class="Symbol">;</a> <a id="13958" href="Definition.LogicalRelation.html#12713" class="Record Operator">_⊩ₗLift_≡_/_</a><a id="13970" class="Symbol">;</a> <a id="13972" href="Definition.LogicalRelation.html#13074" class="Function Operator">_⊩ₗLift_≡_∷_/_</a><a id="13986" class="Symbol">)</a>
</pre>
Reducibility for Π-types (the first two definitions are used also for
Σ-types).
<pre class="Agda"><a id="14081" class="Keyword">open</a> <a id="14086" href="Definition.LogicalRelation.html#11277" class="Module">LogRel</a>
  <a id="14095" class="Keyword">using</a> <a id="14101" class="Symbol">(</a><a id="14102" href="Definition.LogicalRelation.html#13448" class="Record Operator">_⊩ₗB⟨_⟩_</a><a id="14110" class="Symbol">;</a> <a id="14112" href="Definition.LogicalRelation.html#14403" class="Record Operator">_⊩ₗB⟨_⟩_≡_/_</a><a id="14124" class="Symbol">;</a> <a id="14126" href="Definition.LogicalRelation.html#15186" class="Function Operator">_⊩ₗΠ_≡_∷_/_</a><a id="14137" class="Symbol">)</a>
</pre>
Well-formed weakenings were introduced above. The definition of the
logical relation uses a variant of this definition which is logically
equivalent if `Neutrals-included` is inhabited.
<pre class="Agda"><a id="14338" class="Keyword">import</a> <a id="14345" href="Definition.LogicalRelation.Weakening.Restricted.html" class="Module">Definition.LogicalRelation.Weakening.Restricted</a>
  <a id="14395" class="Keyword">using</a> <a id="14401" class="Symbol">(</a><a id="14402" href="Definition.LogicalRelation.Weakening.Restricted.html#844" class="Datatype Operator">_∷ʷʳ_⊇_</a><a id="14409" class="Symbol">;</a> <a id="14411" href="Definition.LogicalRelation.Weakening.Restricted.html#1055" class="Function">∷ʷ⊇→∷ʷʳ⊇</a><a id="14419" class="Symbol">;</a> <a id="14421" href="Definition.LogicalRelation.Weakening.Restricted.html#1342" class="Function">∷ʷʳ⊇→∷ʷ⊇</a><a id="14429" class="Symbol">)</a>
</pre>
Lifting of weakenings is denoted by `lift` rather than \_⇑ (which is
used for substitutions).
<pre class="Agda"><a id="14538" class="Keyword">import</a> <a id="14545" href="Definition.Untyped.NotParametrised.html" class="Module">Definition.Untyped.NotParametrised</a>
  <a id="14582" class="Keyword">using</a> <a id="14588" class="Symbol">(</a><a id="14589" href="Definition.Untyped.NotParametrised.html#3130" class="InductiveConstructor">lift</a><a id="14593" class="Symbol">)</a>
<a id="14595" class="Keyword">import</a> <a id="14602" href="Definition.Typed.Weakening.html" class="Module">Definition.Typed.Weakening</a>
  <a id="14631" class="Keyword">using</a> <a id="14637" class="Symbol">(</a><a id="14638" href="Definition.Typed.Weakening.html#3469" class="Function">liftʷ</a><a id="14643" class="Symbol">)</a>
</pre>
Irrelevance for reducibility judgements.
<pre class="Agda"><a id="14699" class="Keyword">import</a> <a id="14706" href="Definition.LogicalRelation.Irrelevance.html" class="Module">Definition.LogicalRelation.Irrelevance</a>
  <a id="14747" class="Keyword">using</a> <a id="14753" class="Symbol">(</a><a id="14754" href="Definition.LogicalRelation.Irrelevance.html#1944" class="Function">irrelevanceEq</a><a id="14767" class="Symbol">;</a> <a id="14769" href="Definition.LogicalRelation.Irrelevance.html#7487" class="Function">irrelevanceEqTerm</a><a id="14786" class="Symbol">;</a> <a id="14788" href="Definition.LogicalRelation.Irrelevance.html#6045" class="Function">irrelevanceTerm</a><a id="14803" class="Symbol">)</a>
</pre>
Reducibility judgements with hidden reducibility arguments.
<pre class="Agda"><a id="14878" class="Keyword">import</a> <a id="14885" href="Definition.LogicalRelation.Hidden.html" class="Module">Definition.LogicalRelation.Hidden</a>
  <a id="14921" class="Keyword">using</a> <a id="14927" class="Symbol">(</a><a id="14928" href="Definition.LogicalRelation.Hidden.html#1616" class="Function Operator">_⊩⟨_⟩_∷_</a><a id="14936" class="Symbol">;</a> <a id="14938" href="Definition.LogicalRelation.Hidden.html#2021" class="Function Operator">_⊩⟨_⟩_≡_∷_</a><a id="14948" class="Symbol">;</a> <a id="14950" href="Definition.LogicalRelation.Hidden.html#1810" class="Function Operator">_⊩⟨_⟩_≡_</a><a id="14958" class="Symbol">)</a>
</pre>
#### 3.3 Validity and the Fundamental Lemma

`Γ ⊩⟨ ℓ ⟩ 𝒥` implies `Γ ⊢ 𝒥`.
<pre class="Agda"><a id="15048" class="Keyword">import</a> <a id="15055" href="Definition.LogicalRelation.Properties.Escape.html" class="Module">Definition.LogicalRelation.Properties.Escape</a>
  <a id="15102" class="Keyword">using</a> <a id="15108" class="Symbol">(</a><a id="15109" href="Definition.LogicalRelation.Properties.Escape.html#1299" class="Function">escape</a><a id="15115" class="Symbol">;</a> <a id="15117" href="Definition.LogicalRelation.Properties.Escape.html#1728" class="Function">escapeEq</a><a id="15125" class="Symbol">;</a> <a id="15127" href="Definition.LogicalRelation.Properties.Escape.html#1982" class="Function">escapeTerm</a><a id="15137" class="Symbol">;</a> <a id="15139" href="Definition.LogicalRelation.Properties.Escape.html#1864" class="Function">escapeTermEq</a><a id="15151" class="Symbol">)</a>
</pre>
Validity judgements. In addition to the ones in the paper we also use
`Γ ⊩ᵛ⟨ ℓ ⟩ t ∷Level` and `Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷Level`, which are logically
equivalent to `Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ Level` and `Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ Level`,
respectively, when the `Level` type is allowed.
<pre class="Agda"><a id="15422" class="Keyword">import</a> <a id="15429" href="Definition.LogicalRelation.Substitution.html" class="Module">Definition.LogicalRelation.Substitution</a>
  <a id="15471" class="Keyword">using</a>
    <a id="15481" class="Symbol">(</a><a id="15482" href="Definition.LogicalRelation.Substitution.html#1823" class="Function Operator">⊩ᵛ_</a><a id="15485" class="Symbol">;</a> <a id="15487" href="Definition.LogicalRelation.Substitution.html#1950" class="Function Operator">_⊩ᵛ⟨_⟩_</a><a id="15494" class="Symbol">;</a> <a id="15496" href="Definition.LogicalRelation.Substitution.html#2088" class="Function Operator">_⊩ᵛ⟨_⟩_≡_</a><a id="15505" class="Symbol">;</a> <a id="15507" href="Definition.LogicalRelation.Substitution.html#2677" class="Function Operator">_⊩ˢ_∷_</a><a id="15513" class="Symbol">;</a> <a id="15515" href="Definition.LogicalRelation.Substitution.html#2343" class="Function Operator">_⊩ˢ_≡_∷_</a><a id="15523" class="Symbol">;</a> <a id="15525" href="Definition.LogicalRelation.Substitution.html#3101" class="Function Operator">_⊩ᵛ⟨_⟩_∷_</a><a id="15534" class="Symbol">;</a> <a id="15536" href="Definition.LogicalRelation.Substitution.html#2821" class="Function Operator">_⊩ᵛ⟨_⟩_≡_∷_</a><a id="15547" class="Symbol">;</a>
     <a id="15554" href="Definition.LogicalRelation.Substitution.html#3660" class="Function Operator">_⊩ᵛ⟨_⟩_∷Level</a><a id="15567" class="Symbol">;</a> <a id="15569" href="Definition.LogicalRelation.Substitution.html#3264" class="Datatype Operator">_⊩ᵛ⟨_⟩_≡_∷Level</a><a id="15584" class="Symbol">;</a> <a id="15586" href="Definition.LogicalRelation.Substitution.html#11459" class="Function">⊩ᵛ∷L⇔</a><a id="15591" class="Symbol">;</a> <a id="15593" href="Definition.LogicalRelation.Substitution.html#11187" class="Function">⊩ᵛ≡∷L⇔</a><a id="15599" class="Symbol">)</a>
</pre>
Lemma 3.3: Fundamental lemma.
<pre class="Agda"><a id="15644" class="Keyword">import</a> <a id="15651" href="Definition.LogicalRelation.Fundamental.html" class="Module">Definition.LogicalRelation.Fundamental</a>
  <a id="15692" class="Keyword">using</a>
    <a id="15702" class="Symbol">(</a><a id="15703" href="Definition.LogicalRelation.Fundamental.html#1309" class="Function">valid</a><a id="15708" class="Symbol">;</a>
     <a id="15715" href="Definition.LogicalRelation.Fundamental.html#1454" class="Function">fundamental-⊩ᵛ</a><a id="15729" class="Symbol">;</a> <a id="15731" href="Definition.LogicalRelation.Fundamental.html#2075" class="Function">fundamental-⊩ᵛ≡</a><a id="15746" class="Symbol">;</a> <a id="15748" href="Definition.LogicalRelation.Fundamental.html#3351" class="Function">fundamental-⊩ᵛ∷</a><a id="15763" class="Symbol">;</a> <a id="15765" href="Definition.LogicalRelation.Fundamental.html#7267" class="Function">fundamental-⊩ᵛ≡∷</a><a id="15781" class="Symbol">)</a>
</pre>
Lemma 3.4: Validity for the term typing rule for U. The proof sketch
given in the paper does not quite match the proof used here: this
proof goes via a corresponding proof for binary validity. Similar
comments apply to Lemmas 3.5 and 3.6 below.
<pre class="Agda"><a id="16041" class="Keyword">import</a> <a id="16048" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Universe</a>
  <a id="16113" class="Keyword">using</a> <a id="16119" class="Symbol">(</a><a id="16120" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html#11289" class="Function">⊩ᵛU∷U</a><a id="16125" class="Symbol">)</a>
</pre>
Lemma 3.5: Validity for the typing rule univ.
<pre class="Agda"><a id="16186" class="Keyword">import</a> <a id="16193" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Universe</a>
  <a id="16258" class="Keyword">using</a> <a id="16264" class="Symbol">(</a><a id="16265" href="Definition.LogicalRelation.Substitution.Introductions.Universe.html#11753" class="Function">⊩ᵛ∷U→⊩ᵛ</a><a id="16272" class="Symbol">)</a>
</pre>
Lemma 3.6: Validity for the term typing rule for Lift.
<pre class="Agda"><a id="16342" class="Keyword">import</a> <a id="16349" href="Definition.LogicalRelation.Substitution.Introductions.Lift.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Lift</a>
  <a id="16410" class="Keyword">using</a> <a id="16416" class="Symbol">(</a><a id="16417" href="Definition.LogicalRelation.Substitution.Introductions.Lift.html#7140" class="Function">Liftᵗᵛ</a><a id="16423" class="Symbol">)</a>
</pre>
Lemma 3.7: Validity for the term typing rule for Π.
<pre class="Agda"><a id="16490" class="Keyword">import</a> <a id="16497" href="Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma.html" class="Module">Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma</a>
  <a id="16562" class="Keyword">using</a> <a id="16568" class="Symbol">(</a><a id="16569" href="Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma.html#23518" class="Function">ΠΣᵗᵛ</a><a id="16573" class="Symbol">)</a>
</pre>
Level realisers are stable under weakening.
<pre class="Agda"><a id="16632" class="Keyword">import</a> <a id="16639" href="Definition.LogicalRelation.Weakening.html" class="Module">Definition.LogicalRelation.Weakening</a>
  <a id="16678" class="Keyword">using</a> <a id="16684" class="Symbol">(</a><a id="16685" href="Definition.LogicalRelation.Weakening.html#4888" class="Function">wk-↑ⁿ</a><a id="16690" class="Symbol">;</a> <a id="16692" href="Definition.LogicalRelation.Weakening.html#7971" class="Function">wk-↑ᵘ</a><a id="16697" class="Symbol">)</a>
</pre>
Corollary 3.8: Well-typed objects are reducible.
<pre class="Agda"><a id="16761" class="Keyword">import</a> <a id="16768" href="Definition.LogicalRelation.Fundamental.Reducibility.html" class="Module">Definition.LogicalRelation.Fundamental.Reducibility</a>
  <a id="16822" class="Keyword">using</a> <a id="16828" class="Symbol">(</a><a id="16829" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1081" class="Function">reducible-⊩</a><a id="16840" class="Symbol">;</a> <a id="16842" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1299" class="Function">reducible-⊩≡</a><a id="16854" class="Symbol">;</a> <a id="16856" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1451" class="Function">reducible-⊩∷</a><a id="16868" class="Symbol">;</a> <a id="16870" href="Definition.LogicalRelation.Fundamental.Reducibility.html#1691" class="Function">reducible-⊩≡∷</a><a id="16883" class="Symbol">)</a>
</pre>
The identity substitution is reducible.
<pre class="Agda"><a id="16938" class="Keyword">import</a> <a id="16945" href="Definition.LogicalRelation.Substitution.html" class="Module">Definition.LogicalRelation.Substitution</a>
  <a id="16987" class="Keyword">using</a> <a id="16993" class="Symbol">(</a><a id="16994" href="Definition.LogicalRelation.Substitution.html#38328" class="Function">⊩ˢ∷-idSubst</a><a id="17005" class="Symbol">)</a>
</pre>
Atomic neutrals are reducible.
<pre class="Agda"><a id="17051" class="Keyword">import</a> <a id="17058" href="Definition.LogicalRelation.Properties.Neutral.html" class="Module">Definition.LogicalRelation.Properties.Neutral</a>
</pre>
Corollary 3.9: Consistency.
<pre class="Agda"><a id="17145" class="Keyword">import</a> <a id="17152" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="17195" class="Keyword">using</a> <a id="17201" class="Symbol">(</a><a id="17202" href="Definition.Typed.Consequences.Canonicity.html#9637" class="Function">¬Empty</a><a id="17208" class="Symbol">)</a>
</pre>
Corollary 3.10: Canonicity.
<pre class="Agda"><a id="17251" class="Keyword">import</a> <a id="17258" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="17301" class="Keyword">using</a> <a id="17307" class="Symbol">(</a><a id="17308" href="Definition.Typed.Consequences.Canonicity.html#1463" class="Function">canonicity</a><a id="17318" class="Symbol">)</a>
</pre>
Corollary 3.11: Weak head normalisation.
<pre class="Agda"><a id="17374" class="Keyword">import</a> <a id="17381" href="Definition.Typed.Consequences.Reduction.html" class="Module">Definition.Typed.Consequences.Reduction</a>
  <a id="17423" class="Keyword">using</a> <a id="17429" class="Symbol">(</a><a id="17430" href="Definition.Typed.Consequences.Reduction.html#6345" class="Function">whNorm</a><a id="17436" class="Symbol">;</a> <a id="17438" href="Definition.Typed.Consequences.Reduction.html#13640" class="Function">whNormTerm</a><a id="17448" class="Symbol">)</a>
</pre>
Corollary 3.12: Injectivity of and non-confusion for type formers.
More lemmas of this kind can be found in the given modules. Statements
of the form "`A` is not derivable" are interpreted as `¬ A`; note that
if Agda is inconsistent, then `¬ A` and `A` might both be inhabited.
<pre class="Agda"><a id="17741" class="Keyword">import</a> <a id="17748" href="Definition.Typed.Consequences.Injectivity.html" class="Module">Definition.Typed.Consequences.Injectivity</a>
  <a id="17792" class="Keyword">using</a>
    <a id="17802" class="Symbol">(</a><a id="17803" href="Definition.Typed.Consequences.Injectivity.html#1286" class="Function">U-injectivity</a><a id="17816" class="Symbol">;</a> <a id="17818" href="Definition.Typed.Consequences.Injectivity.html#1560" class="Function">Lift-injectivity</a><a id="17834" class="Symbol">;</a>
     <a id="17841" href="Definition.Typed.Consequences.Injectivity.html#3097" class="Function">ΠΣ-injectivity-no-equality-reflection</a><a id="17878" class="Symbol">)</a>
<a id="17880" class="Keyword">import</a> <a id="17887" href="Definition.Typed.Consequences.Inequality.html" class="Module">Definition.Typed.Consequences.Inequality</a>
  <a id="17930" class="Keyword">using</a> <a id="17936" class="Symbol">(</a><a id="17937" href="Definition.Typed.Consequences.Inequality.html#7808" class="Function">Level≢ℕ</a><a id="17944" class="Symbol">;</a> <a id="17946" href="Definition.Typed.Consequences.Inequality.html#2857" class="Function">U≢ℕ</a><a id="17949" class="Symbol">)</a>
</pre>
Corollary 3.13: Canonicity for contexts that only contain level and
type variables.
<pre class="Agda"><a id="18048" class="Keyword">import</a> <a id="18055" href="Definition.Typed.Consequences.Canonicity.html" class="Module">Definition.Typed.Consequences.Canonicity</a>
  <a id="18098" class="Keyword">using</a> <a id="18104" class="Symbol">(</a><a id="18105" href="Definition.Typed.Consequences.Canonicity.html#8636" class="Function">canonicity-Only-Level-or-U</a><a id="18131" class="Symbol">)</a>
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

<pre class="Agda"><a id="18627" class="Keyword">import</a> <a id="18634" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18658" class="Keyword">using</a>
    <a id="18668" class="Symbol">(</a><a id="18669" href="Definition.Conversion.html#5092" class="Record Operator">_⊢_[conv↑]_</a><a id="18680" class="Symbol">;</a> <a id="18682" href="Definition.Conversion.html#5380" class="Datatype Operator">_⊢_[conv↓]_</a><a id="18693" class="Symbol">;</a> <a id="18695" href="Definition.Conversion.html#6398" class="Record Operator">_⊢_[conv↑]_∷_</a><a id="18708" class="Symbol">;</a> <a id="18710" href="Definition.Conversion.html#6743" class="Datatype Operator">_⊢_[conv↓]_∷_</a><a id="18723" class="Symbol">;</a>
     <a id="18730" href="Definition.Conversion.html#1461" class="Datatype Operator">_⊢_~_↑_</a><a id="18737" class="Symbol">;</a> <a id="18739" href="Definition.Conversion.html#4591" class="Record Operator">_⊢_~_↓_</a><a id="18746" class="Symbol">)</a>
</pre>
Level atoms, `Level⁺` and level views.
<pre class="Agda"><a id="18800" class="Keyword">import</a> <a id="18807" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18831" class="Keyword">using</a> <a id="18837" class="Symbol">(</a><a id="18838" href="Definition.Conversion.html#9587" class="Datatype">LevelAtom</a><a id="18847" class="Symbol">;</a> <a id="18849" href="Definition.Conversion.html#9713" class="Function">Level⁺</a><a id="18855" class="Symbol">;</a> <a id="18857" href="Definition.Conversion.html#9775" class="Function">Levelᵛ</a><a id="18863" class="Symbol">)</a>
</pre>
Level view comparison.
<pre class="Agda"><a id="18901" class="Keyword">import</a> <a id="18908" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="18932" class="Keyword">using</a> <a id="18938" class="Symbol">(</a><a id="18939" href="Definition.Conversion.html#9866" class="Function Operator">_≡ᵛ_</a><a id="18943" class="Symbol">;</a> <a id="18945" href="Definition.Conversion.html#10186" class="Function">≤ᵛ</a><a id="18947" class="Symbol">;</a> <a id="18949" href="Definition.Conversion.html#10272" class="Function">≤⁺ᵛ</a><a id="18952" class="Symbol">;</a> <a id="18954" href="Definition.Conversion.html#10351" class="Function">≤⁺</a><a id="18956" class="Symbol">;</a> <a id="18958" href="Definition.Conversion.html#10441" class="Datatype">≤ᵃ</a><a id="18960" class="Symbol">)</a>
</pre>
Operations on level views.
<pre class="Agda"><a id="19002" class="Keyword">import</a> <a id="19009" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="19033" class="Keyword">using</a> <a id="19039" class="Symbol">(</a><a id="19040" href="Definition.Conversion.html#11231" class="Function">sucᵛ</a><a id="19044" class="Symbol">;</a> <a id="19046" href="Definition.Conversion.html#11299" class="Function">supᵛ</a><a id="19050" class="Symbol">)</a>
</pre>
Normalising levels into level views.
<pre class="Agda"><a id="19102" class="Keyword">import</a> <a id="19109" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="19133" class="Keyword">using</a> <a id="19139" class="Symbol">(</a><a id="19140" href="Definition.Conversion.html#12274" class="Record Operator">_⊢_↑ᵛ_</a><a id="19146" class="Symbol">;</a> <a id="19148" href="Definition.Conversion.html#11466" class="Datatype Operator">_⊢_↓ᵛ_</a><a id="19154" class="Symbol">;</a> <a id="19156" href="Definition.Conversion.html#11798" class="Datatype Operator">_⊢_~ᵛ_</a><a id="19162" class="Symbol">)</a>
</pre>
Algorithmic equality is sound.
<pre class="Agda"><a id="19208" class="Keyword">import</a> <a id="19215" href="Definition.Conversion.Soundness.html" class="Module">Definition.Conversion.Soundness</a>
  <a id="19249" class="Keyword">using</a>
    <a id="19259" class="Symbol">(</a><a id="19260" href="Definition.Conversion.Soundness.html#4201" class="Function">soundnessConv↑</a><a id="19274" class="Symbol">;</a> <a id="19276" href="Definition.Conversion.Soundness.html#4444" class="Function">soundnessConv↓</a><a id="19290" class="Symbol">;</a>
     <a id="19297" href="Definition.Conversion.Soundness.html#5238" class="Function">soundnessConv↑Term</a><a id="19315" class="Symbol">;</a> <a id="19317" href="Definition.Conversion.Soundness.html#5861" class="Function">soundnessConv↓Term</a><a id="19335" class="Symbol">;</a>
     <a id="19342" href="Definition.Conversion.Soundness.html#1675" class="Function">soundness~↑</a><a id="19353" class="Symbol">;</a> <a id="19355" href="Definition.Conversion.Soundness.html#3899" class="Function">soundness~↓</a><a id="19366" class="Symbol">)</a>
</pre>
Algorithmic equality is stable under weakening.
<pre class="Agda"><a id="19429" class="Keyword">import</a> <a id="19436" href="Definition.Conversion.Weakening.html" class="Module">Definition.Conversion.Weakening</a>
  <a id="19470" class="Keyword">using</a> <a id="19476" class="Symbol">(</a><a id="19477" href="Definition.Conversion.Weakening.html#6221" class="Function">wkConv↑</a><a id="19484" class="Symbol">;</a> <a id="19486" href="Definition.Conversion.Weakening.html#6526" class="Function">wkConv↓</a><a id="19493" class="Symbol">;</a> <a id="19495" href="Definition.Conversion.Weakening.html#7364" class="Function">wkConv↑Term</a><a id="19506" class="Symbol">;</a> <a id="19508" href="Definition.Conversion.Weakening.html#8078" class="Function">wkConv↓Term</a><a id="19519" class="Symbol">;</a> <a id="19521" href="Definition.Conversion.Weakening.html#1589" class="Function">wk~↑</a><a id="19525" class="Symbol">;</a> <a id="19527" href="Definition.Conversion.Weakening.html#5817" class="Function">wk~↓</a><a id="19531" class="Symbol">)</a>
</pre>
Algorithmic equality is decidable.
<pre class="Agda"><a id="19581" class="Keyword">import</a> <a id="19588" href="Definition.Conversion.Decidable.html" class="Module">Definition.Conversion.Decidable</a>
  <a id="19622" class="Keyword">using</a> <a id="19628" class="Symbol">(</a><a id="19629" href="Definition.Conversion.Decidable.html#29697" class="Function">decConv↑</a><a id="19637" class="Symbol">;</a> <a id="19639" href="Definition.Conversion.Decidable.html#30565" class="Function">decConv↓</a><a id="19647" class="Symbol">;</a> <a id="19649" href="Definition.Conversion.Decidable.html#34356" class="Function">decConv↑Term</a><a id="19661" class="Symbol">;</a> <a id="19663" href="Definition.Conversion.Decidable.html#36438" class="Function">decConv↓Term</a><a id="19675" class="Symbol">;</a> <a id="19677" href="Definition.Conversion.Decidable.html#22940" class="Function">dec~↑</a><a id="19682" class="Symbol">;</a> <a id="19684" href="Definition.Conversion.Decidable.html#28901" class="Function">dec~↓</a><a id="19689" class="Symbol">)</a>
</pre>
Level normalisation is deterministic.
<pre class="Agda"><a id="19742" class="Keyword">import</a> <a id="19749" href="Definition.Conversion.Level.html" class="Module">Definition.Conversion.Level</a>
  <a id="19779" class="Keyword">using</a> <a id="19785" class="Symbol">(</a><a id="19786" href="Definition.Conversion.Level.html#5741" class="Function">deterministic-↑ᵛ</a><a id="19802" class="Symbol">)</a>
</pre>
Lemma 4.1.
<pre class="Agda"><a id="19828" class="Keyword">open</a> <a id="19833" class="Keyword">import</a> <a id="19840" href="Definition.Conversion.EqRelInstance.html" class="Module">Definition.Conversion.EqRelInstance</a>
  <a id="19878" class="Keyword">using</a> <a id="19884" class="Symbol">(</a><a id="19885" class="Keyword">module</a> <a id="19892" href="Definition.Conversion.EqRelInstance.html#2997" class="Module">Lemmas</a><a id="19898" class="Symbol">)</a>
<a id="19900" class="Keyword">open</a> <a id="19905" href="Definition.Conversion.EqRelInstance.html#2997" class="Module">Lemmas</a>
  <a id="19914" class="Keyword">using</a> <a id="19920" class="Symbol">(</a><a id="19921" href="Definition.Conversion.EqRelInstance.html#12091" class="Function">supᵘ-↑ᵛ</a><a id="19928" class="Symbol">)</a>
</pre>
The generic equality relation instance for algorithmic equality.
<pre class="Agda"><a id="20008" class="Keyword">import</a> <a id="20015" href="Definition.Conversion.EqRelInstance.html" class="Module">Definition.Conversion.EqRelInstance</a>
  <a id="20053" class="Keyword">using</a> <a id="20059" class="Symbol">(</a><a id="20060" href="Definition.Conversion.EqRelInstance.html#23156" class="Function">eqRelInstance</a><a id="20073" class="Symbol">)</a>
</pre>
Theorem 4.2: Algorithmic equality is complete with respect to
judgemental equality.
<pre class="Agda"><a id="20172" class="Keyword">import</a> <a id="20179" href="Definition.Conversion.Consequences.Completeness.html" class="Module">Definition.Conversion.Consequences.Completeness</a>
  <a id="20229" class="Keyword">using</a> <a id="20235" class="Symbol">(</a><a id="20236" href="Definition.Conversion.Consequences.Completeness.html#1034" class="Function">completeEq</a><a id="20246" class="Symbol">;</a> <a id="20248" href="Definition.Conversion.Consequences.Completeness.html#1327" class="Function">completeEqTerm</a><a id="20262" class="Symbol">)</a>
</pre>
Corollary 4.3: Judgemental equality of well-formed types and terms is
decidable.
<pre class="Agda"><a id="20358" class="Keyword">import</a> <a id="20365" href="Definition.Typed.Decidable.Equality.html" class="Module">Definition.Typed.Decidable.Equality</a>
  <a id="20403" class="Keyword">using</a> <a id="20409" class="Symbol">(</a><a id="20410" href="Definition.Typed.Decidable.Equality.html#958" class="Function">decEq</a><a id="20415" class="Symbol">;</a> <a id="20417" href="Definition.Typed.Decidable.Equality.html#1207" class="Function">decEqTerm</a><a id="20426" class="Symbol">)</a>
</pre>
Corollary 4.4: Deep normalisation.
<pre class="Agda"><a id="20476" class="Keyword">import</a> <a id="20483" href="Definition.Conversion.FullReduction.html" class="Module">Definition.Conversion.FullReduction</a>
  <a id="20521" class="Keyword">using</a> <a id="20527" class="Symbol">(</a><a id="20528" href="Definition.Conversion.FullReduction.html#19328" class="Function">fullRed</a><a id="20535" class="Symbol">;</a> <a id="20537" href="Definition.Conversion.FullReduction.html#19522" class="Function">fullRedTerm</a><a id="20548" class="Symbol">)</a>
</pre>
Checkable types, checkable terms and inferable terms. The code also
makes use of `Checkable-level`. If `Level` is allowed, then
`Checkable-level t` is logically equivalent to `Checkable t`.
<pre class="Agda"><a id="20753" class="Keyword">import</a> <a id="20760" href="Definition.Typechecking.html" class="Module">Definition.Typechecking</a>
  <a id="20786" class="Keyword">using</a> <a id="20792" class="Symbol">(</a><a id="20793" href="Definition.Typechecking.html#5795" class="Datatype">Checkable-type</a><a id="20807" class="Symbol">;</a> <a id="20809" href="Definition.Typechecking.html#8000" class="Datatype">Checkable</a><a id="20818" class="Symbol">;</a> <a id="20820" href="Definition.Typechecking.html#6224" class="Datatype">Inferable</a><a id="20829" class="Symbol">;</a> <a id="20831" href="Definition.Typechecking.html#8300" class="Datatype">Checkable-level</a><a id="20846" class="Symbol">)</a>
</pre>
The term Π (λ x₀) x₀ is a checkable type but not a checkable term.
Every well-formed, checkable type is inferable.
<pre class="Agda"><a id="20976" class="Keyword">import</a> <a id="20983" href="Definition.Typechecking.html" class="Module">Definition.Typechecking</a>
  <a id="21009" class="Keyword">using</a> <a id="21015" class="Symbol">(</a><a id="21016" href="Definition.Typechecking.html#9153" class="Function">Checkable-type×¬Checkable</a><a id="21041" class="Symbol">;</a> <a id="21043" href="Definition.Typechecking.html#10689" class="Function">⊢→Checkable-type→Inferable</a><a id="21069" class="Symbol">)</a>
</pre>
Theorem 4.5: Decidability of type checking/type inference for certain
classes of terms, types and contexts.
<pre class="Agda"><a id="21192" class="Keyword">import</a> <a id="21199" href="Definition.Typed.Decidable.html" class="Module">Definition.Typed.Decidable</a>
  <a id="21228" class="Keyword">using</a> <a id="21234" class="Symbol">(</a><a id="21235" href="Definition.Typed.Decidable.html#2185" class="Function">decWfCon</a><a id="21243" class="Symbol">;</a> <a id="21245" href="Definition.Typed.Decidable.html#2501" class="Function">decConTypeᶜ</a><a id="21256" class="Symbol">;</a> <a id="21258" href="Definition.Typed.Decidable.html#2788" class="Function">decConTermTypeᶜ</a><a id="21273" class="Symbol">;</a> <a id="21275" href="Definition.Typed.Decidable.html#3128" class="Function">decConTermᵢ</a><a id="21286" class="Symbol">)</a>
</pre>
### 5: Erasing Levels Is Safe

The usage relation. This relation is parametrised by a value of type
`Usage-restrictions`, which for instance makes it possible to disallow
several forms of erased matches.
<pre class="Agda"><a id="21505" class="Keyword">import</a> <a id="21512" href="Graded.Usage.html" class="Module">Graded.Usage</a>
  <a id="21527" class="Keyword">using</a> <a id="21533" class="Symbol">(</a><a id="21534" href="Graded.Usage.html#8746" class="Datatype Operator">_▸[_]_</a><a id="21540" class="Symbol">)</a>
<a id="21542" class="Keyword">import</a> <a id="21549" href="Graded.Usage.Restrictions.html" class="Module">Graded.Usage.Restrictions</a>
  <a id="21577" class="Keyword">using</a> <a id="21583" class="Symbol">(</a><a id="21584" href="Graded.Usage.Restrictions.html#812" class="Record">Usage-restrictions</a><a id="21602" class="Symbol">)</a>
</pre>
Usage contexts.
<pre class="Agda"><a id="21633" class="Keyword">import</a> <a id="21640" href="Graded.Context.html" class="Module">Graded.Context</a>
  <a id="21657" class="Keyword">using</a> <a id="21663" class="Symbol">(</a><a id="21664" href="Graded.Context.html#729" class="Datatype">Conₘ</a><a id="21668" class="Symbol">)</a>
</pre>
Modes. The development supports modalities with or without the zero
mode.
<pre class="Agda"><a id="21757" class="Keyword">import</a> <a id="21764" href="Graded.Mode.html" class="Module">Graded.Mode</a>
  <a id="21778" class="Keyword">using</a> <a id="21784" class="Symbol">(</a><a id="21785" href="Graded.Mode.html#1039" class="Datatype">Mode</a><a id="21789" class="Symbol">)</a>
</pre>
The erasure modality. The development supports two variants of the
erasure modality: with or without support for the zero mode. When the
paper refers to "the erasure modality" it is the one with support for
the zero mode that is meant.
<pre class="Agda"><a id="22040" class="Keyword">import</a> <a id="22047" href="Graded.Modality.Instances.Erasure.html" class="Module">Graded.Modality.Instances.Erasure</a>
  <a id="22083" class="Keyword">using</a> <a id="22089" class="Symbol">(</a><a id="22090" href="Graded.Modality.Instances.Erasure.html#442" class="InductiveConstructor">𝟘</a><a id="22091" class="Symbol">;</a> <a id="22093" href="Graded.Modality.Instances.Erasure.html#444" class="InductiveConstructor">ω</a><a id="22094" class="Symbol">)</a>
<a id="22096" class="Keyword">import</a> <a id="22103" href="Graded.Modality.Instances.Erasure.Modality.html" class="Module">Graded.Modality.Instances.Erasure.Modality</a>
  <a id="22148" class="Keyword">using</a> <a id="22154" class="Symbol">(</a><a id="22155" href="Graded.Modality.Instances.Erasure.Modality.html#2775" class="Function">ErasureModality</a><a id="22170" class="Symbol">)</a>
</pre>
The target language. The term appˢ t u is denoted by `t ∘⟨ s ⟩ u`, the
predicate Valueˢ is called `Value⟨ s ⟩`, sucˢ is called `suc⟨ s ⟩`, ↯ˢ
is called `loop? s`, ⇒ˢᵘᶜ is called `_⇒ˢ_`, \_⊢\_⟶ˢᵘᶜ\_:ℕ is called
`_⊢_⇒ˢ_∷ℕ`, \_⊢\_⟶ˢᵘᶜ\*\_:ℕ is called `_⊢_⇒ˢ*_∷ℕ`, ⇒\*ₛ is called
`_⇒ˢ⟨_⟩*_`, and n̲ is called `sucᵏ n`. The term loop corresponds to
`loop non-strict`.
<pre class="Agda"><a id="22548" class="Keyword">import</a> <a id="22555" href="Graded.Erasure.Target.html" class="Module">Graded.Erasure.Target</a>
  <a id="22579" class="Keyword">using</a> <a id="22585" class="Symbol">(</a><a id="22586" href="Graded.Erasure.Target.html#1253" class="Datatype">Term</a><a id="22590" class="Symbol">;</a> <a id="22592" href="Graded.Erasure.Target.html#673" class="Datatype">Strictness</a><a id="22602" class="Symbol">;</a> <a id="22604" href="Graded.Erasure.Target.html#6149" class="Datatype">Value</a><a id="22609" class="Symbol">;</a> <a id="22611" href="Graded.Erasure.Target.html#6393" class="Function Operator">Value⟨_⟩</a><a id="22619" class="Symbol">;</a> <a id="22621" href="Graded.Erasure.Target.html#7040" class="Datatype Operator">_⇒_</a><a id="22624" class="Symbol">;</a> <a id="22626" href="Graded.Erasure.Target.html#1847" class="Function Operator">suc⟨_⟩</a><a id="22632" class="Symbol">;</a> <a id="22634" href="Graded.Erasure.Target.html#6927" class="Function">sucᵏ</a><a id="22638" class="Symbol">)</a>
<a id="22640" class="Keyword">import</a> <a id="22647" href="Definition.Untyped.html" class="Module">Definition.Untyped</a>
  <a id="22668" class="Keyword">using</a> <a id="22674" class="Symbol">(</a><a id="22675" href="Definition.Untyped.html#3842" class="Function">sucᵏ</a><a id="22679" class="Symbol">)</a>
<a id="22681" class="Keyword">import</a> <a id="22688" href="Graded.Erasure.Target.Non-terminating.html" class="Module">Graded.Erasure.Target.Non-terminating</a>
  <a id="22728" class="Keyword">using</a> <a id="22734" class="Symbol">(</a><a id="22735" href="Graded.Erasure.Target.Non-terminating.html#751" class="Function">loop</a><a id="22739" class="Symbol">)</a>
<a id="22741" class="Keyword">import</a> <a id="22748" href="Graded.Erasure.Extraction.html" class="Module">Graded.Erasure.Extraction</a>
  <a id="22776" class="Keyword">using</a> <a id="22782" class="Symbol">(</a><a id="22783" href="Graded.Erasure.Extraction.html#854" class="Function">loop?</a><a id="22788" class="Symbol">)</a>
<a id="22790" class="Keyword">import</a> <a id="22797" href="Graded.Erasure.SucRed.html" class="Module">Graded.Erasure.SucRed</a>
  <a id="22821" class="Keyword">using</a> <a id="22827" class="Symbol">(</a><a id="22828" href="Graded.Erasure.SucRed.html#5300" class="Datatype Operator">_⇒ˢ_</a><a id="22832" class="Symbol">;</a> <a id="22834" href="Graded.Erasure.SucRed.html#1292" class="Datatype Operator">_⊢_⇒ˢ_∷ℕ</a><a id="22842" class="Symbol">;</a> <a id="22844" href="Graded.Erasure.SucRed.html#1535" class="Datatype Operator">_⊢_⇒ˢ*_∷ℕ</a><a id="22853" class="Symbol">;</a> <a id="22855" href="Graded.Erasure.SucRed.html#8981" class="Function Operator">_⇒ˢ⟨_⟩*_</a><a id="22863" class="Symbol">)</a>
</pre>
The extraction function.
<pre class="Agda"><a id="22903" class="Keyword">import</a> <a id="22910" href="Graded.Erasure.Extraction.html" class="Module">Graded.Erasure.Extraction</a>
  <a id="22938" class="Keyword">using</a> <a id="22944" class="Symbol">(</a><a id="22945" href="Graded.Erasure.Extraction.html#2119" class="Function">erase</a><a id="22950" class="Symbol">)</a>
</pre>
Complete removal of all arguments can, in the strict setting, lead to
non-termination for the extracted program.
<pre class="Agda"><a id="23078" class="Keyword">import</a> <a id="23085" href="Graded.Erasure.Extraction.Non-terminating.html" class="Module">Graded.Erasure.Extraction.Non-terminating</a>
  <a id="23129" class="Keyword">using</a> <a id="23135" class="Symbol">(</a><a id="23136" href="Graded.Erasure.Extraction.Non-terminating.html#12385" class="Function">loops-reduces-forever</a><a id="23157" class="Symbol">;</a> <a id="23159" href="Graded.Erasure.Extraction.Non-terminating.html#13408" class="Function">⊢loops</a><a id="23165" class="Symbol">;</a> <a id="23167" href="Graded.Erasure.Extraction.Non-terminating.html#13721" class="Function">▸loops</a><a id="23173" class="Symbol">)</a>
</pre>
Theorem 5.1: Soundness of erasure. The paper uses the formulation
"erased matches are disallowed for weak Σ and unit types", but the
code uses the formulation "if the modality is non-trivial, then erased
matches are disallowed for weak Σ and unit types as well as the
identity type": the paper focuses on the erasure modality, which is
non-trivial, and identity types are mostly ignored in the text. The
statement in the code also has the condition "equality reflection is
disallowed or the context is empty".
<pre class="Agda"><a id="23698" class="Keyword">open</a> <a id="23703" class="Keyword">import</a> <a id="23710" href="Graded.Erasure.Consequences.Soundness.html" class="Module">Graded.Erasure.Consequences.Soundness</a>
<a id="23748" class="Keyword">open</a> <a id="23753" href="Graded.Erasure.Consequences.Soundness.html#6156" class="Module">Soundness</a>
  <a id="23765" class="Keyword">using</a> <a id="23771" class="Symbol">(</a><a id="23772" href="Graded.Erasure.Consequences.Soundness.html#7745" class="Function">soundness-ℕ</a><a id="23783" class="Symbol">)</a>
</pre>
Corollary 5.2: Soundness of erasure for closed terms.
<pre class="Agda"><a id="23852" class="Keyword">open</a> <a id="23857" href="Graded.Erasure.Consequences.Soundness.html#9809" class="Module">Soundness₀</a>
  <a id="23870" class="Keyword">using</a> <a id="23876" class="Symbol">(</a><a id="23877" href="Graded.Erasure.Consequences.Soundness.html#9966" class="Function">soundness-ℕ</a><a id="23888" class="Symbol">)</a>
</pre>
Some counterexamples to variants of Theorem 5.1, one for the case
where erased matches are allowed for weak Σ-types, and one for the
case where erased matches are allowed for the empty type and the
context is allowed to be inconsistent.
<pre class="Agda"><a id="24140" class="Keyword">import</a> <a id="24147" href="Graded.Erasure.Consequences.Soundness.html" class="Module">Graded.Erasure.Consequences.Soundness</a> <a id="24185" class="Keyword">using</a>
  <a id="24193" class="Symbol">(</a><a id="24194" href="Graded.Erasure.Consequences.Soundness.html#10926" class="Function">soundness-ℕ-only-source-counterexample₁</a><a id="24233" class="Symbol">;</a> <a id="24235" href="Graded.Erasure.Consequences.Soundness.html#18647" class="Function">soundness-ℕ-counterexample₆</a><a id="24262" class="Symbol">)</a>
</pre>
### 6: Discussion and Future Work

The algorithmic η-equality rule for Lift, stability of algorithmic
equality under conversion, and lifting of algorithmic equality of
atomic neutrals with types in WHNF (`Γ ⊢ t ~ u ↓ A`) to algorithmic
equality of terms in WHNF (`Γ ⊢ t [conv↓] u ∷ A`).
<pre class="Agda"><a id="24564" class="Keyword">open</a> <a id="24569" class="Keyword">import</a> <a id="24576" href="Definition.Conversion.html" class="Module">Definition.Conversion</a>
  <a id="24600" class="Keyword">using</a> <a id="24606" class="Symbol">(</a><a id="24607" class="Keyword">module</a> <a id="24614" href="Definition.Conversion.html#6743" class="Module Operator">_⊢_[conv↓]_∷_</a><a id="24627" class="Symbol">)</a>
<a id="24629" class="Keyword">open</a> <a id="24634" href="Definition.Conversion.html#6743" class="Module Operator">_⊢_[conv↓]_∷_</a>
  <a id="24650" class="Keyword">using</a> <a id="24656" class="Symbol">(</a><a id="24657" href="Definition.Conversion.html#7698" class="InductiveConstructor">Lift-η</a><a id="24663" class="Symbol">)</a>
<a id="24665" class="Keyword">import</a> <a id="24672" href="Definition.Conversion.Conversion.html" class="Module">Definition.Conversion.Conversion</a>
  <a id="24707" class="Keyword">using</a> <a id="24713" class="Symbol">(</a><a id="24714" href="Definition.Conversion.Conversion.html#6364" class="Function">convConv↑Term</a><a id="24727" class="Symbol">;</a> <a id="24729" href="Definition.Conversion.Conversion.html#6549" class="Function">convConv↓Term</a><a id="24742" class="Symbol">)</a>
<a id="24744" class="Keyword">import</a> <a id="24751" href="Definition.Conversion.Lift.html" class="Module">Definition.Conversion.Lift</a>
  <a id="24780" class="Keyword">using</a> <a id="24786" class="Symbol">(</a><a id="24787" href="Definition.Conversion.Lift.html#8441" class="Function">lift~toConv↓</a><a id="24799" class="Symbol">)</a>
</pre>
## More pointers to code

Some examples, including a universe-polymorphic identity function and
a universe-polymorphic encoding of vectors (lists of a given length).
<pre class="Agda"><a id="24980" class="Keyword">import</a> <a id="24987" href="Graded.Erasure.Examples.html" class="Module">Graded.Erasure.Examples</a>
  <a id="25013" class="Keyword">using</a> <a id="25019" class="Symbol">(</a><a id="25020" href="Graded.Erasure.Examples.html#4802" class="Function">⊢id</a><a id="25023" class="Symbol">;</a> <a id="25025" href="Graded.Erasure.Examples.html#12777" class="Function">⊢Vec</a><a id="25029" class="Symbol">;</a> <a id="25031" href="Graded.Erasure.Examples.html#23317" class="Function">⊢head</a><a id="25036" class="Symbol">)</a>
</pre>