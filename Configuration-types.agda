------------------------------------------------------------------------
-- Configuration types for the type and usage systems
------------------------------------------------------------------------

-- This formalisation supports a family of graded type theories: one
-- can to some degree choose between different features. Some record
-- types are used to control these choices.

module Configuration-types where

open import Configuration-types.Erased-matches
import Configuration-types.Natrec
import Configuration-types.Omega
import Graded.Context
open import Graded.Modality
import Graded.Mode

import Definition.Untyped
import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
open import Tools.Relation
open import Tools.PropositionalEquality
open import Tools.Sum

private variable
  a b        : Level
  A          : Set _
  n          : Nat
  s          : Definition.Untyped.NotParametrised.Strength
  Γ          : Definition.Untyped.NotParametrised.Con _ _
  γ δ η      : Graded.Context.Conₘ _ _
  m m′ p q r : A

------------------------------------------------------------------------
-- Auxiliary definitions

-- What kind of unfolding is used?

data UnfoldingMode : Set where
  -- Unfold only explicitly specified definitions.
  explicit : UnfoldingMode
  -- Unfold all transitive dependencies of definitions.
  transitive : UnfoldingMode

-- The type JK corresponds to the eliminators J and K.

data JK : Set where
  J K : JK

private variable
  jk : JK

------------------------------------------------------------------------
-- Configuration of the type system

-- There are two configuration types for the type system: one that
-- only depends on a universe level, and one that additionally depends
-- on a grade semiring.

record Type-configuration⁻ (a : Level) : Set (lsuc a) where
  no-eta-equality

  open Definition.Untyped.NotParametrised

  field

    --------------------------------------------------------------------
    -- Universe levels

    -- Is Level a type, and in that case is the type small?
    level-support : Level-support

    -- Are levels of the form "ω + n" allowed?
    Omega-plus-allowed : Set a

    --------------------------------------------------------------------
    -- Unit types

    -- Are unit types of the given strength allowed?
    Unit-allowed : Strength → Set a

    -- Should η-equality be enabled for weak unit types?
    --
    -- This variant of the type system is used to state some soundness
    -- theorems for extraction, see
    -- Graded.Erasure.Consequences.Soundness.Erased-matches.
    η-for-Unitʷ : Bool

    --------------------------------------------------------------------
    -- Identity types

    -- Is the K rule allowed?
    K-allowed : Set a

    -- Is equality reflection allowed?
    Equality-reflection : Set a

    -- Equality-reflection is decided.
    Equality-reflection? : Dec Equality-reflection

    --------------------------------------------------------------------
    -- Quotient types

    -- Are quotient types allowed?
    Quot-allowed : Set a

    --------------------------------------------------------------------
    -- Opaque definitions

    -- Are opaque definitions allowed?
    Opacity-allowed : Set a

    -- Opacity-allowed is decided.
    Opacity-allowed? : Dec Opacity-allowed

    -- Equality reflection is incompatible with opaque definitions.
    no-opaque-equality-reflection :
      Opacity-allowed → ¬ Equality-reflection

    -- How should transitive dependencies of definitions be unfolded?
    unfolding-mode : UnfoldingMode

  ----------------------------------------------------------------------
  -- Some derived definitions relation to universe levels

  opaque

    -- Is the type Level allowed?

    Level-allowed : Set
    Level-allowed = level-support ≢ only-literals

  opaque
    unfolding Level-allowed

    -- Is Level-allowed inhabited?

    Level-allowed? : Dec Level-allowed
    Level-allowed? = ¬? (_ ≟-Level-support _)

  opaque
    unfolding Level-allowed

    -- A characterisation lemma for Level-allowed.

    Level-allowed⇔≢ : Level-allowed ⇔ (level-support ≢ only-literals)
    Level-allowed⇔≢ = id⇔

  opaque

    -- A characterisation lemma for ¬ Level-allowed.

    ¬Level-allowed⇔ :
      (¬ Level-allowed) ⇔ (level-support ≡ only-literals)
    ¬Level-allowed⇔ =
      (¬ Level-allowed)                  ⇔⟨ Level-allowed⇔≢ →-cong-⇔ id⇔ ⟩
      ¬ ¬ level-support ≡ only-literals  ⇔⟨ decidable-stable (_ ≟-Level-support _) , flip _$_ ⟩
      level-support ≡ only-literals      □⇔

  opaque

    -- Is Level a small type?

    Level-is-small : Set
    Level-is-small = level-support ≡ level-type small

  opaque
    unfolding Level-is-small

    -- A characterisation lemma for Level-is-small.

    Level-is-small⇔ :
      Level-is-small ⇔ level-support ≡ level-type small
    Level-is-small⇔ = id⇔

  opaque
    unfolding Level-is-small

    -- Is Level-is-small inhabited?

    Level-is-small? : Dec Level-is-small
    Level-is-small? = _ ≟-Level-support _

  opaque

    -- Is Level a type that is not small?

    Level-is-not-small : Set
    Level-is-not-small = level-support ≡ level-type not-small

  opaque
    unfolding Level-is-not-small

    -- A characterisation lemma for Level-is-not-small.

    Level-is-not-small⇔ :
      Level-is-not-small ⇔ level-support ≡ level-type not-small
    Level-is-not-small⇔ = id⇔

  opaque
    unfolding Level-is-not-small

    -- Is Level-is-not-small inhabited?

    Level-is-not-small? : Dec Level-is-not-small
    Level-is-not-small? = _ ≟-Level-support _

  opaque

    -- A characterisation lemma for Level-allowed.

    Level-allowed⇔⊎ :
      Level-allowed ⇔ (Level-is-small ⊎ Level-is-not-small)
    Level-allowed⇔⊎ =
      Level-allowed                         ⇔⟨ Level-allowed⇔≢ ⟩

      level-support ≢ only-literals         ⇔⟨ (λ neq → case singleton level-support of λ where
                                                  (only-literals        , eq) → ⊥-elim (neq eq)
                                                  (level-type small     , eq) → inj₁ eq
                                                  (level-type not-small , eq) → inj₂ eq)
                                             , [ (λ eq₁ eq₂ → case trans (sym eq₁) eq₂ of λ ())
                                               , (λ eq₁ eq₂ → case trans (sym eq₁) eq₂ of λ ())
                                               ]
                                             ⟩
      level-support ≡ level-type small ⊎
      level-support ≡ level-type not-small  ⇔˘⟨ Level-is-small⇔ ⊎-cong-⇔ Level-is-not-small⇔ ⟩

      Level-is-small ⊎ Level-is-not-small   □⇔

  ----------------------------------------------------------------------
  -- Some derived definitions related to unit types

  -- The strong unit types are only allowed if the following predicate
  -- holds.

  Unitˢ-allowed : Set a
  Unitˢ-allowed = Unit-allowed 𝕤

  -- The weak unit types are only allowed if the following predicate
  -- holds.

  Unitʷ-allowed : Set a
  Unitʷ-allowed = Unit-allowed 𝕨

  -- Unitʷ-η holds exactly when η-for-Unitʷ is true.

  Unitʷ-η : Set
  Unitʷ-η = T η-for-Unitʷ

  opaque

    -- Unitʷ-η is decided.

    Unitʷ-η? : Dec Unitʷ-η
    Unitʷ-η? = T? _

  -- Some typing rules use the following condition.

  Unit-with-η : Strength → Set
  Unit-with-η s = s ≡ 𝕤 ⊎ Unitʷ-η

  opaque

    -- A decision procedure related to Unit-with-η.

    Unit-with-η? : ∀ s → Unit-with-η s ⊎ s ≡ 𝕨 × ¬ Unitʷ-η
    Unit-with-η? 𝕤 = inj₁ (inj₁ refl)
    Unit-with-η? 𝕨 = case Unitʷ-η? of λ where
      (yes η)   → inj₁ (inj₂ η)
      (no no-η) → inj₂ (refl , no-η)

  opaque

    -- Unit-with-η 𝕨 implies Unitʷ-η.

    Unit-with-η-𝕨→Unitʷ-η : Unit-with-η 𝕨 → Unitʷ-η
    Unit-with-η-𝕨→Unitʷ-η (inj₂ η)  = η
    Unit-with-η-𝕨→Unitʷ-η (inj₁ ())

  ----------------------------------------------------------------------
  -- Some derived definitions relation to identity types

  -- No-equality-reflection holds if equality reflection is not
  -- allowed.

  data No-equality-reflection : Set a where
    no-equality-reflection :
      ¬ Equality-reflection → No-equality-reflection

  opaque

    -- A characterisation lemma for No-equality-reflection.

    No-equality-reflection⇔ :
      No-equality-reflection ⇔ (¬ Equality-reflection)
    No-equality-reflection⇔ =
      (λ { (no-equality-reflection not-ok) → not-ok }) ,
      no-equality-reflection

  opaque

    -- No-equality-reflection is decided.

    No-equality-reflection? : Dec No-equality-reflection
    No-equality-reflection? =
      Dec-map (sym⇔ No-equality-reflection⇔) (¬? Equality-reflection?)

  opaque

    -- A characterisation lemma for No-equality-reflection or-empty_.

    No-equality-reflection-or-empty⇔ :
      No-equality-reflection or-empty Γ ⇔
      (¬ Equality-reflection ⊎ Empty-con Γ)
    No-equality-reflection-or-empty⇔ {Γ} =
      No-equality-reflection or-empty Γ     ⇔⟨ or-empty⇔ ⟩
      No-equality-reflection ⊎ Empty-con Γ  ⇔⟨ No-equality-reflection⇔ ⊎-cong-⇔ id⇔ ⟩
      ¬ Equality-reflection ⊎ Empty-con Γ   □⇔

  opaque

    -- No-equality-reflection or-empty_ is decidable.

    No-equality-reflection-or-empty? :
      Dec (No-equality-reflection or-empty Γ)
    No-equality-reflection-or-empty? =
      No-equality-reflection? or-empty?

  ----------------------------------------------------------------------
  -- Some derived definitions related to quotient types

  opaque

    -- Are the higher quotient constructors neutral?

    Higher-quotient-constructors-neutral : Set a
    Higher-quotient-constructors-neutral =
      Quot-allowed × ¬ Equality-reflection

  opaque
    unfolding Higher-quotient-constructors-neutral

    -- A characterisation lemma for
    -- Higher-quotient-constructors-neutral.

    Higher-quotient-constructors-neutral⇔ :
      Higher-quotient-constructors-neutral ⇔
      (Quot-allowed × ¬ Equality-reflection)
    Higher-quotient-constructors-neutral⇔ = id⇔

  ----------------------------------------------------------------------
  -- A derived definition related to opaque definitions

  opaque

    -- No-equality-reflection holds if opacity is allowed.

    Opacity-allowed→No-equality-reflection :
      Opacity-allowed → No-equality-reflection
    Opacity-allowed→No-equality-reflection =
      no-equality-reflection ∘→ no-opaque-equality-reflection

-- This type depends on a grade semiring.

record Type-configuration {M : Set a} (𝕄 : Modality M) :
         Set (lsuc a) where
  no-eta-equality

  open Configuration-types.Natrec 𝕄
  open Definition.Untyped M
  open Modality 𝕄

  field
    -- Configuration parameters that do not depend on the grade
    -- semiring.
    TC⁻ : Type-configuration⁻ a

  open Type-configuration⁻ TC⁻ public

  ----------------------------------------------------------------------
  -- Π- and Σ-types

  field
    -- Are Π- or Σ-types of the given kind allowed?
    ΠΣ-allowed : BinderMode → (p q : M) → Set a

  -- Are Π-types of the given kind allowed?

  Π-allowed : M → M → Set a
  Π-allowed = ΠΣ-allowed BMΠ

  -- Are Σ-types of the given kind allowed?

  Σ-allowed : Strength → M → M → Set a
  Σ-allowed = ΠΣ-allowed ∘→ BMΣ

  -- Are strong Σ-types of the given kind allowed?

  Σˢ-allowed : M → M → Set a
  Σˢ-allowed = Σ-allowed 𝕤

  -- Are weak Σ-types of the given kind allowed?

  Σʷ-allowed : M → M → Set a
  Σʷ-allowed = Σ-allowed 𝕨

  -- Is the type Erased, defined using the given strength, allowed?

  Erased-allowed : Strength → Set a
  Erased-allowed s = Unit-allowed s × Σ-allowed s 𝟘 𝟘

  -- Is the strong variant of Erased allowed?

  Erasedˢ-allowed : Set a
  Erasedˢ-allowed = Erased-allowed 𝕤

  -- Is the weak variant of Erased allowed?

  Erasedʷ-allowed : Set a
  Erasedʷ-allowed = Erased-allowed 𝕨

  ----------------------------------------------------------------------
  -- Identity types

  field
    -- Does the type system allow []-cong for the given strength?
    []-cong-allowed : Strength → Set a

    -- If []-cong is allowed for a given strength, then Erased is
    -- allowed for the same strength.
    []-cong→Erased : []-cong-allowed s → Erased-allowed s

    -- If []-cong is allowed (for any strength), then the modality is
    -- not trivial.
    []-cong→¬Trivial : []-cong-allowed s → ¬ Trivial

  -- Is the strong variant of []-cong allowed?

  []-congˢ-allowed : Set a
  []-congˢ-allowed = []-cong-allowed 𝕤

  -- Is the weak variant of []-cong allowed?

  []-congʷ-allowed : Set a
  []-congʷ-allowed = []-cong-allowed 𝕨

  ----------------------------------------------------------------------
  -- A derived definition related to universe levels

  opaque

    -- Is the given level allowed to be used as a level literal?

    Allowed-literal : Lvl n → Set a
    Allowed-literal (ωᵘ+ _)   = Omega-plus-allowed
    Allowed-literal (level t) = Level-literal t × ¬ Level-allowed

  ----------------------------------------------------------------------
  -- A derived definition related to Π- and Σ-types

  -- A variant of ΠΣ-allowed for BindingType.

  BindingType-allowed : BindingType → Set a
  BindingType-allowed (BM b p q) = ΠΣ-allowed b p q

------------------------------------------------------------------------
-- Configuration of the type and usage systems

-- This type depends on a mode structure.

record Configuration {M : Set a} {Mode : Set b} {𝕄 : Modality M}
         (𝐌 : Graded.Mode.IsMode Mode 𝕄) : Set (lsuc a ⊔ b) where
  no-eta-equality

  open Configuration-types.Natrec 𝕄
  open Configuration-types.Omega 𝕄
  open Definition.Untyped M
  open Graded.Context 𝕄
  open Graded.Mode Mode 𝕄
  open IsMode 𝐌
  open Modality 𝕄

  field
    -- Configuration of the type system.
    TC : Type-configuration 𝕄

  open Type-configuration TC public

  ----------------------------------------------------------------------
  -- The grade ω

  field
    -- Should the usage rules that require the grade ω be allowed?
    usage-rules-with-ω : Usage-with-or-without-omega

  -- A type that is inhabited iff the usage rules that require the
  -- grade ω are allowed.

  Usage-allows-omega : Set a
  Usage-allows-omega = Usage-with-omega usage-rules-with-ω

  ----------------------------------------------------------------------
  -- The empty type

  field
    -- Does the usage relation allow emptyrec with the given grade, at
    -- the given mode?
    Emptyrec-allowed : Mode → M → Set a

    -- Emptyrec-allowed is upwards closed in the mode.
    Emptyrec-allowed-upwards-closed :
      Emptyrec-allowed m p → m ≤ᵐ m′ → Emptyrec-allowed m′ p

  ----------------------------------------------------------------------
  -- Unit types

  field
    -- Does the usage relation allow unitrec with the given grades, at
    -- the given mode?
    Unitrec-allowed : Mode → (p q : M) → Set a

    -- Unitrec-allowed is upwards closed in the mode.
    Unitrec-allowed-upwards-closed :
      Unitrec-allowed m p q → m ≤ᵐ m′ → Unitrec-allowed m′ p q

    -- Should strong unit types act as "sinks"?
    starˢ-sink : Bool

  ----------------------------------------------------------------------
  -- Σ-types

  field
    -- Does the usage relation allow prodrec for the given grades, at
    -- the given mode?
    Prodrec-allowed : Mode → (r p q : M) → Set a

    -- Prodrec-allowed is upwards closed in the mode.
    Prodrec-allowed-upwards-closed :
      Prodrec-allowed m r p q → m ≤ᵐ m′ → Prodrec-allowed m′ r p q

  ----------------------------------------------------------------------
  -- Natural numbers

  field
    -- Which usage rule for natrec should be used?
    natrec-mode : Natrec-mode

  -- Three mutually exclusive types which correspond to each of the
  -- three possibilities for natrec-mode.

  Nr-available : Set a
  Nr-available = Natrec-mode-has-nr natrec-mode

  Nr-not-available : Set a
  Nr-not-available = Natrec-mode-no-nr natrec-mode

  Nr-not-available-GLB : Set a
  Nr-not-available-GLB = Natrec-mode-no-nr-glb natrec-mode

  field
    -- If nr functions are used, then they must be compatible with the
    -- modes.
    mode-supports-nr :
      ⦃ ok : Nr-available ⦄ →
      Mode-supports-nr ⦃ has-nr = Natrec-mode-Has-nr ok ⦄ 𝐌

  ----------------------------------------------------------------------
  -- Identity types

  field
    -- Is everything erased in the usage rule for Id?
    Id-erased : Set a

    -- Id-erased is decided.
    Id-erased? : Dec Id-erased

    -- What kinds of erased matches are allowed for J and K (for the
    -- given mode)?
    erased-matches-for-JK : JK → Mode → Erased-matches

  -- What kinds of erased matches are allowed for J (for the given
  -- mode)?

  erased-matches-for-J : Mode → Erased-matches
  erased-matches-for-J = erased-matches-for-JK J

  -- What kinds of erased matches are allowed for K (for the given
  -- mode)?

  erased-matches-for-K : Mode → Erased-matches
  erased-matches-for-K = erased-matches-for-JK K

  field
    -- If m ≤ᵐ m′, then the usage rules for J and K are at least as
    -- permissive for m′ as for m. (See Jₘ-generalised,
    -- J₀ₘ₁-generalised, Kₘ-generalised and K₀ₘ₁-generalised in
    -- Graded.Usage.Properties.)
    erased-matches-for-JK-≤ᵉᵐ :
      m ≤ᵐ m′ →
      erased-matches-for-JK jk m ≤ᵉᵐ erased-matches-for-JK jk m′

    -- If at most some erased matches are allowed for either J or K
    -- for some mode, then Usage-allows-omega holds.
    erased-matches-for-JK-supports-ω :
      erased-matches-for-JK jk m ≤ᵉᵐ some → Usage-allows-omega

    -- Does the usage relation allow []-cong for the given strength,
    -- at the given mode? (The formalisation supports variants of
    -- []-cong for both strong and weak variants of Erased.)
    []-cong-allowed-mode : Strength → Mode → Set a

    -- If []-cong-allowed-mode holds for a given strength, then
    -- []-cong-allowed holds.
    []-cong-allowed-mode→[]-cong-allowed :
      []-cong-allowed-mode s m → []-cong-allowed s

    -- []-cong-allowed-mode is upwards closed in the mode.
    []-cong-allowed-mode-upwards-closed :
      []-cong-allowed-mode s m → m ≤ᵐ m′ → []-cong-allowed-mode s m′

  ----------------------------------------------------------------------
  -- Quotient types

  field
    -- If quotients are allowed, then the mode structure is
    -- non-trivial: the higher quotient constructors are only allowed
    -- in erased contexts.
    Quot-allowed→¬Trivialᵐ :
      Quot-allowed → ¬ Trivialᵐ

    -- Is the motive of qrec erased?
    Qrec-motive-erased : Set a

    -- Qrec-motive-erased is decided.
    Qrec-motive-erased? : Dec Qrec-motive-erased

  ----------------------------------------------------------------------
  -- Some derived definitions related to ω

  opaque

    -- Usage-allows-omega is propositional.

    Usage-allows-omega-propositional :
      (p q : Usage-allows-omega) → p ≡ q
    Usage-allows-omega-propositional = Usage-with-omega-propositional

  opaque

    -- Usage-allows-omega is decided.

    Usage-allows-omega? : Dec Usage-allows-omega
    Usage-allows-omega? = Usage-with-omega?

  ----------------------------------------------------------------------
  -- A derived definition related to the empty type

  opaque

    -- If emptyrec is allowed at mode m (for some grade) then it is
    -- also allowed at mode m′ ·ᵐ m.

    Emptyrec-allowed-·ᵐ :
      Emptyrec-allowed m p →
      Emptyrec-allowed (m′ ·ᵐ m) p
    Emptyrec-allowed-·ᵐ ok =
      Emptyrec-allowed-upwards-closed ok ·ᵐ-increasingˡ

  ----------------------------------------------------------------------
  -- Some derived definition related to unit types

  opaque

    -- If emptyrec is allowed at mode m (for some grades) then it
    -- is also allowed at mode m′ ·ᵐ m.

    Unitrec-allowed-·ᵐ :
      Unitrec-allowed m p q →
      Unitrec-allowed (m′ ·ᵐ m) p q
    Unitrec-allowed-·ᵐ ok =
      Unitrec-allowed-upwards-closed ok ·ᵐ-increasingˡ

  -- Do strong unit types act as "sinks"?

  Starˢ-sink : Set
  Starˢ-sink = T starˢ-sink

  -- Strong unit types are not allowed to both act and not act as
  -- sinks.

  not-sink-and-no-sink : Starˢ-sink → ¬ Starˢ-sink → ⊥
  not-sink-and-no-sink sink ¬sink with starˢ-sink
  … | false = sink
  … | true = ¬sink _

  -- Strong unit types either act or do not act as sinks.

  sink-or-no-sink : Starˢ-sink ⊎ ¬ Starˢ-sink
  sink-or-no-sink with starˢ-sink
  … | false = inj₂ idᶠ
  … | true = inj₁ _

  ----------------------------------------------------------------------
  -- A derived definition related to Σ-types

  opaque

    -- If prodrec is allowed at mode m (for some grade) then it is
    -- also allowed at mode m′ ·ᵐ m.

    Prodrec-allowed-·ᵐ :
      Prodrec-allowed m r p q →
      Prodrec-allowed (m′ ·ᵐ m) r p q
    Prodrec-allowed-·ᵐ ok =
      Prodrec-allowed-upwards-closed ok ·ᵐ-increasingˡ

  ----------------------------------------------------------------------
  -- Some derived definitions related to natural numbers

  opaque

    -- Multiplication by a mode distributes over nrᶜ.

    ⌜⌝-·ᶜ-nrᶜ :
      ⦃ ok : Nr-available ⦄ →
      ⌜ m ⌝ ·ᶜ nrᶜ ⦃ Natrec-mode-Has-nr ok ⦄ p r γ δ η ≈ᶜ
      nrᶜ ⦃ Natrec-mode-Has-nr ok ⦄ p r (⌜ m ⌝ ·ᶜ γ) (⌜ m ⌝ ·ᶜ δ)
        (⌜ m ⌝ ·ᶜ η)
    ⌜⌝-·ᶜ-nrᶜ {γ = ε} {(ε)} {(ε)} = ε
    ⌜⌝-·ᶜ-nrᶜ {γ = _ ∙ _} {_ ∙ _} {_ ∙ _} ⦃ ok ⦄ =
      ⌜⌝-·ᶜ-nrᶜ ∙
      Mode-supports-nr.⌜⌝-·-nr ⦃ has-nr = Natrec-mode-Has-nr ok ⦄
        mode-supports-nr

  opaque

    -- A variant of ⌞nr⌟-decreasing₁.

    ⌞⌟·ᵐ⌞nr⌟₁ :
      ⦃ ok : Nr-available ⦄ {z s n : M} →
      ⌞ z ⌟ ·ᵐ ⌞ Has-nr.nr (Natrec-mode-Has-nr ok) p r z s n ⌟ ≡ ⌞ z ⌟
    ⌞⌟·ᵐ⌞nr⌟₁ ⦃ ok ⦄ =
      sym $
      Mode-supports-nr.⌞nr⌟-decreasing₁
        ⦃ has-nr = Natrec-mode-Has-nr ok ⦄ mode-supports-nr

  opaque

    -- A variant of ⌞nr⌟-decreasing₃.

    ⌞⌟·ᵐ⌞nr⌟₃ :
      ⦃ ok : Nr-available ⦄ {z s n : M} →
      ⌞ n ⌟ ·ᵐ ⌞ Has-nr.nr (Natrec-mode-Has-nr ok) p r z s n ⌟ ≡ ⌞ n ⌟
    ⌞⌟·ᵐ⌞nr⌟₃ ⦃ ok ⦄ =
      sym $
      Mode-supports-nr.⌞nr⌟-decreasing₃
        ⦃ has-nr = Natrec-mode-Has-nr ok ⦄ mode-supports-nr

  ----------------------------------------------------------------------
  -- Some derived definitions related to identity types

  opaque

    -- A variant of erased-matches-for-JK-≤ᵉᵐ for J.

    erased-matches-for-J-≤ᵉᵐ :
      m ≤ᵐ m′ → erased-matches-for-J m ≤ᵉᵐ erased-matches-for-J m′
    erased-matches-for-J-≤ᵉᵐ = erased-matches-for-JK-≤ᵉᵐ

  opaque

    -- A variant of erased-matches-for-JK-≤ᵉᵐ for K.

    erased-matches-for-K-≤ᵉᵐ :
      m ≤ᵐ m′ → erased-matches-for-K m ≤ᵉᵐ erased-matches-for-K m′
    erased-matches-for-K-≤ᵉᵐ = erased-matches-for-JK-≤ᵉᵐ

  instance

    -- If at most some erased matches are allowed for either J or K
    -- for some mode, then Usage-allows-omega holds.

    erased-matches-JK-≤-some-Usage-allows-omega :
      ⦃ ok : erased-matches-for-JK jk m ≤ᵉᵐ some ⦄ →
      Usage-allows-omega
    erased-matches-JK-≤-some-Usage-allows-omega ⦃ ok ⦄ =
      erased-matches-for-JK-supports-ω
        (≤ᵉᵐ-transitive (erased-matches-for-JK-≤ᵉᵐ 𝟙ᵐ≤) ok)

    {-# INCOHERENT erased-matches-JK-≤-some-Usage-allows-omega #-}

  instance

    -- If some erased matches are allowed for either J or K for some
    -- mode, then at most some matches are allowed.

    erased-matches-JK-≡-some-≤-some :
      ⦃ ok : erased-matches-for-JK jk m ≡ some ⦄ →
      erased-matches-for-JK jk m ≤ᵉᵐ some
    erased-matches-JK-≡-some-≤-some ⦃ ok ⦄ =
      subst (_≤ᵉᵐ some) (sym ok) _

    {-# INCOHERENT erased-matches-JK-≡-some-≤-some #-}

  opaque

    -- The usage rules for J and K are at least as permissive for
    -- m′ ·ᵐ m as for m.

    erased-matches-for-JK-≤ᵉᵐ·ᵐ :
      erased-matches-for-JK jk m ≤ᵉᵐ erased-matches-for-JK jk (m′ ·ᵐ m)
    erased-matches-for-JK-≤ᵉᵐ·ᵐ =
      erased-matches-for-JK-≤ᵉᵐ ·ᵐ-increasingˡ

  opaque

    -- If all erased matches are allowed for J or K for m, then they
    -- are allowed for m′ ·ᵐ m.

    erased-matches-for-JK-all·ᵐ :
      erased-matches-for-JK jk m ≡ all →
      erased-matches-for-JK jk (m′ ·ᵐ m) ≡ all
    erased-matches-for-JK-all·ᵐ ≡all =
      ≤ᵉᵐ→≡all→≡all erased-matches-for-JK-≤ᵉᵐ·ᵐ ≡all

  opaque

    -- If all erased matches are allowed for J for m, then they are
    -- allowed for m′ ·ᵐ m.

    erased-matches-for-J-all·ᵐ :
      erased-matches-for-J m ≡ all →
      erased-matches-for-J (m′ ·ᵐ m) ≡ all
    erased-matches-for-J-all·ᵐ = erased-matches-for-JK-all·ᵐ

  opaque

    -- If all erased matches are allowed for K for m, then they are
    -- allowed for m′ ·ᵐ m.

    erased-matches-for-K-all·ᵐ :
      erased-matches-for-K m ≡ all →
      erased-matches-for-K (m′ ·ᵐ m) ≡ all
    erased-matches-for-K-all·ᵐ = erased-matches-for-JK-all·ᵐ

  opaque

    -- If some erased matches are allowed for J or K for the mode m,
    -- then some or all erased matches are allowed for m′ ·ᵐ m.

    erased-matches-for-JK-some·ᵐ :
      erased-matches-for-JK jk m ≡ some →
      erased-matches-for-JK jk (m′ ·ᵐ m) ≡ all ⊎
      erased-matches-for-JK jk (m′ ·ᵐ m) ≡ some
    erased-matches-for-JK-some·ᵐ {m} {m′} ≡-some =
      some≤ᵉᵐ→ (subst (_≤ᵉᵐ erased-matches-for-JK _ (m′ ·ᵐ m))
                 ≡-some erased-matches-for-JK-≤ᵉᵐ·ᵐ)

  opaque

    -- If some erased matches are allowed for J for the mode m, then
    -- some or all erased matches are allowed for m′ ·ᵐ m.

    erased-matches-for-J-some·ᵐ :
      erased-matches-for-J m ≡ some →
      erased-matches-for-J (m′ ·ᵐ m) ≡ all ⊎
      erased-matches-for-J (m′ ·ᵐ m) ≡ some
    erased-matches-for-J-some·ᵐ = erased-matches-for-JK-some·ᵐ

  opaque

    -- If some erased matches are allowed for K for the mode m, then
    -- some or all erased matches are allowed for m′ ·ᵐ m.

    erased-matches-for-K-some·ᵐ :
      erased-matches-for-K m ≡ some →
      erased-matches-for-K (m′ ·ᵐ m) ≡ all ⊎
      erased-matches-for-K (m′ ·ᵐ m) ≡ some
    erased-matches-for-K-some·ᵐ = erased-matches-for-JK-some·ᵐ

  opaque

    -- If []-cong is allowed for a given strength and the mode m, then
    -- []-cong is allowed for m′ ·ᵐ m.

    []-cong-allowed-mode-·ᵐ :
      []-cong-allowed-mode s m →
      []-cong-allowed-mode s (m′ ·ᵐ m)
    []-cong-allowed-mode-·ᵐ ok =
      []-cong-allowed-mode-upwards-closed ok ·ᵐ-increasingˡ

  ----------------------------------------------------------------------
  -- Some definitions related to erased matches

  -- The property of not allowing (certain) erased matches:
  -- * Erased matches are allowed for emptyrec.
  -- * "Erased" matches are allowed for unitrec if η-equality is allowed
  --   for weak unit types.
  -- * "Erased" matches are allowed for trivial modalities.
  -- * Erased matches are allowed when the mode is ⌜ 𝟘 ⌝.

  No-erased-matches : Set (a ⊔ b)
  No-erased-matches =
    ¬ Trivial →
    (∀ {m r p q} → Prodrec-allowed m r p q → r ≡ 𝟘 → ⌜ m ⌝ ≡ 𝟘) ×
    (∀ {m p q} → Unitrec-allowed m p q → p ≡ 𝟘 → ⌜ m ⌝ ≢ 𝟘 → Unitʷ-η) ×
    (∀ {s m} → []-cong-allowed-mode s m → ⌜ m ⌝ ≡ 𝟘) ×
    erased-matches-for-J 𝟙ᵐ ≡ none ×
    erased-matches-for-K 𝟙ᵐ ≡ none

  -- The property of not allowing certain erased matches:
  -- * Erased matches are allowed for emptyrec and unitrec.
  -- * "Erased" matches are allowed for trivial modalities.
  -- * Erased matches are allowed when the mode is ⌜ 𝟘 ⌝.

  Only-some-erased-matches : Set (a ⊔ b)
  Only-some-erased-matches =
    ¬ Trivial →
    (∀ {m r p q} → Prodrec-allowed m r p q → r ≡ 𝟘 → ⌜ m ⌝ ≡ 𝟘) ×
    (∀ {s m} → []-cong-allowed-mode s m → ⌜ m ⌝ ≡ 𝟘) ×
    erased-matches-for-J 𝟙ᵐ ≡ none ×
    erased-matches-for-K 𝟙ᵐ ≡ none

  opaque

    -- If Unitʷ-η holds for C, then Only-some-erased-matches C implies
    -- No-erased-matches C.

    Only-some-erased-matches→No-erased-matches :
      Unitʷ-η → Only-some-erased-matches → No-erased-matches
    Only-some-erased-matches→No-erased-matches η =
      Σ.map idᶠ ((λ {_ _ _} _ _ _ → η) ,_) ∘→_
