------------------------------------------------------------------------
-- Variants of the type system
------------------------------------------------------------------------

module Definition.Typed.Variant where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.Relation
open import Tools.Sum

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

private variable
  Γ : Con _ _

-- This type makes it possible to choose between different variants of
-- the type system.
--
-- See also Definition.Typed.Restrictions.Type-restrictions.

data UnfoldingMode : Set where
  -- Unfold only explicitly specified definitions.
  explicit   : UnfoldingMode

  -- Unfold all transitive dependencies of definitions.
  transitive : UnfoldingMode

record Type-variant (a : Level) : Set (lsuc a) where
  no-eta-equality
  field

    -- How should transitive dependencies of definitions be unfolded?

    unfolding-mode : UnfoldingMode

    -- Should η-equality be enabled for weak unit types?
    --
    -- This variant of the type system is used to state some soundness
    -- theorems for extraction, see
    -- Graded.Erasure.Consequences.Soundness.Erased-matches.

    η-for-Unitʷ : Bool

    -- Are quotient types allowed?
    Quot-allowed : Set a

    -- Equality reflection is only allowed if the given predicate
    -- holds.
    Equality-reflection : Set a

    -- Equality-reflection is decided.
    Equality-reflection? : Dec Equality-reflection

  -- Unitʷ-η holds exactly when η-for-Unitʷ is true.

  Unitʷ-η : Set
  Unitʷ-η = T η-for-Unitʷ

  opaque

    -- Unitʷ-η is decided.

    Unitʷ-η? : Dec Unitʷ-η
    Unitʷ-η? = T? _

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
