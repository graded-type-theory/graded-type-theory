------------------------------------------------------------------------
-- Restrictions on typing derivations
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Typed.Restrictions
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Typed.Variant
open import Definition.Untyped M

open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.Relation
open import Tools.PropositionalEquality
open import Tools.Sum
open import Tools.Unit

-- This type specifies what variant of the type system should be used.
-- Various things can be disallowed, and one can also choose between
-- different sets of rules.

record Type-restrictions : Set (lsuc a) where
  no-eta-equality
  field
    -- What variant of the type system should be used?
    type-variant : Type-variant

  open Type-variant type-variant public

  field
    -- Unit types of either variant are only allowed if the given
    -- predicate holds.
    Unit-allowed : Strength → Set a

    -- Restrictions imposed upon Π- and Σ-types.
    ΠΣ-allowed : BinderMode → (p q : M) → Set a

  -- The strong unit types are only allowed if the following predicate
  -- holds.

  Unitˢ-allowed : Set a
  Unitˢ-allowed = Unit-allowed 𝕤

  -- The weak unit types are only allowed if the following predicate
  -- holds.

  Unitʷ-allowed : Set a
  Unitʷ-allowed = Unit-allowed 𝕨

  -- Restrictions imposed upon Π-types.

  Π-allowed : M → M → Set a
  Π-allowed = ΠΣ-allowed BMΠ

  -- Restrictions imposed upon Σ-types.

  Σ-allowed : Strength → M → M → Set a
  Σ-allowed = ΠΣ-allowed ∘→ BMΣ

  -- Restrictions imposed upon strong Σ-types.

  Σˢ-allowed : M → M → Set a
  Σˢ-allowed = Σ-allowed 𝕤

  -- Restrictions imposed upon weak Σ-types.

  Σʷ-allowed : M → M → Set a
  Σʷ-allowed = Σ-allowed 𝕨

  -- The type Erased A is only allowed if Erased-allowed holds.
  -- Note that the Erased type can be defined using either a
  -- weak or strong unit type.

  Erased-allowed : Strength → Set a
  Erased-allowed s = Unit-allowed s × Σ-allowed s 𝟘 𝟘

  Erasedˢ-allowed = Erased-allowed 𝕤
  Erasedʷ-allowed = Erased-allowed 𝕨

  field
    -- The K rule is only allowed if the given predicate holds.
    K-allowed : Set a

    -- []-cong is only allowed if the given predicate holds.
    -- Note that []-cong can be used with the Erased type
    -- defined using either a weak or a strong unit type.
    []-cong-allowed : Strength → Set a

    -- If []-cong is allowed, then Erased is allowed.
    []-cong→Erased : ∀ {s} → []-cong-allowed s → Erased-allowed s

    -- If []-cong is allowed, then the modality is not trivial.
    []-cong→¬Trivial : ∀ {s} → []-cong-allowed s → ¬ Trivial

  []-congˢ-allowed = []-cong-allowed 𝕤
  []-congʷ-allowed = []-cong-allowed 𝕨

  -- A variant of ΠΣ-allowed for BindingType.

  BindingType-allowed : BindingType → Set a
  BindingType-allowed (BM b p q) = ΠΣ-allowed b p q

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

open Type-restrictions
