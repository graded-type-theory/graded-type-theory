------------------------------------------------------------------------
-- A modality for linear types.
------------------------------------------------------------------------

open import Tools.Bool using (T; false)
open import Tools.Level
open import Tools.Sum

open import Graded.Modality.Instances.Zero-one-many false as 𝟘𝟙ω
open import Graded.Modality.Variant lzero

module Graded.Modality.Instances.Linearity
  -- The modality variant.
  (variant : Modality-variant)
  where

open Modality-variant variant

open 𝟘𝟙ω renaming (Zero-one-many to Linearity) public

open import Graded.Modality Linearity
open import Graded.FullReduction.Assumptions
import Graded.Modality.Properties

open import Definition.Typed.Restrictions Linearity
open import Definition.Untyped using (BMΣ; Σₚ)

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

private variable
  rs : Type-restrictions

-- A "linear types" modality.

linearityModality : Modality
linearityModality = zero-one-many-modality variant

-- An alternative (not very good) "linear types" modality.
--
-- See Graded.Modality.Instances.Linearity.Bad for some examples that
-- illustrate in what sense this modality is not very good. The
-- modality linearityModality does not suffer from these problems (see
-- Graded.Modality.Instances.Linearity.Good), but note that, at the
-- time of writing, this formalisation does not contain any solid
-- evidence showing that linearityModality captures a good notion of
-- "linearity".

bad-linearity-modality : Modality
bad-linearity-modality = zero-one-many-greatest variant

-- The nr function obtained from linearityModality (if any) is
-- incomparable to (neither bounded from below nor from above by) the
-- nr function obtained from bad-linearity-modality.

incomparable :
  (nr-available : Nr-available) →
  let nr₁ = linearityModality
              .Modality.has-nr nr-available .Has-nr.nr
      nr₂ = bad-linearity-modality
              .Modality.has-nr nr-available .Has-nr.nr
  in
  (∃₂ λ p r → ∃₃ λ z s n → ¬ nr₁ p r z s n ≤ nr₂ p r z s n) ×
  (∃₂ λ p r → ∃₃ λ z s n → ¬ nr₂ p r z s n ≤ nr₁ p r z s n)
incomparable _ =
    (𝟘 , 𝟙 , 𝟘 , 𝟘 , 𝟙 , (λ ()))
  , (𝟘 , 𝟙 , 𝟙 , 𝟘 , 𝟙 , (λ ()))

-- The "linear types" modality has a well-behaved zero.

linearity-has-well-behaved-zero : Has-well-behaved-zero (Modality.semiring-with-meet linearityModality)
linearity-has-well-behaved-zero = zero-one-many-has-well-behaved-zero

open Graded.Modality.Properties linearityModality

-- An instance of Type-restrictions is suitable for the full reduction
-- theorem if
-- * Unit-allowed does not hold,
-- * Σₚ-allowed 𝟘 p does not hold, and
-- * Σₚ-allowed ω p does not hold.

Suitable-for-full-reduction :
  Type-restrictions → Set
Suitable-for-full-reduction rs =
  ¬ Unit-allowed ×
  (∀ p → ¬ Σₚ-allowed 𝟘 p) ×
  (∀ p → ¬ Σₚ-allowed ω p)
  where
  open Type-restrictions rs

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ Suitable-for-full-reduction
suitable-for-full-reduction rs =
    record rs
      { Unit-allowed = ⊥
      ; ΠΣ-allowed   = λ b p q → ΠΣ-allowed b p q × (b ≡ BMΣ Σₚ → p ≡ 𝟙)
      }
  , idᶠ
  , (λ _ → ((λ ()) ∘→ (_$ refl)) ∘→ proj₂)
  , (λ _ → ((λ ()) ∘→ (_$ refl)) ∘→ proj₂)
  where
  open Type-restrictions rs

-- The full reduction assumptions hold for linearityModality and any
-- "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction rs →
  Full-reduction-assumptions linearityModality rs
full-reduction-assumptions (¬Unit , ¬𝟘 , ¬ω) = record
  { 𝟙≤𝟘    = ⊥-elim ∘→ ¬Unit
  ; ≡𝟙⊎𝟙≤𝟘 = λ where
      {p = 𝟘} ok → ⊥-elim (¬𝟘 _ ok)
      {p = ω} ok → ⊥-elim (¬ω _ ok)
      {p = 𝟙} _  → inj₁ refl
  }
