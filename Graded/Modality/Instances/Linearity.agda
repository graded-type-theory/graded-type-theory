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

open import Definition.Untyped using (BMΣ; 𝕤; 𝕨)
import Definition.Typed.Restrictions
import Graded.Usage.Restrictions

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

-- A "linear types" modality.

linearityModality : Modality
linearityModality = zero-one-many-modality variant

open Definition.Typed.Restrictions linearityModality
open Graded.Usage.Restrictions linearityModality

private variable
  rs : Type-restrictions
  us : Usage-restrictions


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

instance

  -- The "linear types" modality has a well-behaved zero.

  linearity-has-well-behaved-zero :
    Has-well-behaved-zero
      (Modality.semiring-with-meet linearityModality)
  linearity-has-well-behaved-zero = zero-one-many-has-well-behaved-zero

open Graded.Modality.Properties linearityModality

-- Instances of Type-restrictions and Usage-restrictions are suitable
-- for the full reduction theorem if
-- * Unitˢ-allowed does not hold or Starˢ-sink holds,
-- * Σˢ-allowed 𝟘 p does not hold, and
-- * Σˢ-allowed ω p does not hold.

Suitable-for-full-reduction :
  Type-restrictions → Usage-restrictions → Set
Suitable-for-full-reduction rs us =
  (¬ Unitˢ-allowed ⊎ Starˢ-sink) ×
  (∀ p → ¬ Σˢ-allowed 𝟘 p) ×
  (∀ p → ¬ Σˢ-allowed ω p)
  where
  open Type-restrictions rs
  open Usage-restrictions us

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ λ rs → Suitable-for-full-reduction rs us
suitable-for-full-reduction {us} rs =
    record rs
      { Unit-allowed =
          λ { 𝕨 → Unitʷ-allowed ; 𝕤 → Unitˢ-allowed × Starˢ-sink }
      ; ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 𝟙)
      ; []-cong-allowed =
          λ { 𝕨 → []-congʷ-allowed ; 𝕤 → ⊥ }
      ; []-cong→Erased =
          λ { {s = 𝕨} ok →
                []-cong→Erased ok .proj₁ , []-cong→Erased ok .proj₂
              , λ ()
            ; {s = 𝕤} ()
            }
      ; []-cong→¬Trivial = λ { {s = 𝕨} _ (); {s = 𝕤} () }
      }
  , (case sink-or-no-sink of λ where
      (inj₁ sink) → inj₂ sink
      (inj₂ ¬sink) → inj₁ (λ x → not-sink-and-no-sink (proj₂ x) ¬sink))
  , (λ _ → ((λ ()) ∘→ (_$ refl)) ∘→ proj₂)
  , (λ _ → ((λ ()) ∘→ (_$ refl)) ∘→ proj₂)
  where
  open Type-restrictions rs
  open Usage-restrictions us

-- The full reduction assumptions hold for linearityModality and any
-- "suitable" Type-restrictions and Usage-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction rs us →
  Full-reduction-assumptions rs us
full-reduction-assumptions (¬Unit⊎sink , ¬𝟘 , ¬ω) = record
  { sink⊎𝟙≤𝟘 = case ¬Unit⊎sink of λ where
    (inj₁ ¬Unit) → ⊥-elim ∘→ ¬Unit
    (inj₂ sink)  → λ _ → inj₁ sink
  ; ≡𝟙⊎𝟙≤𝟘   = λ where
      {p = 𝟘} ok → ⊥-elim (¬𝟘 _ ok)
      {p = ω} ok → ⊥-elim (¬ω _ ok)
      {p = 𝟙} _  → inj₁ refl
  }

-- Type and usage restrictions that satisfy the full reduction
-- assumptions are "suitable".

full-reduction-assumptions-suitable :
  Full-reduction-assumptions rs us → Suitable-for-full-reduction rs us
full-reduction-assumptions-suitable {us = us} as =
    (case sink-or-no-sink of λ where
      (inj₁ sink)  → inj₂ sink
      (inj₂ ¬sink) → inj₁ (λ Unit-ok → case sink⊎𝟙≤𝟘 Unit-ok of λ where
        (inj₁ sink) → not-sink-and-no-sink sink ¬sink
        (inj₂ ())))
  , (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
      (inj₁ ())
      (inj₂ (_ , _ , ())))
  , (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
      (inj₁ ())
      (inj₂ (() , _)))
  where
  open Full-reduction-assumptions as
  open Usage-restrictions us
