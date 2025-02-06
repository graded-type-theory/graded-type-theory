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

-- The nr function zero-one-many-has-nr.nr is
-- incomparable to (neither bounded from below nor from above by) the
-- nr function zero-one-many-greatest-star-nr.nr

incomparable :
 let nr₁ = zero-one-many-has-nr .Has-nr.nr
     nr₂ = zero-one-many-greatest-star-nr .Has-nr.nr
  in
  (∃₅ λ p r z s n → ¬ nr₁ p r z s n ≤ nr₂ p r z s n) ×
  (∃₅ λ p r z s n → ¬ nr₂ p r z s n ≤ nr₁ p r z s n)
incomparable =
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
-- * whenever Unitˢ-allowed holds, then Starˢ-sink holds,
-- * Unitʷ-allowed and Unitʷ-η do not both hold,
-- * Σˢ-allowed 𝟘 p does not hold, and
-- * Σˢ-allowed ω p does not hold.

Suitable-for-full-reduction :
  Type-restrictions → Usage-restrictions → Set
Suitable-for-full-reduction rs us =
  (Unitˢ-allowed → Starˢ-sink) ×
  (Unitʷ-allowed → ¬ Unitʷ-η) ×
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
      { Unit-allowed = λ where
          𝕨 → Unitʷ-allowed × ¬ Unitʷ-η
          𝕤 → Unitˢ-allowed × Starˢ-sink
      ; ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q × (b ≡ BMΣ 𝕤 → p ≡ 𝟙)
      ; []-cong-allowed = λ where
          𝕨 → []-congʷ-allowed × ¬ Unitʷ-η
          𝕤 → ⊥
      ; []-cong→Erased = λ where
          {s = 𝕨} (ok , no-η) →
              ([]-cong→Erased ok .proj₁ , no-η)
            , []-cong→Erased ok .proj₂
            , λ ()
          {s = 𝕤} ()
      ; []-cong→¬Trivial = λ { {s = 𝕨} _ (); {s = 𝕤} () }
      }
  , proj₂
  , proj₂
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
full-reduction-assumptions (sink , no-η , ¬𝟘 , ¬ω) = record
  { sink⊎𝟙≤𝟘 = λ where
      {s = 𝕤} ok _         → inj₁ (refl , sink ok)
      {s = 𝕨} _  (inj₁ ())
      {s = 𝕨} ok (inj₂ η)  → ⊥-elim (no-η ok η)
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
    (λ ok → case sink⊎𝟙≤𝟘 ok (inj₁ refl) of λ where
       (inj₁ (_ , sink)) → sink
       (inj₂ ()))
  , (λ ok η → case sink⊎𝟙≤𝟘 ok (inj₂ η) of λ where
       (inj₁ (() , _))
       (inj₂ ()))
  , (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
      (inj₁ ())
      (inj₂ (_ , _ , ())))
  , (λ p Σ-ok → case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
      (inj₁ ())
      (inj₂ (() , _)))
  where
  open Full-reduction-assumptions as
  open Usage-restrictions us
