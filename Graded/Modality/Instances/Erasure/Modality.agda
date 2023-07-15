------------------------------------------------------------------------
-- The erasure modality.
------------------------------------------------------------------------

module Graded.Modality.Instances.Erasure.Modality where

open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open import Graded.Modality.Instances.Erasure
open import Graded.Modality.Variant lzero

open import Graded.Modality Erasure public

-- Erasure annotations forms a semiring with meet

erasure-semiring-with-meet : Semiring-with-meet
erasure-semiring-with-meet = record
  { _+_ = _+_
  ; _·_ = _·_
  ; _∧_ = _∧_
  ; 𝟘 = 𝟘
  ; 𝟙 = ω
  ; +-·-Semiring = +-·-Semiring
  ; ∧-Semilattice = +-Semilattice
  ; ·-distrib-∧ = ·-distrib-+
  ; +-distrib-∧ = +-distrib-+
  }

-- The zero of the erasure semiring is well-behaved

erasure-has-well-behaved-zero : Has-well-behaved-zero erasure-semiring-with-meet
erasure-has-well-behaved-zero = record
  { 𝟙≢𝟘 = λ ()
  ; is-𝟘? = λ where
      𝟘 → yes refl
      ω → no (λ ())
  ; zero-product = λ where
      {p = 𝟘} {q = 𝟘} _  → inj₁ refl
      {p = 𝟘} {q = ω} _  → inj₁ refl
      {p = ω} {q = 𝟘} _  → inj₂ refl
      {p = ω} {q = ω} ()
  ; +-positiveˡ = λ where
      {p = 𝟘}         _  → refl
      {p = ω} {q = 𝟘} ()
      {p = ω} {q = ω} ()
  ; ∧-positiveˡ = λ where
      {p = 𝟘} _ → refl
      {p = ω} ()
  }

instance

  -- A natrec-star operator can be defined for Erasure.

  erasure-has-star : Has-star erasure-semiring-with-meet
  erasure-has-star = record
    { _⊛_▷_ = _⊛_▷_
    ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
    ; +-sub-interchangeable-⊛ = +-sub-interchangeable-⊛
    ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
    ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
    }

-- Erasure modality instances (for different modality variants).

ErasureModality : Modality-variant → Modality
ErasureModality variant = record
  { variant            = variant
  ; semiring-with-meet = erasure-semiring-with-meet
  ; has-star           = λ _ → erasure-has-star
  ; 𝟘-well-behaved     = λ _ → erasure-has-well-behaved-zero
  ; +-decreasingˡ      = λ _ _ → +-decreasingˡ
  }
