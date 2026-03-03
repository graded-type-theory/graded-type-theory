------------------------------------------------------------------------
-- The erasure modality.
------------------------------------------------------------------------

module Graded.Modality.Instances.Erasure.Modality where

open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

open import Graded.Modality.Instances.Erasure
import Graded.Modality.Properties.Star as Star

open import Graded.Modality Erasure public

-- Erasure modality instance

ErasureModality : Modality
ErasureModality = record
  { _+_ = _+_
  ; _·_ = _·_
  ; _∧_ = _∧_
  ; 𝟘 = 𝟘
  ; 𝟙 = ω
  ; ω = ω
  ; ω·+≤ω·ʳ = λ {p = p} → +-decreasingʳ p
  ; ω≤𝟙 = refl
  ; is-𝟘? = _≟ 𝟘
  ; +-·-Semiring = +-·-Semiring
  ; ∧-Semilattice = +-Semilattice
  ; ·-distrib-∧ = ·-distrib-+
  ; +-distrib-∧ = +-distrib-+
  }

instance

  -- The zero of the erasure modality is well-behaved.

  erasure-has-well-behaved-zero :
    Has-well-behaved-zero ErasureModality
  erasure-has-well-behaved-zero = record
    { non-trivial = λ ()
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

  erasure-has-star : Has-star ErasureModality
  erasure-has-star = record
    { _⊛_▷_ = _⊛_▷_
    ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
    ; +-sub-interchangeable-⊛ = +-sub-interchangeable-⊛
    ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
    ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
    }

  -- An nr function can be defined for Erasure.

  erasure-has-nr : Has-nr ErasureModality
  erasure-has-nr = Star.has-nr ErasureModality

-- The nr function.

nr : Erasure → Erasure → Erasure → Erasure → Erasure → Erasure
nr = Has-nr.nr erasure-has-nr

instance

  -- The nr function factors

  erasure-has-factoring-nr : Is-factoring-nr erasure-has-nr
  erasure-has-factoring-nr = record
    { nr₂ = λ p r → ω
    ; nr₂≢𝟘 = λ ()
    ; nr-factoring = λ {
        {p} {r} {z} {s} {(𝟘)} → refl ;
        {p} {r} {(𝟘)} {s} {(ω)} → refl ;
        {p} {r} {(ω)} {s} {(ω)} → refl }
    }
    where
    nr-factoring : {p r z s n : Erasure} → nr p r z s n ≡ ω · n + nr p r z s n
    nr-factoring {n = 𝟘} = refl
    nr-factoring {z = 𝟘} {n = ω} = refl
    nr-factoring {z = ω} {n = ω} = refl
