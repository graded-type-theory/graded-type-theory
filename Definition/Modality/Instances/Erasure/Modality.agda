open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions

module Definition.Modality.Instances.Erasure.Modality
  (restrictions : Restrictions Erasure)
  where

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Definition.Modality Erasure public
open import Tools.Sum

-- Erasure forms a modality

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

erasure-has-well-behaved-zero : Has-well-behaved-zero erasure-semiring-with-meet
erasure-has-well-behaved-zero = record
  { 𝟙≉𝟘 = λ ()
  ; is-𝟘? = λ where
      𝟘 → yes refl
      ω → no (λ ())
  ; zero-product = λ where
      {p = 𝟘} {q = 𝟘} _  → inj₁ refl
      {p = 𝟘} {q = ω} _  → inj₁ refl
      {p = ω} {q = 𝟘} _  → inj₂ refl
      {p = ω} {q = ω} ()
  ; positiveˡ = λ where
      {p = 𝟘}         _  → refl
      {p = ω} {q = 𝟘} ()
      {p = ω} {q = ω} ()
  ; ∧≤𝟘ˡ = λ where
      {p = 𝟘} _ → refl
      {p = ω} ()
  }

erasure-semiring-with-meet-and-star : Semiring-with-meet-and-star
erasure-semiring-with-meet-and-star = record
  { semiring-with-meet = erasure-semiring-with-meet
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
  ; +-sub-interchangeable-⊛ = +-sub-interchangeable-⊛
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
  }

ErasureModality : Modality
ErasureModality = record
  { semiring-with-meet-and-star = erasure-semiring-with-meet-and-star
  ; restrictions = restrictions
  ; 𝟘-well-behaved = λ _ → erasure-has-well-behaved-zero
  }
