{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions

module Definition.Modality.Instances.Erasure.Modality
  (restrictions : Restrictions Erasure′)
  where

open import Tools.Product
open import Tools.PropositionalEquality

open import Definition.Modality Erasure′ public
open import Tools.Algebra Erasure′

-- Erasures form a modality

erasureModalityWithout⊛ : ModalityWithout⊛
erasureModalityWithout⊛ = record
  { _+_ = _+_
  ; _·_ = _·_
  ; _∧_ = _∧_
  ; 𝟘 = 𝟘
  ; 𝟙 = ω
  ; +-·-Semiring = +-·-Semiring
  ; ∧-Semilattice = +-Semilattice
  ; ·-distrib-∧ = ·-distrib-+
  ; +-distrib-∧ = +-distrib-+
  ; restrictions = restrictions
  }

ErasureModality : Modality
ErasureModality = record
  { modalityWithout⊛ = erasureModalityWithout⊛
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
  ; ⊛-cong = cong₃ _⊛_▷_
  ; +-sub-interchangable-⊛ = +-sub-interchangable-⊛
  ; ·-sub-distribʳ-⊛ = ·-sub-distribʳ-⊛
  ; ⊛-sub-distrib-∧ = λ r → ⊛-sub-distribˡ-∧ r , ⊛-sub-distribʳ-∧ r
  }
