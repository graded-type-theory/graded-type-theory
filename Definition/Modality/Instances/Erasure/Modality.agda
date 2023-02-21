open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions

module Definition.Modality.Instances.Erasure.Modality
  (restrictions : Restrictions Erasure)
  where

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Definition.Modality Erasure public
open import Tools.Algebra Erasure
open import Tools.Sum

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
  ; 𝟘ᵐ→𝟙≉𝟘 = λ _ ()
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
  ; 𝟘≮ = λ where
      refl → refl
  ; ∧≤𝟘ˡ = λ where
      {p = 𝟘} _  → refl
      {p = ω} ()
  ; ≉𝟘→≤𝟙 = λ where
      {p = 𝟘} 𝟘≉𝟘 → ⊥-elim (𝟘≉𝟘 refl)
      {p = ω} _   → refl
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
  ; ⊛≤𝟘ˡ = λ where
      {p = 𝟘} _  → refl
      {p = ω} ()
  ; ⊛≤𝟘ʳ = λ where
      {p = _} {q = 𝟘} _  → refl
      {p = 𝟘} {q = ω} ()
      {p = ω} {q = ω} ()
  }
