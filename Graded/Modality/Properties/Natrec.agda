------------------------------------------------------------------------
-- Properties of nr
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.Natrec
  {a} {M : Set a} (𝕄 : Semiring-with-meet M)
  where

open Semiring-with-meet 𝕄

open import Graded.Modality.Properties.PartialOrder 𝕄
open import Graded.Modality.Properties.Multiplication 𝕄

open import Tools.Empty
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder ≤-poset as RPo

private variable
  p r : M

------------------------------------------------------------------------
-- Properties of nr functions

module _ ⦃ has-nr : Has-nr _ 𝕄 ⦄ where

  open Has-nr has-nr

  opaque

    nr-𝟘 : nr p r 𝟘 𝟘 𝟘 ≡ 𝟘
    nr-𝟘 {p} {r} = ≤-antisym (nr-zero ≤-refl) (begin
      𝟘                               ≡˘⟨ ·-zeroʳ _ ⟩
      nr p r 𝟘 𝟘 𝟘 · 𝟘               ≤⟨ nr-· ⟩
      nr p r (𝟘 · 𝟘) (𝟘 · 𝟘) (𝟘 · 𝟘) ≡⟨ cong (λ x → nr p r x x x) (·-zeroˡ _) ⟩
      nr p r 𝟘 𝟘 𝟘                    ∎)
      where
      open RPo

------------------------------------------------------------------------
-- "Optimal" nr functions

-- A type used to express that there isn't a greatest factoring nr function.

record No-greatest-factoring-nr : Set a where
  field
    -- There are two nr functions
    has-nr₁ : Has-nr M 𝕄
    has-nr₂ : Has-nr M 𝕄
    -- Both nr functions are factoring
    factoring₁ : Has-factoring-nr M 𝕄 ⦃ has-nr₁ ⦄
    factoring₂ : Has-factoring-nr M 𝕄 ⦃ has-nr₂ ⦄

  open Has-nr has-nr₁ renaming (nr to nr₁)
  open Has-nr has-nr₂ renaming (nr to nr₂)

  field
    -- There is some input to the nr functions...
    p₀ r₀ z₀ s₀ n₀ : M

    -- ...such that their outputs are not equal...
    nr₁≢nr₂ : nr₁ p₀ r₀ z₀ s₀ n₀ ≢ nr₂ p₀ r₀ z₀ s₀ n₀

    -- ...and there is no other possible output that is greater than both
    -- i.e. no other nr function could be greater than both of them.
    nr≰ : ∀ q → nr₁ p₀ r₀ z₀ s₀ n₀ ≤ q → nr₂ p₀ r₀ z₀ s₀ n₀ ≤ q → ⊥
