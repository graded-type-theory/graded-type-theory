------------------------------------------------------------------------
-- A finite semiring is a modality instance.
------------------------------------------------------------------------

open import Tools.Bool hiding (_∧_)
open import Tools.Fin
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
import Graded.Modality

module Graded.Modality.Instances.Finite
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Semiring-with-meet)
  (fin : ∃ λ n → Σ (Fin (1+ n) → M)
                 λ f → Σ (M → Fin (1+ n))
                 λ f⁻¹ → ((p : M) → f (f⁻¹ p) ≡ p))
  where

private
  variable
    n : Nat

open Semiring-with-meet 𝕄

import Graded.Modality.Instances.LowerBounded 𝕄 as LB
open import Graded.Modality.Variant a
open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Nullary

|M| : Nat
|M| = 1+ (proj₁ fin)

f : Fin |M| → M
f = proj₁ (proj₂ fin)

f⁻¹ : M → Fin |M|
f⁻¹ = proj₁ (proj₂ (proj₂ fin))

f-f⁻¹ : (p : M) → f (f⁻¹ p) ≡ p
f-f⁻¹ = proj₂ (proj₂ (proj₂ fin))

-- n-ary meet

⋀ : (Fin (1+ n) → M) → M
⋀ {Nat.zero} aₙ = aₙ x0
⋀ {1+ n} aₙ = (aₙ x0) ∧ (⋀ (λ x → aₙ (x +1)))

-- ∞ is the meet of all elements

∞ : M
∞ = ⋀ f

-- ⋀ is decreasing (i.e. smaller than all its arguments)

⋀-decr : (f : Fin (1+ n) → M) → (x : Fin (1+ n)) → ⋀ f ≤ f x
⋀-decr {0} f x0 = ≤-refl
⋀-decr {1+ n} f x0 = ∧-decreasingˡ _ _
⋀-decr {1+ n} f (_+1 x) = ≤-trans (∧-decreasingʳ _ _) (⋀-decr (λ x → f (x +1)) x)

-- ∞ is the least element

∞-min : (p : M) → ∞ ≤ p
∞-min p = ≤-trans (⋀-decr f (f⁻¹ p)) (≤-reflexive (f-f⁻¹ p))

-- The least element can be used to define a natrec-star operator.

has-star : Has-star 𝕄
has-star = LB.has-star ∞ ∞-min

-- If certain properties hold, then 𝕄 can be turned into a certain
-- kind of modality.

isModality :
  (variant : Modality-variant) →
  let open Modality-variant variant in
  (T 𝟘ᵐ-allowed → Has-well-behaved-zero 𝕄) →
  (T 𝟘ᵐ-allowed → ¬ Nr-available → ∀ p q → p + q ≤ p) →
  Modality
isModality = LB.isModality ∞ ∞-min
