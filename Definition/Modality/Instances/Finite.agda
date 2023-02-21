open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Definition.Modality

-- A finite ringoid is a modality instance.

module Definition.Modality.Instances.Finite
  {a} {M : Set a} (𝕄 : ModalityWithout⊛ M)
  (fin : ∃ λ n → Σ (Fin (1+ n) → M)
                 λ f → Σ (M → Fin (1+ n))
                 λ f⁻¹ → ((p : M) → f (f⁻¹ p) ≡ p)) where

private
  variable
    n : Nat

open ModalityWithout⊛ 𝕄

open import Definition.Modality.Properties.Meet 𝕄
open import Definition.Modality.Properties.PartialOrder 𝕄

|M| : Nat
|M| = 1+ (proj₁ fin)

f : Fin |M| → M
f = proj₁ (proj₂ fin)

f⁻¹ : M → Fin |M|
f⁻¹ = proj₁ (proj₂ (proj₂ fin))

f-f⁻¹ : (p : M) → f (f⁻¹ p) ≈ p
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

-- Since M′ has a least element, it is a modality

isModality : Modality M
isModality = LB.isModality
  where import Definition.Modality.Instances.LowerBounded 𝕄 ∞ ∞-min as LB
