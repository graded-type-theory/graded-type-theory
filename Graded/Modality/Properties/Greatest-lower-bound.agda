------------------------------------------------------------------------
-- Properties of greatest lower bounds.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.Greatest-lower-bound
  {a} {M : Set a} (𝕄 : Semiring-with-meet M) where

open Semiring-with-meet 𝕄

open import Graded.Modality.Properties.PartialOrder 𝕄
open import Graded.Modality.Properties.Has-well-behaved-zero 𝕄

open import Tools.Algebra M
open import Tools.Empty
open import Tools.Nat using (Sequence)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
    p p′ q q′ r r′ : M
    pᵢ qᵢ : Sequence M

opaque

  -- Greatest lower bounds of constant sequences

  GLB-const :
    (∀ i → pᵢ i ≡ p) →
    Greatest-lower-bound p pᵢ
  GLB-const pᵢ≡p =
      (λ i → ≤-reflexive (sym (pᵢ≡p i)))
    , λ q q≤ → ≤-trans (q≤ 0) (≤-reflexive (pᵢ≡p 0))

opaque

  -- A variant of the above

  GLB-const′ :
    Greatest-lower-bound p (λ _ → p)
  GLB-const′ = GLB-const (λ _ → refl)

opaque

  -- Congruence of greatest lower bounds

  GLB-cong :
    p ≡ q →
    (∀ i → pᵢ i ≡ qᵢ i) →
    Greatest-lower-bound p pᵢ →
    Greatest-lower-bound q qᵢ
  GLB-cong refl pᵢ≡qᵢ (p≤ , p-GLB) =
    (λ i → ≤-trans (p≤ i) (≤-reflexive (pᵢ≡qᵢ i))) ,
    λ q q≤ → p-GLB q (λ i → ≤-trans (q≤ i) (≤-reflexive (sym (pᵢ≡qᵢ i))))

opaque

  -- Congruence of greatest lower bounds

  GLB-congˡ :
    (∀ i → pᵢ i ≡ qᵢ i) →
    Greatest-lower-bound p pᵢ →
    Greatest-lower-bound p qᵢ
  GLB-congˡ = GLB-cong refl

opaque

  -- Congruence of greatest lower bounds

  GLB-congʳ :
    p ≡ q →
    Greatest-lower-bound p pᵢ →
    Greatest-lower-bound q pᵢ
  GLB-congʳ p≡q = GLB-cong p≡q λ _ → refl

opaque

  -- The greatest lower bound, if it exists, is unique

  GLB-unique :
    Greatest-lower-bound p pᵢ →
    Greatest-lower-bound q pᵢ →
    p ≡ q
  GLB-unique p-GLB q-GLB =
    ≤-antisym (q-GLB .proj₂ _ (p-GLB .proj₁))
      (p-GLB .proj₂ _ (q-GLB .proj₁))

opaque

  -- If 𝟘 is the greatest lower bounds of a sequence then the sequence is
  -- constantly 𝟘 (if the modality has a well-behaved zero).

  𝟘-GLB-inv :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    Greatest-lower-bound 𝟘 pᵢ → ∀ i → pᵢ i ≡ 𝟘
  𝟘-GLB-inv 𝟘-glb i = 𝟘≮ (𝟘-glb .proj₁ i)

opaque

  -- An kind of inversion lemma for greatest lower bounds of
  -- certain sequences.

  ≢p-GLB-inv :
    p ≢ q → Greatest-lower-bound p pᵢ → (∀ i → pᵢ i ≡ q) → ⊥
  ≢p-GLB-inv p≢q p-glb pᵢ≡q =
    p≢q (≤-antisym (≤-trans (p-glb .proj₁ 0) (≤-reflexive (pᵢ≡q 0)))
          (p-glb .proj₂ _ (λ i → ≤-reflexive (sym (pᵢ≡q i)))))
