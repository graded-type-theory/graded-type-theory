open import Definition.Modality

module Definition.Modality.Properties.Star
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Properties.PartialOrder modalityWithout⊛
open import Definition.Modality.Properties.Meet modalityWithout⊛

open import Tools.Algebra M
open import Tools.Bool using (T)
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    p p′ q q′ r r′ : M

-- Variants of ⊛-congurence

⊛-cong : p ≈ p′ → q ≈ q′ → r ≈ r′ → p ⊛ q ▷ r ≈ p′ ⊛ q′ ▷ r′
⊛-cong = cong₃ _⊛_▷_

⊛ᵣ-cong : p ≈ p′ → q ≈ q′ → p ⊛ q ▷ r ≈ p′ ⊛ q′ ▷ r
⊛ᵣ-cong p≈p′ q≈q′ = ⊛-cong p≈p′ q≈q′ ≈-refl

⊛ᵣ-congˡ : q ≈ q′ → p ⊛ q ▷ r ≈ p ⊛ q′ ▷ r
⊛ᵣ-congˡ q≈q′ = ⊛ᵣ-cong ≈-refl q≈q′

⊛ᵣ-congʳ : p ≈ p′ → p ⊛ q ▷ r ≈ p′ ⊛ q ▷ r
⊛ᵣ-congʳ p≈p′ = ⊛ᵣ-cong p≈p′ ≈-refl

-- ⊛ is monotone on the first two arguments
-- If p ≤ p′ and q ≤ q′ then p ⊛ q ▷ r ≤ p′ ⊛ q′ ≤ r

⊛-monotone : p ≤ p′ → q ≤ q′ → p ⊛ q ▷ r ≤ p′ ⊛ q′ ▷ r
⊛-monotone {p} {p′} {q} {q′} {r} p≤p′ q≤q′ = begin
  p ⊛ q ▷ r
    ≈⟨ ⊛ᵣ-cong p≤p′ q≤q′ ⟩
  (p ∧ p′) ⊛ (q ∧ q′) ▷ r
    ≤⟨ ⊛-sub-distribˡ-∧ r (p ∧ p′) q q′ ⟩
  ((p ∧ p′) ⊛ q ▷ r) ∧ ((p ∧ p′) ⊛ q′ ▷ r)
    ≤⟨ ∧-monotone (⊛-sub-distribʳ-∧ r q p p′) (⊛-sub-distribʳ-∧ r q′ p p′) ⟩
  ((p ⊛ q ▷ r) ∧ (p′ ⊛ q ▷ r)) ∧ (p ⊛ q′ ▷ r ∧ p′ ⊛ q′ ▷ r)
    ≤⟨ ∧-decreasingʳ _ _ ⟩
  p ⊛ q′ ▷ r ∧ p′ ⊛ q′ ▷ r
    ≤⟨ ∧-decreasingʳ _ _ ⟩
  p′ ⊛ q′ ▷ r ∎
  where open import Tools.Reasoning.PartialOrder ≤-poset

-- ⊛ is idempotent on 𝟘 w.r.t the first two arguments
-- 𝟘 ⊛ 𝟘 ▷ r ≈ 𝟘
⊛-idem-𝟘 : (r : M) → (_⊛_▷ r) IdempotentOn 𝟘
⊛-idem-𝟘 r = ≤-antisym (⊛-ineq₂ 𝟘 𝟘 r) 𝟘≤𝟘⊛𝟘
  where
  open import Tools.Reasoning.PartialOrder ≤-poset
  𝟘≤𝟘⊛𝟘 = begin
    𝟘                     ≈˘⟨ ·-zeroʳ (𝟘 ⊛ 𝟘 ▷ r) ⟩
    (𝟘 ⊛ 𝟘 ▷ r) · 𝟘       ≤⟨ ·-sub-distribʳ-⊛ r 𝟘 𝟘 𝟘 ⟩
    (𝟘 · 𝟘) ⊛ (𝟘 · 𝟘) ▷ r ≈⟨ ⊛ᵣ-cong (·-zeroˡ 𝟘) (·-zeroˡ 𝟘) ⟩
    𝟘 ⊛ 𝟘 ▷ r ∎

-- If the mode 𝟘ᵐ is allowed and p ⊛ q ▷ r is equal to zero, then p is
-- equal to zero.

⊛≈𝟘ˡ : T 𝟘ᵐ-allowed → p ⊛ q ▷ r ≈ 𝟘 → p ≈ 𝟘
⊛≈𝟘ˡ {p = p} {q = q} {r = r} ok p⊛q▷r≈𝟘 = 𝟘≮ ok (begin
  𝟘          ≈˘⟨ p⊛q▷r≈𝟘 ⟩
  p ⊛ q ▷ r  ≤⟨ ⊛-ineq₂ _ _ _ ⟩
  p          ∎)
  where
  open import Tools.Reasoning.PartialOrder ≤-poset

-- If the mode 𝟘ᵐ is allowed and p ⊛ q ▷ r is equal to zero, then q is
-- equal to zero.

⊛≈𝟘ʳ : T 𝟘ᵐ-allowed → p ⊛ q ▷ r ≈ 𝟘 → q ≈ 𝟘
⊛≈𝟘ʳ {p = p} {q = q} {r = r} ok p⊛q▷r≈𝟘 = positiveˡ ok (𝟘≮ ok (begin
  𝟘                  ≈˘⟨ p⊛q▷r≈𝟘 ⟩
  p ⊛ q ▷ r          ≤⟨ ⊛-ineq₁ _ _ _ ⟩
  q + r · p ⊛ q ▷ r  ∎))
  where
  open import Tools.Reasoning.PartialOrder ≤-poset
