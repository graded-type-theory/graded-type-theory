------------------------------------------------------------------------
-- Properties related to usage contexts which hold if 𝟘 is
-- well-behaved
------------------------------------------------------------------------

import Graded.Modality

module Graded.Context.Properties.Has-well-behaved-zero
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Modality 𝕄)
  (𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet)
  where

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

open import Graded.Context 𝕄
open import Graded.Context.Properties.Lookup 𝕄
open import Graded.Modality.Natrec-star-instances
open import Graded.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet 𝟘-well-behaved
open import Graded.Modality.Properties.PartialOrder semiring-with-meet

private variable
  n       : Nat
  γ δ η χ : Conₘ _
  p r     : M

-- If ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r) ⟨ x ⟩ is 𝟘, then γ ⟨ x ⟩, δ ⟨ x ⟩
-- and η ⟨ x ⟩ are all 𝟘.

⟨⟩≡𝟘→⟨⟩≡𝟘-⊛ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ∀ γ (x : Fin n) →
  ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r) ⟨ x ⟩ ≡ 𝟘 →
  γ ⟨ x ⟩ ≡ 𝟘 × η ⟨ x ⟩ ≡ 𝟘 × δ ⟨ x ⟩ ≡ 𝟘
⟨⟩≡𝟘→⟨⟩≡𝟘-⊛ {η = η} {δ = δ} {p = p} {r = r} γ x ≡𝟘 =
    ∧-positiveˡ (⊛≡𝟘ˡ lemma)
  , ∧-positiveʳ (⊛≡𝟘ˡ lemma)
  , +-positiveˡ (⊛≡𝟘ʳ lemma)
  where
  open Tools.Reasoning.PropositionalEquality

  lemma =
    (γ ⟨ x ⟩ ∧ η ⟨ x ⟩) ⊛ δ ⟨ x ⟩ + (p ·ᶜ η) ⟨ x ⟩ ▷ r  ≡˘⟨ cong₂ (_⊛_▷ _) (lookup-distrib-∧ᶜ γ _ _) (lookup-distrib-+ᶜ δ _ _) ⟩
    (γ ∧ᶜ η) ⟨ x ⟩ ⊛ (δ +ᶜ p ·ᶜ η) ⟨ x ⟩ ▷ r            ≡˘⟨ lookup-distrib-⊛ᶜ (γ ∧ᶜ _) _ _ _ ⟩
    ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r) ⟨ x ⟩                 ≡⟨ ≡𝟘 ⟩
    𝟘                                                   ∎

-- If χ ≤ᶜ γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) and χ ⟨ x ⟩ is 𝟘, then
-- γ ⟨ x ⟩, δ ⟨ x ⟩ and η ⟨ x ⟩ are all 𝟘.

⟨⟩≡𝟘→⟨⟩≡𝟘-fixpoint :
  χ ≤ᶜ γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) →
  (x : Fin n) →
  χ ⟨ x ⟩ ≡ 𝟘 →
  γ ⟨ x ⟩ ≡ 𝟘 × η ⟨ x ⟩ ≡ 𝟘 × δ ⟨ x ⟩ ≡ 𝟘
⟨⟩≡𝟘→⟨⟩≡𝟘-fixpoint
  {χ = χ} {γ = γ} {η = η} {δ = δ} {p = p} {r = r} fix x ≡𝟘 =
    ∧-positiveˡ lemma
  , ∧-positiveˡ (∧-positiveʳ lemma)
  , +-positiveˡ (∧-positiveʳ (∧-positiveʳ lemma))
  where
  open Tools.Reasoning.PartialOrder ≤-poset

  lemma = 𝟘≮ $ begin
    𝟘                                                         ≡˘⟨ ≡𝟘 ⟩
    χ ⟨ x ⟩                                                   ≤⟨ lookup-monotone _ fix ⟩
    (γ ∧ᶜ η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)) ⟨ x ⟩                 ≡⟨ lookup-distrib-∧ᶜ γ _ _ ⟩
    γ ⟨ x ⟩ ∧ (η ∧ᶜ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ)) ⟨ x ⟩            ≡⟨ cong (_ ∧_) $ lookup-distrib-∧ᶜ η _ _ ⟩
    γ ⟨ x ⟩ ∧ η ⟨ x ⟩ ∧ (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) ⟨ x ⟩         ≡⟨ cong (γ ⟨ _ ⟩ ∧_) $ cong (_ ∧_) $ lookup-distrib-+ᶜ δ _ _ ⟩
    γ ⟨ x ⟩ ∧ η ⟨ x ⟩ ∧ (δ ⟨ x ⟩ + (p ·ᶜ η +ᶜ r ·ᶜ χ) ⟨ x ⟩)  ∎
