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
open import Tools.Sum

open import Graded.Context 𝕄
open import Graded.Context.Properties.Lookup 𝕄
open import Graded.Context.Properties.Natrec 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet 𝟘-well-behaved
open import Graded.Modality.Properties.Star semiring-with-meet as Star
open import Graded.Modality.Properties.PartialOrder semiring-with-meet

private variable
  n       : Nat
  x       : Fin _
  γ δ η χ : Conₘ _
  p r     : M

-- If γ is bounded by δ and γ ⟨ x ⟩ is 𝟘, then δ ⟨ x ⟩ is 𝟘.

≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 : γ ≤ᶜ δ → γ ⟨ x ⟩ ≡ 𝟘 → δ ⟨ x ⟩ ≡ 𝟘
≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 {γ = γ} {δ = δ} {x = x} =
  γ ≤ᶜ δ                       →⟨ lookup-monotone _ ⟩
  γ ⟨ x ⟩ ≤ δ ⟨ x ⟩            →⟨ ≤→≡𝟘→≡𝟘 ⟩
  (γ ⟨ x ⟩ ≡ 𝟘 → δ ⟨ x ⟩ ≡ 𝟘)  □

-- The value of nrᶜ p r is only 𝟘ᶜ for 𝟘ᶜ, 𝟘ᶜ and 𝟘ᶜ.

nrᶜ-positive :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  nrᶜ p r γ δ η ≈ᶜ 𝟘ᶜ → γ ≈ᶜ 𝟘ᶜ × δ ≈ᶜ 𝟘ᶜ × η ≈ᶜ 𝟘ᶜ
nrᶜ-positive {γ = ε} {δ = ε} {η = ε} _ =
  ε , ε , ε
nrᶜ-positive {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (p ∙ q) =
  case nrᶜ-positive p of λ {
    (p₁ , p₂ , p₃) →
  case nr-positive 𝟘-well-behaved q of λ {
    (q₁ , q₂ , q₃) →
  p₁ ∙ q₁ , p₂ ∙ q₂ , p₃ ∙ q₃ }}

-- If (γ +ᶜ δ) ⟨ x ⟩ is 𝟘, then γ ⟨ x ⟩ and δ ⟨ x ⟩ are both 𝟘.

+ᶜ-positive-⟨⟩ : ∀ γ → (γ +ᶜ δ) ⟨ x ⟩ ≡ 𝟘 → γ ⟨ x ⟩ ≡ 𝟘 × δ ⟨ x ⟩ ≡ 𝟘
+ᶜ-positive-⟨⟩ {δ = δ} {x = x} γ =
  (γ +ᶜ δ) ⟨ x ⟩ ≡ 𝟘         ≡⟨ cong (_≡ _) (lookup-distrib-+ᶜ γ _ _) ⟩→
  γ ⟨ x ⟩ + δ ⟨ x ⟩ ≡ 𝟘      →⟨ +-positive ⟩
  γ ⟨ x ⟩ ≡ 𝟘 × δ ⟨ x ⟩ ≡ 𝟘  □

-- If (p ·ᶜ γ) ⟨ x ⟩ is 𝟘, then p is 𝟘 or γ ⟨ x ⟩ is 𝟘.

·ᶜ-zero-product-⟨⟩ : ∀ γ → (p ·ᶜ γ) ⟨ x ⟩ ≡ 𝟘 → p ≡ 𝟘 ⊎ γ ⟨ x ⟩ ≡ 𝟘
·ᶜ-zero-product-⟨⟩ {p = p} {x = x} γ =
  (p ·ᶜ γ) ⟨ x ⟩ ≡ 𝟘   ≡⟨ cong (_≡ _) (lookup-distrib-·ᶜ γ _ _) ⟩→
  p · γ ⟨ x ⟩ ≡ 𝟘      →⟨ zero-product ⟩
  p ≡ 𝟘 ⊎ γ ⟨ x ⟩ ≡ 𝟘  □

-- If (nrᶜ p r γ δ η) ⟨ x ⟩ is 𝟘, then γ ⟨ x ⟩, δ ⟨ x ⟩ and η ⟨ x ⟩
-- are all 𝟘.

nrᶜ-positive-⟨⟩ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ∀ γ →
  nrᶜ p r γ δ η ⟨ x ⟩ ≡ 𝟘 →
  γ ⟨ x ⟩ ≡ 𝟘 × δ ⟨ x ⟩ ≡ 𝟘 × η ⟨ x ⟩ ≡ 𝟘
nrᶜ-positive-⟨⟩ {p = p} {r = r} {δ = δ} {η = η} {x = x} γ =
  nrᶜ p r γ δ η ⟨ x ⟩ ≡ 𝟘                   ≡⟨ cong (_≡ _) (nrᶜ-⟨⟩ γ) ⟩→
  nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≡ 𝟘  →⟨ nr-positive 𝟘-well-behaved ⟩
  γ ⟨ x ⟩ ≡ 𝟘 × δ ⟨ x ⟩ ≡ 𝟘 × η ⟨ x ⟩ ≡ 𝟘   □

-- If ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r) ⟨ x ⟩ is 𝟘, then γ ⟨ x ⟩, δ ⟨ x ⟩
-- and η ⟨ x ⟩ are all 𝟘.

⟨⟩≡𝟘→⟨⟩≡𝟘-⊛ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ∀ γ (x : Fin n) →
  ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r) ⟨ x ⟩ ≡ 𝟘 →
  γ ⟨ x ⟩ ≡ 𝟘 × δ ⟨ x ⟩ ≡ 𝟘 × η ⟨ x ⟩ ≡ 𝟘
⟨⟩≡𝟘→⟨⟩≡𝟘-⊛ {η = η} {δ = δ} {p = p} {r = r} γ x =
  ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r) ⟨ x ⟩ ≡ 𝟘   →⟨ trans lemma ⟩
  nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ≡ 𝟘  →⟨ nr-positive 𝟘-well-behaved ⟩
  γ ⟨ x ⟩ ≡ 𝟘 × δ ⟨ x ⟩ ≡ 𝟘 × η ⟨ x ⟩ ≡ 𝟘   □
  where
  open Tools.Reasoning.PropositionalEquality

  instance

    has-nr′ : Has-nr semiring-with-meet
    has-nr′ = Star.has-nr

  lemma =
    nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)                ≡⟨⟩
    (γ ⟨ x ⟩ ∧ η ⟨ x ⟩) ⊛ δ ⟨ x ⟩ + p · η ⟨ x ⟩ ▷ r     ≡˘⟨ ⊛ᵣ-congˡ (+-congˡ (lookup-distrib-·ᶜ η _ _)) ⟩
    (γ ⟨ x ⟩ ∧ η ⟨ x ⟩) ⊛ δ ⟨ x ⟩ + (p ·ᶜ η) ⟨ x ⟩ ▷ r  ≡˘⟨ cong₂ (_⊛_▷ _) (lookup-distrib-∧ᶜ γ _ _) (lookup-distrib-+ᶜ δ _ _) ⟩
    (γ ∧ᶜ η) ⟨ x ⟩ ⊛ (δ +ᶜ p ·ᶜ η) ⟨ x ⟩ ▷ r            ≡˘⟨ lookup-distrib-⊛ᶜ (γ ∧ᶜ _) _ _ _ ⟩
    ((γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r) ⟨ x ⟩                 ∎

-- If χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ and χ ⟨ x ⟩ is 𝟘, then δ ⟨ x ⟩ is 𝟘.

⟨⟩≡𝟘→⟨⟩≡𝟘-fixpoint :
  χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ →
  χ ⟨ x ⟩ ≡ 𝟘 → δ ⟨ x ⟩ ≡ 𝟘
⟨⟩≡𝟘→⟨⟩≡𝟘-fixpoint {χ = χ} {δ = δ} {p = p} {η = η} {r = r} {x = x}
  fix ≡𝟘 =
                                          $⟨ lemma ⟩
  𝟘 ≤ δ ⟨ x ⟩ + (p ·ᶜ η +ᶜ r ·ᶜ χ) ⟨ x ⟩  →⟨ 𝟘≮ ⟩
  δ ⟨ x ⟩ + (p ·ᶜ η +ᶜ r ·ᶜ χ) ⟨ x ⟩ ≡ 𝟘  →⟨ +-positiveˡ ⟩
  δ ⟨ x ⟩ ≡ 𝟘                             □
  where
  open Tools.Reasoning.PartialOrder ≤-poset

  lemma = begin
    𝟘                                   ≡˘⟨ ≡𝟘 ⟩
    χ ⟨ x ⟩                             ≤⟨ lookup-monotone _ fix ⟩
    (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) ⟨ x ⟩       ≡⟨ lookup-distrib-+ᶜ δ _ _ ⟩
    δ ⟨ x ⟩ + (p ·ᶜ η +ᶜ r ·ᶜ χ) ⟨ x ⟩  ∎
