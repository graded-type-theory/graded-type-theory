------------------------------------------------------------------------
-- Properties of the star operator.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Context.Properties.Star
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Modality 𝕄)
  ⦃ has-star : Has-star semiring-with-meet ⦄
  where

open import Graded.Context 𝕄
open import Graded.Context.Properties.Equivalence 𝕄
open import Graded.Context.Properties.PartialOrder 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    n : Nat
    r r′ : M
    γ γ′ δ δ′ : Conₘ n

-- ⊛ᶜ is a solution to the inequality x ≤ᶜ q +ᶜ r ·ᶜ x
-- γ ⊛ᶜ δ ▷ r ≤ᶜ δ +ᶜ r ·ᶜ γ ⊛ᶜ δ ▷ r
⊛ᶜ-ineq₁ : (γ δ : Conₘ n) (r : M) → γ ⊛ᶜ δ ▷ r ≤ᶜ δ +ᶜ r ·ᶜ γ ⊛ᶜ δ ▷ r
⊛ᶜ-ineq₁ ε ε r = ε
⊛ᶜ-ineq₁ (γ ∙ p) (δ ∙ q) r = ⊛ᶜ-ineq₁ γ δ r ∙ ⊛-ineq₁ p q r

-- ⊛ᶜ is a solution to the inequality x ≤ᶜ γ
-- γ ⊛ᶜ δ ▷ r ≤ᶜ γ
⊛ᶜ-ineq₂ : (γ δ : Conₘ n) (r : M) → γ ⊛ᶜ δ ▷ r ≤ᶜ γ
⊛ᶜ-ineq₂ ε ε r = ε
⊛ᶜ-ineq₂ (γ ∙ p) (δ ∙ q) r = ⊛ᶜ-ineq₂ γ δ r ∙ ⊛-ineq₂ p q r

-- ⊛ᶜ solves the following system of inequalities
-- γ ⊛ᶜ δ ▷ r ≤ᶜ δ +ᶜ r ·ᶜ γ ⊛ᶜ δ ▷ r
-- γ ⊛ᶜ δ ▷ r ≤ᶜ γ

⊛ᶜ-ineq : ((γ δ : Conₘ n) (r : M) → γ ⊛ᶜ δ ▷ r ≤ᶜ δ +ᶜ r ·ᶜ γ ⊛ᶜ δ ▷ r)
        × ((γ δ : Conₘ n) (r : M) → γ ⊛ᶜ δ ▷ r ≤ᶜ γ)
⊛ᶜ-ineq = ⊛ᶜ-ineq₁ , ⊛ᶜ-ineq₂

-- ⊛ᶜ is idempotent on 𝟘ᶜ on the first two arguments
-- 𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r ≈ᶜ 𝟘ᶜ

⊛ᶜ-idem-𝟘ᶜ : (r : M) → 𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r ≈ᶜ 𝟘ᶜ {n = n}
⊛ᶜ-idem-𝟘ᶜ {0} r = ≈ᶜ-refl
⊛ᶜ-idem-𝟘ᶜ {1+ n} r = (⊛ᶜ-idem-𝟘ᶜ r) ∙ (⊛-idem-𝟘 r)

-- Context scaling right sub-distributes over ⊛ w.r.t the first two arguments
-- (p ⊛ q ▷ r) ·ᶜ γ ≤ᶜ (p ·ᶜ γ) ⊛ᶜ (q ·ᶜ γ) ▷ r

·ᶜ-sub-distribʳ-⊛ : (p q r : M) (γ : Conₘ n) → p ⊛ q ▷ r ·ᶜ γ ≤ᶜ (p ·ᶜ γ) ⊛ᶜ q ·ᶜ γ ▷ r
·ᶜ-sub-distribʳ-⊛ p q r ε = ≤ᶜ-refl
·ᶜ-sub-distribʳ-⊛ p q r (γ ∙ p′) = (·ᶜ-sub-distribʳ-⊛ p q r γ) ∙ ·-sub-distribʳ-⊛ r p′ p q

-- Addition is sub-interchangeable over ⊛ᶜ w.r.t the first two arguments
-- (γ ⊛ᵣ δ) + (γ′ ⊛ᵣ δ′) ≤ (γ + γ′) ⊛ᵣ (δ + δ′)

+ᶜ-sub-interchangeable-⊛ᶜ : (r : M) → (γ δ γ′ δ′ : Conₘ n)
                         → (γ ⊛ᶜ δ ▷ r) +ᶜ (γ′ ⊛ᶜ δ′ ▷ r) ≤ᶜ (γ +ᶜ γ′) ⊛ᶜ (δ +ᶜ δ′) ▷ r
+ᶜ-sub-interchangeable-⊛ᶜ r ε ε ε ε = ε
+ᶜ-sub-interchangeable-⊛ᶜ  r (γ ∙ p) (δ ∙ q) (γ′ ∙ p′) (δ′ ∙ q′) =
  +ᶜ-sub-interchangeable-⊛ᶜ r γ δ γ′ δ′ ∙ +-sub-interchangeable-⊛ r p q p′ q′

-- Congruence of ⊛ᶜ
⊛ᶜ-cong : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → r ≡ r′ → γ ⊛ᶜ δ ▷ r ≈ᶜ γ′ ⊛ᶜ δ′ ▷ r′
⊛ᶜ-cong ε ε r≡r′ = ε
⊛ᶜ-cong (γ≈ᶜγ′ ∙ p≡p′) (δ≈ᶜδ′ ∙ q≡q′) r≡r′ =
  ⊛ᶜ-cong γ≈ᶜγ′ δ≈ᶜδ′ r≡r′ ∙ ⊛-cong p≡p′ q≡q′ r≡r′

⊛ᵣᶜ-cong : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → γ ⊛ᶜ δ ▷ r ≈ᶜ γ′ ⊛ᶜ δ′ ▷ r
⊛ᵣᶜ-cong γ≈ᶜγ′ δ≈ᶜδ′ = ⊛ᶜ-cong γ≈ᶜγ′ δ≈ᶜδ′ refl

⊛ᵣᶜ-congˡ : δ ≈ᶜ δ′ → γ ⊛ᶜ δ ▷ r ≈ᶜ γ ⊛ᶜ δ′ ▷ r
⊛ᵣᶜ-congˡ δ≈ᶜδ′ = ⊛ᵣᶜ-cong ≈ᶜ-refl δ≈ᶜδ′

⊛ᵣᶜ-congʳ : γ ≈ᶜ γ′ → γ ⊛ᶜ δ ▷ r ≈ᶜ γ′ ⊛ᶜ δ ▷ r
⊛ᵣᶜ-congʳ γ≈ᶜγ′ = ⊛ᵣᶜ-cong γ≈ᶜγ′ ≈ᶜ-refl

-- ⊛ᶜ is monotone on its first two arguments
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ ⊛ᶜ δ ▷ r ≤ᶜ γ′ ⊛ᶜ δ′ ▷ r

⊛ᶜ-monotone : γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → γ ⊛ᶜ δ ▷ r ≤ᶜ γ′ ⊛ᶜ δ′ ▷ r
⊛ᶜ-monotone {γ = ε} {γ′ = ε} {δ = ε} {δ′ = ε} γ≤γ′ δ≤δ′ =
  ε
⊛ᶜ-monotone
  {γ = _ ∙ _} {γ′ = _ ∙ _} {δ = _ ∙ _} {δ′ = _ ∙ _}
  (γ≤γ′ ∙ p≤p′) (δ≤δ′ ∙ q≤q′) =
  ⊛ᶜ-monotone γ≤γ′ δ≤δ′ ∙ ⊛-monotone p≤p′ q≤q′

⊛ᶜ-monotoneˡ : δ ≤ᶜ δ′ → γ ⊛ᶜ δ ▷ r ≤ᶜ γ ⊛ᶜ δ′ ▷ r
⊛ᶜ-monotoneˡ δ≤δ′ = ⊛ᶜ-monotone ≤ᶜ-refl δ≤δ′

⊛ᶜ-monotoneʳ : γ ≤ᶜ γ′ → γ ⊛ᶜ δ ▷ r ≤ᶜ γ′ ⊛ᶜ δ ▷ r
⊛ᶜ-monotoneʳ γ≤γ′ = ⊛ᶜ-monotone γ≤γ′ ≤ᶜ-refl
