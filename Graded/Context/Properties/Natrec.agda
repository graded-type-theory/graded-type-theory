------------------------------------------------------------------------
-- Properties of nrᶜ
------------------------------------------------------------------------

import Graded.Modality

module Graded.Context.Properties.Natrec
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Modality 𝕄)
  ⦃ has-nr : Has-nr semiring-with-meet ⦄
  where

open import Graded.Context 𝕄
open import Graded.Context.Properties.Equivalence 𝕄
open import Graded.Context.Properties.Addition 𝕄
open import Graded.Context.Properties.Multiplication 𝕄
open import Graded.Modality.Nr-instances

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality as RP
import Tools.Reasoning.Equivalence as RE

private variable
  m                       : Nat
  x                       : Fin _
  n p r s z               : M
  γ γ₁ γ₂ δ δ₁ δ₂ η η₁ η₂ : Conₘ _

-- The function nrᶜ p r preserves context equality.

nrᶜ-cong :
  γ₁ ≈ᶜ γ₂ → δ₁ ≈ᶜ δ₂ → η₁ ≈ᶜ η₂ →
  nrᶜ p r γ₁ δ₁ η₁ ≈ᶜ nrᶜ p r γ₂ δ₂ η₂
nrᶜ-cong
  {γ₁ = ε} {γ₂ = ε} {δ₁ = ε} {δ₂ = ε} {η₁ = ε} {η₂ = ε} _ _ _ =
  ε
nrᶜ-cong
  {γ₁ = _ ∙ z₁} {γ₂ = _ ∙ z₂} {δ₁ = _ ∙ s₁} {δ₂ = _ ∙ s₂}
  {η₁ = _ ∙ n₁} {η₂ = _ ∙ n₂} {p = p} {r = r}
  (p₁ ∙ p₂) (q₁ ∙ q₂) (r₁ ∙ r₂) =
  nrᶜ-cong p₁ q₁ r₁ ∙
  (nr p r z₁ s₁ n₁  ≡⟨ cong₂ (nr _ _ _) q₂ r₂ ⟩
   nr p r z₁ s₂ n₂  ≡⟨ cong (λ z → nr _ _ z _ _) p₂ ⟩
   nr p r z₂ s₂ n₂  ∎)
  where
  open RP

-- The function nrᶜ p r is monotone.

nrᶜ-monotone :
  γ₁ ≤ᶜ γ₂ → δ₁ ≤ᶜ δ₂ → η₁ ≤ᶜ η₂ →
  nrᶜ p r γ₁ δ₁ η₁ ≤ᶜ nrᶜ p r γ₂ δ₂ η₂
nrᶜ-monotone
  {γ₁ = ε} {γ₂ = ε} {δ₁ = ε} {δ₂ = ε} {η₁ = ε} {η₂ = ε} _ _ _ =
  ε
nrᶜ-monotone
  {γ₁ = _ ∙ _} {γ₂ = _ ∙ _} {δ₁ = _ ∙ _} {δ₂ = _ ∙ _}
  {η₁ = _ ∙ _} {η₂ = _ ∙ _}
  (p₁ ∙ p₂) (q₁ ∙ q₂) (r₁ ∙ r₂) =
  nrᶜ-monotone p₁ q₁ r₁ ∙ nr-monotone p₂ q₂ r₂

-- Multiplication from the right sub-distributes over nrᶜ p r.

nrᶜ-·ᶜ : nr p r z s n ·ᶜ γ ≤ᶜ nrᶜ p r (z ·ᶜ γ) (s ·ᶜ γ) (n ·ᶜ γ)
nrᶜ-·ᶜ {γ = ε}     = ε
nrᶜ-·ᶜ {γ = _ ∙ _} = nrᶜ-·ᶜ ∙ nr-·

-- Addition is sub-interchangeable with nrᶜ p r.

nrᶜ-+ᶜ :
  nrᶜ p r γ₁ δ₁ η₁ +ᶜ nrᶜ p r γ₂ δ₂ η₂ ≤ᶜ
  nrᶜ p r (γ₁ +ᶜ γ₂) (δ₁ +ᶜ δ₂) (η₁ +ᶜ η₂)
nrᶜ-+ᶜ
  {γ₁ = ε} {δ₁ = ε} {η₁ = ε} {γ₂ = ε} {δ₂ = ε} {η₂ = ε} =
  ε
nrᶜ-+ᶜ
  {γ₁ = _ ∙ _} {δ₁ = _ ∙ _} {η₁ = _ ∙ _}
  {γ₂ = _ ∙ _} {δ₂ = _ ∙ _} {η₂ = _ ∙ _} =
  nrᶜ-+ᶜ ∙ nr-+

-- The value of nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ is 𝟘ᶜ.

nrᶜ-𝟘ᶜ : nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = m}
nrᶜ-𝟘ᶜ {m = 0}    = ε
nrᶜ-𝟘ᶜ {m = 1+ _} = nrᶜ-𝟘ᶜ ∙ nr-𝟘

-- If η is bounded by 𝟘ᶜ, then nrᶜ p r γ δ η is bounded by γ.

nrᶜ-zero : η ≤ᶜ 𝟘ᶜ → nrᶜ p r γ δ η ≤ᶜ γ
nrᶜ-zero {η = ε}     {γ = ε}     {δ = ε}     _         = ε
nrᶜ-zero {η = _ ∙ _} {γ = _ ∙ _} {δ = _ ∙ _} (p₁ ∙ p₂) =
  nrᶜ-zero p₁ ∙ nr-zero p₂

-- The value nrᶜ p r γ δ η is bounded by
-- δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ nrᶜ p r γ δ η.

nrᶜ-suc : nrᶜ p r γ δ η ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ nrᶜ p r γ δ η
nrᶜ-suc {γ = ε}     {δ = ε}     {η = ε}     = ε
nrᶜ-suc {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} = nrᶜ-suc ∙ nr-suc

-- If the function nr p r z s is decreasing for all z and s, then
-- nrᶜ p r γ δ is decreasing.

nrᶜ-decreasing :
  (∀ z s n → nr p r z s n ≤ n) →
  nrᶜ p r γ δ η ≤ᶜ η
nrᶜ-decreasing {γ = ε}     {δ = ε}     {η = ε}     _             = ε
nrᶜ-decreasing {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} nr-decreasing =
  nrᶜ-decreasing nr-decreasing ∙ nr-decreasing _ _ _

-- The natrec usage functions commute (in a certain sense) with the
-- context update operation.

nrᶜ-,≔ :
  nrᶜ p r (γ , x ≔ z) (δ , x ≔ s) (η , x ≔ n) ≈ᶜ
  nrᶜ p r γ δ η , x ≔ nr p r z s n
nrᶜ-,≔ {γ = _ ∙ _} {x = x0}   {δ = _ ∙ _} {η = _ ∙ _} = ≈ᶜ-refl
nrᶜ-,≔ {γ = _ ∙ _} {x = _ +1} {δ = _ ∙ _} {η = _ ∙ _} =
  nrᶜ-,≔ ∙ refl

-- The natrec usage functions commute (in a certain sense) with the
-- context lookup operation.

nrᶜ-⟨⟩ :
  (γ : Conₘ m) →
  nrᶜ p r γ δ η ⟨ x ⟩ ≡ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)
nrᶜ-⟨⟩ {δ = _ ∙ _} {η = _ ∙ _} {x = x0}   (_ ∙ _) = refl
nrᶜ-⟨⟩ {δ = _ ∙ _} {η = _ ∙ _} {x = _ +1} (γ ∙ _) = nrᶜ-⟨⟩ γ


-- If the nr function is "factoring" then nrᶜ also factors in a
-- certain way

nrᶜ-factoring : ⦃ _ : Has-factoring-nr semiring-with-meet ⦄
              → nrᶜ p r γ δ η ≈ᶜ nr₂ p r ·ᶜ η +ᶜ nrᶜ p r γ δ 𝟘ᶜ
nrᶜ-factoring {γ = ε} {(ε)} {(ε)} = ε
nrᶜ-factoring {γ = _ ∙ _} {_ ∙ _} {_ ∙ _} =
  nrᶜ-factoring ∙ nr-factoring
