------------------------------------------------------------------------
-- Properties of nrᶜ
------------------------------------------------------------------------

import Graded.Modality

module Graded.Context.Properties.Natrec
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Modality 𝕄)
  where

open import Graded.Context 𝕄
open import Graded.Context.Properties.Equivalence 𝕄
open import Graded.Context.Properties.Addition 𝕄
open import Graded.Context.Properties.Multiplication 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties.Natrec semiring-with-meet

open import Tools.Fin
open import Tools.Nat using (Nat; 1+; Sequence)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality as RP
import Tools.Reasoning.Equivalence as RE

private variable
  m i                     : Nat
  x                       : Fin _
  n p q r s z             : M
  γ γ₁ γ₂ δ δ₁ δ₂ η η₁ η₂ : Conₘ _

module _  ⦃ has-nr : Has-nr semiring-with-meet ⦄ where

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
  nrᶜ-,≔ {γ = ε}     {x = ()}
  nrᶜ-,≔ {γ = _ ∙ _} {x = x0}   {δ = _ ∙ _} {η = _ ∙ _} = ≈ᶜ-refl
  nrᶜ-,≔ {γ = _ ∙ _} {x = _ +1} {δ = _ ∙ _} {η = _ ∙ _} =
    nrᶜ-,≔ ∙ refl

  -- The natrec usage functions commute (in a certain sense) with the
  -- context lookup operation.

  nrᶜ-⟨⟩ :
    (γ : Conₘ m) →
    nrᶜ p r γ δ η ⟨ x ⟩ ≡ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩)
  nrᶜ-⟨⟩ {δ = ε}                 {x = ()}
  nrᶜ-⟨⟩ {δ = _ ∙ _} {η = _ ∙ _} {x = x0}   (_ ∙ _) = refl
  nrᶜ-⟨⟩ {δ = _ ∙ _} {η = _ ∙ _} {x = _ +1} (γ ∙ _) = nrᶜ-⟨⟩ γ

  opaque

    -- If the nr function satisfies Linearity-like-nr-for-𝟘, then a
    -- corresponding property holds for nrᶜ.

    nrᶜ-linearity-like-for-𝟘 :
      Linearity-like-nr-for-𝟘 →
      nrᶜ p 𝟘 γ δ η ≈ᶜ ((𝟙 ∧ p) ·ᶜ η +ᶜ δ) ∧ᶜ (η +ᶜ γ)
    nrᶜ-linearity-like-for-𝟘 {γ = ε}     {δ = ε}     {η = ε}     _   = ε
    nrᶜ-linearity-like-for-𝟘 {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} hyp =
      nrᶜ-linearity-like-for-𝟘 hyp ∙ hyp

  opaque

    -- If the nr function satisfies Linearity-like-nr-for-𝟙, then a
    -- corresponding property holds for nrᶜ.

    nrᶜ-linearity-like-for-𝟙 :
      Linearity-like-nr-for-𝟙 →
      nrᶜ p 𝟙 γ δ η ≈ᶜ (𝟙 + p) ·ᶜ η +ᶜ ω ·ᶜ δ +ᶜ γ
    nrᶜ-linearity-like-for-𝟙 {γ = ε}     {δ = ε}     {η = ε}     _   = ε
    nrᶜ-linearity-like-for-𝟙 {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} hyp =
      nrᶜ-linearity-like-for-𝟙 hyp ∙ hyp

module _
  ⦃ has-nr : Has-nr semiring-with-meet ⦄
  ⦃ is-factoring-nr : Is-factoring-nr has-nr ⦄ where

  opaque

    -- If the nr function is "factoring" then nrᶜ also factors in a
    -- certain way

    nrᶜ-factoring : nrᶜ p r γ δ η ≈ᶜ nr₂ p r ·ᶜ η +ᶜ nrᶜ p r γ δ 𝟘ᶜ
    nrᶜ-factoring {γ = ε} {(ε)} {(ε)} = ε
    nrᶜ-factoring {γ = _ ∙ _} {_ ∙ _} {_ ∙ _} =
      nrᶜ-factoring ∙ nr-factoring

-- The sequence nrᵢ lifted to contexts

nrᵢᶜ : ∀ {n} → M → Conₘ n → Conₘ n → Sequence (Conₘ n)
nrᵢᶜ r ε ε i = ε
nrᵢᶜ r (γ ∙ p) (δ ∙ q) i =
  nrᵢᶜ r γ δ i ∙ nrᵢ r p q i

opaque

  -- Congruence for nrᵢᶜ

  nrᵢᶜ-cong : γ₁ ≈ᶜ γ₂ → δ₁ ≈ᶜ δ₂ → nrᵢᶜ r γ₁ δ₁ i ≈ᶜ nrᵢᶜ r γ₂ δ₂ i
  nrᵢᶜ-cong ε ε = ε
  nrᵢᶜ-cong (γ≈γ′ ∙ refl) (δ≈δ′ ∙ refl) =
    nrᵢᶜ-cong γ≈γ′ δ≈δ′ ∙ refl

opaque

  -- The sequence nrᵢᶜ r 𝟘ᶜ 𝟘ᶜ is constantly 𝟘ᶜ.

  nrᵢᶜ-𝟘ᶜ : ∀ {n i} → nrᵢᶜ {n} r 𝟘ᶜ 𝟘ᶜ i ≈ᶜ 𝟘ᶜ
  nrᵢᶜ-𝟘ᶜ {n = 0} = ε
  nrᵢᶜ-𝟘ᶜ {n = 1+ n} {i} =
    nrᵢᶜ-𝟘ᶜ ∙ nrᵢ-𝟘 i

opaque

  -- A monotonicity property for nrᵢᶜ.

  nrᵢᶜ-monotone : γ₁ ≤ᶜ γ₂ → δ₁ ≤ᶜ δ₂ → nrᵢᶜ r γ₁ δ₁ i ≤ᶜ nrᵢᶜ r γ₂ δ₂ i
  nrᵢᶜ-monotone {γ₁ = ε} {(ε)} {(ε)} {(ε)} _ _ = ε
  nrᵢᶜ-monotone {γ₁ = _ ∙ _} {(_ ∙ _)} {(_ ∙ _)} {(_ ∙ _)} {i}
    (γ≤ ∙ p≤) (δ≤ ∙ q≤) = nrᵢᶜ-monotone γ≤ δ≤ ∙ nrᵢ-monotone i p≤ q≤

opaque

  -- A "computation rule" for nrᵢᶜ.

  nrᵢᶜ-zero : nrᵢᶜ r γ δ 0 ≈ᶜ γ
  nrᵢᶜ-zero {γ = ε} {(ε)} = ε
  nrᵢᶜ-zero {γ = γ ∙ p} {δ ∙ q} = nrᵢᶜ-zero ∙ refl

opaque

  -- A "computation rule" for nrᵢᶜ.

  nrᵢᶜ-suc : nrᵢᶜ r γ δ (1+ i) ≈ᶜ δ +ᶜ r ·ᶜ nrᵢᶜ r γ δ i
  nrᵢᶜ-suc {γ = ε} {(ε)} = ε
  nrᵢᶜ-suc {γ = γ ∙ p} {δ ∙ q} =
    nrᵢᶜ-suc ∙ refl

opaque

  -- Adding two nrᵢᶜ sequences is the same as pairwise adding the arguments.

  nrᵢᶜ-+ᶜ : nrᵢᶜ r (γ₁ +ᶜ γ₂) (δ₁ +ᶜ δ₂) i ≈ᶜ nrᵢᶜ r γ₁ δ₁ i +ᶜ nrᵢᶜ r γ₂ δ₂ i
  nrᵢᶜ-+ᶜ {(r)} {γ₁ = ε} {(ε)} {(ε)} {(ε)} {(i)} = ε
  nrᵢᶜ-+ᶜ {(r)} {γ₁ = _ ∙ _} {_ ∙ _} {_ ∙ _} {_ ∙ _} {(i)} =
    nrᵢᶜ-+ᶜ ∙ nrᵢ-+ i


opaque

  -- Multiplication right-distributes over nrᵢᶜ.

  ·ᶜ-distribʳ-nrᵢᶜ : nrᵢ r p q i ·ᶜ γ ≈ᶜ nrᵢᶜ r (p ·ᶜ γ) (q ·ᶜ γ) i
  ·ᶜ-distribʳ-nrᵢᶜ {γ = ε} = ε
  ·ᶜ-distribʳ-nrᵢᶜ {i} {γ = γ ∙ p′} =
    ·ᶜ-distribʳ-nrᵢᶜ ∙ ·-distribʳ-nrᵢ i
