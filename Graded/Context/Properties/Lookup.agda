------------------------------------------------------------------------
-- Properties of context lookup.
------------------------------------------------------------------------

import Graded.Modality

module Graded.Context.Properties.Lookup
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties.Equivalence 𝕄
open import Graded.Context.Properties.Natrec 𝕄
open import Graded.Context.Properties.PartialOrder 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality as PE

private
  variable
    n i : Nat
    x : Fin n
    p r : M
    γ δ : Conₘ n

-- Every lookup in a zero-context is zero
-- 𝟘ᶜ ⟨ x ⟩ ≡ 𝟘

𝟘ᶜ-lookup : (x : Fin n) → 𝟘ᶜ ⟨ x ⟩ ≡ 𝟘
𝟘ᶜ-lookup x0     = PE.refl
𝟘ᶜ-lookup (x +1) = 𝟘ᶜ-lookup x

-- The result of looking up anything in 𝟙ᶜ is 𝟙.

𝟙ᶜ-lookup : (x : Fin n) → 𝟙ᶜ ⟨ x ⟩ ≡ 𝟙
𝟙ᶜ-lookup x0     = PE.refl
𝟙ᶜ-lookup (x +1) = 𝟙ᶜ-lookup x

-- Context lookup is a monotone function
-- If γ ≤ᶜ δ then γ⟨x⟩ ≤ δ⟨x⟩

lookup-monotone : (x : Fin n) → γ ≤ᶜ δ → (γ ⟨ x ⟩) ≤ (δ ⟨ x ⟩)
lookup-monotone {γ = ε}             ()
lookup-monotone {γ = γ ∙ p} {δ ∙ q} x0     (γ≤δ ∙ p≤q) = p≤q
lookup-monotone {γ = γ ∙ p} {δ ∙ q} (x +1) (γ≤δ ∙ p≤q) = lookup-monotone x γ≤δ

-- The lookup function preserves equivalence.

lookup-cong : γ ≈ᶜ δ → γ ⟨ x ⟩ ≡ δ ⟨ x ⟩
lookup-cong γ≈ᶜδ = ≤-antisym
  (lookup-monotone _ (≤ᶜ-reflexive γ≈ᶜδ))
  (lookup-monotone _ (≤ᶜ-reflexive (≈ᶜ-sym γ≈ᶜδ)))

-- Context lookup distributes over addition
-- (γ +ᶜ δ)⟨x⟩ ≡ γ⟨x⟩ + δ⟨x⟩

lookup-distrib-+ᶜ : (γ δ : Conₘ n) (x : Fin n) → (γ +ᶜ δ) ⟨ x ⟩ ≡ γ ⟨ x ⟩ + δ ⟨ x ⟩
lookup-distrib-+ᶜ ε       _       ()
lookup-distrib-+ᶜ (γ ∙ p) (δ ∙ q) x0     = PE.refl
lookup-distrib-+ᶜ (γ ∙ p) (δ ∙ q) (x +1) = lookup-distrib-+ᶜ γ δ x

-- Context lookup distributes over multiplication
-- (p ·ᶜ γ)⟨x⟩ ≡ p · γ⟨x⟩

lookup-distrib-·ᶜ : (γ : Conₘ n) (p : M) (x : Fin n) → (p ·ᶜ γ) ⟨ x ⟩ ≡ p · γ ⟨ x ⟩
lookup-distrib-·ᶜ ε       _ ()
lookup-distrib-·ᶜ (γ ∙ q) p x0     = PE.refl
lookup-distrib-·ᶜ (γ ∙ q) p (x +1) = lookup-distrib-·ᶜ γ p x

-- Context lookup distributes over meet
-- (γ ∧ᶜ δ)⟨x⟩ ≡ γ⟨x⟩ ∧ δ⟨x⟩

lookup-distrib-∧ᶜ : (γ δ : Conₘ n) (x : Fin n)
                  → (γ ∧ᶜ δ) ⟨ x ⟩ ≡ (γ ⟨ x ⟩) ∧ (δ ⟨ x ⟩)
lookup-distrib-∧ᶜ ε       _       ()
lookup-distrib-∧ᶜ (γ ∙ p) (δ ∙ q) x0     = PE.refl
lookup-distrib-∧ᶜ (γ ∙ p) (δ ∙ q) (x +1) = lookup-distrib-∧ᶜ γ δ x

-- Context lookup distributes over ⊛ᶜ
-- (γ ⊛ᶜ δ ▷ r)⟨x⟩ ≡ γ⟨x⟩ ⊛ δ⟨x⟩ ▷ r

lookup-distrib-⊛ᶜ :
  ⦃ has-star : Has-star 𝕄 ⦄ →
  (γ δ : Conₘ n) (r : M) (x : Fin n) →
  (γ ⊛ᶜ δ ▷ r) ⟨ x ⟩ ≡ (γ ⟨ x ⟩) ⊛ (δ ⟨ x ⟩) ▷ r
lookup-distrib-⊛ᶜ ε       _       _ ()
lookup-distrib-⊛ᶜ (γ ∙ p) (δ ∙ q) r x0     = PE.refl
lookup-distrib-⊛ᶜ (γ ∙ p) (δ ∙ q) r (x +1) = lookup-distrib-⊛ᶜ γ δ r x

opaque

  -- Context lookup distributes over nrᵢᶜ

  lookup-distrib-nrᵢᶜ :
    ∀ r (γ δ : Conₘ n) x → (nrᵢᶜ r γ δ i) ⟨ x ⟩ ≡ nrᵢ r (γ ⟨ x ⟩) (δ ⟨ x ⟩) i
  lookup-distrib-nrᵢᶜ r ε ε ()
  lookup-distrib-nrᵢᶜ r (_ ∙ _) (_ ∙ _) x0 = refl
  lookup-distrib-nrᵢᶜ r (γ ∙ _) (δ ∙ _) (x +1) =
    lookup-distrib-nrᵢᶜ r γ δ x

-- Lookup is consistent with context updates
-- (γ , x ≔ p) ⟨ x ⟩ ≡ p

update-lookup : (γ : Conₘ n) (x : Fin n) → (γ , x ≔ p) ⟨ x ⟩ ≡ p
update-lookup ε       ()
update-lookup (_ ∙ _) x0     = PE.refl
update-lookup (γ ∙ _) (x +1) = update-lookup γ x

opaque

  -- One can express "is equal to 𝟘ᶜ" using the lookup operation.

  ≈ᶜ𝟘ᶜ⇔⟨⟩≡𝟘 : γ ≈ᶜ 𝟘ᶜ ⇔ (∀ x → γ ⟨ x ⟩ ≡ 𝟘)
  ≈ᶜ𝟘ᶜ⇔⟨⟩≡𝟘 = to , from
    where
    to : γ ≈ᶜ 𝟘ᶜ → ∀ x → γ ⟨ x ⟩ ≡ 𝟘
    to {γ = ε}     ε         ()
    to {γ = _ ∙ _} (_  ∙ ≡𝟘) x0     = ≡𝟘
    to {γ = _ ∙ _} (≈𝟘 ∙ _)  (x +1) = to ≈𝟘 x

    from : (∀ x → γ ⟨ x ⟩ ≡ 𝟘) → γ ≈ᶜ 𝟘ᶜ
    from {γ = ε}     _   = ε
    from {γ = _ ∙ _} hyp = from (hyp ∘→ _+1) ∙ hyp x0
