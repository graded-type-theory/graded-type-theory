------------------------------------------------------------------------
-- Properties of the bounded distributive lattice modality related to
-- usage.
------------------------------------------------------------------------

open import Configuration-types
import Tools.Algebra
open import Tools.PropositionalEquality as PE
open import Tools.Relation
import Graded.Modality.Instances.Bounded-distributive-lattice
import Graded.Mode.Instances.Bounded-distributive-lattice

module Graded.Modality.Instances.Bounded-distributive-lattice.Usage
  {a} (M : Set a)
  (open Tools.Algebra M)
  (bl : Bounded-distributive-lattice)
  (open Bounded-distributive-lattice bl)
  (is-⊤? : (p : M) → Dec (p ≡ ⊤))
  (open Graded.Modality.Instances.Bounded-distributive-lattice _ bl is-⊤?)
  (open Graded.Mode.Instances.Bounded-distributive-lattice bl is-⊤?)
  (C : Configuration bounded-distributive-lattice-isMode)
  where

open Configuration C

open import Graded.Context modality
open import Graded.Context.Properties modality
open import Graded.Modality M
open import Graded.Usage C
open import Graded.Usage.Inversion C

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality

open Modality modality

private variable
  x : Fin _
  p q r ℓ : M
  γ δ η θ : Conₘ _
  A z s n : Term _


opaque

  -- An alternative usage rule for variables

  varₘ′ : γ ≤ᶜ 𝟘ᶜ , x ≔ ℓ → γ ▸[ ℓ ] var x
  varₘ′ γ≤ = sub var γ≤

opaque

  -- A usage inversion lemma for variables

  inv-usage-var′ : γ ▸[ ℓ ] var x → γ ≤ᶜ 𝟘ᶜ , x ≔ ℓ
  inv-usage-var′ ▸x = inv-usage-var ▸x


opaque

  -- An alternative usage rule for natrec

  natrec-no-nr-glbₘ′ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ ℓ ] z →
    δ ∙ ℓ ∨ p ∙ ℓ ∨ r ▸[ ℓ ] s →
    η ▸[ ℓ ] n →
    θ ∙ ⊤ ▸[ ⊤ ] A →
    η ∧ᶜ γ ∧ᶜ δ ▸[ ℓ ] natrec p q r A z s n
  natrec-no-nr-glbₘ′ {γ} {δ} {η} ▸z ▸s ▸n ▸A =
    let ▸A′ = sub-≈ᶜ ▸A (≈ᶜ-refl ∙ ·-zeroˡ _)
    in  sub-≈ᶜ (natrec-no-nr-glbₘ ▸z ▸s ▸n ▸A′ nrᵢ-⊥-glb nrᵢᶜ-glbᶜ) $ begin
      η ∧ᶜ γ ∧ᶜ δ          ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-identityˡ _) ⟩
      (⊥ ·ᶜ η) ∧ᶜ (γ ∧ᶜ δ) ≈˘⟨ +ᶜ≈ᶜ∧ᶜ ⟩
      (⊥ ·ᶜ η) +ᶜ (γ ∧ᶜ δ) ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- A usage inversion lemma for natrec

  inv-usage-natrec-no-nr-glb′ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    γ ▸[ ℓ ] natrec p q r A z s n →
    ∃₄ λ δ η θ φ → δ ▸[ ℓ ] z × η ∙ ℓ ∨ p ∙ ℓ ∨ r ▸[ ℓ ] s ×
    θ ▸[ ℓ ] n × φ ∙ 𝟘 ▸[ 𝟘 ] A × γ ≤ᶜ θ ∧ᶜ δ ∧ᶜ η
  inv-usage-natrec-no-nr-glb′ {γ} {r} ▸nr =
    let δ , η , θ , φ , x , χ , ▸z , ▸s , ▸n , ▸A , γ≤ , x-GLB , χ-GLB = inv-usage-natrec-no-nr-glb ▸nr
        open ≤ᶜ-reasoning
        χ≤ = begin
          χ                      ≤⟨ χ-GLB .proj₁ 1 ⟩
          nrᵢᶜ r δ η 1           ≈⟨ nrᵢᶜ-suc ⟩
          η +ᶜ r ·ᶜ nrᵢᶜ r δ η 0 ≈⟨ +ᶜ≈ᶜ∧ᶜ ⟩
          η ∧ᶜ r ·ᶜ nrᵢᶜ r δ η 0 ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
          η                      ∎
    in  _ , _ , _ , _ , ▸z , ▸s , ▸n , sub-≈ᶜ ▸A (≈ᶜ-refl ∙ PE.sym (·-zeroˡ _)) , (begin
        γ ≤⟨ γ≤ ⟩
        x ·ᶜ θ +ᶜ χ ≤⟨ +ᶜ-monotone (·ᶜ-monotoneˡ (x-GLB .proj₁ 0)) (∧ᶜ-greatest-lower-bound (χ-GLB .proj₁ 0) χ≤) ⟩
        𝟙 ·ᶜ θ +ᶜ nrᵢᶜ r δ η 0 ∧ᶜ η ≈⟨ +ᶜ-cong (·ᶜ-identityˡ _) (∧ᶜ-congʳ nrᵢᶜ-zero) ⟩
        θ +ᶜ δ ∧ᶜ η ≈⟨ +ᶜ≈ᶜ∧ᶜ ⟩
        θ ∧ᶜ δ ∧ᶜ η ∎)
