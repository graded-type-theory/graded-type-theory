------------------------------------------------------------------------
-- Properties related to usage substitution for the "Zero-one" mode
-- structure.
------------------------------------------------------------------------

open import Configuration-types
import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Substitution.Properties.Zero-one
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (mode-variant : Mode-variant 𝕄)
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (C : Configuration Zero-one-isMode)
  where

open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Mode Mode 𝕄
open import Graded.Substitution C
open import Graded.Substitution.Properties C as S
  hiding (substₘ-lemma₀; substₘ-lemma₁)
open import Graded.Usage C
open import Graded.Usage.Properties C
open import Graded.Usage.Properties.Zero-one mode-variant C

open import Tools.Bool
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open Mode-variant mode-variant

private variable
  m n : Nat
  mo : Mode
  mos mos₁ mos₂ : Mode-vector _
  σ : Subst _ _
  p : M
  t : Term[ _ ] _
  γ : Conₘ _

------------------------------------------------------------------------
-- Well-formed substitutions

opaque

  -- A preservation lemma for _▶[_]_ that holds if 𝟘ᵐ is not allowed.

  ▶-without-𝟘ᵐ :
    (Ψ : Substₘ m n) →
    ¬ T 𝟘ᵐ-allowed →
    Ψ ▶[ mos₁ ] σ → Ψ ▶[ mos₂ ] σ
  ▶-without-𝟘ᵐ Ψ not-ok =
    ▶-cong Ψ (λ _ → Mode-propositional-without-𝟘ᵐ not-ok)

opaque

  -- An inversion lemma for _▶[_]_ related to multiplication.

  ▶-⌞·⌟ :
    (Ψ : Substₘ m n) (γ : Conₘ n) →
    Ψ ▶[ ⌞ p ·ᶜ γ ⌟ᶜ ] σ →
    (p ≡ 𝟘 × T 𝟘ᵐ-allowed) ⊎ (Ψ ▶[ ⌞ γ ⌟ᶜ ] σ)
  ▶-⌞·⌟ {p = p} {σ = σ} Ψ γ Ψ▶ = 𝟘ᵐ-allowed-elim
    (λ ok → case is-𝟘? p of λ where
       (yes p≡𝟘) → inj₁ (p≡𝟘 , ok)
       (no p≢𝟘)  → inj₂ λ x →
         case ▸-⌞·⌟
           (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-·ᶜ γ _ _)) (Ψ▶ x))
              (begin
                 ⌜ ⌞ p · γ ⟨ x ⟩ ⌟ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
                 (𝟘ᶜ , x ≔ ⌜ ⌞ p · γ ⟨ x ⟩ ⌟ ⌝) <* Ψ      ≡˘⟨ cong (λ p → (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) <* Ψ)
                                                                  (lookup-distrib-·ᶜ γ _ _) ⟩
                 (𝟘ᶜ , x ≔ ⌜ ⌞ p ·ᶜ γ ⌟ᶜ x ⌝) <* Ψ         ∎))
         of λ where
           (inj₂ ▸γx) → sub-≈ᶜ ▸γx (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ))
           (inj₁ ▸p)  → lemma _ _ _ (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸p)
    (λ not-ok → inj₂ (▶-without-𝟘ᵐ Ψ not-ok Ψ▶))
    where
    open ≤ᶜ-reasoning

    lemma :
      ∀ mo₁ mo₂ x →
      mo₁ ≡ 𝟙ᵐ →
      ⌜ mo₁ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ ▸[ mo₁ ] t →
      (𝟘ᶜ , x ≔ ⌜ mo₂ ⌝) <* Ψ ▸[ mo₂ ] t
    lemma 𝟘ᵐ _  _ ()
    lemma 𝟙ᵐ 𝟘ᵐ x _  ▸t = sub (▸-𝟘₀₁ ▸t)
      (begin
         (𝟘ᶜ , x ≔ 𝟘) <* Ψ  ≡⟨ cong (_<* Ψ) 𝟘ᶜ,≔𝟘 ⟩
         𝟘ᶜ <* Ψ            ≈⟨ <*-zeroˡ Ψ ⟩
         𝟘ᶜ                 ∎)
    lemma 𝟙ᵐ 𝟙ᵐ x _ ▸t = sub ▸t
      (begin
         (𝟘ᶜ , x ≔ 𝟙) <* Ψ       ≈˘⟨ ·ᶜ-identityˡ _ ⟩
         𝟙 ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ∎)

------------------------------------------------------------------------
-- Substitution lemmas

  -- A substitution lemma for the mode 𝟘ᵐ[ ok ]: if σ is well-formed and
  -- t is well-resourced with respect to any context and mode, then
  -- t [ σ ] is well-resourced with respect to the zero usage context
  -- and the mode 𝟘ᵐ[ ok ].

  substₘ-lemma₀ :
    ∀ ⦃ ok ⦄ (Ψ : Substₘ m n) →
    Ψ ▶[ mos ] σ → γ ▸[ mo ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t [ σ ]
  substₘ-lemma₀ ⦃ ok ⦄ Ψ ▶σ ▸t =
    ▸-cong 𝟘ᵐ?≡𝟘ᵐ (S.substₘ-lemma₀ (𝟘ᵐ-allowed→¬Trivialᵐ ok) ▶σ ▸t)

opaque

  -- A substitution lemma for the case where the mode 𝟘ᵐ is not allowed.

  substₘ-lemma₁ :
    ¬ T 𝟘ᵐ-allowed →
    (Ψ : Substₘ m n) →
    Ψ ▶[ mos ] σ → γ ▸[ mo ] t → substₘ Ψ γ ▸[ 𝟙ᵐ ] t [ σ ]
  substₘ-lemma₁ not-ok Ψ ▶σ ▸t =
    S.substₘ-lemma₁ (¬𝟘ᵐ-allowed→Trivialᵐ not-ok) ▶σ ▸t
