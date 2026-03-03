------------------------------------------------------------------------
-- Some properties related to usage and the weak variant of Erased
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Erased.Usage.No-eta
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Properties R
open import Graded.Modality.Properties 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Erased.No-eta 𝕄
open import Definition.Untyped.Sigma 𝕄

open import Graded.Derived.Sigma R

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.Sum
open import Tools.PropositionalEquality as PE using (_≡_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  A t : Term _
  γ δ : Conₘ _
  m   : Mode
  ok  : T _

------------------------------------------------------------------------
-- Usage rules

opaque
  unfolding erased fst⟨_⟩

  -- A usage rule for erased.

  ▸erased′ :
    (Trivialᵐ → Trivial) →
    γ ▸[ 𝟘ᵐ ] t →
    δ ▸[ 𝟘ᵐ ] A →
    Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘 →
    𝟘ᶜ ▸[ 𝟘ᵐ ] erased A t
  ▸erased′ {γ} {t} {δ} {A} hyp ▸t ▸A ok =
    case trivialᵐ? of λ where
      (yes 𝟙ᵐ≡𝟘ᵐ) →
        ▸-trivialᵐ 𝟙ᵐ≡𝟘ᵐ
          (sub (fstʷₘ (≡-trivialᵐ 𝟙ᵐ≡𝟘ᵐ)
                  (≡-trivial (hyp 𝟙ᵐ≡𝟘ᵐ)) ok ▸t ▸A)
               (≈ᶜ-trivial (hyp 𝟙ᵐ≡𝟘ᵐ)))
      (no 𝟙ᵐ≢𝟘ᵐ) →
        fstʷₘ-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ ok (▸-𝟘′ 𝟙ᵐ≢𝟘ᵐ ▸t) ▸A

opaque

  -- Another usage rule for erased.

  ▸erased :
    ¬ Trivialᵐ →
    γ ▸[ 𝟘ᵐ ] t →
    δ ▸[ 𝟘ᵐ ] A →
    Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘 →
    𝟘ᶜ ▸[ 𝟘ᵐ ] erased A t
  ▸erased 𝟙ᵐ≢𝟘ᵐ ▸t ▸A ok =
    ▸erased′ (⊥-elim ∘→ 𝟙ᵐ≢𝟘ᵐ) ▸t ▸A ok

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque
  unfolding erased fst⟨_⟩

  -- An inversion lemma for erased.

  inv-usage-erased :
    γ ▸[ m ] erased A t →
    ∃ λ δ →
    𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
    ⌜ 𝟘ᵐ ⌝ ·ᶜ δ ▸[ 𝟘ᵐ ] A ×
    γ ≤ᶜ 𝟘ᶜ ×
    𝟘 ≤ ⌜ m ⌝ ×
    Prodrec-allowed m (𝟘 ∧ 𝟙) 𝟘 𝟘
  inv-usage-erased {γ} {m} {A} {t} ▸erased =
    let η , _ , γ≤ , ▸t , ▸A , 𝟘∧⌜m⌝𝟘≤⌜m⌝ , P-ok =
          inv-usage-fstʷ (ᵐ·-identityʳ-≤𝟙 (∧-decreasingʳ _ _)) ▸erased
        𝟘≤⌜m⌝ = let open ≤-reasoning in begin
          𝟘             ≡˘⟨ ∧-idem _ ⟩
          𝟘 ∧ 𝟘         ≡˘⟨ ∧-congˡ (·-zeroʳ _) ⟩
          𝟘 ∧ ⌜ m ⌝ · 𝟘 ≤⟨ 𝟘∧⌜m⌝𝟘≤⌜m⌝ ⟩
          ⌜ m ⌝ ∎
        open ≤ᶜ-reasoning
    in  _ , sub (▸-𝟘 (▸-·′ ▸t)) (begin
              𝟘ᶜ                   ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
              ⌜ 𝟘ᵐ ⌝ ·ᶜ 𝟘ᶜ         ≈˘⟨ ·ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
              ⌜ 𝟘ᵐ ⌝ ·ᶜ 𝟘 ·ᶜ η     ≤⟨ ·ᶜ-monotoneʳ (·ᶜ-monotoneˡ 𝟘≤⌜m⌝) ⟩
              ⌜ 𝟘ᵐ ⌝ ·ᶜ ⌜ m ⌝ ·ᶜ η ∎)
          , ▸-𝟘 ▸A
          , ≤ᶜ-trans γ≤ (∧ᶜ-decreasingˡ _ _)
          , 𝟘≤⌜m⌝ , P-ok
