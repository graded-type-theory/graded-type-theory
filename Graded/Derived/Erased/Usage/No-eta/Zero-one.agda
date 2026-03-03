------------------------------------------------------------------------
-- Some properties related to usage and the weak variant of Erased
-- and the Zero-one mode structure.
------------------------------------------------------------------------

open import Graded.Modality
import Graded.Mode.Instances.Zero-one
import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Derived.Erased.Usage.No-eta.Zero-one
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Graded.Mode.Instances.Zero-one.Variant 𝕄)
  {mode-variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (R : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Mode-variant mode-variant
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Properties R
open import Graded.Modality.Properties 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Erased.No-eta 𝕄

import Graded.Derived.Erased.Usage.No-eta R as U

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Function
open import Tools.Product
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

  -- A usage rule for erased.

  ▸erased′ :
    (¬ T 𝟘ᵐ-allowed → Trivial) →
    γ ▸[ 𝟘ᵐ? ] t →
    δ ▸[ 𝟘ᵐ? ] A →
    Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘 →
    𝟘ᶜ ▸[ 𝟘ᵐ? ] erased A t
  ▸erased′ hyp ▸t ▸A ok =
    U.▸erased′ (hyp ∘→ Trivialᵐ→¬𝟘ᵐ-allowed) ▸t ▸A ok


opaque

  -- Another usage rule for erased.

  ▸erased :
    γ ▸[ 𝟘ᵐ[ ok ] ] t →
    δ ▸[ 𝟘ᵐ[ ok ] ] A →
    Prodrec-allowed 𝟘ᵐ[ ok ] (𝟘 ∧ 𝟙) 𝟘 𝟘 →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] erased A t
  ▸erased {ok} ▸t ▸A ok′ =
    ▸-cong 𝟘ᵐ?≡𝟘ᵐ (U.▸erased (𝟘ᵐ-allowed→¬Trivialᵐ ok)
      (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A)
      (PE.subst (λ m → Prodrec-allowed m (𝟘 ∧ 𝟙) _ _) (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ok′))

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque

  -- An inversion lemma for erased.

  inv-usage-erased :
    γ ▸[ m ] erased A t →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t ×
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] A ×
    γ ≤ᶜ 𝟘ᶜ ×
    m ≡ 𝟘ᵐ[ ok ] ×
    Prodrec-allowed m (𝟘 ∧ 𝟙) 𝟘 𝟘
  inv-usage-erased {ok} ▸erased =
    let δ , ▸t , ▸A , γ≤ , 𝟘≤⌜m⌝ , ok′ = U.inv-usage-erased ▸erased
    in    ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t
        , sub-≈ᶜ (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A) (begin
            𝟘ᶜ           ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
            𝟘 ·ᶜ δ       ≈˘⟨ ·ᶜ-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
            ⌜ 𝟘ᵐ? ⌝ ·ᶜ δ ∎)
        , γ≤ , lemma _ 𝟘≤⌜m⌝ , ok′
    where
    open ≈ᶜ-reasoning
    lemma : ∀ m → 𝟘 ≤ ⌜ m ⌝ → m ≡ 𝟘ᵐ[ ok ]
    lemma 𝟘ᵐ _   = 𝟘ᵐ-cong
    lemma 𝟙ᵐ 𝟘≤𝟙 = ⊥-elim (𝟘≰𝟙 ⦃ 𝟘-well-behaved ok ⦄ 𝟘≤𝟙)
