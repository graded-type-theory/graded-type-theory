------------------------------------------------------------------------
-- Some properties related to usage and Erased without η-equality
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Erased.NoEta.Usage
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Graded.Derived.Erased.NoEta.Untyped 𝕄
open import Graded.Derived.Erased.Usage 𝕄 R 𝕨 public

open import Graded.Derived.Sigma 𝕄 R

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.Sum
open import Tools.PropositionalEquality as PE using (_≡_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  A t : Term _
  γ δ : Conₘ _
  m   : Mode
  ok  : T _

------------------------------------------------------------------------
-- Usage rules

-- A usage rule for erased.

▸erased : γ ▸[ 𝟘ᵐ[ ok ] ] t →
          δ ▸[ 𝟘ᵐ[ ok ] ] A →
          Prodrec-allowed 𝟘ᵐ[ ok ] (𝟘 ∧ 𝟙) 𝟘 𝟘 →
          𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] erased A t
▸erased {ok = ok} ▸t ▸A P-ok =
  ▸-𝟘 (fstʷₘ-𝟘ᵐ ⦃ ok ⦄ P-ok ▸t ▸A)

------------------------------------------------------------------------
-- Inversion lemmas for usage

-- An inversion lemma for erased.

inv-usage-erased :
  γ ▸[ m ] erased A t →
  𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t ×
  𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] A ×
  γ ≤ᶜ 𝟘ᶜ ×
  m ≡ 𝟘ᵐ[ ok ] ×
  Prodrec-allowed m (𝟘 ∧ 𝟙) 𝟘 𝟘
inv-usage-erased {γ} {m} {ok} ▸erased =
  case inv-usage-fstʷ (inj₁ $ 𝟘ᵐ.𝟘≰𝟙 ok) ▸erased of λ
    (η , _ , γ≤ , ▸t , ▸A , 𝟘∧⌜m⌝𝟘≤⌜m⌝ , P-ok) →
  case
    (let open Tools.Reasoning.PartialOrder ≤-poset in begin
       𝟘              ≡˘⟨ ∧-idem _ ⟩
       𝟘 ∧ 𝟘          ≡˘⟨ ∧-congˡ $ ·-zeroʳ _ ⟩
       𝟘 ∧ ⌜ m ⌝ · 𝟘  ≤⟨ 𝟘∧⌜m⌝𝟘≤⌜m⌝ ⟩
       ⌜ m ⌝          ∎)
  of λ
    𝟘≤⌜m⌝ →
  case PE.singleton m of λ where
    (𝟙ᵐ , PE.refl) →
      ⊥-elim $ 𝟘ᵐ.𝟘≰𝟙 ok 𝟘≤⌜m⌝
    (𝟘ᵐ , PE.refl) →
        ▸-𝟘 ▸t
      , ▸-𝟘 ▸A
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           γ        ≤⟨ γ≤ ⟩
           𝟘ᶜ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
           𝟘ᶜ       ∎)
      , 𝟘ᵐ-cong
      , P-ok
