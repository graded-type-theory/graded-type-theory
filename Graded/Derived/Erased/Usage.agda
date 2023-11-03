------------------------------------------------------------------------
-- Some properties related to usage and Erased
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Erased.Usage
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions M)
  where

open Modality 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Graded.Derived.Erased.Untyped 𝕄

open import Tools.Bool
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  A t : Term _
  γ   : Conₘ _
  m   : Mode
  ok  : T _

private

  -- A lemma used below.

  ᵐ·𝟘≡𝟘ᵐ : ∀ m ok → m ᵐ· 𝟘 PE.≡ 𝟘ᵐ[ ok ]
  ᵐ·𝟘≡𝟘ᵐ m _ =
    m ᵐ· 𝟘   ≡⟨ ᵐ·-zeroʳ m ⟩
    𝟘ᵐ?      ≡⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
    𝟘ᵐ[ _ ]  ∎
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Usage rules

opaque

  -- A usage rule for Erased.

  ▸Erased :
    γ ▸[ 𝟘ᵐ? ] A →
    γ ▸[ m ] Erased A
  ▸Erased {γ} {m} ▸A = sub
    (ΠΣₘ
       (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸A)
       (sub Unitₘ
          (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
             𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
             𝟘ᶜ              ∎)))
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       γ +ᶜ 𝟘ᶜ  ∎)

opaque

  -- A usage rule for [_].

  ▸[] : γ ▸[ 𝟘ᵐ? ] t → 𝟘ᶜ ▸[ m ] [ t ]
  ▸[] {γ} {m} ▸t = sub
    (prodₚₘ (▸-cong (PE.sym (ᵐ·-zeroʳ m)) ▸t) starₘ)
    (begin
       𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
       𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
       𝟘 ·ᶜ γ ∧ᶜ 𝟘ᶜ  ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A usage rule for erased.

▸erased : γ ▸[ 𝟘ᵐ[ ok ] ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] erased t
▸erased {ok = ok} ▸t = fstₘ
  𝟘ᵐ[ ok ]
  (▸-cong (PE.sym lemma) (▸-𝟘 ▸t))
  lemma
  λ ()
  where
  open Tools.Reasoning.PropositionalEquality

  lemma =
    𝟘ᵐ[ ok ] ᵐ· 𝟘  ≡⟨ ᵐ·𝟘≡𝟘ᵐ 𝟘ᵐ[ ok ] _ ⟩
    𝟘ᵐ[ ok ]       ∎

------------------------------------------------------------------------
-- Inversion lemmas for usage

opaque

  -- An inversion lemma for Erased.

  inv-usage-Erased : γ ▸[ m ] Erased A → γ ▸[ 𝟘ᵐ? ] A
  inv-usage-Erased {γ} {m} ▸Erased =
    case inv-usage-ΠΣ ▸Erased of λ {
      (invUsageΠΣ {δ = δ} {η = η} ▸A ▸Unit γ≤) →
    sub (▸-cong (ᵐ·-zeroʳ m) ▸A) $ begin
      γ        ≤⟨ γ≤ ⟩
      δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ (tailₘ-monotone (inv-usage-Unit ▸Unit)) ⟩
      δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
      δ        ∎ }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- An inversion lemma for [_].

  inv-usage-[] : γ ▸[ m ] [ t ] → (∃ λ δ → δ ▸[ 𝟘ᵐ? ] t) × γ ≤ᶜ 𝟘ᶜ
  inv-usage-[] {γ} {m} ▸[] =
    case inv-usage-prodₚ ▸[] of λ {
      (invUsageProdₚ {δ = δ} {η = η} ▸t ▸star γ≤) →
      (_ , ▸-cong (ᵐ·-zeroʳ m) ▸t)
    , (begin
         γ            ≤⟨ γ≤ ⟩
         𝟘 ·ᶜ δ ∧ᶜ η  ≈⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘ᶜ ∧ᶜ η      ≤⟨ ∧ᶜ-monotoneʳ (inv-usage-star ▸star) ⟩
         𝟘ᶜ ∧ᶜ 𝟘ᶜ     ≈⟨ ∧ᶜ-idem _ ⟩
         𝟘ᶜ           ∎) }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for erased.

inv-usage-erased :
  γ ▸[ m ] erased t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t × γ ≤ᶜ 𝟘ᶜ × m PE.≡ 𝟘ᵐ[ ok ]
inv-usage-erased {γ = γ} {ok = ok} ▸[] =
  case inv-usage-fst ▸[] of λ where
    (invUsageFst {δ = δ} m PE.refl ▸t γ≤ _) →
        ▸-𝟘 ▸t
      , (begin
           γ   ≤⟨ γ≤ ⟩
           δ   ≤⟨ ▸-𝟘ᵐ (▸-cong (ᵐ·𝟘≡𝟘ᵐ m ok) ▸t) ⟩
           𝟘ᶜ  ∎)
      , ᵐ·𝟘≡𝟘ᵐ m _
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
