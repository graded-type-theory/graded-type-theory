------------------------------------------------------------------------
-- Some properties related to usage and Erased
------------------------------------------------------------------------

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

-- A usage rule for Erased.

▸Erased :
  γ ▸[ 𝟘ᵐ[ ok ] ] A →
  𝟘ᶜ ▸[ m ] Erased A
▸Erased {γ = γ} {ok = ok} {m = m} ▸A = sub
  (ΠΣₘ
     (▸-cong (PE.sym (ᵐ·𝟘≡𝟘ᵐ m ok)) (▸-𝟘 ▸A))
     (sub Unitₘ
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ              ∎)))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
     𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)

-- A usage rule for [_].

▸[] : γ ▸[ 𝟘ᵐ[ ok ] ] t → 𝟘ᶜ ▸[ m ] [ t ]
▸[] {ok = ok} {m = m} ▸t = sub
  (prodₚₘ (▸-cong (PE.sym (ᵐ·𝟘≡𝟘ᵐ m ok)) (▸-𝟘 ▸t)) starₘ)
  (begin
     𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
     𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
     𝟘 ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎)
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

-- An inversion lemma for Erased.

inv-usage-Erased : γ ▸[ m ] Erased A → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] A × γ ≤ᶜ 𝟘ᶜ
inv-usage-Erased {γ = γ} {m = m} {ok = ok} ▸Erased =
  case inv-usage-ΠΣ ▸Erased of
    λ (invUsageΠΣ {δ = δ} {η = η} ▸A ▸Unit γ≤) →
    ▸-𝟘 ▸A
  , (begin
       γ        ≤⟨ γ≤ ⟩
       δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ (tailₘ-monotone (inv-usage-Unit ▸Unit)) ⟩
       δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
       δ        ≤⟨ ▸-𝟘ᵐ (▸-cong (ᵐ·𝟘≡𝟘ᵐ m ok) ▸A) ⟩
       𝟘ᶜ       ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for [_].

inv-usage-[] : γ ▸[ m ] [ t ] → (∀ {ok} → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t) × γ ≤ᶜ 𝟘ᶜ
inv-usage-[] {γ = γ} {m = m} ▸[] =
  case inv-usage-prodₚ ▸[] of
    λ (invUsageProdₚ {δ = δ} {η = η} ▸t ▸star γ≤) →
    (λ {_} → ▸-𝟘 ▸t)
  , (begin
       γ            ≤⟨ γ≤ ⟩
       𝟘 ·ᶜ δ ∧ᶜ η  ≈⟨ ∧ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
       𝟘ᶜ ∧ᶜ η      ≤⟨ ∧ᶜ-monotoneʳ (inv-usage-star ▸star) ⟩
       𝟘ᶜ ∧ᶜ 𝟘ᶜ     ≈⟨ ∧ᶜ-idem _ ⟩
       𝟘ᶜ           ∎)
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
