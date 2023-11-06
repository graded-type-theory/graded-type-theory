------------------------------------------------------------------------
-- Some properties related to usage and Erased with η-equality
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Erased.Eta.Usage
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
open import Graded.Derived.Erased.Eta.Untyped 𝕄
open import Graded.Derived.Erased.Usage 𝕄 R Σₚ public

open import Tools.Bool
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  t : Term _
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
