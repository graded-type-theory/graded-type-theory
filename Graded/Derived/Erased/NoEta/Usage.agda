------------------------------------------------------------------------
-- Some properties related to usage and Erased without η-equality
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Erased.NoEta.Usage
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Usage-restrictions M)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Graded.Derived.Erased.NoEta.Untyped 𝕄
open import Graded.Derived.Erased.Usage 𝕄 R 𝕨 public

open import Graded.Derived.Sigma 𝕄 R

open import Tools.Bool using (T)
open import Tools.Function
open import Tools.Product
open import Tools.Sum
import Tools.PropositionalEquality as PE
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
          Prodrec-allowed (𝟘 ∧ 𝟙) 𝟘 𝟘 →
          γ ▸[ 𝟘ᵐ[ ok ] ] erased A t
▸erased {ok = ok} ▸t ▸A P-ok =
  fstʷₘ-𝟘ᵐ ⦃ ok ⦄ P-ok ▸t ▸A

------------------------------------------------------------------------
-- Inversion lemmas for usage

-- An inversion lemma for erased.

inv-usage-erased :
  (ok : T 𝟘ᵐ-allowed) →
  γ ▸[ m ] erased A t →
  γ ▸[ m ] t × ∃ λ δ → δ ▸[ 𝟘ᵐ? ] A ×
  γ ≤ᶜ 𝟘ᶜ × Prodrec-allowed (𝟘 ∧ 𝟙) 𝟘 𝟘
inv-usage-erased {γ = γ} ok ▸[] =
  case inv-usage-fstʷ (inj₁ 𝟘≰𝟙) ▸[] of λ {
    (η , δ , γ≤ , ▸t , ▸A , _ , P-ok) →
  sub ▸t (≤ᶜ-trans γ≤ (∧ᶜ-decreasingʳ _ _))
  , _ , ▸A , ≤ᶜ-trans γ≤ (∧ᶜ-decreasingˡ _ _) , P-ok }
  where
  open import Graded.Modality.Properties.Has-well-behaved-zero
    semiring-with-meet ⦃ 𝟘-well-behaved ok ⦄
