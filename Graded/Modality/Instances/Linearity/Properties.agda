------------------------------------------------------------------------
-- Properties of the linearity modality
------------------------------------------------------------------------

open import Tools.Bool
open import Tools.Level

open import Graded.Usage.Restrictions
open import Graded.Modality.Variant lzero
import Graded.Modality.Instances.Linearity

module Graded.Modality.Instances.Linearity.Properties
  (variant : Modality-variant)
  (open Modality-variant variant)
  (open Graded.Modality.Instances.Linearity variant)
  (UR : Usage-restrictions Linearity) where

open Usage-restrictions UR

open import Definition.Untyped Linearity
open import Definition.Untyped.Sigma Linearity

open import Graded.Context linearityModality
open import Graded.Derived.Sigma linearityModality UR as S
  using (fstʷ; sndʷ)
open import Graded.Mode  linearityModality
open import Graded.Usage linearityModality UR

open import Tools.PropositionalEquality
open import Tools.Relation

private variable
  p q : Linearity
  A   : Term _

¬prodrecₘ-Linearity : Prodrec-allowed 𝟙 𝟙 𝟘
                    → ¬ (∀ {n} {γ η : Conₘ n} {δ m r p q t u A}
                        → γ ▸[ m ᵐ· r ] t
                        → δ ∙ ⌜ m ⌝ · r  · p ∙ ⌜ m ⌝ · r ▸[ m ] u
                        → η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
                        → Prodrec-allowed r p q
                        → r ·ᶜ γ +ᶜ δ ▸[ m ] prodrecˢ p t u)
¬prodrecₘ-Linearity ok = S.¬prodrecₘ ok (λ ())

-- A certain usage rule for fstʷ 𝟙 A (where A has type Term 1) does
-- not hold.

¬fstʷₘ′ :
  {A : Term 1} →
  ¬ ({γ : Conₘ 1} {t : Term 1} →
     γ ▸[ 𝟙ᵐ ] t →
     γ ▸[ 𝟙ᵐ ] fstʷ 𝟙 A t)
¬fstʷₘ′ = S.¬fstʷₘ′ (λ ())

-- A certain usage rule for fstʷ does not hold.

¬fstʷₘ :
  ¬ (∀ {γ : Conₘ 1} {t : Term 1} {p m′} m →
     γ ▸[ m ᵐ· p ] t →
     m ᵐ· p ≡ m′ →
     (m′ ≡ 𝟙ᵐ → p ≤ 𝟙) →
     γ ▸[ m′ ] fstʷ p A t)
¬fstʷₘ = S.¬fstʷₘ (λ ())

-- A certain usage rule for sndʷ p q A B (where A has type Term 1)
-- does not hold.

¬sndʷₘ :
  {A : Term 1} (B : Term 2) →
  ¬ ({γ : Conₘ 1} {t : Term 1} →
     γ ▸[ 𝟙ᵐ ] t →
     γ ▸[ 𝟙ᵐ ] sndʷ p q A B t)
¬sndʷₘ B = S.¬sndʷₘ B (λ ())
