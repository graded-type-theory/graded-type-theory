------------------------------------------------------------------------
-- Properties of the linearity modality instance
------------------------------------------------------------------------


open import Graded.Usage.Restrictions
open import Graded.Mode.Restrictions
import Graded.Modality.Instances.Linearity as L

module Graded.Modality.Instances.Linearity.Properties
  (mrs : Mode-restrictions)
  (open L mrs)
  (UR : Usage-restrictions Linearity) where

open Usage-restrictions UR

open import Definition.Untyped Linearity
open import Definition.Untyped.Sigma Linearity

open import Graded.Context linearityModality
open import Graded.Derived.Sigma linearityModality UR as S
  using (fstᵣ; sndᵣ)
open import Graded.Mode  linearityModality
open import Graded.Usage linearityModality UR

open import Tools.Nullary
open import Tools.PropositionalEquality

private variable
  p q : Linearity
  A   : Term _

¬prodrecₘ-Linearity : Prodrec-allowed 𝟙 𝟙 𝟘
                    → ¬ (∀ {n} {γ η : Conₘ n} {δ m r p q t u A}
                        → γ ▸[ m ᵐ· r ] t
                        → δ ∙ ⌜ m ⌝ · r  · p ∙ ⌜ m ⌝ · r ▸[ m ] u
                        → η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
                        → Prodrec-allowed r p q
                        → r ·ᶜ γ +ᶜ δ ▸[ m ] prodrecₚ p t u)
¬prodrecₘ-Linearity ok = S.¬prodrecₘ ok (λ ())

-- A certain usage rule for fstᵣ 𝟙 A (where A has type Term 1) does
-- not hold.

¬fstᵣₘ′ :
  {A : Term 1} →
  ¬ ({γ : Conₘ 1} {t : Term 1} →
     γ ▸[ 𝟙ᵐ ] t →
     γ ▸[ 𝟙ᵐ ] fstᵣ 𝟙 A t)
¬fstᵣₘ′ = S.¬fstᵣₘ′ (λ ())

-- A certain usage rule for fstᵣ does not hold.

¬fstᵣₘ :
  ¬ (∀ {γ : Conₘ 1} {t : Term 1} {p m′} m →
     γ ▸[ m ᵐ· p ] t →
     m ᵐ· p ≡ m′ →
     (m′ ≡ 𝟙ᵐ → p ≤ 𝟙) →
     γ ▸[ m′ ] fstᵣ p A t)
¬fstᵣₘ = S.¬fstᵣₘ (λ ())

-- A certain usage rule for sndᵣ p q A B (where A has type Term 1)
-- does not hold.

¬sndᵣₘ :
  {A : Term 1} (B : Term 2) →
  ¬ ({γ : Conₘ 1} {t : Term 1} →
     γ ▸[ 𝟙ᵐ ] t →
     γ ▸[ 𝟙ᵐ ] sndᵣ p q A B t)
¬sndᵣₘ B = S.¬sndᵣₘ B (λ ())
