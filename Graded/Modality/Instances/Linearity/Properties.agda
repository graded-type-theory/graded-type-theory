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

open import Definition.Untyped.Sigma Linearity

open import Graded.Context linearityModality
open import Graded.Derived.Sigma linearityModality UR
open import Graded.Mode  linearityModality
open import Graded.Usage linearityModality UR

open import Tools.Nat
open import Tools.Nullary

¬prodrecₘ-Linearity : Prodrec-allowed 𝟙 𝟙 𝟘
                    → ¬ (∀ {n} {γ : Conₘ n} {η : Conₘ (1+ n)} {δ m r p q t u A}
                        → γ ▸[ m ᵐ· p ] t
                        → δ ∙ ⌜ m ⌝ · r  · p ∙ ⌜ m ⌝ · r ▸[ m ] u
                        → η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A
                        → Prodrec-allowed r p q
                        → r ·ᶜ γ +ᶜ δ ▸[ m ] prodrecₚ p t u)
¬prodrecₘ-Linearity ok = ¬prodrecₘ ok (λ ())
