------------------------------------------------------------------------
-- Some examples related to the linearity modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Instances.Linearity
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linearity.Good
  -- The modality variant.
  (variant : Modality-variant)
  (open Modality-variant variant)
  -- There is a dedicated nr function.
  (nr-available : Nr-available)
  (open Graded.Modality.Instances.Linearity variant
          (λ ¬-nr-available _ → ¬-nr-available nr-available))
  (TR : Type-restrictions Linearity)
  (open Type-restrictions TR)
  (UR : Usage-restrictions Linearity)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  where

open import Tools.Empty
open import Tools.Function
open import Tools.Nullary
import Tools.Reasoning.PartialOrder

open import Graded.Context linearityModality
open import Graded.Context.Properties linearityModality
open import Graded.Modality Linearity
open import Graded.Modality.Instances.Examples
  linearityModality TR Π-𝟙-𝟘
open import Graded.Modality.Properties linearityModality
open import Graded.Modality.Dedicated-nr linearityModality
open import Graded.Mode linearityModality
open import Graded.Usage linearityModality UR
open import Graded.Usage.Inversion linearityModality UR

private
  module M = Modality linearityModality

private instance

  -- A Dedicated-nr instance.

  has-dedicated-nr : Dedicated-nr
  has-dedicated-nr = dedicated-nr nr-available

-- The term double is not well-resourced.

¬▸double : ¬ ε ▸[ 𝟙ᵐ ] double
¬▸double ▸λ+ =
  case inv-usage-lam ▸λ+ of λ {
    (invUsageLam {δ = ε} ▸+ ε) →
  case inv-usage-natrec ▸+ of λ {
    (invUsageNatrec _ _ _ _ _ (invUsageNatrecNoNr _)) →
       ⊥-elim not-nr-and-no-nr;
    (invUsageNatrec {δ = _ ∙ p} {η = _ ∙ q} {θ = _ ∙ r}
       ▸x0₁ _ ▸x0₂ _ (_ ∙ 𝟙≤nr) invUsageNatrecNr) →
  case inv-usage-var ▸x0₁ of λ {
    (_ ∙ p≤𝟙) →
  case inv-usage-var ▸x0₂ of λ {
    (_ ∙ r≤𝟙) →
  case begin
    𝟙                  ≤⟨ 𝟙≤nr ⟩
    𝟙 · r + ω · q + p  ≤⟨ +-monotone (·-monotoneʳ {r = 𝟙} r≤𝟙) (+-monotoneʳ p≤𝟙) ⟩
    𝟙 + ω · q + 𝟙      ≡⟨ M.+-congˡ {x = 𝟙} (M.+-comm (ω · q) _) ⟩
    𝟙 + 𝟙 + ω · q      ≡˘⟨ M.+-assoc 𝟙 𝟙 (ω · q) ⟩
    ω                  ∎
  of λ () }}}}
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- The term plus is well-resourced.

▸plus : ε ▸[ 𝟙ᵐ ] plus
▸plus =
  lamₘ $
  lamₘ $
  natrecₘ var (sucₘ var) var $
  sub ℕₘ $ begin
    𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
    𝟘ᶜ                ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
