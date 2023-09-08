------------------------------------------------------------------------
-- Some examples related to the linear or affine types modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Dedicated-nr
open import Graded.Modality.Instances.Linear-or-affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linear-or-affine.Good
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Dedicated-nr (linear-or-affine variant))
  (TR : Type-restrictions Linear-or-affine)
  (open Type-restrictions TR)
  (UR : Usage-restrictions Linear-or-affine)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  -- There is a dedicated nr function.
  ⦃ has-nr : Dedicated-nr ⦄
  where

open import Tools.Empty
open import Tools.Function
open import Tools.Nullary
import Tools.Reasoning.PartialOrder

open import Graded.Modality Linear-or-affine

private

  -- The modality that is used in this file.

  linear-or-affine′ : Modality
  linear-or-affine′ = linear-or-affine variant

  module M = Modality linear-or-affine′

open import Graded.Context linear-or-affine′
open import Graded.Context.Properties linear-or-affine′
open import Graded.Modality.Instances.Examples
  linear-or-affine′ TR Π-𝟙-𝟘
open import Graded.Modality.Properties linear-or-affine′
open import Graded.Mode linear-or-affine′
open import Graded.Usage linear-or-affine′ UR
open import Graded.Usage.Inversion linear-or-affine′ UR

-- The term double is not well-resourced.

¬▸double : ¬ ε ▸[ 𝟙ᵐ ] double
¬▸double ▸λ+ =
  case inv-usage-lam ▸λ+ of λ {
    (invUsageLam {δ = ε} ▸+ ε) →
  case inv-usage-natrec ▸+ of λ {
    (invUsageNatrec _ _ _ _ _ (invUsageNatrecNoNr _ _ _ _)) →
       ⊥-elim not-nr-and-no-nr;
    (invUsageNatrec {δ = _ ∙ p} {η = _ ∙ q} {θ = _ ∙ r}
       ▸x0₁ _ ▸x0₂ _ (_ ∙ 𝟙≤nr) invUsageNatrecNr) →
  case inv-usage-var ▸x0₁ of λ {
    (_ ∙ p≤𝟙) →
  case inv-usage-var ▸x0₂ of λ {
    (_ ∙ r≤𝟙) →
  case begin
    𝟙                   ≤⟨ 𝟙≤nr ⟩
    𝟙 · r + ≤ω · q + p  ≤⟨ +-monotone (·-monotoneʳ {r = 𝟙} r≤𝟙) (+-monotoneʳ {r = ≤ω · q} p≤𝟙) ⟩
    𝟙 + ≤ω · q + 𝟙      ≡⟨ M.+-congˡ {x = 𝟙} (M.+-comm (≤ω · q) _) ⟩
    𝟙 + 𝟙 + ≤ω · q      ≡˘⟨ M.+-assoc 𝟙 𝟙 (≤ω · q) ⟩
    ≤ω + ≤ω · q         ≡⟨ +-zeroˡ (≤ω · q) ⟩
    ≤ω                  ∎
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
    𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ ⌜ 𝟘ᵐ? ⌝ ⟩
    𝟘ᶜ                ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
