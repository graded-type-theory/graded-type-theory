------------------------------------------------------------------------
-- Some examples related to the "bad" linear or affine types modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Dedicated-nr
open import Graded.Modality.Instances.Linear-or-affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linear-or-affine.Bad
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Dedicated-nr (bad-linear-or-affine variant))
  (TR : Type-restrictions (bad-linear-or-affine variant))
  (open Type-restrictions TR)
  (UR : Usage-restrictions (bad-linear-or-affine variant))
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  -- There is a dedicated nr function.
  ⦃ has-nr : Dedicated-nr ⦄
  where

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum

open import Graded.Modality Linear-or-affine

private

  -- The modality that is used in this file.

  linear-or-affine′ : Modality
  linear-or-affine′ = bad-linear-or-affine variant

  module M = Modality linear-or-affine′

open import Graded.Context linear-or-affine′
open import Graded.Context.Properties linear-or-affine′
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Modality.Properties linear-or-affine′
open import Graded.Mode linear-or-affine′
open import Graded.Usage linear-or-affine′ UR
open import Graded.Usage.Inversion linear-or-affine′ UR

-- The term double is well-resourced (even though it can be given a
-- linear type).

▸double : ε ▸[ 𝟙ᵐ ] double
▸double =
  lamₘ $
  natrecₘ var (sucₘ var) var $
  sub ℕₘ $ begin
    𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ ⌜ 𝟘ᵐ? ⌝ ⟩
    𝟘ᶜ                ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The term plus is not well-resourced.

¬▸plus : ¬ ε ▸[ 𝟙ᵐ ] plus
¬▸plus ▸λλ+ =
  case inv-usage-lam ▸λλ+ of λ {
    (invUsageLam ▸λ+ _) →
  case inv-usage-lam ▸λ+ of λ {
    (invUsageLam {δ = _ ∙ ≤ω} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟘}  _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ ≤𝟙} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟙}  ▸+ _) →
  case inv-usage-natrec ▸+ of λ {
    (invUsageNatrec _ _ _ _ _ (invUsageNatrecNoNr _ _ _ _)) →
       ⊥-elim not-nr-and-no-nr;
    (invUsageNatrec {δ = _ ∙ p ∙ _} {η = _ ∙ q ∙ _} {θ = _ ∙ r ∙ _}
       ▸x0 _ _ _ (_ ∙ 𝟙≤nr ∙ _) invUsageNatrecNr) →
  case inv-usage-var ▸x0 of λ {
    (_ ∙ p≤𝟘 ∙ _) →
  case +≡𝟙 (𝟙-maximal 𝟙≤nr) of λ {
    (inj₂ (_ , ≤ω·≡𝟙)) →
      ≤ω·≢𝟙 (q + 𝟘) ≤ω·≡𝟙;
    (inj₁ (p∧r≡𝟙 , _)) →
  case ∧≡𝟙 p∧r≡𝟙 of λ {
    (p≡𝟙 , _) →
  case begin
    𝟙  ≡˘⟨ p≡𝟙 ⟩
    p  ≤⟨ p≤𝟘 ⟩
    𝟘  ∎
  of λ () }}}}}}
  where
  open Tools.Reasoning.PartialOrder ≤-poset
