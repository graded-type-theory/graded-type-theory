------------------------------------------------------------------------
-- Some examples related to the "bad" linearity modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Dedicated-nr
import Graded.Modality.Instances.Linearity
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linearity.Bad
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Linearity variant)
  (open Graded.Modality.Dedicated-nr bad-linearity-modality)
  (TR : Type-restrictions bad-linearity-modality)
  (open Type-restrictions TR)
  (UR : Usage-restrictions bad-linearity-modality)
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

open import Graded.Context bad-linearity-modality
open import Graded.Context.Properties bad-linearity-modality
open import Graded.Modality Linearity
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Modality.Properties bad-linearity-modality
open import Graded.Mode bad-linearity-modality
open import Graded.Usage bad-linearity-modality UR
open import Graded.Usage.Inversion bad-linearity-modality UR

private
  module M = Modality bad-linearity-modality

-- The term double is well-resourced (even though it can be given a
-- linear type).

▸double : ε ▸[ 𝟙ᵐ ] double
▸double =
  lamₘ $
  natrecₘ var (sucₘ var) var $
  sub ℕₘ $ begin
    𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
    𝟘ᶜ                ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The term plus is not well-resourced.

¬▸plus : ¬ ε ▸[ 𝟙ᵐ ] plus
¬▸plus ▸λλ+ =
  case inv-usage-lam ▸λλ+ of λ {
    (invUsageLam ▸λ+ _) →
  case inv-usage-lam ▸λ+ of λ {
    (invUsageLam {δ = _ ∙ ω} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟘} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟙} ▸+ _) →
  case inv-usage-natrec ▸+ of λ {
    (invUsageNatrec _ _ _ _ _ (invUsageNatrecNoNr _ _ _ _)) →
       ⊥-elim not-nr-and-no-nr;
    (invUsageNatrec {δ = _ ∙ p ∙ _} {η = _ ∙ _ ∙ _} {θ = _ ∙ q ∙ _}
       ▸x0 _ _ _ (_ ∙ 𝟙≤nr ∙ _) invUsageNatrecNr) →
  case inv-usage-var ▸x0 of λ {
    (_ ∙ p≤𝟘 ∙ _) →
  case +≡𝟙 (𝟙-maximal idᶠ 𝟙≤nr) of λ {
    (inj₂ (_ , ω·≡𝟙)) →
      ω·≢𝟙 ω·≡𝟙;
    (inj₁ (p∧q≡𝟙 , _)) →
  case ∧≡𝟙 p∧q≡𝟙 of λ {
    (inj₁ (_ , _ , ()));
    (inj₂ (inj₁ (_ , _ , ())));
    (inj₂ (inj₂ (p≡𝟙 , _))) →
  case begin
    𝟙  ≡˘⟨ p≡𝟙 ⟩
    p  ≤⟨ p≤𝟘 ⟩
    𝟘  ∎
  of λ () }}}}}}
  where
  open Tools.Reasoning.PartialOrder ≤-poset
