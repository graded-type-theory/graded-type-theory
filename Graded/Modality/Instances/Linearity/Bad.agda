------------------------------------------------------------------------
-- Some examples related to the "bad" linearity modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Instances.Linearity
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linearity.Bad
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Linearity variant)
  (TR : Type-restrictions linearityModality)
  (open Type-restrictions TR)
  (UR : Usage-restrictions linearityModality)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  where

open import Graded.Restrictions linearityModality
open import Graded.Usage.Restrictions.Natrec linearityModality
open import Graded.Modality Linearity

private
  module M = Modality linearityModality

  -- The "bad" nr function is used
  UR′ = nr-available-UR zero-one-many-greatest-star-nr UR
  open Usage-restrictions UR′
  instance
    has-nr : Nr-available
    has-nr = Natrec-mode-has-nr.Nr ⦃ zero-one-many-greatest-star-nr ⦄

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum

open import Graded.Context linearityModality
open import Graded.Context.Properties linearityModality
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Modality.Properties linearityModality
open import Graded.Mode linearityModality
open import Graded.Usage linearityModality UR′
open import Graded.Usage.Inversion linearityModality UR′

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
  case inv-usage-natrec-has-nr ▸+ of λ {
    (_ ∙ p ∙ _ , _ ∙ _ ∙ _ , _ ∙ q ∙ _ , _
               , ▸x0 , _ , _ , _ , _ ∙ 𝟙≤nr ∙ _) →
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
