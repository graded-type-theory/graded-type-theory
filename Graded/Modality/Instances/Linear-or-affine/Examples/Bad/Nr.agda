------------------------------------------------------------------------
-- Some examples related to the linear or affine types modality with a
-- "bad" nr function.
------------------------------------------------------------------------

open import Tools.Level

open import Graded.Modality.Instances.Linear-or-affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linear-or-affine.Examples.Bad.Nr
  -- The modality variant.
  (variant : Modality-variant)
  (UR : Usage-restrictions (linear-or-affine variant))
  where

open import Tools.Function
open import Tools.Product
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum

open import Graded.Modality Linear-or-affine
open import Graded.Restrictions (linear-or-affine variant)
open import Graded.Usage.Restrictions.Natrec (linear-or-affine variant)

private

  -- The modality that is used in this file.

  linear-or-affine′ : Modality
  linear-or-affine′ = linear-or-affine variant

  module M = Modality linear-or-affine′

  -- The "bad" nr function is used
  UR′ = nr-available-UR bad-linear-or-affine-has-nr UR
  open Usage-restrictions UR′
  instance
    has-nr : Nr-available
    has-nr = Natrec-mode-has-nr.Nr ⦃ bad-linear-or-affine-has-nr ⦄

open import Graded.Context linear-or-affine′
open import Graded.Context.Properties linear-or-affine′
open import Graded.Modality.Properties linear-or-affine′
open import Graded.Mode linear-or-affine′
open import Graded.Usage linear-or-affine′ UR′
open import Graded.Usage.Inversion linear-or-affine′ UR′

open import Definition.Untyped.Nat linear-or-affine′

opaque
  unfolding bad-linear-or-affine-has-nr

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

opaque
  unfolding bad-linear-or-affine-has-nr

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
    case inv-usage-natrec-has-nr ▸+ of λ {
      (_ ∙ p ∙ _ , _ ∙ q ∙ _ , _ ∙ r ∙ _ , _ , ▸x0 , _ , _ , _ , _ ∙ 𝟙≤nr ∙ _) →
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
