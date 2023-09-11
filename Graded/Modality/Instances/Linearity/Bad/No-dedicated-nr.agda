------------------------------------------------------------------------
-- Some examples related to a "linearity" modality without a dedicated
-- nr function
------------------------------------------------------------------------

open import Tools.Bool using (T; T-not⇔¬-T)
open import Tools.Level
open import Tools.Nullary

open import Definition.Typed.Restrictions

import Graded.Modality.Instances.Linearity
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr
  -- The modality variant.
  (variant : Modality-variant)
  (open Modality-variant variant)
  -- There is no dedicated nr function.
  (not-available : ¬ Nr-available)
  -- The mode 𝟘ᵐ is not allowed.
  (not-ok : ¬ T 𝟘ᵐ-allowed)
  (open Graded.Modality.Instances.Linearity variant (λ _ → not-ok))
  (TR : Type-restrictions Linearity)
  (open Type-restrictions TR)
  (UR : Usage-restrictions Linearity)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  where

open import Tools.Empty
open import Tools.Function
open import Tools.Product
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

  -- A No-dedicated-nr instance.

  ¬-dedicated-nr : No-dedicated-nr
  ¬-dedicated-nr = no-dedicated-nr (T-not⇔¬-T .proj₂ not-available)

-- The term double is well-resourced (even though it can be given a
-- linear type).

▸double : ε ▸[ 𝟙ᵐ ] double
▸double =
  lamₘ $
  natrec-no-nrₘ var (sucₘ var) var
    (sub ℕₘ $ begin
       𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
       𝟘ᶜ                ∎)
    ≤ᶜ-refl
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
    (invUsageNatrec _ _ _ _ _ invUsageNatrecNr) →
       ⊥-elim not-nr-and-no-nr;
    (invUsageNatrec
       {δ = _ ∙ p ∙ _} {η = _ ∙ q ∙ _} {θ = _ ∙ r ∙ _} {χ = _ ∙ s ∙ _}
       ▸x0 _ _ _ (_ ∙ 𝟙≤s ∙ _)
       (invUsageNatrecNoNr (_ ∙ s≤p∧r∧[q+𝟘r+𝟙s] ∙ _))) →
  case inv-usage-var ▸x0 of λ {
    (_ ∙ p≤𝟘 ∙ _) →
  case begin
    𝟙                            ≤⟨ 𝟙≤s ⟩
    s                            ≤⟨ s≤p∧r∧[q+𝟘r+𝟙s] ⟩
    p ∧ r ∧ (q + 𝟘 · r + 𝟙 · s)  ≤⟨ ∧-decreasingˡ p _ ⟩
    p                            ≤⟨ p≤𝟘 ⟩
    𝟘                            ∎
  of λ () }}}}
  where
  open Tools.Reasoning.PartialOrder ≤-poset
