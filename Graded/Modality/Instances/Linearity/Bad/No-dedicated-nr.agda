------------------------------------------------------------------------
-- Some examples related to a "linearity" modality without a dedicated
-- nr function
------------------------------------------------------------------------

open import Tools.Bool using (T; T-not⇔¬-T)
open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Dedicated-nr
import Graded.Modality.Instances.Linearity
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linearity.Bad.No-dedicated-nr
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Linearity variant)
  (open Graded.Modality.Dedicated-nr linearityModality)
  (TR : Type-restrictions linearityModality)
  (open Type-restrictions TR)
  (UR : Usage-restrictions linearityModality)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  -- There is no dedicated nr function.
  ⦃ no-nr : No-dedicated-nr ⦄
  where

open Modality-variant variant

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.Reasoning.PartialOrder
open import Tools.Relation

open import Graded.Context linearityModality
open import Graded.Context.Properties linearityModality
open import Graded.Modality Linearity
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Modality.Properties linearityModality
open import Graded.Mode linearityModality
open import Graded.Usage linearityModality UR
open import Graded.Usage.Inversion linearityModality UR

private
  module M = Modality linearityModality

-- The term double is well-resourced (even though it can be given a
-- linear type) if and only if 𝟘ᵐ is not allowed.

▸double : (¬ T 𝟘ᵐ-allowed) ⇔ ε ▸[ 𝟙ᵐ ] double
▸double =
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
     λ not-ok →
       lamₘ $
       natrec-no-nrₘ var (sucₘ var) var
         (sub ℕₘ $ begin
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
            𝟘ᶜ                ∎)
         ≤ᶜ-refl
         (⊥-elim ∘→ not-ok)
         ≤ᶜ-refl
         ≤ᶜ-refl)
  , (let open Tools.Reasoning.PartialOrder ≤-poset in
     λ ▸λ+ ok →
       case inv-usage-lam ▸λ+ of λ {
         (invUsageLam ▸+ _) →
       case inv-usage-natrec ▸+ of λ {
         (invUsageNatrec _ _ _ _ _ invUsageNatrecNr) →
            ⊥-elim not-nr-and-no-nr;
         (invUsageNatrec {η = _ ∙ q} {χ = _ ∙ p}
            _ ▸suc _ _ (_ ∙ 𝟙≤p) (invUsageNatrecNoNr _ p≤q _ _)) →
       case p≤q ok of λ {
         (_ ∙ p≤q) →
       case inv-usage-suc ▸suc of λ {
         (invUsageSuc {δ = _ ∙ r ∙ _ ∙ _} ▸x0 (_ ∙ q≤r ∙ _ ∙ _)) →
       case inv-usage-var ▸x0 of λ {
         (_ ∙ r≤𝟘 ∙ _ ∙ _) →
       case begin
         𝟙  ≤⟨ 𝟙≤p ⟩
         p  ≤⟨ p≤q ⟩
         q  ≤⟨ q≤r ⟩
         r  ≤⟨ r≤𝟘 ⟩
         𝟘  ∎
       of λ () }}}}})

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
    (invUsageNatrec {δ = _ ∙ p ∙ _} {χ = _ ∙ s ∙ _}
       ▸x0 _ _ _ (_ ∙ 𝟙≤s ∙ _)
       (invUsageNatrecNoNr (_ ∙ s≤p ∙ _) _ _ _)) →
  case inv-usage-var ▸x0 of λ {
    (_ ∙ p≤𝟘 ∙ _) →
  case begin
    𝟙  ≤⟨ 𝟙≤s ⟩
    s  ≤⟨ s≤p ⟩
    p  ≤⟨ p≤𝟘 ⟩
    𝟘  ∎
  of λ () }}}}
  where
  open Tools.Reasoning.PartialOrder ≤-poset
