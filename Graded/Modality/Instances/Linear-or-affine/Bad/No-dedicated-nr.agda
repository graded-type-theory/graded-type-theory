------------------------------------------------------------------------
-- Some examples related to a "linear or affine types" modality
-- without a dedicated nr function
------------------------------------------------------------------------

open import Tools.Bool using (T; T-not⇔¬-T)
open import Tools.Level
open import Tools.Nullary

open import Definition.Typed.Restrictions

open import Graded.Modality.Instances.Linear-or-affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linear-or-affine.Bad.No-dedicated-nr
  -- The modality variant.
  (variant : Modality-variant)
  (open Modality-variant variant)
  (TR : Type-restrictions Linear-or-affine)
  (open Type-restrictions TR)
  (UR : Usage-restrictions Linear-or-affine)
  -- There is no dedicated nr function.
  (not-available : ¬ Nr-available)
  -- The mode 𝟘ᵐ is not allowed.
  (not-ok : ¬ T 𝟘ᵐ-allowed)
  -- It is assumed that "Π 𝟙 , 𝟘" is allowed.
  (Π-𝟙-𝟘 : Π-allowed 𝟙 𝟘)
  where

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.Reasoning.PartialOrder

open import Graded.Modality Linear-or-affine

private

  -- The modality that is used in this file.

  linear-or-affine′ : Modality
  linear-or-affine′ =
    linear-or-affine variant (λ _ → not-ok)

  module M = Modality linear-or-affine′

open import Graded.Context linear-or-affine′
open import Graded.Context.Properties linear-or-affine′
open import Graded.Modality Linear-or-affine
open import Graded.Modality.Instances.Examples
  linear-or-affine′ TR Π-𝟙-𝟘
open import Graded.Modality.Properties linear-or-affine′
open import Graded.Modality.Dedicated-nr linear-or-affine′
open import Graded.Mode linear-or-affine′
open import Graded.Usage linear-or-affine′ UR
open import Graded.Usage.Inversion linear-or-affine′ UR

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
       𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ ⌜ 𝟘ᵐ? ⌝ ⟩
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
    (invUsageLam {δ = _ ∙ ≤ω} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟘}  _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ ≤𝟙} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟙}  ▸+ _) →
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
