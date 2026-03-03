------------------------------------------------------------------------
-- Some examples related to a "linearity" modality without a dedicated
-- nr function
------------------------------------------------------------------------

open import Graded.Modality.Instances.Linearity
open import Graded.Usage.Restrictions
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant linearityModality

module Graded.Modality.Instances.Linearity.Examples.Bad.No-nr
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant)
  (UR : Usage-restrictions linearityModality Zero-one-isMode)
  (open Usage-restrictions UR)
  -- There is no dedicated nr function.
  ⦃ no-nr : Nr-not-available ⦄
  where

open Mode-variant variant

open import Tools.Bool using (T; T-not⇔¬-T)
open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.Reasoning.PartialOrder
open import Tools.Relation

open import Graded.Context linearityModality
open import Graded.Context.Properties linearityModality
open import Graded.Modality Linearity
open import Graded.Modality.Properties linearityModality
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties.Zero-one variant UR

open import Definition.Untyped.Nat linearityModality

private
  module M = Modality linearityModality

opaque

  -- The term double is well-resourced (even though it can be given a
  -- linear type) if and only if 𝟘ᵐ is not allowed.

  ▸double : (¬ T 𝟘ᵐ-allowed) ⇔ ε ▸[ 𝟙ᵐ ] double
  ▸double =
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
       λ not-ok →
         lamₘ $
         natrec-no-nrₘ₀₁ var (sucₘ var) var
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
         case inv-usage-natrec-no-nr₀₁ ▸+ of λ {
           (_ , _ ∙ q , _ , _ , _ ∙ p , _ , ▸suc , _
              , _ , (_ ∙ 𝟙≤p) , _ , p≤q , _ , _) →
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

opaque

  -- The term plus is not well-resourced.

  ¬▸plus : ¬ ε ▸[ 𝟙ᵐ ] plus
  ¬▸plus ▸λλ+ =
    case inv-usage-lam ▸λλ+ of λ {
      (invUsageLam ▸λ+ _) →
    case inv-usage-lam ▸λ+ of λ {
      (invUsageLam {δ = _ ∙ ω} _  (_ ∙ ()));
      (invUsageLam {δ = _ ∙ 𝟘} _  (_ ∙ ()));
      (invUsageLam {δ = _ ∙ 𝟙} ▸+ _) →
    case inv-usage-natrec-no-nr ▸+ of λ {
      (_ ∙ p ∙ _ , _ , _ , _ , _ ∙ s ∙ _ , ▸x0 , _ , _
                 , _ , (_ ∙ 𝟙≤s ∙ _) , (_ ∙ s≤p ∙ _) , _) →
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
