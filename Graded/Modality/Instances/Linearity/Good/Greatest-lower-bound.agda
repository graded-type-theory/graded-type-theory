------------------------------------------------------------------------
-- Some examples related to the linearity modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Instances.Linearity
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linearity.Good.Greatest-lower-bound
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

  -- The usage rule for natrec with greatest lower bounds is used
  UR′ = nr-not-available-glb-UR zero-one-many-supports-glb-for-natrec UR
  open Usage-restrictions UR′
  instance
    no-nr : Nr-not-available-GLB
    no-nr = No-nr-glb ⦃ zero-one-many-supports-glb-for-natrec ⦄

open import Tools.Function
open import Tools.Nat using (1+)
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Graded.Context linearityModality
open import Graded.Context.Properties linearityModality
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Modality.Properties linearityModality
open import Graded.Mode linearityModality
open import Graded.Usage linearityModality UR′
open import Graded.Usage.Inversion linearityModality UR′

private

  opaque

    -- The greatest lower bound of nrᵢ 𝟙 𝟙 𝟘 is 𝟙.

    𝟙-GLB : M.Greatest-lower-bound 𝟙 (M.nrᵢ 𝟙 𝟙 𝟘)
    𝟙-GLB = ≤-reflexive ∘→ lemma , λ { 𝟘 q≤ → q≤ 0 ; 𝟙 q≤ → q≤ 0 ; ω q≤ → ≤-refl}
      where
      lemma : ∀ i → 𝟙 ≡ M.nrᵢ 𝟙 𝟙 𝟘 i
      lemma 0 = refl
      lemma (1+ i) rewrite sym (lemma i) = refl

opaque

  -- The term double is not well-resourced.

  ¬▸double : ¬ ε ▸[ 𝟙ᵐ ] double
  ¬▸double ▸λ+ =
    case inv-usage-lam ▸λ+ of λ {
      (invUsageLam {δ = ε} ▸+ ε) →
    case inv-usage-natrec-no-nr-glb ▸+ of λ {
      (_ ∙ p , _ ∙ q , _ ∙ r , _ ∙ _ , p′ , _ ∙ q′
             , ▸x0₁ , ▸sucx0₂ , ▸x0₃ , _ , _ ∙ 𝟙≤ , p′-GLB , q′-GLB′) →
    case inv-usage-var ▸x0₁ of λ {
      (_ ∙ p≤𝟙) →
    case inv-usage-var ▸x0₃ of λ {
      (_ ∙ r≤𝟙) →
    case inv-usage-suc ▸sucx0₂ of λ {
      (invUsageSuc {δ = _ ∙ _ ∙ _ ∙ _} ▸x0₂ (_ ∙ q≤q″ ∙ _ ∙ _)) →
    case inv-usage-var ▸x0₂ of λ {
      (_ ∙ q″≤𝟘 ∙ _ ∙ _) →
    let _ , q′-GLB = GLBᶜ-pointwise q′-GLB′
        q′≤𝟙 = GLB-monotone (λ i → nrᵢ-monotone i p≤𝟙 (≤-trans q≤q″ q″≤𝟘))
                 q′-GLB 𝟙-GLB
        p′≡𝟙 = GLB-unique p′-GLB 𝟙-GLB
    in case begin
      𝟙           ≤⟨ 𝟙≤ ⟩
      p′ · r + q′ ≤⟨ +-monotone (·-monotoneʳ r≤𝟙) q′≤𝟙 ⟩
      p′ · 𝟙 + 𝟙 ≡⟨ M.+-congʳ (M.·-congʳ p′≡𝟙) ⟩
      𝟙 · 𝟙 + 𝟙  ≡⟨⟩
      ω           ∎ of λ () }}}}}}
    where
    open Tools.Reasoning.PartialOrder ≤-poset


opaque

  -- The term plus is well-resourced.

  ▸plus : ε ▸[ 𝟙ᵐ ] plus
  ▸plus =
    lamₘ $
    lamₘ $
    natrec-no-nr-glbₘ var (sucₘ var) var
      (sub ℕₘ $ begin
       𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
       𝟘ᶜ                ∎)
      𝟙-GLB
      (GLBᶜ-pointwise′ (GLBᶜ-pointwise′ ε-GLB GLB-nrᵢ-𝟘) 𝟙-GLB)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
