------------------------------------------------------------------------
-- Some examples related to the linear or affine types modality with the
-- usage rule for natrec using greatest lower bounds.
------------------------------------------------------------------------

open import Graded.Modality.Instances.Linear-or-affine
open import Graded.Usage.Restrictions
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant linear-or-affine

module Graded.Modality.Instances.Linear-or-affine.Examples.Good.Greatest-lower-bound
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant)
  (UR : Usage-restrictions linear-or-affine Zero-one-isMode)
  where

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Graded.Modality Linear-or-affine
open import Graded.Usage.Restrictions.Natrec linear-or-affine

private

  module M = Modality linear-or-affine

  open import Graded.Restrictions.Zero-one linear-or-affine variant

  UR′ = nr-not-available-glb-UR linear-or-affine-supports-glb-for-natrec UR
  open Usage-restrictions UR′
  instance
    no-nr : Nr-not-available-GLB
    no-nr = No-nr-glb ⦃ linear-or-affine-supports-glb-for-natrec ⦄

open import Graded.Context linear-or-affine
open import Graded.Context.Properties linear-or-affine
import Graded.Derived.Nat UR′ as N
open import Graded.Modality.Properties linear-or-affine
  hiding (nrᵢ-𝟘-GLB)
open import Graded.Usage UR′
open import Graded.Usage.Inversion UR′
open import Graded.Usage.Properties UR′
open import Graded.Usage.Weakening UR′

open import Definition.Untyped Linear-or-affine
open import Definition.Untyped.Nat linear-or-affine

private variable
  n : Nat
  γ δ η : Conₘ _
  t u : Term _
  m : Mode
  p : Linear-or-affine

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
                 q′-GLB nrᵢ-const-GLB₁
        p′≡𝟙 = GLB-unique p′-GLB nrᵢ-const-GLB₁
    in case begin
      𝟙           ≤⟨ 𝟙≤ ⟩
      p′ · r + q′ ≤⟨ +-monotone (·-monotoneʳ {r = p′} r≤𝟙) q′≤𝟙 ⟩
      p′ · 𝟙 + 𝟙 ≡⟨ M.+-congʳ (M.·-congʳ p′≡𝟙) ⟩
      𝟙 · 𝟙 + 𝟙  ≡⟨⟩
      ≤ω          ∎ of λ () }}}}}}
    where
    open Tools.Reasoning.PartialOrder ≤-poset


opaque

  -- A usage rule for plus′

  ▸plus′ :
    γ ▸[ m ] t → δ ▸[ m ] u →
    γ +ᶜ δ ▸[ m ] plus′ t u
  ▸plus′ = N.▸plus′₂

opaque

  -- The term plus is well-resourced.

  ▸plus : ε ▸[ 𝟙ᵐ ] plus
  ▸plus = N.▸plus

opaque

  -- A usage rule for f′.

  ▸f′ :
    γ ▸[ 𝟙ᵐ ] t →
    δ ▸[ 𝟙ᵐ ] u →
    γ +ᶜ δ ▸[ 𝟙ᵐ ] f′ t u
  ▸f′ = N.▸f′₂

opaque

  -- The term f is well-resourced.

  ▸f : ε ▸[ 𝟙ᵐ ] f
  ▸f = N.▸f

opaque

  -- A usage rule for pred′

  ▸pred′ :
    γ ▸[ m ] t →
    γ ▸[ m ] pred′ t
  ▸pred′ = N.▸pred′₂

opaque

  -- A usage rule for pred

  ▸pred : ε ▸[ 𝟙ᵐ ] pred
  ▸pred = N.▸pred
