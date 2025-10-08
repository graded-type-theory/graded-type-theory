------------------------------------------------------------------------
-- Some examples related to the affine types modality with the usage
-- rule for natrec using greatest lower bounds.
------------------------------------------------------------------------

open import Tools.Level

import Graded.Modality.Instances.Affine
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Affine.Examples.Good.Greatest-lower-bound
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Affine variant)
  (UR : Usage-restrictions affineModality)
  where

open import Graded.Restrictions affineModality
open import Graded.Usage.Restrictions.Natrec affineModality
open import Graded.Modality Affine

private
  module M = Modality affineModality

  -- The usage rule for natrec with greatest lower bounds is used
  UR′ = nr-not-available-glb-UR zero-one-many-supports-glb-for-natrec UR
  open Usage-restrictions UR′
  instance
    no-nr : Nr-not-available-GLB
    no-nr = No-nr-glb ⦃ zero-one-many-supports-glb-for-natrec ⦄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Graded.Context affineModality
open import Graded.Context.Properties affineModality
import Graded.Derived.Nat affineModality UR′ as N
open import Graded.Modality.Properties affineModality
  hiding (nrᵢ-𝟘-GLB)
open import Graded.Mode affineModality
open import Graded.Usage affineModality UR′
open import Graded.Usage.Inversion affineModality UR′
open import Graded.Usage.Properties affineModality UR′
open import Graded.Usage.Weakening affineModality UR′

open import Definition.Untyped Affine
open import Definition.Untyped.Nat affineModality

private variable
  n : Nat
  l : Universe-level
  γ δ η γ₁ γ₂ δ₁ δ₂ η₁ η₂ : Conₘ _
  A k t u nl cs P xs : Term _
  m : Mode
  p p₁ p₂ p₃ p₄ q₁ q₂ q₃ r₁ r₂ : Affine

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
      p′ · r + q′ ≤⟨ +-monotone (·-monotoneʳ r≤𝟙) q′≤𝟙 ⟩
      p′ · 𝟙 + 𝟙 ≡⟨ M.+-congʳ (M.·-congʳ p′≡𝟙) ⟩
      𝟙 · 𝟙 + 𝟙  ≡⟨⟩
      ω           ∎ of λ () }}}}}}
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

------------------------------------------------------------------------
-- Usage rules for Vectors, see also Graded.Derived.Vec

module Vec
  (s : Strength)
  (p : Affine)
  where

  open import Definition.Untyped.Vec affineModality s p
  import Graded.Derived.Vec s p UR′ as ▸V

  opaque

    -- A usage rule for Vec′

    ▸Vec′ :
      γ ▸[ m ] k →
      δ ▸[ m ᵐ· p ] A →
      γ +ᶜ ω ·ᶜ δ ▸[ m ] Vec′ l A k
    ▸Vec′ {γ} {δ} ▸k ▸A =
      sub-≈ᶜ (▸V.▸Vec′ ▸k ▸A nrᵢᶜ-𝟙-GLBᶜ) $ begin
        γ +ᶜ ω ·ᶜ δ       ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityˡ _) ⟩
        γ +ᶜ 𝟘ᶜ +ᶜ ω ·ᶜ δ ∎
      where
      open ≈ᶜ-reasoning

  opaque

    -- A usage rule for vecrec′

    ▸vecrec′ :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ · p ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · p₄ ▸[ m ] cs →
      δ₁ ▸[ m ] k →
      δ₂ ▸[ m ᵐ· r₂ ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m r₂ q₂ →
      Prodrec-allowed m r₂ p q₂ →
      M.Greatest-lower-bound r₂ (M.nrᵢ p₄ p₂ p₃) →
      nrᶜ ⦃ zero-one-many-has-nr ⦄ 𝟘 p₄ γ₁ γ₂ 𝟘ᶜ +ᶜ nr 𝟘 p₄ 𝟙 p₁ 𝟘 ·ᶜ δ₁ +ᶜ r₂ ·ᶜ δ₂
        ▸[ m ] vecrec′ l p₁ p₄ r₂ q₁ q₂ A P nl cs k xs
    ▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸A ▸P ok₁ ok₂ ok₃ =
       ▸V.▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸A ▸P (nr-nrᵢ-GLB _) ok₃
                    nrᶜ-nrᵢᶜ-GLBᶜ nrᵢᶜ-𝟙-GLBᶜ ok₁ ok₂

  opaque

    -- A usage rule for vecrec′ for erased recursive calls

    ▸vecrec′-𝟘 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ · p ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · 𝟘 ▸[ m ] cs →
      δ₁ ▸[ m ] k →
      δ₂ ▸[ m ᵐ· (p₂ ∧ p₃) ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (p₂ ∧ p₃) q₂ →
      Prodrec-allowed m (p₂ ∧ p₃) p q₂ →
      (γ₁ ∧ᶜ γ₂) +ᶜ (p₁ ∧ 𝟙) ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂
        ▸[ m ] vecrec′ l p₁ 𝟘 (p₂ ∧ p₃) q₁ q₂ A P nl cs k xs
    ▸vecrec′-𝟘 {γ₁} {γ₂} {p₁} {p₂} {p₃} {δ₁} {δ₂} ▸nl ▸cs ▸k ▸xs ▸A ▸P ok₁ ok₂ =
      sub-≈ᶜ (▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸A ▸P ok₁ ok₂ (nrᵢ-𝟘-GLB _ _)) $ begin
        γ₁ ∧ᶜ γ₂ +ᶜ (p₁ ∧ 𝟙) ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂                                       ≈⟨ +ᶜ-congʳ (∧ᶜ-comm _ _) ⟩
        γ₂ ∧ᶜ γ₁ +ᶜ (p₁ ∧ 𝟙) ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂                                       ≈˘⟨ +ᶜ-congʳ (∧ᶜ-congʳ (+ᶜ-identityˡ _)) ⟩
        (𝟘ᶜ +ᶜ γ₂) ∧ᶜ γ₁ +ᶜ (p₁ ∧ 𝟙) ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂                               ≈˘⟨ +ᶜ-congʳ (∧ᶜ-cong (+ᶜ-congʳ (·ᶜ-zeroʳ _)) (+ᶜ-identityˡ _)) ⟩
        (𝟙 ·ᶜ 𝟘ᶜ +ᶜ γ₂) ∧ᶜ (𝟘ᶜ +ᶜ γ₁) +ᶜ (p₁ ∧ 𝟙) ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂                  ≈˘⟨ +ᶜ-congʳ nrᶜ-𝟘-≈ᶜ ⟩
        nrᶜ ⦃ zero-one-many-has-nr ⦄ 𝟘 𝟘 γ₁ γ₂ 𝟘ᶜ +ᶜ nr 𝟘 𝟘 𝟙 p₁ 𝟘 ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂ ∎
      where
      open ≈ᶜ-reasoning

  opaque

    -- A usage rule for vecrec′ for affine recursive calls

    ▸vecrec′-𝟙 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ · p ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · 𝟙 ▸[ m ] cs →
      δ₁ ▸[ m ] k →
      δ₂ ▸[ m ᵐ· (p₂ + ω · p₃) ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (p₂ + ω · p₃) q₂ →
      Prodrec-allowed m (p₂ + ω · p₃) p q₂ →
      (γ₁ +ᶜ ω ·ᶜ γ₂) +ᶜ (𝟙 + ω · p₁) ·ᶜ δ₁ +ᶜ (p₂ + ω · p₃) ·ᶜ δ₂
        ▸[ m ] vecrec′ l p₁ 𝟙 (p₂ + ω · p₃) q₁ q₂ A P nl cs k xs
    ▸vecrec′-𝟙 {γ₁} {γ₂} {p₁} {p₂} {p₃} {δ₁} {δ₂} ▸nl ▸cs ▸k ▸xs ▸A ▸P ok₁ ok₂ =
      sub-≈ᶜ (▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸A ▸P ok₁ ok₂ (nrᵢ-𝟙-GLB _ _)) $ begin
        (γ₁ +ᶜ ω ·ᶜ γ₂) +ᶜ (𝟙 + ω · p₁) ·ᶜ δ₁ +ᶜ (p₂ + ω · p₃) ·ᶜ δ₂                             ≈⟨ +ᶜ-congʳ (+ᶜ-comm _ _) ⟩
        (ω ·ᶜ γ₂ +ᶜ γ₁) +ᶜ (𝟙 + ω · p₁) ·ᶜ δ₁ +ᶜ (p₂ + ω · p₃) ·ᶜ δ₂                             ≈˘⟨ +ᶜ-congʳ (+ᶜ-identityˡ _) ⟩
        (𝟘ᶜ +ᶜ ω ·ᶜ γ₂ +ᶜ γ₁) +ᶜ (𝟙 + ω · p₁) ·ᶜ δ₁ +ᶜ (p₂ + ω · p₃) ·ᶜ δ₂                       ≈˘⟨ +ᶜ-congʳ (+ᶜ-congʳ (·ᶜ-zeroʳ _)) ⟩
        (𝟙 ·ᶜ 𝟘ᶜ +ᶜ ω ·ᶜ γ₂ +ᶜ γ₁) +ᶜ (𝟙 + ω · p₁) ·ᶜ δ₁ +ᶜ (p₂ + ω · p₃) ·ᶜ δ₂                  ≈˘⟨ +ᶜ-cong nrᶜ-𝟙-≈ᶜ (+ᶜ-congʳ (·ᶜ-congʳ (M.+-comm (ω · p₁) 𝟙))) ⟩
         nrᶜ ⦃ zero-one-many-has-nr ⦄ 𝟘 𝟙 γ₁ γ₂ 𝟘ᶜ +ᶜ nr 𝟘 𝟙 𝟙 p₁ 𝟘 ·ᶜ δ₁ +ᶜ (p₂ + ω · p₃) ·ᶜ δ₂ ∎
      where
      open ≈ᶜ-reasoning

  opaque

    -- A usage rule for vecrec′ for unrestricted recursive calls

    ▸vecrec′-ω :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ · p ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · ω ▸[ m ] cs →
      δ₁ ▸[ m ] k →
      δ₂ ▸[ m ᵐ· (ω · (p₂ + p₃)) ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (ω · (p₂ + p₃)) q₂ →
      Prodrec-allowed m (ω · (p₂ + p₃)) p q₂ →
      ω ·ᶜ (γ₁ +ᶜ γ₂) +ᶜ ω ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂
        ▸[ m ] vecrec′ l p₁ ω (ω · (p₂ + p₃)) q₁ q₂ A P nl cs k xs
    ▸vecrec′-ω {γ₁} {γ₂} {p₁} {p₂} {p₃} {δ₁} {δ₂} ▸nl ▸cs ▸k ▸xs ▸A ▸P ok₁ ok₂ =
      sub-≈ᶜ (▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸A ▸P ok₁ ok₂ (nrᵢ-ω-GLB _ _)) $ begin
      ω ·ᶜ (γ₁ +ᶜ γ₂) +ᶜ ω ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂                                       ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-comm _ _)) ⟩
      ω ·ᶜ (γ₂ +ᶜ γ₁) +ᶜ ω ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂                                       ≈˘⟨ +ᶜ-cong (·ᶜ-congˡ (+ᶜ-identityˡ _)) (+ᶜ-congʳ (·ᶜ-congʳ (M.+-comm (ω · p₁) ω))) ⟩
      ω ·ᶜ (𝟘ᶜ +ᶜ γ₂ +ᶜ γ₁) +ᶜ (ω · p₁ + ω) ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂                      ≈˘⟨ +ᶜ-cong nrᶜ-ω-≈ᶜ (+ᶜ-congʳ (·ᶜ-congʳ (M.·-distribˡ-+ ω p₁ 𝟙))) ⟩
      nrᶜ ⦃ zero-one-many-has-nr ⦄ 𝟘 ω γ₁ γ₂ 𝟘ᶜ +ᶜ nr 𝟘 ω 𝟙 p₁ 𝟘 ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂ ∎
      where
      open ≈ᶜ-reasoning
