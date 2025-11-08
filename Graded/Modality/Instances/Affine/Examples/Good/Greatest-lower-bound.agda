------------------------------------------------------------------------
-- Some examples related to the affine types modality with the usage
-- rule for natrec using greatest lower bounds.
------------------------------------------------------------------------

open import Graded.Modality.Instances.Affine
open import Graded.Usage.Restrictions
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant affineModality

module Graded.Modality.Instances.Affine.Examples.Good.Greatest-lower-bound
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant)
  (UR : Usage-restrictions affineModality Zero-one-isMode)
  where

open import Graded.Restrictions affineModality Zero-one-isMode
open import Graded.Usage.Restrictions.Natrec affineModality
open import Graded.Modality Affine
open import Graded.Mode Mode affineModality

private
  module M = Modality affineModality

  -- The usage rule for natrec with greatest lower bounds is used
  UR′ = nr-not-available-glb-UR zero-one-many-supports-glb-for-natrec UR
  open Usage-restrictions UR′
  instance
    no-nr : Nr-not-available-GLB
    no-nr = No-nr-glb ⦃ zero-one-many-supports-glb-for-natrec ⦄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Graded.Context affineModality
open import Graded.Context.Properties affineModality
import Graded.Derived.Nat UR′ as N
open import Graded.Modality.Properties affineModality
  hiding (nrᵢ-𝟘-GLB)
open import Graded.Mode Mode affineModality
open import Graded.Usage UR′
open import Graded.Usage.Inversion UR′
open import Graded.Usage.Properties UR′
open import Graded.Usage.Weakening UR′

open import Definition.Untyped Affine
open import Definition.Untyped.Nat affineModality
open import Definition.Typed.Restrictions affineModality


private variable
  n : Nat
  γ γ₁ γ₂ γ₃ γ₄ γ₅ δ δ₁ δ₂ η η₁ η₂ η₃ θ : Conₘ _
  a b A B k l h t t₁ t₂ t₃ u nl cs P xs : Term _
  m : Mode
  p p₁ p₂ p₃ p₄ q q₁ q₂ q₃ r r₁ r₂ : Affine

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

  open import Definition.Untyped.Vec
    affineModality Zero-one-isMode s p
  import Graded.Derived.Vec s p UR′ as ▸V

  opaque

    -- A usage rule for Vec′

    ▸Vec′ :
      γ ▸[ 𝟘ᵐ? ] l →
      δ ▸[ m ᵐ· p ] A →
      η ▸[ m ] k →
      η +ᶜ ω ·ᶜ p ·ᶜ δ ▸[ m ] Vec′ l A k
    ▸Vec′ {δ} {η} ▸l ▸A ▸k =
      sub-≈ᶜ (▸V.▸Vec′ ▸l ▸A ▸k nrᵢᶜ-𝟙-GLBᶜ) $ begin
        η +ᶜ ω ·ᶜ p ·ᶜ δ        ≈˘⟨ +ᶜ-congˡ (+ᶜ-identityˡ _) ⟩
        η +ᶜ 𝟘ᶜ +ᶜ ω ·ᶜ p ·ᶜ δ  ∎
      where
      open ≈ᶜ-reasoning

  opaque

    -- A usage rule for vecrec′

    ▸vecrec′ :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ · p ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · p₄ ▸[ m ] cs →
      δ₁ ▸[ m ] k →
      δ₂ ▸[ m ᵐ· r₂ ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m r₂ q₂ →
      Prodrec-allowed m r₂ p q₂ →
      M.Greatest-lower-bound r₂ (M.nrᵢ p₄ p₂ p₃) →
      nrᶜ ⦃ zero-one-many-has-nr ⦄ 𝟘 p₄ γ₁ γ₂ 𝟘ᶜ +ᶜ nr 𝟘 p₄ 𝟙 p₁ 𝟘 ·ᶜ δ₁ +ᶜ r₂ ·ᶜ δ₂
        ▸[ m ] vecrec′ p₁ p₄ r₂ q₁ q₂ l A P nl cs k xs
    ▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸l ▸A ▸P ok₁ ok₂ ok₃ =
       ▸V.▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸l ▸A ▸P (nr-nrᵢ-GLB _) ok₃
                    nrᶜ-nrᵢᶜ-GLBᶜ nrᵢᶜ-𝟙-GLBᶜ ok₁ ok₂

  opaque

    -- A usage rule for vecrec′ for erased recursive calls

    ▸vecrec′-𝟘 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ · p ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · 𝟘 ▸[ m ] cs →
      δ₁ ▸[ m ] k →
      δ₂ ▸[ m ᵐ· (p₂ ∧ p₃) ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (p₂ ∧ p₃) q₂ →
      Prodrec-allowed m (p₂ ∧ p₃) p q₂ →
      (γ₁ ∧ᶜ γ₂) +ᶜ (p₁ ∧ 𝟙) ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂
        ▸[ m ] vecrec′ p₁ 𝟘 (p₂ ∧ p₃) q₁ q₂ l A P nl cs k xs
    ▸vecrec′-𝟘
      {γ₁} {γ₂} {p₁} {p₂} {p₃} {δ₁} {δ₂}
      ▸nl ▸cs ▸k ▸xs ▸l ▸A ▸P ok₁ ok₂ =
      sub-≈ᶜ
        (▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸l ▸A ▸P ok₁ ok₂ (nrᵢ-𝟘-GLB _ _)) $
      begin
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
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (p₂ + ω · p₃) q₂ →
      Prodrec-allowed m (p₂ + ω · p₃) p q₂ →
      (γ₁ +ᶜ ω ·ᶜ γ₂) +ᶜ (𝟙 + ω · p₁) ·ᶜ δ₁ +ᶜ (p₂ + ω · p₃) ·ᶜ δ₂
        ▸[ m ] vecrec′ p₁ 𝟙 (p₂ + ω · p₃) q₁ q₂ l A P nl cs k xs
    ▸vecrec′-𝟙
      {γ₁} {γ₂} {p₁} {p₂} {p₃} {δ₁} {δ₂}
      ▸nl ▸cs ▸k ▸xs ▸l ▸A ▸P ok₁ ok₂ =
      sub-≈ᶜ
        (▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸l ▸A ▸P ok₁ ok₂ (nrᵢ-𝟙-GLB _ _)) $
      begin
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
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q₁ ∙ ⌜ 𝟘ᵐ? ⌝ · q₂ ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (ω · (p₂ + p₃)) q₂ →
      Prodrec-allowed m (ω · (p₂ + p₃)) p q₂ →
      ω ·ᶜ (γ₁ +ᶜ γ₂) +ᶜ ω ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂
        ▸[ m ] vecrec′ p₁ ω (ω · (p₂ + p₃)) q₁ q₂ l A P nl cs k xs
    ▸vecrec′-ω
      {γ₁} {γ₂} {p₁} {p₂} {p₃} {δ₁} {δ₂}
      ▸nl ▸cs ▸k ▸xs ▸l ▸A ▸P ok₁ ok₂ =
      sub-≈ᶜ
        (▸vecrec′ ▸nl ▸cs ▸k ▸xs ▸l ▸A ▸P ok₁ ok₂ (nrᵢ-ω-GLB _ _)) $
      begin
        ω ·ᶜ (γ₁ +ᶜ γ₂) +ᶜ ω ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂  ≈⟨ +ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-comm _ _)) ⟩

        ω ·ᶜ (γ₂ +ᶜ γ₁) +ᶜ ω ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂  ≈˘⟨ +ᶜ-cong (·ᶜ-congˡ (+ᶜ-identityˡ _)) (+ᶜ-congʳ (·ᶜ-congʳ (M.+-comm (ω · p₁) ω))) ⟩

        ω ·ᶜ (𝟘ᶜ +ᶜ γ₂ +ᶜ γ₁) +ᶜ
        (ω · p₁ + ω) ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂          ≈˘⟨ +ᶜ-cong nrᶜ-ω-≈ᶜ (+ᶜ-congʳ (·ᶜ-congʳ (M.·-distribˡ-+ ω p₁ 𝟙))) ⟩

        nrᶜ ⦃ zero-one-many-has-nr ⦄ 𝟘 ω γ₁ γ₂ 𝟘ᶜ +ᶜ
        nr 𝟘 ω 𝟙 p₁ 𝟘 ·ᶜ δ₁ +ᶜ (ω · (p₂ + p₃)) ·ᶜ δ₂         ∎
      where
      open ≈ᶜ-reasoning

------------------------------------------------------------------------
-- Usage rules for Lists, see also Graded.Derived.List

module List
  (pₕ pₗ : Affine)
  where

  open import Definition.Untyped.List
    affineModality Zero-one-isMode pₕ pₗ
  import Graded.Derived.List pₕ pₗ UR′ as ▸L

  opaque

    -- A usage rule for List

    ▸List :
      γ ▸[ 𝟘ᵐ? ] l →
      δ ▸[ m ᵐ· pₕ ] A →
      ω ·ᶜ pₕ ·ᶜ δ ▸[ m ] List l A
    ▸List {δ} ▸l ▸A = sub-≈ᶜ (▸L.▸List ▸l ▸A nrᵢᶜ-𝟙-GLBᶜ) $ begin
      ω ·ᶜ pₕ ·ᶜ δ       ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ ω ·ᶜ pₕ ·ᶜ δ ∎
      where
      open ≈ᶜ-reasoning

  opaque

    -- A usage rule for nil

    ▸nil : 𝟘ᶜ ▸[ m ] nil A
    ▸nil = ▸L.▸nil

  opaque

    -- A usage rule for cons

    ▸cons :
      γ ▸[ 𝟘ᵐ? ] l →
      δ ▸[ 𝟘ᵐ? ] A →
      η ▸[ m ᵐ· pₕ ] h →
      θ ▸[ m ] t →
      Prodrec-allowed m 𝟙 pₗ 𝟘 →
      pₕ ·ᶜ η +ᶜ θ ▸[ m ] cons l A h t
    ▸cons ▸l ▸A ▸h ▸t ok = ▸L.▸cons ▸l ▸A ▸h ▸t nrᵢᶜ-𝟙-GLBᶜ ok

  opaque

    -- A usage rule for listrec

    ▸listrec :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · p₃ ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      M.Greatest-lower-bound r₁ (M.nrᵢ p₃ 𝟙 (p₂ · pₗ)) →
      M.Greatest-lower-bound r₂ (M.nrᵢ p₃ p₁ p₂) →
      Greatest-lower-boundᶜ γ (nrᵢᶜ p₃ γ₁ γ₂) →
      r · pₗ ≤ r₁ →
      r ≤ r₂ →
      Unitrec-allowed m r₂ q →
      Prodrec-allowed m r₂ pₕ q →
      Prodrec-allowed m r pₗ q →
      r ·ᶜ δ +ᶜ γ ▸[ m ] listrec r r₂ p₂ p₃ q l A P nl cs xs
    ▸listrec
      ▸nl ▸cs ▸xs ▸l ▸A ▸P r₁-GLB r₂-GLB γ-GLB ≤r₁ ≤r₂ ok₁ ok₂ ok₃ =
      ▸L.▸listrec ▸nl ▸cs ▸xs ▸l ▸A ▸P r₁-GLB r₂-GLB γ-GLB nrᵢᶜ-𝟙-GLBᶜ
        ≤r₁ ≤r₂ ok₁ ok₂ ok₃

  opaque

    -- A usage rule for listrec for erased recursive calls

    ▸listrec-𝟘 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · 𝟘 ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      r · pₗ ≤ 𝟙 ∧ p₂ · pₗ →
      r ≤ p₁ ∧ p₂ →
      Unitrec-allowed m (p₁ ∧ p₂) q →
      Prodrec-allowed m (p₁ ∧ p₂) pₕ q →
      Prodrec-allowed m r pₗ q →
      r ·ᶜ δ +ᶜ (γ₁ ∧ᶜ γ₂) ▸[ m ]
        listrec r (p₁ ∧ p₂) p₂ 𝟘 q l A P nl cs xs
    ▸listrec-𝟘 ▸nl ▸cs ▸xs ▸l ▸A ▸P rpₗ≤ r≤ ok₁ ok₂ ok₃ =
      ▸listrec ▸nl ▸cs ▸xs ▸l ▸A ▸P (nrᵢ-𝟘-GLB _ _) (nrᵢ-𝟘-GLB _ _)
        nrᵢᶜ-𝟘-GLBᶜ rpₗ≤ r≤ ok₁ ok₂ ok₃

  opaque

    -- A usage rule for listrec for affine recursive calls

    ▸listrec-𝟙 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · 𝟙 ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      r · pₗ ≤ 𝟙 + ω · p₂ · pₗ →
      r ≤ p₁ + ω · p₂ →
      Unitrec-allowed m (p₁ + ω · p₂) q →
      Prodrec-allowed m (p₁ + ω · p₂) pₕ q →
      Prodrec-allowed m r pₗ q →
      r ·ᶜ δ +ᶜ γ₁ +ᶜ ω ·ᶜ γ₂ ▸[ m ]
        listrec r (p₁ + ω · p₂) p₂ 𝟙 q l A P nl cs xs
    ▸listrec-𝟙 ▸nl ▸cs ▸xs ▸l ▸A ▸P rpₗ≤ r≤ ok₁ ok₂ ok₃ =
      ▸listrec ▸nl ▸cs ▸xs ▸l ▸A ▸P (nrᵢ-𝟙-GLB _ _) (nrᵢ-𝟙-GLB _ _)
        nrᵢᶜ-𝟙-GLBᶜ rpₗ≤ r≤ ok₁ ok₂ ok₃

  opaque

    -- A usage rule for listrec for unrestricted recursive calls

    ▸listrec-ω :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · ω ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      r · pₗ ≤ ω →
      r ≤ ω · (p₁ + p₂) →
      Unitrec-allowed m (ω · (p₁ + p₂)) q →
      Prodrec-allowed m (ω · (p₁ + p₂)) pₕ q →
      Prodrec-allowed m r pₗ q →
      r ·ᶜ δ +ᶜ ω ·ᶜ (γ₁ +ᶜ γ₂) ▸[ m ]
        listrec r (ω · (p₁ + p₂)) p₂ ω q l A P nl cs xs
    ▸listrec-ω ▸nl ▸cs ▸xs ▸l ▸A ▸P rpₗ≤ r≤ ok₁ ok₂ ok₃ =
      ▸listrec ▸nl ▸cs ▸xs ▸l ▸A ▸P (nrᵢ-ω-GLB _ _) (nrᵢ-ω-GLB _ _)
        nrᵢᶜ-ω-GLBᶜ (≤-trans rpₗ≤ refl) r≤ ok₁ ok₂ ok₃

------------------------------------------------------------------------
-- Usage rules for Lists where the length of the list is given grade 𝟙
-- see also above and Graded.Derived.List

module List-pₗ≡𝟙
  (pₕ : Affine)
  where

  open import Definition.Untyped.List
    affineModality Zero-one-isMode pₕ 𝟙
  module ▸L = List pₕ 𝟙

  opaque

    -- A usage rule for listrec for erased recursive calls

    ▸listrec-𝟘 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · 𝟘 ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (p₁ ∧ p₂) q →
      Prodrec-allowed m (p₁ ∧ p₂) pₕ q →
      Prodrec-allowed m (𝟙 ∧ p₁ ∧ p₂) 𝟙 q →
      (𝟙 ∧ p₁ ∧ p₂) ·ᶜ δ +ᶜ (γ₁ ∧ᶜ γ₂) ▸[ m ]
        listrec (𝟙 ∧ p₁ ∧ p₂) (p₁ ∧ p₂) p₂ 𝟘 q l A P nl cs xs
    ▸listrec-𝟘 {p₁} {p₂} ▸nl ▸cs ▸xs ▸l ▸A ▸P ok₁ ok₂ ok₃ =
      ▸L.▸listrec-𝟘 ▸nl ▸cs ▸xs ▸l ▸A ▸P
        (begin
          (𝟙 ∧ p₁ ∧ p₂) · 𝟙 ≈⟨ M.·-identityʳ _ ⟩
          𝟙 ∧ p₁ ∧ p₂       ≤⟨ ∧-monotoneʳ {r = 𝟙} (∧-decreasingʳ p₁ p₂) ⟩
          𝟙 ∧ p₂            ≈˘⟨ M.∧-congˡ {x = 𝟙} (M.·-identityʳ p₂) ⟩
          𝟙 ∧ p₂ · 𝟙        ∎)
        (∧-decreasingʳ 𝟙 (p₁ ∧ p₂))
        ok₁ ok₂ ok₃
      where
      open Tools.Reasoning.PartialOrder ≤-poset

  opaque

    -- A usage rule for listrec for affine recursive calls
    -- Note that ω · p₂ + (𝟙 ∧ p₁) is 𝟙 iff p₂ is 𝟘 and p₁ is 𝟘 or 𝟙 and ω otherwise

    ▸listrec-𝟙 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · 𝟙 ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (p₁ + ω · p₂) q →
      Prodrec-allowed m (p₁ + ω · p₂) pₕ q →
      Prodrec-allowed m (ω · p₂ + (𝟙 ∧ p₁)) 𝟙 q →
      (ω · p₂ + (𝟙 ∧ p₁)) ·ᶜ δ +ᶜ γ₁ +ᶜ ω ·ᶜ γ₂ ▸[ m ]
        listrec (ω · p₂ + (𝟙 ∧ p₁)) (p₁ + ω · p₂) p₂ 𝟙 q l A P nl cs xs
    ▸listrec-𝟙 {p₁} {p₂} ▸nl ▸cs ▸xs ▸l ▸A ▸P ok₁ ok₂ ok₃ =
      ▸L.▸listrec-𝟙 ▸nl ▸cs ▸xs ▸l ▸A ▸P
        (begin
          (ω · p₂ + (𝟙 ∧ p₁)) · 𝟙 ≈⟨ M.·-identityʳ _ ⟩
          ω · p₂ + (𝟙 ∧ p₁)       ≤⟨ +-monotoneʳ (∧-decreasingˡ 𝟙 p₁) ⟩
          ω · p₂ + 𝟙              ≈⟨ M.+-comm _ 𝟙 ⟩
          𝟙 + ω · p₂              ≈˘⟨ M.+-congˡ (M.·-congˡ {x = ω} (M.·-identityʳ p₂)) ⟩
          𝟙 + ω · p₂ · 𝟙          ∎)
        (begin
          ω · p₂ + (𝟙 ∧ p₁) ≤⟨ +-monotoneʳ (∧-decreasingʳ 𝟙 p₁) ⟩
          ω · p₂ + p₁       ≈⟨ M.+-comm _ p₁ ⟩
          p₁ + ω · p₂       ∎)
        ok₁ ok₂ ok₃
      where
      open Tools.Reasoning.PartialOrder ≤-poset

  opaque

    -- A usage rule for listrec for unrestricted recursive calls

    ▸listrec-ω :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · ω ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] l →
      η₂ ▸[ 𝟘ᵐ? ] A →
      η₃ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (ω · (p₁ + p₂)) q →
      Prodrec-allowed m (ω · (p₁ + p₂)) pₕ q →
      Prodrec-allowed m ω 𝟙 q →
      ω ·ᶜ δ +ᶜ ω ·ᶜ (γ₁ +ᶜ γ₂) ▸[ m ]
        listrec ω (ω · (p₁ + p₂)) p₂ ω q l A P nl cs xs
    ▸listrec-ω {p₁} {p₂} ▸nl ▸cs ▸xs ▸l ▸A ▸P ok₁ ok₂ ok₃ =
      ▸L.▸listrec-ω ▸nl ▸cs ▸xs ▸l ▸A ▸P ≤-refl (ω≤ (p₁ + p₂))
        ok₁ ok₂ ok₃

------------------------------------------------------------------------
-- Usage rules for Sum, see also Graded.Derived.Sum

module Sum
  (TR : Type-restrictions)
  where

  open import Definition.Untyped.Sum TR
  import Graded.Derived.Sum TR UR′ as S

  opaque
    unfolding sumrec

    -- A usage lemma for sumrec
    -- The uses p of the scrutinee must be less than its uses of either
    -- branch but not 𝟘.

    ▸sumrec :
      γ₁ ▸[ 𝟘ᵐ? ] a →
      γ₂ ▸[ 𝟘ᵐ? ] b →
      γ₃ ▸[ 𝟘ᵐ? ] A →
      γ₄ ▸[ 𝟘ᵐ? ] B →
      γ₅ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      δ₁ ∙ ⌜ m ⌝ · p₁ ▸[ m ] t₁ →
      δ₂ ∙ ⌜ m ⌝ · p₂ ▸[ m ] t₂ →
      η ▸[ m ] t₃ →
      p ≤ p₁ →
      p ≤ p₂ →
      p ≢ 𝟘 →
      S.Sum-allowed 𝟘ᵐ? →
      Prodrec-allowed m p 𝟙 q →
      Prodrec-allowed m 𝟙 𝟙 (q + p) →
      Unitrec-allowed m 𝟙 (q + p) →
      Emptyrec-allowed m 𝟘 →
      p ·ᶜ η +ᶜ δ₁ ∧ᶜ δ₂ ▸[ m ] sumrec q p a b A B P t₁ t₂ t₃
    ▸sumrec {m} {p₁} {p₂} ▸a ▸b ▸A ▸B ▸P ▸l ▸r ▸t p≤p₁ p≤p₂ p≢𝟘 ok₁ ok₂ ok₃ ok₄ ok₅ =
      S.▸sumrec ▸a ▸b ▸A ▸B ▸P ▸l ▸r (▸-cong (lemma₂ _ p≢𝟘) ▸t) p≤p₁ p≤p₂ (lemma₁ _ p≢𝟘)
        ok₁ ok₂ ok₃ ok₄ ok₅
      where
      lemma₁ : ∀ p → p ≢ 𝟘 → ⌜ m ⌝ · p ≤ ⌜ m ⌝
      lemma₁ 𝟘 p≢𝟘 = ⊥-elim (p≢𝟘 refl)
      lemma₁ 𝟙 _ = ≤-reflexive (M.·-identityʳ _)
      lemma₁ ω _ = ·ω-decreasing
      lemma₂ : ∀ p → p ≢ 𝟘 → m ≡ m ᵐ· p
      lemma₂ 𝟘 p≢𝟘 = ⊥-elim (p≢𝟘 refl)
      lemma₂ 𝟙 _ = sym ᵐ·-identityʳ
      lemma₂ ω _ = sym (ᵐ·-identityʳ-≤𝟙 (ω≤ 𝟙))
