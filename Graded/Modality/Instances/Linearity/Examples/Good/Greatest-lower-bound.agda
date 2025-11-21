------------------------------------------------------------------------
-- Some examples related to the linearity modality with the usage rule
-- for natrec using greatest lower bounds.
------------------------------------------------------------------------

open import Graded.Modality.Instances.Linearity
open import Graded.Usage.Restrictions
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant linearityModality

module Graded.Modality.Instances.Linearity.Examples.Good.Greatest-lower-bound
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant)
  (UR : Usage-restrictions linearityModality Zero-one-isMode)
  where

open import Graded.Restrictions.Zero-one linearityModality variant
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

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Graded.Context linearityModality
open import Graded.Context.Properties linearityModality
import Graded.Derived.Nat UR′ as N
open import Graded.Modality.Properties linearityModality
  hiding (nrᵢ-𝟘-GLB)
open import Graded.Usage UR′
open import Graded.Usage.Inversion UR′
open import Graded.Usage.Properties UR′
open import Graded.Usage.Weakening UR′

open import Definition.Untyped Linearity
open import Definition.Untyped.Nat linearityModality

private variable
  n : Nat
  l : Universe-level
  γ δ η γ₁ γ₂ δ₁ δ₂ η₁ η₂ : Conₘ _
  t u k h A P xs nl cs : Term _
  m : Mode
  p p₁ p₂ p₃ p₄ q q₁ q₂ r r₁ r₂ : Linearity

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
                 q′-GLB (nrᵢ-𝟙-GLB 𝟙 𝟘)
        p′≡𝟙 = GLB-unique p′-GLB (nrᵢ-𝟙-GLB 𝟙 𝟘)
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
  (p : Linearity)
  where

  open import Definition.Untyped.Vec linearityModality Zero-one-isMode s p
  import Graded.Derived.Vec s p UR′ as ▸V

  opaque

    -- A usage rule for Vec′

    ▸Vec′ :
      γ ▸[ m ] k →
      δ ▸[ m ] A →
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
        (ω ·ᶜ 𝟘ᶜ +ᶜ γ₂) ∧ᶜ (𝟘ᶜ +ᶜ γ₁) +ᶜ (p₁ ∧ 𝟙) ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂                  ≈˘⟨ +ᶜ-congʳ nrᶜ-𝟘-≈ᶜ ⟩
        nrᶜ ⦃ zero-one-many-has-nr ⦄ 𝟘 𝟘 γ₁ γ₂ 𝟘ᶜ +ᶜ nr 𝟘 𝟘 𝟙 p₁ 𝟘 ·ᶜ δ₁ +ᶜ (p₂ ∧ p₃) ·ᶜ δ₂ ∎
      where
      open ≈ᶜ-reasoning

  opaque

    -- A usage rule for vecrec′ for linear recursive calls

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

------------------------------------------------------------------------
-- Usage rules for Lists, see also Graded.Derived.List

module List
  (pₕ pₗ : Linearity)
  where

  open import Definition.Untyped.List linearityModality Zero-one-isMode pₕ pₗ
  import Graded.Derived.List pₕ pₗ UR′ as ▸L

  opaque

    -- A usage rule for List

    ▸List :
      γ ▸[ m ] A →
      ω ·ᶜ γ ▸[ m ] List l A
    ▸List {γ} ▸A = sub-≈ᶜ (▸L.▸List ▸A nrᵢᶜ-𝟙-GLBᶜ) $ begin
      ω ·ᶜ γ       ≈˘⟨ +ᶜ-identityˡ _ ⟩
      𝟘ᶜ +ᶜ ω ·ᶜ γ ∎
      where
      open ≈ᶜ-reasoning

  opaque

    -- A usage rule for nil

    ▸nil : 𝟘ᶜ ▸[ m ] nil l A
    ▸nil = ▸L.▸nil

  opaque

    -- A usage rule for cons

    ▸cons :
      γ ▸[ m ᵐ· pₕ ] h →
      δ ▸[ m ] t →
      η ▸[ 𝟘ᵐ? ] A →
      Prodrec-allowed m 𝟙 pₗ 𝟘 →
      pₕ ·ᶜ γ +ᶜ δ ▸[ m ] cons l A h t
    ▸cons ▸h ▸t ▸A ok = ▸L.▸cons ▸h ▸t ▸A nrᵢᶜ-𝟙-GLBᶜ ok

  opaque

    -- A usage rule for listrec

    ▸listrec :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · p₃ ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      M.Greatest-lower-bound r₁ (M.nrᵢ p₃ 𝟙 (p₂ · pₗ)) →
      M.Greatest-lower-bound r₂ (M.nrᵢ p₃ p₁ p₂) →
      Greatest-lower-boundᶜ γ (nrᵢᶜ p₃ γ₁ γ₂) →
      r · pₗ ≤ r₁ →
      r ≤ r₂ →
      Unitrec-allowed m r₂ q →
      Prodrec-allowed m r₂ pₕ q →
      Prodrec-allowed m r pₗ q →
      r ·ᶜ δ +ᶜ γ ▸[ m ] listrec l r r₂ p₂ p₃ q A P nl cs xs
    ▸listrec ▸nl ▸cs ▸xs ▸A ▸P r₁-GLB r₂-GLB γ-GLB ≤r₁ ≤r₂ ok₁ ok₂ ok₃ =
      ▸L.▸listrec ▸nl ▸cs ▸xs ▸A ▸P r₁-GLB r₂-GLB γ-GLB nrᵢᶜ-𝟙-GLBᶜ ≤r₁ ≤r₂ ok₁ ok₂ ok₃

  opaque

    -- A usage rule for listrec for erased recursive calls

    ▸listrec-𝟘 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · 𝟘 ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      r · pₗ ≤ 𝟙 ∧ p₂ · pₗ →
      r ≤ p₁ ∧ p₂ →
      Unitrec-allowed m (p₁ ∧ p₂) q →
      Prodrec-allowed m (p₁ ∧ p₂) pₕ q →
      Prodrec-allowed m r pₗ q →
      r ·ᶜ δ +ᶜ (γ₁ ∧ᶜ γ₂) ▸[ m ] listrec l r (p₁ ∧ p₂) p₂ 𝟘 q A P nl cs xs
    ▸listrec-𝟘 ▸nl ▸cs ▸xs ▸A ▸P rpₗ≤ r≤ ok₁ ok₂ ok₃ =
      ▸listrec ▸nl ▸cs ▸xs ▸A ▸P (nrᵢ-𝟘-GLB _ _) (nrᵢ-𝟘-GLB _ _)
        nrᵢᶜ-𝟘-GLBᶜ rpₗ≤ r≤ ok₁ ok₂ ok₃

  opaque

    -- A usage rule for listrec for linear recursive calls

    ▸listrec-𝟙 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · 𝟙 ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      r · pₗ ≤ 𝟙 + ω · p₂ · pₗ →
      r ≤ p₁ + ω · p₂ →
      Unitrec-allowed m (p₁ + ω · p₂) q →
      Prodrec-allowed m (p₁ + ω · p₂) pₕ q →
      Prodrec-allowed m r pₗ q →
      r ·ᶜ δ +ᶜ γ₁ +ᶜ ω ·ᶜ γ₂ ▸[ m ] listrec l r (p₁ + ω · p₂) p₂ 𝟙 q A P nl cs xs
    ▸listrec-𝟙 ▸nl ▸cs ▸xs ▸A ▸P rpₗ≤ r≤ ok₁ ok₂ ok₃ =
      ▸listrec ▸nl ▸cs ▸xs ▸A ▸P (nrᵢ-𝟙-GLB _ _) (nrᵢ-𝟙-GLB _ _)
        nrᵢᶜ-𝟙-GLBᶜ rpₗ≤ r≤ ok₁ ok₂ ok₃

  opaque

    -- A usage rule for listrec for unrestricted recursive calls

    ▸listrec-ω :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · ω ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      r · pₗ ≤ ω →
      r ≤ ω · (p₁ + p₂) →
      Unitrec-allowed m (ω · (p₁ + p₂)) q →
      Prodrec-allowed m (ω · (p₁ + p₂)) pₕ q →
      Prodrec-allowed m r pₗ q →
      r ·ᶜ δ +ᶜ ω ·ᶜ (γ₁ +ᶜ γ₂) ▸[ m ] listrec l r (ω · (p₁ + p₂)) p₂ ω q A P nl cs xs
    ▸listrec-ω ▸nl ▸cs ▸xs ▸A ▸P rpₗ≤ r≤ ok₁ ok₂ ok₃ =
      ▸listrec ▸nl ▸cs ▸xs ▸A ▸P (nrᵢ-ω-GLB _ _) (nrᵢ-ω-GLB _ _)
        nrᵢᶜ-ω-GLBᶜ (≤-trans rpₗ≤ refl) r≤ ok₁ ok₂ ok₃

------------------------------------------------------------------------
-- Usage rules for Lists where the length of the list is given grade 𝟙
-- see also above and Graded.Derived.List

module List-pₗ≡𝟙
  (pₕ : Linearity)
  where

  open import Definition.Untyped.List linearityModality Zero-one-isMode pₕ 𝟙
  module ▸L = List pₕ 𝟙

  opaque

    -- A usage rule for listrec for erased recursive calls

    ▸listrec-𝟘 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · 𝟘 ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (p₁ ∧ p₂) q →
      Prodrec-allowed m (p₁ ∧ p₂) pₕ q →
      Prodrec-allowed m (𝟙 ∧ p₁ ∧ p₂) 𝟙 q →
      (𝟙 ∧ p₁ ∧ p₂) ·ᶜ δ +ᶜ (γ₁ ∧ᶜ γ₂) ▸[ m ] listrec l (𝟙 ∧ p₁ ∧ p₂) (p₁ ∧ p₂) p₂ 𝟘 q A P nl cs xs
    ▸listrec-𝟘 {p₁} {p₂} ▸nl ▸cs ▸xs ▸A ▸P ok₁ ok₂ ok₃ =
      ▸L.▸listrec-𝟘 ▸nl ▸cs ▸xs ▸A ▸P
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

    -- A usage rule for listrec for linear recursive calls
    -- Note that ω · p₂ + (𝟙 ∧ p₁) is 𝟙 iff p₂ is 𝟘 and p₁ is 𝟙 and ω otherwise

    ▸listrec-𝟙 :
      γ₁ ▸[ m ] nl →
      γ₂ ∙ ⌜ m ⌝ · p₁ · pₕ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · 𝟙 ▸[ m ] cs →
      δ ▸[ m ] xs →
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (p₁ + ω · p₂) q →
      Prodrec-allowed m (p₁ + ω · p₂) pₕ q →
      Prodrec-allowed m (ω · p₂ + (𝟙 ∧ p₁)) 𝟙 q →
      (ω · p₂ + (𝟙 ∧ p₁)) ·ᶜ δ +ᶜ γ₁ +ᶜ ω ·ᶜ γ₂ ▸[ m ] listrec l (ω · p₂ + (𝟙 ∧ p₁)) (p₁ + ω · p₂) p₂ 𝟙 q A P nl cs xs
    ▸listrec-𝟙 {p₁} {p₂} ▸nl ▸cs ▸xs ▸A ▸P ok₁ ok₂ ok₃ =
      ▸L.▸listrec-𝟙 ▸nl ▸cs ▸xs ▸A ▸P
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
      η₁ ▸[ 𝟘ᵐ? ] A →
      η₂ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
      Unitrec-allowed m (ω · (p₁ + p₂)) q →
      Prodrec-allowed m (ω · (p₁ + p₂)) pₕ q →
      Prodrec-allowed m ω 𝟙 q →
      ω ·ᶜ δ +ᶜ ω ·ᶜ (γ₁ +ᶜ γ₂) ▸[ m ] listrec l ω (ω · (p₁ + p₂)) p₂ ω q A P nl cs xs
    ▸listrec-ω {p₁} {p₂} ▸nl ▸cs ▸xs ▸A ▸P ok₁ ok₂ ok₃ =
      ▸L.▸listrec-ω ▸nl ▸cs ▸xs ▸A ▸P ≤-refl (ω≤ (p₁ + p₂)) ok₁ ok₂ ok₃
