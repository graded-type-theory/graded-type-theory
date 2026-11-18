------------------------------------------------------------------------
-- Some examples related to the linear or affine types modality with the
-- usage rule for natrec using greatest lower bounds.
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality.Instances.Linear-or-affine
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant linear-or-affine

module Graded.Modality.Instances.Linear-or-affine.Examples.Good.Greatest-lower-bound
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant)
  (C : Configuration Zero-one-isMode)
  where

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Configuration-types.Configuration.Zero-one
  linear-or-affine variant
open import Configuration-types.Natrec linear-or-affine

open import Graded.Modality Linear-or-affine

private

  module M = Modality linear-or-affine

  C′ = nr-not-available-glb linear-or-affine-supports-glb-for-natrec C
  open Configuration C′
  instance
    no-nr : Nr-not-available-GLB
    no-nr = No-nr-glb ⦃ linear-or-affine-supports-glb-for-natrec ⦄

open import Graded.Context linear-or-affine
open import Graded.Context.Properties linear-or-affine
import Graded.Derived.Nat C′ as N
import Graded.Derived.Sum C′ as S
open import Graded.Modality.Properties linear-or-affine
  hiding (nrᵢ-𝟘-GLB)
open import Graded.Usage C′
open import Graded.Usage.Inversion C′
open import Graded.Usage.Properties C′
open import Graded.Usage.Weakening C′

open import Definition.Untyped Linear-or-affine
open import Definition.Untyped.Nat linear-or-affine
open import Definition.Untyped.Sum TC

private variable
  n : Nat
  γ γ₁ γ₂ γ₃ γ₄ γ₅ δ δ₁ δ₂ η : Conₘ _
  t u A B t₁ t₂ t₃ P : Term _
  a b : Lvl _
  m : Mode
  p p₁ p₂ q : Linear-or-affine

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

------------------------------------------------------------------------
-- Usage rules for Sum, see also Graded.Derived.Sum

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
  ▸sumrec
    {m} {p₁} {p₂}
    ▸a ▸b ▸A ▸B ▸P ▸l ▸r ▸t p≤p₁ p≤p₂ p≢𝟘 ok₁ ok₂ ok₃ ok₄ ok₅ =
    S.▸sumrec ▸a ▸b ▸A ▸B ▸P ▸l ▸r (▸-cong (lemma₂ _ p≢𝟘) ▸t) p≤p₁ p≤p₂
      (lemma₁ _ p≢𝟘) ok₁ ok₂ ok₃ ok₄ ok₅
    where
    lemma₁ : ∀ p → p ≢ 𝟘 → ⌜ m ⌝ · p ≤ ⌜ m ⌝
    lemma₁ 𝟘 p≢𝟘 = ⊥-elim (p≢𝟘 refl)
    lemma₁ 𝟙 _ = ≤-reflexive (M.·-identityʳ _)
    lemma₁ ≤𝟙 _ = let open ≤-reasoning in begin
      ⌜ m ⌝ · ≤𝟙 ≤⟨ ·-monotoneʳ {p = ≤𝟙} {q = 𝟙} {r = ⌜ m ⌝} refl ⟩
      ⌜ m ⌝ · 𝟙  ≈⟨ M.·-identityʳ _ ⟩
      ⌜ m ⌝      ∎
    lemma₁ ≤ω _ = ·ω-decreasing
    lemma₂ : ∀ p → p ≢ 𝟘 → m ≡ m ᵐ· p
    lemma₂ 𝟘 p≢𝟘 = ⊥-elim (p≢𝟘 refl)
    lemma₂ 𝟙 _ = sym ᵐ·-identityʳ
    lemma₂ ≤𝟙 _ = sym (ᵐ·-identityʳ-≤𝟙 refl)
    lemma₂ ≤ω _ = sym (ᵐ·-identityʳ-≤𝟙 refl)
