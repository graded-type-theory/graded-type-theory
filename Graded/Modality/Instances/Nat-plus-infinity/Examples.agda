------------------------------------------------------------------------
-- Some examples related to the Nat-plus-infinity modality with the
-- usage rule for natrec using greatest lower bounds.
------------------------------------------------------------------------

import Graded.Modality.Instances.Nat-plus-infinity
open import Graded.Usage.Restrictions
import Graded.Mode.Instances.Zero-one
import Graded.Mode.Instances.Zero-one.Variant
open import Tools.Bool

module Graded.Modality.Instances.Nat-plus-infinity.Examples
  (total : Bool)
  (open Graded.Modality.Instances.Nat-plus-infinity total)
  (open Graded.Mode.Instances.Zero-one.Variant ℕ⊎∞-modality)
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant renaming (⌞_⌟ to ⌞_⌟′))
  (UR : Usage-restrictions ℕ⊎∞-modality Zero-one-isMode)
  where

open import Graded.Restrictions.Zero-one ℕ⊎∞-modality variant
open import Graded.Usage.Restrictions.Natrec ℕ⊎∞-modality
open import Graded.Modality ℕ⊎∞

private
  module M = Modality ℕ⊎∞-modality

  -- The usage rule for natrec with greatest lower bounds is used
  UR′ = nr-not-available-glb-UR ℕ⊎∞-supports-glb-for-natrec UR
  open Usage-restrictions UR′
  instance
    no-nr : Nr-not-available-GLB
    no-nr = No-nr-glb ⦃ ℕ⊎∞-supports-glb-for-natrec ⦄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Graded.Context ℕ⊎∞-modality
open import Graded.Context.Properties ℕ⊎∞-modality
open import Graded.Modality.Properties ℕ⊎∞-modality
open import Graded.Usage UR′
open import Graded.Usage.Inversion UR′

open import Definition.Untyped ℕ⊎∞
open import Definition.Typed.Restrictions ℕ⊎∞-modality

private variable
  γ : Conₘ _
  m : Mode
  q₁ q₂ q₃ : ℕ⊎∞

------------------------------------------------------------------------
-- Usage rules for Sum, see also Graded.Derived.Sum

module Sum
  (TR : Type-restrictions)
  where

  open import Definition.Untyped.Sum TR
  import Graded.Derived.Sum TR UR′ as S

  opaque
    unfolding sumrec

    -- A certain usage lemma for sumrec does not hold if the flat order is used
    -- C.f. e.g. Graded.Modality.Instances.Linearity.Examples.Good.Greatest-lower-bound.▸sumrec

    ¬▸sumrec :
      ¬ T total →
      ¬ (∀ {n} {a : Term n} {b A B P l r t m p p₁ p₂ q γ₁ γ₂ γ₃ γ₄ γ₅ δ₁ δ₂ η} →
        γ₁ ▸[ 𝟘ᵐ? ] a →
        γ₂ ▸[ 𝟘ᵐ? ] b →
        γ₃ ▸[ 𝟘ᵐ? ] A →
        γ₄ ▸[ 𝟘ᵐ? ] B →
        γ₅ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] P →
        δ₁ ∙ ⌜ m ⌝ · p₁ ▸[ m ] l →
        δ₂ ∙ ⌜ m ⌝ · p₂ ▸[ m ] r →
        η ▸[ m ] t →
        p ≤ p₁ →
        p ≤ p₂ →
        p ≢ M.𝟘 →
        p ·ᶜ η +ᶜ δ₁ ∧ᶜ δ₂ ▸[ m ] sumrec q p a b A B P l r t)
    ¬▸sumrec flat ▸sumrec =
      let lr : Term 1
          lr = prodʷ ⌞ 1 ⌟ (var x0) (var x0)
          t : Term 0
          t = sumrec ⌞ 0 ⌟ ⌞ 2 ⌟ zeroᵘ zeroᵘ ℕ ℕ (Σʷ ⌞ 1 ⌟ , ⌞ 0 ⌟ ▷ ℕ ▹ ℕ)
                 lr lr (inl zero)
          ▸lr : ε ∙ ⌜ 𝟙ᵐ ⌝ · ⌞ 2 ⌟ ▸[ 𝟙ᵐ ] lr
          ▸lr = sub (prodʷₘ var var) (ε ∙ (begin
            ⌜ 𝟙ᵐ ⌝ · ⌞ 2 ⌟                   ≡⟨⟩
            ⌞ 1 ⌟ · ⌜ 𝟙ᵐ ⌝ + ⌞ 1 ⌟           ≡˘⟨ M.+-congʳ (M.·-congˡ (⌜⌝-cong ⌞𝟙⌟)) ⟩
            ⌞ 1 ⌟ · ⌜ ⌞ ⌞ 1 ⌟ ⌟′ ⌝ + ⌞ 1 ⌟   ≡⟨⟩
            ⌞ 1 ⌟ · ⌜ 𝟙ᵐ ᵐ· ⌞ 1 ⌟ ⌝ + ⌜ 𝟙ᵐ ⌝ ∎))
          ▸P : ε ∙ ⌜ 𝟘ᵐ? ⌝ · ⌞ 0 ⌟ ▸[ 𝟘ᵐ? ] Σʷ ⌞ 1 ⌟ , ⌞ 0 ⌟ ▷ ℕ ▹ ℕ
          ▸P = sub (ΠΣₘ ℕₘ (sub-≈ᶜ ℕₘ (≈ᶜ-refl ∙ M.·-zeroʳ _))) (ε ∙ (begin
            ⌜ 𝟘ᵐ? ⌝ · ⌞ 0 ⌟       ≈⟨ M.·-zeroʳ _ ⟩
            ⌞ 0 ⌟                 ≈˘⟨ M.+-identityˡ _ ⟩
            ⌞ 0 ⌟ + ⌞ 0 ⌟         ≈˘⟨ M.+-congʳ (M.·-zeroʳ ⌞ 1 ⌟) ⟩
            ⌞ 1 ⌟ · ⌞ 0 ⌟ + ⌞ 0 ⌟ ∎))
          ▸t : ε ▸[ 𝟙ᵐ ] t
          ▸t = ▸sumrec {l = lr} {r = lr} {p₁ = ⌞ 2 ⌟} {p₂ = ⌞ 2 ⌟}
                 zeroᵘₘ zeroᵘₘ ℕₘ ℕₘ ▸P ▸lr ▸lr (S.▸inl zeroₘ) ≤-refl ≤-refl (λ ())
      in  case S.inv-usage-sumrec {l = lr} {r = lr} ▸t of λ {
            (_ , _ , _ , _ , _ , _ ∙ q₁ ∙ q₂ , _ ∙ q₃ ∙ q₄ , _ , _ , _ , _ , _ , _
               , ▸l , ▸r , _ , _ , _ , _ , _ , _ , _ , _ , _ , mp≤ , _) →
          2≰1 (begin
            ⌞ 2 ⌟                      ≡⟨⟩
            ⌜ 𝟙ᵐ ⌝ · ⌞ 2 ⌟             ≤⟨ mp≤ ⟩
            ⌜ 𝟙ᵐ ⌝ + (q₁ M.∧ q₃)       ≤⟨ +-monotoneʳ (∧-monotone (lemma ▸l) (lemma ▸r)) ⟩
            ⌜ 𝟙ᵐ ⌝ + (⌞ 0 ⌟ M.∧ ⌞ 0 ⌟) ≈⟨ M.+-congˡ (M.∧-idem _) ⟩
            ⌜ 𝟙ᵐ ⌝ + ⌞ 0 ⌟             ≡⟨⟩
            ⌞ 1 ⌟                      ∎)}
      where
      open ≤-reasoning
      lemma :
        γ ∙ q₁ ∙ q₂ ∙ q₃ ▸[ 𝟙ᵐ ] prodʷ ⌞ 1 ⌟ (lower (var x0)) (lower (var x0)) →
        q₁ ≤ ⌞ 0 ⌟
      lemma {q₁} ▸lr =
        case inv-usage-prodʷ ▸lr of λ {
          (invUsageProdʷ {δ = _ ∙ p₁ ∙ _ ∙ _} {η = _ ∙ p₂ ∙ _ ∙ _} ▸x0₁ ▸x0₂ (_ ∙ q₁≤ ∙ _ ∙ _)) →
        begin
          q₁              ≤⟨ q₁≤ ⟩
          ⌞ 1 ⌟ · p₁ + p₂ ≈⟨ M.+-congʳ (M.·-identityˡ _) ⟩
          p₁ + p₂         ≤⟨ +-monotone
                               (headₘ-monotone (tailₘ-monotone (tailₘ-monotone (inv-usage-var (inv-usage-lower ▸x0₁)))))
                               (headₘ-monotone (tailₘ-monotone (tailₘ-monotone (inv-usage-var (inv-usage-lower ▸x0₂))))) ⟩
          ⌞ 0 ⌟ + ⌞ 0 ⌟   ≈⟨ M.+-identityˡ _ ⟩
          ⌞ 0 ⌟           ∎}
      2≰1 : ¬ (⌞ 2 ⌟ ≤ ⌞ 1 ⌟)
      2≰1 = 2≰1′ _ refl
        where
        2≰1′ : ∀ b → b ≡ total → ⌞ 2 ⌟ ≡ (if b then ⌞ 2 ⌟ else ∞) → ⊥
        2≰1′ false _ ()
        2≰1′ true refl _ = flat _
