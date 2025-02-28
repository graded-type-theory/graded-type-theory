------------------------------------------------------------------------
-- Some examples related to the "bad" linearity modality
------------------------------------------------------------------------

open import Tools.Level

open import Definition.Typed.Restrictions

import Graded.Modality.Instances.Linearity
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linearity.Bad
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

  -- The "bad" nr function is used
  UR′ = nr-available-UR zero-one-many-greatest-star-nr UR
  open Usage-restrictions UR′
  instance
    has-nr : Nr-available
    has-nr = Natrec-mode-has-nr.Nr ⦃ zero-one-many-greatest-star-nr ⦄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open import Definition.Untyped Linearity

open import Graded.Context linearityModality
open import Graded.Context.Properties linearityModality
open import Graded.Modality.Instances.Examples TR Π-𝟙-𝟘
open import Graded.Modality.Properties linearityModality
open import Graded.Mode linearityModality
open import Graded.Usage linearityModality UR′
open import Graded.Usage.Inversion linearityModality UR′

private variable
  γ δ : Conₘ _
  t u : Term _
  m : Mode
  n : Nat

-- The term double is well-resourced (even though it can be given a
-- linear type).

▸double : ε ▸[ 𝟙ᵐ ] double
▸double =
  lamₘ $
  natrecₘ var (sucₘ var) var $
  sub ℕₘ $ begin
    𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ M.·-zeroʳ _ ⟩
    𝟘ᶜ                ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- A usage rule for plus′

  ▸plus′ : γ ▸[ m ] t → δ ▸[ m ] u → γ ∧ᶜ δ ▸[ m ] plus′ t u
  ▸plus′ ▸t ▸u =
    sub (natrecₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} ▸t (sucₘ (sub var (≤ᶜ-refl ∙ ≤-reflexive (M.·-zeroʳ _) ∙ ≤-reflexive (M.·-identityʳ _))))
          ▸u (sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (M.·-zeroʳ _))))
        (lemma _ _)
    where
    open Tools.Reasoning.PropositionalEquality
    lemma′ : ∀ p q → Has-nr.nr zero-one-many-greatest-star-nr 𝟘 𝟙 p 𝟘 q ≡ p ∧ q
    lemma′ p q = begin
      (p ∧ q) ⊛ 𝟘 + 𝟘 · q ▷ 𝟙 ≡⟨⟩
      p ∧ q + ω · (𝟘 + 𝟘 · q) ≡⟨⟩
      p ∧ q + ω · (𝟘 · q)     ≡⟨⟩
      p ∧ q + ω · 𝟘           ≡⟨⟩
      p ∧ q + 𝟘               ≡⟨ M.+-identityʳ _ ⟩
      p ∧ q ∎
    lemma : (γ δ : Conₘ n) → γ ∧ᶜ δ ≤ᶜ nrᶜ ⦃ zero-one-many-greatest-star-nr ⦄ 𝟘 𝟙 γ 𝟘ᶜ δ
    lemma ε ε = ε
    lemma (γ ∙ p) (δ ∙ q) =
      lemma γ δ ∙ ≤-reflexive (sym (lemma′ p q))

opaque

  -- Usage for plus′ applied to two different variables

  ▸plus′-x₀-x₁ : ε ∙ ω ∙ ω ▸[ 𝟙ᵐ ] plus′ (var x0) (var x1)
  ▸plus′-x₀-x₁ = ▸plus′ var var

opaque

  -- Usage for plus′ applied to the same variable twice

  ▸plus′-x₀-x₀ : ε ∙ 𝟙 ▸[ 𝟙ᵐ ] plus′ (var x0) (var x0)
  ▸plus′-x₀-x₀ = ▸plus′ var var

-- The term plus is not well-resourced.

¬▸plus : ¬ ε ▸[ 𝟙ᵐ ] plus
¬▸plus ▸λλ+ =
  case inv-usage-lam ▸λλ+ of λ {
    (invUsageLam ▸λ+ _) →
  case inv-usage-lam ▸λ+ of λ {
    (invUsageLam {δ = _ ∙ ω} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟘} _  (_ ∙ ()));
    (invUsageLam {δ = _ ∙ 𝟙} ▸+ _) →
  case inv-usage-natrec-has-nr ▸+ of λ {
    (_ ∙ p ∙ _ , _ ∙ _ ∙ _ , _ ∙ q ∙ _ , _
               , ▸x0 , _ , _ , _ , _ ∙ 𝟙≤nr ∙ _) →
  case inv-usage-var ▸x0 of λ {
    (_ ∙ p≤𝟘 ∙ _) →
  case +≡𝟙 (𝟙-maximal idᶠ 𝟙≤nr) of λ {
    (inj₂ (_ , ω·≡𝟙)) →
      ω·≢𝟙 ω·≡𝟙;
    (inj₁ (p∧q≡𝟙 , _)) →
  case ∧≡𝟙 p∧q≡𝟙 of λ {
    (inj₁ (_ , _ , ()));
    (inj₂ (inj₁ (_ , _ , ())));
    (inj₂ (inj₂ (p≡𝟙 , _))) →
  case begin
    𝟙  ≡˘⟨ p≡𝟙 ⟩
    p  ≤⟨ p≤𝟘 ⟩
    𝟘  ∎
  of λ () }}}}}}
  where
  open Tools.Reasoning.PartialOrder ≤-poset
