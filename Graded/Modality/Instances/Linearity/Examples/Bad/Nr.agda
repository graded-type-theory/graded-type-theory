------------------------------------------------------------------------
-- Some examples related to the linearity modality using a "bad" nr
-- function.
------------------------------------------------------------------------

open import Tools.Level

import Graded.Modality.Instances.Linearity
open import Graded.Modality.Variant lzero
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Linearity.Examples.Bad.Nr
  -- The modality variant.
  (variant : Modality-variant)
  (open Graded.Modality.Instances.Linearity variant)
  (UR : Usage-restrictions linearityModality)
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
open import Definition.Untyped.Nat linearityModality

open import Graded.Context linearityModality
open import Graded.Context.Properties linearityModality
open import Graded.Modality.Properties linearityModality
open import Graded.Mode linearityModality
open import Graded.Usage linearityModality UR′
open import Graded.Usage.Inversion linearityModality UR′
open import Graded.Usage.Properties linearityModality UR′

private variable
  γ δ : Conₘ _
  t u : Term _
  m : Mode
  n : Nat

private opaque

  -- A lemma used below

  ▸ℕ : 𝟘ᶜ {n = n} ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ▸[ 𝟘ᵐ? ] ℕ
  ▸ℕ = sub ℕₘ (≤ᶜ-reflexive (≈ᶜ-refl ∙ M.·-zeroʳ _))

opaque

  -- The term double is well-resourced (even though it can be given a
  -- linear type).

  ▸double : ε ▸[ 𝟙ᵐ ] double
  ▸double =
    lamₘ $
    natrecₘ var (sucₘ var) var ▸ℕ

opaque

  -- A usage rule for plus′

  ▸plus′ : γ ▸[ m ] t → δ ▸[ m ] u → γ ∧ᶜ δ ▸[ m ] plus′ t u
  ▸plus′ ▸t ▸u =
    sub (natrecₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} ▸t (sucₘ (sub-≈ᶜ var (≈ᶜ-refl ∙ M.·-zeroʳ _ ∙ M.·-identityʳ _)))
          ▸u ▸ℕ)
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
      p ∧ q                   ∎
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
