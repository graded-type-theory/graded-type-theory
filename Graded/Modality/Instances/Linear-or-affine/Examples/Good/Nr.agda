------------------------------------------------------------------------
-- Some examples related to the linear or affine types modality with a
-- "good" nr function.
------------------------------------------------------------------------

open import Tools.Level

open import Configuration-types

open import Graded.Modality.Instances.Linear-or-affine
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant linear-or-affine

module Graded.Modality.Instances.Linear-or-affine.Examples.Good.Nr
  {variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one variant)
  (C : Configuration Zero-one-isMode)
  where

open import Tools.Function
open import Tools.Nat using (Nat)
import Tools.Reasoning.PartialOrder
open import Tools.Product
open import Tools.Relation

open import Configuration-types.Configuration.Zero-one
  linear-or-affine variant
open import Configuration-types.Natrec linear-or-affine

open import Graded.Modality Linear-or-affine

private

  module M = Modality linear-or-affine

  -- The nr function is used
  C′ = nr-available linear-or-affine-has-nr C
  open Configuration C′
  instance
    has-nr : Nr-available
    has-nr = Natrec-mode-has-nr.Nr ⦃ linear-or-affine-has-nr ⦄

open import Graded.Context linear-or-affine
open import Graded.Context.Properties linear-or-affine
open import Graded.Modality.Properties linear-or-affine
open import Graded.Usage C′
open import Graded.Usage.Inversion C′
open import Graded.Usage.Properties C′
open import Graded.Usage.Weakening C′

open import Definition.Untyped Linear-or-affine
open import Definition.Untyped.Nat linear-or-affine

private variable
  n   : Nat
  γ δ : Conₘ _
  m   : Mode
  t u : Term _

private opaque

  -- A lemma used below

  ▸ℕ : 𝟘ᶜ {n = n} ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ▸[ 𝟘ᵐ? ] ℕ
  ▸ℕ = sub-≈ᶜ ℕₘ (≈ᶜ-refl ∙ M.·-zeroʳ ⌜ 𝟘ᵐ? ⌝)

opaque

  -- The term double is not well-resourced.

  ¬▸double : ¬ ε ▸[ 𝟙ᵐ ] double
  ¬▸double ▸λ+ =
    case inv-usage-lam ▸λ+ of λ {
      (invUsageLam {δ = ε} ▸+ ε) →
    case inv-usage-natrec-has-nr ▸+ of λ {
      (_ ∙ p , _ ∙ q , _ ∙ r , _ , ▸x0₁ , _ , ▸x0₂ , _ , _ ∙ 𝟙≤nr) →
    case inv-usage-var ▸x0₁ of λ {
      (_ ∙ p≤𝟙) →
    case inv-usage-var ▸x0₂ of λ {
      (_ ∙ r≤𝟙) →
    case begin
      𝟙                   ≤⟨ 𝟙≤nr ⟩
      𝟙 · r + ≤ω · q + p  ≤⟨ +-monotone (·-monotoneʳ {r = 𝟙} r≤𝟙) (+-monotoneʳ {r = ≤ω · q} p≤𝟙) ⟩
      𝟙 + ≤ω · q + 𝟙      ≡⟨ M.+-congˡ {x = 𝟙} (M.+-comm (≤ω · q) _) ⟩
      𝟙 + 𝟙 + ≤ω · q      ≡˘⟨ M.+-assoc 𝟙 𝟙 (≤ω · q) ⟩
      ≤ω + ≤ω · q         ≡⟨ +-zeroˡ (≤ω · q) ⟩
      ≤ω                  ∎
    of λ () }}}}
    where
    open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- A usage rule for plus′.

  ▸plus′ : γ ▸[ m ] t → δ ▸[ m ] u → γ +ᶜ δ ▸[ m ] plus′ t u
  ▸plus′ {m} ▸t ▸u =
    sub (natrecₘ {δ = 𝟘ᶜ} ▸t
          (sub-≈ᶜ (sucₘ var) (≈ᶜ-refl ∙ M.·-zeroʳ ⌜ m ⌝ ∙ M.·-identityʳ _))
          ▸u ▸ℕ)
        (lemma _ _)
    where
    open Tools.Reasoning.PartialOrder ≤-poset
    lemma′ : ∀ p q → p + q ≤ Has-nr.nr linear-or-affine-has-nr 𝟘 𝟙 p 𝟘 q
    lemma′ p q = begin
      p + q                                       ≈⟨ M.+-comm p q ⟩
      q + p                                       ≡⟨⟩
      q + 𝟘 + p                                   ≈˘⟨ M.+-congʳ (M.·-identityˡ q) ⟩
      𝟙 · q + ≤ω · 𝟘 + p                          ≡⟨⟩
      Has-nr.nr linear-or-affine-has-nr 𝟘 𝟙 p 𝟘 q ∎
    lemma : (γ δ : Conₘ n) → γ +ᶜ δ ≤ᶜ nrᶜ ⦃ has-nr = linear-or-affine-has-nr ⦄ 𝟘 𝟙 γ 𝟘ᶜ δ
    lemma ε ε = ε
    lemma (γ ∙ p) (δ ∙ q) = lemma γ δ ∙ lemma′ p q

opaque

  -- The term plus is well-resourced.

  ▸plus : ε ▸[ 𝟙ᵐ ] plus
  ▸plus =
    lamₘ $
    lamₘ $
    ▸plus′ var var

opaque
  unfolding f′

  -- A usage rule for f′.

  ▸f′ : γ ▸[ m ] t → δ ▸[ m ] u → γ +ᶜ δ ▸[ m ] f′ t u
  ▸f′ {γ} {m} ▸t ▸u =
    sub (natrecₘ {δ = γ +ᶜ 𝟘ᶜ} ▸t
          (▸plus′ (wkUsage (step (step id)) ▸t)
            (sub-≈ᶜ var (≈ᶜ-refl ∙ M.·-identityʳ _ ∙ M.·-zeroʳ ⌜ m ⌝)))
          ▸u ▸ℕ)
        (lemma _ _)
    where
    open Tools.Reasoning.PartialOrder ≤-poset
    lemma′ : ∀ p q → p + q ≤ Has-nr.nr linear-or-affine-has-nr 𝟙 𝟘 p (p + 𝟘) q
    lemma′ p q = begin
      p + q                                             ≡⟨ M.+-comm p q ⟩
      q + p                                             ≡˘⟨ M.∧-idem _ ⟩
      (q + p) ∧ (q + p)                                 ≡˘⟨ M.∧-congʳ (M.+-cong (M.·-identityˡ q) (M.+-identityʳ p)) ⟩
      (𝟙 · q + p + 𝟘) ∧ (q + p)                         ≡⟨⟩
      Has-nr.nr linear-or-affine-has-nr 𝟙 𝟘 p (p + 𝟘) q ∎
    lemma : (γ δ : Conₘ n) → γ +ᶜ δ ≤ᶜ nrᶜ ⦃ has-nr = linear-or-affine-has-nr ⦄ 𝟙 𝟘 γ (γ +ᶜ 𝟘ᶜ) δ
    lemma ε ε = ε
    lemma (γ ∙ p) (δ ∙ q) = lemma γ δ ∙ lemma′ p q

opaque
  unfolding f

  -- The term f is well-resourced.

  ▸f : ε ▸[ 𝟙ᵐ ] f
  ▸f = lamₘ $ lamₘ $ ▸f′ var var

opaque

  -- A usage rule for pred′.

  ▸pred′ : γ ▸[ m ] t → γ ▸[ m ] pred′ t
  ▸pred′ {m} ▸t =
    sub (natrecₘ {δ = 𝟘ᶜ} zeroₘ
      (sub-≈ᶜ var (≈ᶜ-refl ∙ M.·-identityʳ _ ∙ M.·-zeroʳ ⌜ m ⌝))
      ▸t ▸ℕ)
      (lemma _)
    where
    open Tools.Reasoning.PartialOrder ≤-poset
    lemma′ : ∀ p → p ≤ Has-nr.nr linear-or-affine-has-nr 𝟙 𝟘 𝟘 𝟘 p
    lemma′ p = begin
      p                                        ≈˘⟨ M.+-identityʳ _ ⟩
      p + 𝟘                                    ≈˘⟨ M.∧-idem _ ⟩
      (p + 𝟘) ∧ (p + 𝟘)                        ≈˘⟨ M.∧-congʳ (M.+-congʳ (M.·-identityˡ p)) ⟩
      (𝟙 · p + 𝟘) ∧ (p + 𝟘)                    ≡⟨⟩
      Has-nr.nr linear-or-affine-has-nr 𝟙 𝟘 𝟘 𝟘 p ∎
    lemma : (γ : Conₘ n) → γ ≤ᶜ nrᶜ ⦃ has-nr = linear-or-affine-has-nr ⦄ 𝟙 𝟘 𝟘ᶜ 𝟘ᶜ γ
    lemma ε = ε
    lemma (γ ∙ p) = lemma γ ∙ lemma′ p

opaque

  -- The term pred is well-resourced.

  ▸pred : ε ▸[ 𝟙ᵐ ] pred
  ▸pred = lamₘ $ ▸pred′ (sub-≈ᶜ var (ε ∙ M.·-identityʳ _))
