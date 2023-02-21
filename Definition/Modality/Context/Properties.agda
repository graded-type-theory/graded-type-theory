open import Definition.Modality

module Definition.Modality.Context.Properties
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Context 𝕄

open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.Equivalence

open import Definition.Modality.Context.Properties.Addition 𝕄 public
open import Definition.Modality.Context.Properties.Equivalence 𝕄 public
open import Definition.Modality.Context.Properties.Lookup 𝕄 public
open import Definition.Modality.Context.Properties.Meet 𝕄 public
open import Definition.Modality.Context.Properties.Multiplication 𝕄 public
open import Definition.Modality.Context.Properties.PartialOrder 𝕄 public
open import Definition.Modality.Context.Properties.Star 𝕄 public
open import Definition.Modality.Context.Properties.Update 𝕄 public

private
  variable
    n : Nat
    p q r r′ : M
    γ γ′ δ δ′ η : Conₘ n

-- Context extension is monotone w.r.t the tail
-- If γ ≤ᶜ δ then γ ∙ p ≤ᶜ δ ∙ p

∙-monotoneˡ : {γ δ : Conₘ n} {p : M} → γ ≤ᶜ δ → γ ∙ p ≤ᶜ δ ∙ p
∙-monotoneˡ γ≤δ = γ≤δ ∙ ≤-refl

-- Context extension is monotone w.r.t the head
-- If p ≤ q then γ ∙ p ≤ᶜ γ ∙ q

∙-monotoneʳ : {γ : Conₘ n} {p q : M} → p ≤ q → γ ∙ p ≤ᶜ γ ∙ q
∙-monotoneʳ p≤q = ≤ᶜ-refl ∙ p≤q

-- Context extension is monotone
-- If γ ≤ᶜ δ and p ≤ q then γ ∙ p ≤ᶜ δ ∙ q

∙-monotone : {γ δ : Conₘ n} {p q : M} → γ ≤ᶜ δ → p ≤ q → γ ∙ p ≤ᶜ δ ∙ q
∙-monotone γ≤δ p≤q = ≤ᶜ-trans (∙-monotoneˡ γ≤δ) (∙-monotoneʳ p≤q)

----------------------------------
-- Propeties of headₘ and tailₘ --
----------------------------------

-- tailₘ distributes over meet
-- tailₘ (γ ∧ᶜ δ) ≡ tailₘ γ ∧ᶜ tailₘ δ

tailₘ-distrib-∧ᶜ : (γ δ : Conₘ (1+ n)) → tailₘ (γ ∧ᶜ δ) ≡ (tailₘ γ) ∧ᶜ (tailₘ δ)
tailₘ-distrib-∧ᶜ (ε ∙ p) (ε ∙ q) = PE.refl
tailₘ-distrib-∧ᶜ (γ ∙ p′ ∙ p) (δ ∙ q′ ∙ q) = cong (_∙ _) (tailₘ-distrib-∧ᶜ (γ ∙ p) (δ ∙ q))

-- headₘ distributes over meet
-- headₘ (γ ∧ᶜ δ) ≡ headₘ γ ∧ headₘ δ

head-distrib-∧ : (γ δ : Conₘ (1+ n)) → headₘ (γ ∧ᶜ δ) ≡ (headₘ γ) ∧ (headₘ δ)
head-distrib-∧ (γ ∙ p) (δ ∙ q) = PE.refl

-- The headₘ and tailₘ functions correctly give the head and tail of the context
-- tailₘ γ ∙ headₘ γ ≡ γ

headₘ-tailₘ-correct : (γ : Conₘ (1+ n)) → tailₘ γ ∙ headₘ γ ≡ γ
headₘ-tailₘ-correct (γ ∙ p) = PE.refl

-- Congruence of tailₘ
-- If γ ≈ᶜ δ then tailₘ γ ≈ᶜ tailₘ δ

tailₘ-cong : {γ δ : Conₘ (1+ n)} → γ ≈ᶜ δ → tailₘ γ ≈ᶜ tailₘ δ
tailₘ-cong (γ≈δ ∙ p≈q) = γ≈δ

-- Congruence of headₘ
-- If γ ≈ᶜ δ then headₘ γ ≈ᶜ headₘ δ

headₘ-cong : {γ δ : Conₘ (1+ n)} → γ ≈ᶜ δ → headₘ γ ≈ headₘ δ
headₘ-cong (γ≈δ ∙ p≈q) = p≈q

-- tailₘ is monotone
-- If γ ≤ᶜ δ then tailₘ γ ≤ᶜ tailₘ δ

tailₘ-monotone : {γ δ : Conₘ (1+ n)} → γ ≤ᶜ δ → tailₘ γ ≤ᶜ tailₘ δ
tailₘ-monotone {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) = γ≤δ

-- headₘ is monotone
-- If γ ≤ᶜ δ then headₘ γ ≤ᶜ headₘ δ

headₘ-monotone : {γ δ : Conₘ (1+ n)} → γ ≤ᶜ δ → headₘ γ ≤ headₘ δ
headₘ-monotone {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) = p≤q

------------------------------------------------------------------------
-- Properties that hold if 𝟙 ≈ 𝟘

-- If 𝟙 ≈ 𝟘, then every vector is equal to 𝟘ᶜ.

≈ᶜ𝟘ᶜ : 𝟙 ≈ 𝟘 → γ ≈ᶜ 𝟘ᶜ
≈ᶜ𝟘ᶜ {γ = γ} 𝟙≈𝟘 = begin
  γ       ≈˘⟨ ·ᶜ-identityˡ _ ⟩
  𝟙 ·ᶜ γ  ≈⟨ ·ᶜ-congʳ 𝟙≈𝟘 ⟩
  𝟘 ·ᶜ γ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
  𝟘ᶜ      ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

-- If 𝟙 ≈ 𝟘, then _≈ᶜ_ is trivial.

≈ᶜ-trivial : 𝟙 ≈ 𝟘 → γ ≈ᶜ δ
≈ᶜ-trivial {γ = γ} {δ = δ} 𝟙≈𝟘 = begin
  γ   ≈⟨ ≈ᶜ𝟘ᶜ 𝟙≈𝟘 ⟩
  𝟘ᶜ  ≈˘⟨ ≈ᶜ𝟘ᶜ 𝟙≈𝟘 ⟩
  δ   ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
