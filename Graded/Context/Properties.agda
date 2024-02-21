------------------------------------------------------------------------
-- Properties of modality (grade) contexts.
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Context.Properties
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Graded.Modality.Properties 𝕄
open import Graded.Context 𝕄

open import Tools.Algebra M
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.PropositionalEquality
import Tools.Reasoning.Equivalence

open import Graded.Context.Properties.Addition 𝕄 public
open import Graded.Context.Properties.Equivalence 𝕄 public
open import Graded.Context.Properties.Has-well-behaved-zero 𝕄 public
open import Graded.Context.Properties.Lookup 𝕄 public
open import Graded.Context.Properties.Meet 𝕄 public
open import Graded.Context.Properties.Multiplication 𝕄 public
open import Graded.Context.Properties.Natrec 𝕄 public
open import Graded.Context.Properties.PartialOrder 𝕄 public
open import Graded.Context.Properties.Star 𝕄 public
open import Graded.Context.Properties.Update 𝕄 public

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
tailₘ-distrib-∧ᶜ (ε ∙ p) (ε ∙ q) = refl
tailₘ-distrib-∧ᶜ (γ ∙ p′ ∙ p) (δ ∙ q′ ∙ q) = cong (_∙ _) (tailₘ-distrib-∧ᶜ (γ ∙ p) (δ ∙ q))

-- headₘ distributes over meet
-- headₘ (γ ∧ᶜ δ) ≡ headₘ γ ∧ headₘ δ

head-distrib-∧ : (γ δ : Conₘ (1+ n)) → headₘ (γ ∧ᶜ δ) ≡ (headₘ γ) ∧ (headₘ δ)
head-distrib-∧ (γ ∙ p) (δ ∙ q) = refl

-- The headₘ and tailₘ functions correctly give the head and tail of the context
-- tailₘ γ ∙ headₘ γ ≡ γ

headₘ-tailₘ-correct : (γ : Conₘ (1+ n)) → tailₘ γ ∙ headₘ γ ≡ γ
headₘ-tailₘ-correct (γ ∙ p) = refl

-- Congruence of tailₘ
-- If γ ≈ᶜ δ then tailₘ γ ≈ᶜ tailₘ δ

tailₘ-cong : {γ δ : Conₘ (1+ n)} → γ ≈ᶜ δ → tailₘ γ ≈ᶜ tailₘ δ
tailₘ-cong (γ≈ᶜδ ∙ _) = γ≈ᶜδ

-- Congruence for headₘ.

headₘ-cong : {γ δ : Conₘ (1+ n)} → γ ≈ᶜ δ → headₘ γ ≡ headₘ δ
headₘ-cong (_ ∙ p≡q) = p≡q

-- tailₘ is monotone
-- If γ ≤ᶜ δ then tailₘ γ ≤ᶜ tailₘ δ

tailₘ-monotone : {γ δ : Conₘ (1+ n)} → γ ≤ᶜ δ → tailₘ γ ≤ᶜ tailₘ δ
tailₘ-monotone {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) = γ≤δ

-- headₘ is monotone
-- If γ ≤ᶜ δ then headₘ γ ≤ᶜ headₘ δ

headₘ-monotone : {γ δ : Conₘ (1+ n)} → γ ≤ᶜ δ → headₘ γ ≤ headₘ δ
headₘ-monotone {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) = p≤q

------------------------------------------------------------------------
-- Properties that hold for trivial modalities

-- If the modality is trivial, then every vector is equal to 𝟘ᶜ.

≈ᶜ𝟘ᶜ : Trivial → γ ≈ᶜ 𝟘ᶜ
≈ᶜ𝟘ᶜ {γ = γ} 𝟙≡𝟘 = begin
  γ       ≈˘⟨ ·ᶜ-identityˡ _ ⟩
  𝟙 ·ᶜ γ  ≈⟨ ·ᶜ-congʳ 𝟙≡𝟘 ⟩
  𝟘 ·ᶜ γ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
  𝟘ᶜ      ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

-- If the modality is trivial, then _≈ᶜ_ is trivial.

≈ᶜ-trivial : Trivial → γ ≈ᶜ δ
≈ᶜ-trivial {γ = γ} {δ = δ} 𝟙≡𝟘 = begin
  γ   ≈⟨ ≈ᶜ𝟘ᶜ 𝟙≡𝟘 ⟩
  𝟘ᶜ  ≈˘⟨ ≈ᶜ𝟘ᶜ 𝟙≡𝟘 ⟩
  δ   ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

------------------------------------------------------------------------
-- Left semimodules

-- Contexts form a preleft semimodule

Conₘ-preSemimodule : ∀ {n} → IsPreleftSemimodule +-·-Semiring′ _≡_ _+ᶜ_ (𝟘ᶜ {n}) _·ᶜ_
Conₘ-preSemimodule = record
  { *ₗ-cong = cong₂ _·ᶜ_
  ; *ₗ-zeroˡ = λ γ → ≈ᶜ→≡ (·ᶜ-zeroˡ γ)
  ; *ₗ-distribʳ = λ γ p q → ≈ᶜ→≡ (·ᶜ-distribʳ-+ᶜ p q γ)
  ; *ₗ-identityˡ = λ γ → ≈ᶜ→≡ (·ᶜ-identityˡ γ)
  ; *ₗ-assoc = λ p q γ → ≈ᶜ→≡ (·ᶜ-assoc p q γ)
  ; *ₗ-zeroʳ = λ p → ≈ᶜ→≡ (·ᶜ-zeroʳ p)
  ; *ₗ-distribˡ = λ p γ δ → ≈ᶜ→≡ (·ᶜ-distribˡ-+ᶜ p γ δ)
  }

-- Contexts form a left semimodule

Conₘ-semimodule : ∀ {n} → IsLeftSemimodule +-·-Semiring′ _≡_ _+ᶜ_ (𝟘ᶜ {n}) _·ᶜ_
Conₘ-semimodule = record
  { +ᴹ-isCommutativeMonoid = +ᶜ-commutativeMonoid
  ; isPreleftSemimodule = Conₘ-preSemimodule
  }

------------------------------------------------------------------------
-- Some properties that are related to the usage rules for identity
-- types

private opaque

  -- Some lemmas used below.

  ⋀ᶜ⁴𝟘ᶜ : 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = n}
  ⋀ᶜ⁴𝟘ᶜ =
    flip ≈ᶜ-trans (∧ᶜ-idem _) $ ∧ᶜ-congˡ $
    flip ≈ᶜ-trans (∧ᶜ-idem _) $ ∧ᶜ-congˡ $
    ∧ᶜ-idem _

  ⋀ᶜ⁵𝟘ᶜ : 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = n}
  ⋀ᶜ⁵𝟘ᶜ = flip ≈ᶜ-trans (∧ᶜ-idem _) $ ∧ᶜ-congˡ ⋀ᶜ⁴𝟘ᶜ

opaque

  -- A lemma related to some of the usage rules for J and K.

  ω·ᶜ⋀ᶜ²𝟘ᶜ : ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ) ≈ᶜ 𝟘ᶜ {n = n}
  ω·ᶜ⋀ᶜ²𝟘ᶜ = begin
    ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ≈⟨ ·ᶜ-congˡ $ ∧ᶜ-idem _ ⟩
    ω ·ᶜ 𝟘ᶜ          ≈⟨ ·ᶜ-zeroʳ _ ⟩
    𝟘ᶜ               ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

opaque

  -- A lemma related to one of the usage rules for K.

  ω·ᶜ⋀ᶜ⁴𝟘ᶜ : ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ) ≈ᶜ 𝟘ᶜ {n = n}
  ω·ᶜ⋀ᶜ⁴𝟘ᶜ = begin
    ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ≈⟨ ·ᶜ-congˡ ⋀ᶜ⁴𝟘ᶜ ⟩
    ω ·ᶜ 𝟘ᶜ                      ≈⟨ ·ᶜ-zeroʳ _ ⟩
    𝟘ᶜ                           ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

opaque

  -- A lemma related to one of the usage rules for J.

  ω·ᶜ⋀ᶜ⁵𝟘ᶜ : ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ) ≈ᶜ 𝟘ᶜ {n = n}
  ω·ᶜ⋀ᶜ⁵𝟘ᶜ = begin
    ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ≈⟨ ·ᶜ-congˡ ⋀ᶜ⁵𝟘ᶜ ⟩
    ω ·ᶜ 𝟘ᶜ                            ≈⟨ ·ᶜ-zeroʳ _ ⟩
    𝟘ᶜ                                 ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid
