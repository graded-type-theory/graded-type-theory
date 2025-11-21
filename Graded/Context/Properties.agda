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
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; Sequence)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
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
    γ γ′ δ δ′ η η′ : Conₘ n
    pᵢ : Sequence M
    γᵢ δᵢ : Sequence (Conₘ _)

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

-- tailₘ distributes over addition
-- tailₘ (γ +ᶜ δ) ≡ tailₘ γ +ᶜ tailₘ δ

tailₘ-distrib-+ᶜ : (γ δ : Conₘ (1+ n)) → tailₘ (γ +ᶜ δ) ≈ᶜ (tailₘ γ) +ᶜ (tailₘ δ)
tailₘ-distrib-+ᶜ (γ ∙ p) (δ ∙ q) = ≈ᶜ-refl

-- headₘ distributes over addition
-- headₘ (γ +ᶜ δ) ≡ headₘ γ +ᶜ headₘ δ

headₘ-distrib-+ᶜ : (γ δ : Conₘ (1+ n)) → headₘ (γ +ᶜ δ) ≡ (headₘ γ) + (headₘ δ)
headₘ-distrib-+ᶜ (γ ∙ p) (δ ∙ q) = refl

-- tailₘ distributes over multiplication
-- tailₘ (p ·ᶜ γ) ≡ p ·ᶜ tailₘ γ

tailₘ-distrib-·ᶜ : (p : M) (γ : Conₘ (1+ n)) → tailₘ (p ·ᶜ γ) ≈ᶜ p ·ᶜ (tailₘ γ)
tailₘ-distrib-·ᶜ p (γ ∙ q) = ≈ᶜ-refl

-- headₘ distributes over multiplication
-- headₘ (p ·ᶜ γ) ≡ p ·ᶜ headₘ γ

headₘ-distrib-·ᶜ : (p : M) (γ : Conₘ (1+ n)) → headₘ (p ·ᶜ γ) ≡ p · headₘ γ
headₘ-distrib-·ᶜ p (γ ∙ q) = refl

-- The headₘ and tailₘ functions correctly give the head and tail of the context
-- tailₘ γ ∙ headₘ γ ≡ γ

headₘ-tailₘ-correct : (γ : Conₘ (1+ n)) → tailₘ γ ∙ headₘ γ ≡ γ
headₘ-tailₘ-correct (γ ∙ p) = refl

-- A propositional uniqueness principle for contexts

decomposeᶜ : (γ : Conₘ n) → Conₘ n
decomposeᶜ {0} γ = ε
decomposeᶜ {1+ n} γ = decomposeᶜ (tailₘ γ) ∙ headₘ γ

decomposeᶜ-correct : (γ : Conₘ n) → decomposeᶜ γ ≡ γ
decomposeᶜ-correct ε = refl
decomposeᶜ-correct (γ ∙ p) = cong (_∙ p) (decomposeᶜ-correct γ)

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

  +ᶜ⁴𝟘ᶜ : 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = n}
  +ᶜ⁴𝟘ᶜ =
    flip ≈ᶜ-trans (+ᶜ-identityˡ _) $ +ᶜ-congˡ $
    flip ≈ᶜ-trans (+ᶜ-identityˡ _) $ +ᶜ-congˡ $
    +ᶜ-identityˡ _

  +ᶜ⁵𝟘ᶜ : 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = n}
  +ᶜ⁵𝟘ᶜ = flip ≈ᶜ-trans (+ᶜ-identityˡ _) $ +ᶜ-congˡ +ᶜ⁴𝟘ᶜ

opaque

  -- A lemma related to some of the usage rules for J and K.

  ω·ᶜ+ᶜ²𝟘ᶜ : ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ) ≈ᶜ 𝟘ᶜ {n = n}
  ω·ᶜ+ᶜ²𝟘ᶜ = begin
    ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ≈⟨ ·ᶜ-congˡ $ +ᶜ-identityˡ _ ⟩
    ω ·ᶜ 𝟘ᶜ          ≈⟨ ·ᶜ-zeroʳ _ ⟩
    𝟘ᶜ               ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

opaque

  -- A lemma related to one of the usage rules for K.

  ω·ᶜ+ᶜ⁴𝟘ᶜ : ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ) ≈ᶜ 𝟘ᶜ {n = n}
  ω·ᶜ+ᶜ⁴𝟘ᶜ = begin
    ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ≈⟨ ·ᶜ-congˡ +ᶜ⁴𝟘ᶜ ⟩
    ω ·ᶜ 𝟘ᶜ                      ≈⟨ ·ᶜ-zeroʳ _ ⟩
    𝟘ᶜ                           ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

opaque

  -- A lemma related to one of the usage rules for J.

  ω·ᶜ+ᶜ⁵𝟘ᶜ : ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ) ≈ᶜ 𝟘ᶜ {n = n}
  ω·ᶜ+ᶜ⁵𝟘ᶜ = begin
    ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ≈⟨ ·ᶜ-congˡ +ᶜ⁵𝟘ᶜ ⟩
    ω ·ᶜ 𝟘ᶜ                            ≈⟨ ·ᶜ-zeroʳ _ ⟩
    𝟘ᶜ                                 ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

------------------------------------------------------------------------
-- Some properties that are related to greatest lower bounds of
-- context sequences.

opaque

  -- ε is the greatest lower bound of all sequences of empty contexts

  ε-GLB : {δᵢ : Sequence (Conₘ 0)} → Greatest-lower-boundᶜ ε δᵢ
  ε-GLB = (λ i → lemma _) , (λ { ε _ → ε })
    where
    lemma : ∀ δ → ε ≤ᶜ δ
    lemma ε = ε

opaque

  -- Greatest lower bounds of contexts are pointwise greatest lower
  -- bounds.

  GLBᶜ-pointwise : ∀ {δ : Sequence (Conₘ (1+ n))} →
                   Greatest-lower-boundᶜ γ δ →
                   Greatest-lower-boundᶜ (tailₘ γ) (tailₘ ∘→ δ) ×
                   Greatest-lower-bound (headₘ γ) (headₘ ∘→ δ)
  GLBᶜ-pointwise {γ = γ ∙ p} {δ} (γ≤ , γ-glb) =
      ((λ i → tailₘ-monotone (γ≤ i)) , γₜ-glb)
    , ((λ i → headₘ-monotone (γ≤ i)) , γₕ-glb)
    where
    open ≤ᶜ-reasoning
    γₜ-glb : ∀ η → (∀ i → η ≤ᶜ tailₘ (δ i)) → η ≤ᶜ γ
    γₜ-glb η η≤ = tailₘ-monotone $ γ-glb (η ∙ p) λ i → begin
      η ∙ p                     ≤⟨ η≤ i ∙ headₘ-monotone (γ≤ i) ⟩
      tailₘ (δ i) ∙ headₘ (δ i) ≡⟨ headₘ-tailₘ-correct (δ i) ⟩
      δ i                       ∎
    γₕ-glb : ∀ q → (∀ i → q ≤ headₘ (δ i)) → q ≤ p
    γₕ-glb q q≤ = headₘ-monotone $ γ-glb (γ ∙ q) λ i → begin
      γ ∙ q                     ≤⟨ tailₘ-monotone (γ≤ i) ∙ q≤ i ⟩
      tailₘ (δ i) ∙ headₘ (δ i) ≡⟨ headₘ-tailₘ-correct (δ i) ⟩
      δ i                       ∎

opaque

  -- Pointwise greatest lower bounds are greatest lower bounds.

  GLBᶜ-pointwise′ :
    ∀ {δᵢ : Sequence (Conₘ (1+ n))} →
    Greatest-lower-boundᶜ (tailₘ γ) (tailₘ ∘→ δᵢ) →
    Greatest-lower-bound (headₘ γ) (headₘ ∘→ δᵢ) →
    Greatest-lower-boundᶜ γ δᵢ
  GLBᶜ-pointwise′ {γ = γ ∙ p} {δᵢ} (γ≤ , γ-glb) (p≤ , p-glb) =
    (λ i → subst (_ ≤ᶜ_) (headₘ-tailₘ-correct (δᵢ i)) (γ≤ i ∙ p≤ i)) ,
    λ {(η ∙ q) η≤ →
      γ-glb η (tailₘ-monotone ∘→ η≤) ∙
      p-glb q (headₘ-monotone ∘→ η≤)}

opaque

  -- Congruence of greatest lower bounds

  GLBᶜ-cong :
    γ ≈ᶜ δ →
    (∀ i → γᵢ i ≈ᶜ δᵢ i) →
    Greatest-lower-boundᶜ γ γᵢ →
    Greatest-lower-boundᶜ δ δᵢ
  GLBᶜ-cong γ≈δ γᵢ≈δᵢ (γ≤ , γ-glb) =
      (λ i → ≤ᶜ-trans (≤ᶜ-reflexive (≈ᶜ-sym γ≈δ))
               (≤ᶜ-trans (γ≤ i) (≤ᶜ-reflexive (γᵢ≈δᵢ i))))
    , λ η η≤ → ≤ᶜ-trans (γ-glb _ (λ i → ≤ᶜ-trans (η≤ i)
                           (≤ᶜ-reflexive (≈ᶜ-sym (γᵢ≈δᵢ i)))))
                 (≤ᶜ-reflexive γ≈δ)

opaque

  -- Congruence of greatest lower bounds

  GLBᶜ-congʳ :
    γ ≈ᶜ δ →
    Greatest-lower-boundᶜ γ γᵢ →
    Greatest-lower-boundᶜ δ γᵢ
  GLBᶜ-congʳ γ≈δ = GLBᶜ-cong γ≈δ λ _ → ≈ᶜ-refl


opaque

  -- Greatest lower bounds of equal sequences are equal

  GLBᶜ-congˡ :
    (∀ i → γᵢ i ≈ᶜ δᵢ i) →
    Greatest-lower-boundᶜ γ γᵢ →
    Greatest-lower-boundᶜ γ δᵢ
  GLBᶜ-congˡ = GLBᶜ-cong ≈ᶜ-refl


opaque

  -- The greatest lower bound, if it exists, is unique

  GLBᶜ-unique :
    Greatest-lower-boundᶜ γ γᵢ →
    Greatest-lower-boundᶜ δ γᵢ →
    γ ≈ᶜ δ
  GLBᶜ-unique γ-GLB δ-GLB =
    ≤ᶜ-antisym (δ-GLB .proj₂ _ (γ-GLB .proj₁))
      (γ-GLB .proj₂ _ (δ-GLB .proj₁))

opaque

  -- If γᵢ ≤ᶜ δᵢ (pointwise) then the greatest lower bound of γᵢ is
  -- lower than the greatest lower bound of δᵢ (if they exist)

  GLBᶜ-monotone :
    (∀ i → γᵢ i ≤ᶜ δᵢ i) →
    Greatest-lower-boundᶜ γ γᵢ →
    Greatest-lower-boundᶜ δ δᵢ →
    γ ≤ᶜ δ
  GLBᶜ-monotone γᵢ≤δᵢ γ-GLB δ-GLB =
    δ-GLB .proj₂ _ (λ i → ≤ᶜ-trans (γ-GLB .proj₁ i) (γᵢ≤δᵢ i))

opaque

  -- Greatest lower bounds of constant sequences

  GLBᶜ-const :
    (∀ i → γᵢ i ≈ᶜ γ) →
    Greatest-lower-boundᶜ γ γᵢ
  GLBᶜ-const γᵢ≈γ  =
    (λ i → ≤ᶜ-reflexive (≈ᶜ-sym (γᵢ≈γ i))) ,
    (λ η η≤ → ≤ᶜ-trans (η≤ 0) (≤ᶜ-reflexive (γᵢ≈γ 0)))

opaque

  -- If 𝟘ᶜ is the greatest lower bounds of a sequence then the sequence
  -- is constantly 𝟘ᶜ (if the modality has a well-behaved zero).

  𝟘ᶜ-GLBᶜ-inv :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero _ semiring-with-meet ⦄ →
    Greatest-lower-boundᶜ 𝟘ᶜ γᵢ → ∀ i → γᵢ i ≈ᶜ 𝟘ᶜ
  𝟘ᶜ-GLBᶜ-inv (𝟘≤ , 𝟘-glb) i = 𝟘ᶜ≮ (𝟘≤ i)

opaque

  -- Lifting the property that the modality preserves addition from the
  -- left to contexts.

  +-GLB→+ᶜ-GLBᶜ :
    {γᵢ : Sequence (Conₘ n)} →
    (∀ {p q pᵢ} → Greatest-lower-bound p pᵢ →
                  Greatest-lower-bound (q + p) (λ i → q + pᵢ i)) →
    Greatest-lower-boundᶜ γ γᵢ →
    Greatest-lower-boundᶜ (δ +ᶜ γ) (λ i → δ +ᶜ γᵢ i)
  +-GLB→+ᶜ-GLBᶜ {γ = ε} {(ε)} {(γᵢ)} +-GLB γ-GLB = ε-GLB
  +-GLB→+ᶜ-GLBᶜ {γ = γ ∙ p} {δ ∙ q} {(γᵢ)} +-GLB γp-GLB =
    let γ-glb , p-glb = GLBᶜ-pointwise γp-GLB
    in  GLBᶜ-pointwise′
          (GLBᶜ-congˡ (λ i → ≈ᶜ-sym (tailₘ-distrib-+ᶜ (δ ∙ q) (γᵢ i)))
            (+-GLB→+ᶜ-GLBᶜ +-GLB γ-glb))
          (GLB-congˡ (λ i → sym (headₘ-distrib-+ᶜ (δ ∙ q) (γᵢ i)))
            (+-GLB p-glb))

opaque

  -- Lifting the property that the modality preserves multiplication
  -- from the left to contexts.

  ·-GLBˡ→·ᶜ-GLBᶜˡ :
    {γᵢ : Sequence (Conₘ n)} →
    (∀ {p q pᵢ} → Greatest-lower-bound p pᵢ →
                  Greatest-lower-bound (q · p) (λ i → q · pᵢ i)) →
    Greatest-lower-boundᶜ γ γᵢ →
    Greatest-lower-boundᶜ (q ·ᶜ γ) (λ i → q ·ᶜ γᵢ i)
  ·-GLBˡ→·ᶜ-GLBᶜˡ {γ = ε} {γᵢ} ·-GLB γ-GLB = ε-GLB
  ·-GLBˡ→·ᶜ-GLBᶜˡ {γ = γ ∙ p} {q} {γᵢ} ·-GLB γp-GLB =
    let γ-glb , p-glb = GLBᶜ-pointwise γp-GLB
    in  GLBᶜ-pointwise′
          (GLBᶜ-congˡ (λ i → ≈ᶜ-sym (tailₘ-distrib-·ᶜ q (γᵢ i)))
            (·-GLBˡ→·ᶜ-GLBᶜˡ ·-GLB γ-glb))
          (GLB-congˡ (λ i → sym (headₘ-distrib-·ᶜ q (γᵢ i)))
            (·-GLB p-glb))

opaque

  -- Lifting the property that the modality preserves multiplication
  -- from the right to contexts.

  ·-GLBʳ→·ᶜ-GLBᶜʳ :
    {pᵢ : Sequence M} →
    (∀ {p q pᵢ} → Greatest-lower-bound p pᵢ →
                  Greatest-lower-bound (p · q) (λ i → pᵢ i · q)) →
    Greatest-lower-bound p pᵢ →
    Greatest-lower-boundᶜ (p ·ᶜ γ) (λ i → pᵢ i ·ᶜ γ)
  ·-GLBʳ→·ᶜ-GLBᶜʳ {γ = ε} ·-GLB p-glb =
    GLBᶜ-const (λ _ → ≈ᶜ-refl)
  ·-GLBʳ→·ᶜ-GLBᶜʳ {γ = γ ∙ q} ·-GLB p-glb =
    GLBᶜ-pointwise′ (·-GLBʳ→·ᶜ-GLBᶜʳ ·-GLB p-glb)
      (·-GLB p-glb)

opaque

  -- Lifting the property that the modality preserves addition of nrᵢ
  -- sequences to contexts.

  +nrᵢ-GLB→+ᶜnrᵢᶜ-GLBᶜ :
    (∀ {p p′ r z z′ s s′} →
       Greatest-lower-bound p (nrᵢ r z s) →
       Greatest-lower-bound p′ (nrᵢ r z′ s′) →
       ∃ λ q → Greatest-lower-bound q (nrᵢ r (z + z′) (s + s′)) ×
               p + p′ ≤ q) →
    Greatest-lower-boundᶜ η (nrᵢᶜ r γ δ) →
    Greatest-lower-boundᶜ η′ (nrᵢᶜ r γ′ δ′) →
    ∃ λ χ′ → Greatest-lower-boundᶜ χ′ (nrᵢᶜ r (γ +ᶜ γ′) (δ +ᶜ δ′)) ×
             η +ᶜ η′ ≤ᶜ χ′
  +nrᵢ-GLB→+ᶜnrᵢᶜ-GLBᶜ {η = ε} {γ = ε} {(ε)} {(ε)} {(ε)} {(ε)}
    +nrᵢ-GLB η-glb η′-glb =
    ε , GLBᶜ-const (λ _ → ε) , ε
  +nrᵢ-GLB→+ᶜnrᵢᶜ-GLBᶜ
    {η = η ∙ p} {r} {γ = γ ∙ z} {δ ∙ s} {η′ ∙ p′} {γ′ ∙ z′} {δ′ ∙ s′}
    +nrᵢ-GLB ηp-glb ηp′-glb =
    let η-glb , p-glb = GLBᶜ-pointwise ηp-glb
        η′-glb , p′-glb = GLBᶜ-pointwise ηp′-glb
        x , x-glb , ≤x = +nrᵢ-GLB p-glb p′-glb
        χ , χ-glb , ≤χ = +nrᵢ-GLB→+ᶜnrᵢᶜ-GLBᶜ +nrᵢ-GLB η-glb η′-glb
        glb = GLBᶜ-pointwise′ {γ = χ ∙ x}
                {δᵢ = λ i → nrᵢᶜ r (γ +ᶜ γ′) (δ +ᶜ δ′) i ∙
                           nrᵢ r (z + z′) (s + s′) i}
                χ-glb x-glb
    in  χ ∙ x , glb , ≤χ ∙ ≤x

opaque

  -- If all nrᵢ r sequences have a greatest lower bound then so do
  -- all nrᵢᶜ r sequences.

  ∃nrᵢ-GLB→∃nrᵢᶜ-GLB :
    (∀ z s → ∃ λ x → Greatest-lower-bound x (nrᵢ r z s)) →
    (γ δ : Conₘ n) → ∃ λ χ → Greatest-lower-boundᶜ χ (nrᵢᶜ r γ δ)
  ∃nrᵢ-GLB→∃nrᵢᶜ-GLB nrᵢ-GLB ε ε =
    ε , ε-GLB
  ∃nrᵢ-GLB→∃nrᵢᶜ-GLB nrᵢ-GLB (γ ∙ p) (δ ∙ q) =
    let χ , χ-glb = ∃nrᵢ-GLB→∃nrᵢᶜ-GLB nrᵢ-GLB γ δ
        x , x-glb = nrᵢ-GLB p q
    in  χ ∙ x , GLBᶜ-pointwise′ χ-glb x-glb

opaque

  -- If all greatest lower bounds of nrᵢ exist then so does
  -- all greatest lower bounds of nrᵢᶜ.

  GLB-nrᵢ→GLBᶜ-nrᵢᶜ :
    (∀ r z s → ∃ λ p → Greatest-lower-bound p (nrᵢ r z s)) →
    ∀ r (γ δ : Conₘ n) → ∃ λ η → Greatest-lower-boundᶜ η (nrᵢᶜ r γ δ)
  GLB-nrᵢ→GLBᶜ-nrᵢᶜ glb-nrᵢ r ε ε = ε , ε-GLB
  GLB-nrᵢ→GLBᶜ-nrᵢᶜ glb-nrᵢ r (γ ∙ p) (δ ∙ p′) =
    let q , q-glb = glb-nrᵢ r p p′
        η , η-glb = GLB-nrᵢ→GLBᶜ-nrᵢᶜ glb-nrᵢ r γ δ
    in  η ∙ q , GLBᶜ-pointwise′ η-glb q-glb

opaque

  -- The greatest lower bound of nrᵢᶜ 𝟘 γ δ is γ ∧ᶜ δ.

  Greatest-lower-boundᶜ-nrᵢᶜ-𝟘 :
    Greatest-lower-boundᶜ (γ ∧ᶜ δ) (nrᵢᶜ 𝟘 γ δ)
  Greatest-lower-boundᶜ-nrᵢᶜ-𝟘 {γ = ε} {δ = ε} =
    ε-GLB
  Greatest-lower-boundᶜ-nrᵢᶜ-𝟘 {γ = _ ∙ _} {δ = _ ∙ _} =
    GLBᶜ-pointwise′ Greatest-lower-boundᶜ-nrᵢᶜ-𝟘
      Greatest-lower-bound-nrᵢ-𝟘

opaque

  -- Greatest lower bounds can be pointwise "switched" between two
  -- contexts.

  Conₘ-interchange-GLBᶜ :
    Greatest-lower-boundᶜ γ γᵢ →
    Greatest-lower-boundᶜ δ δᵢ →
    ∀ x →
    Greatest-lower-boundᶜ (γ , x ≔ δ ⟨ x ⟩) (λ i → γᵢ i , x ≔ δᵢ i ⟨ x ⟩)
  Conₘ-interchange-GLBᶜ {γ = ε} {δ = ε} _ _ ()
  Conₘ-interchange-GLBᶜ {γ = _ ∙ _} {γᵢ} {δ = _ ∙ _} {δᵢ} γp-glb δq-glb x0 =
    let γ-glb , _ = GLBᶜ-pointwise γp-glb
        _ , q-glb = GLBᶜ-pointwise δq-glb
    in  GLBᶜ-pointwise′
          (GLBᶜ-congˡ
            (λ i → subst (_ ≈ᶜ_) (sym (cong tailₘ (update-head (γᵢ i) _))) ≈ᶜ-refl)
            γ-glb)
         (GLB-congˡ
           (λ i → sym (trans (cong headₘ (update-head (γᵢ i) _))
                    (headₘ-⟨⟩ (δᵢ i))))
           q-glb)
  Conₘ-interchange-GLBᶜ {γ = _ ∙ _} {γᵢ} {δ = _ ∙ _} {δᵢ} γp-glb δq-glb (x +1) =
    let γ-glb , p-glb = GLBᶜ-pointwise γp-glb
        δ-glb , q-glb = GLBᶜ-pointwise δq-glb
        γ′-glb = Conₘ-interchange-GLBᶜ γ-glb δ-glb x
    in  GLBᶜ-pointwise′
          (GLBᶜ-congˡ
            (λ i → subst ((tailₘ (γᵢ i) , x ≔ tailₘ (δᵢ i) ⟨ x ⟩) ≈ᶜ_)
                     (sym (cong tailₘ (update-step (γᵢ i) _ x)))
                     (update-congʳ (sym (tailₘ-⟨⟩ (δᵢ i)))))
            γ′-glb)
          (GLB-congˡ
            (λ i → sym (cong headₘ (update-step (γᵢ i) _ x)))
            p-glb)

opaque

  -- If greatest lower bounds of nrᵢ sequences are decidable then so are
  -- nrᵢᶜ sequences.

  nrᵢᶜ-GLBᶜ? :
    (∀ r p q → Dec (∃ λ x → Greatest-lower-bound x (nrᵢ r p q))) →
    ∀ r (γ δ : Conₘ n) → Dec (∃ λ η → Greatest-lower-boundᶜ η (nrᵢᶜ r γ δ))
  nrᵢᶜ-GLBᶜ? _ r ε ε = yes (ε , ε-GLB)
  nrᵢᶜ-GLBᶜ? GLB? r (γ ∙ p) (δ ∙ q) =
    lemma (GLB? r p q) (nrᵢᶜ-GLBᶜ? GLB? r γ δ)
    where
    lemma :
      Dec (∃ λ x → Greatest-lower-bound x (nrᵢ r p q)) →
      Dec (∃ λ χ → Greatest-lower-boundᶜ χ (nrᵢᶜ r γ δ)) →
      Dec (∃ λ η → Greatest-lower-boundᶜ η (nrᵢᶜ r (γ ∙ p) (δ ∙ q)))
    lemma (no ¬glb) _ =
      no (λ (η , η-GLB) →
        ¬glb (headₘ η , GLBᶜ-pointwise η-GLB .proj₂))
    lemma (yes _) (no ¬glb) =
      no (λ (η , η-GLB) →
        ¬glb (tailₘ η , GLBᶜ-pointwise η-GLB .proj₁))
    lemma (yes (x , x-glb)) (yes (η , η-glb)) =
      yes (η ∙ x , GLBᶜ-pointwise′ η-glb x-glb)

opaque

  -- If all nrᵢ sequences have a greatest lower bound then so does all
  -- nrᵢᶜ sequences.

  nrᵢᶜ-has-GLBᶜ :
    (∀ r p q → ∃ λ x → Greatest-lower-bound x (nrᵢ r p q)) →
    ∀ r (γ δ : Conₘ n) → ∃ λ η → Greatest-lower-boundᶜ η (nrᵢᶜ r γ δ)
  nrᵢᶜ-has-GLBᶜ nrᵢ-has-GLB r ε ε = ε , ε-GLB
  nrᵢᶜ-has-GLBᶜ nrᵢ-has-GLB r (γ ∙ p) (δ ∙ q) =
    let x , x-glb = nrᵢ-has-GLB r p q
        χ , χ-glb = nrᵢᶜ-has-GLBᶜ nrᵢ-has-GLB r γ δ
    in  χ ∙ x , GLBᶜ-pointwise′ χ-glb x-glb

opaque

  -- The greatest lower bound of nrᵢᶜ 𝟘 γ δ is γ ∧ᶜ δ.

  nrᵢᶜ-𝟘-GLB : Greatest-lower-boundᶜ (γ ∧ᶜ δ) (nrᵢᶜ 𝟘 γ δ)
  nrᵢᶜ-𝟘-GLB {γ = ε}     {δ = ε}     = ε-GLB
  nrᵢᶜ-𝟘-GLB {γ = _ ∙ _} {δ = _ ∙ _} =
    GLBᶜ-pointwise′ nrᵢᶜ-𝟘-GLB nrᵢ-𝟘-GLB

opaque

  -- The greatest lower bound of the sequence nrᵢᶜ 𝟙 γ 𝟘ᶜ is γ

  nrᵢᶜ-const-GLBᶜ₁ : Greatest-lower-boundᶜ γ (nrᵢᶜ 𝟙 γ 𝟘ᶜ)
  nrᵢᶜ-const-GLBᶜ₁ {γ = ε} = ε-GLB
  nrᵢᶜ-const-GLBᶜ₁ {γ = γ ∙ p} =
    GLBᶜ-pointwise′ nrᵢᶜ-const-GLBᶜ₁ nrᵢ-const-GLB₁

opaque

  -- The greatest lower bound of the sequence nrᵢᶜ 𝟘 γ γ is γ

  nrᵢᶜ-const-GLBᶜ₂ : Greatest-lower-boundᶜ γ (nrᵢᶜ 𝟘 γ γ)
  nrᵢᶜ-const-GLBᶜ₂ {γ = ε} = ε-GLB
  nrᵢᶜ-const-GLBᶜ₂ {γ = γ ∙ p} =
    GLBᶜ-pointwise′ nrᵢᶜ-const-GLBᶜ₂ nrᵢ-const-GLB₂

opaque

  -- The greatest lower bound of the sequence nrᵢ r 𝟘ᶜ 𝟘ᶜ is 𝟘ᶜ.

  GLBᶜ-nrᵢᶜ-𝟘ᶜ : Greatest-lower-boundᶜ (𝟘ᶜ {n = n}) (nrᵢᶜ r 𝟘ᶜ 𝟘ᶜ)
  GLBᶜ-nrᵢᶜ-𝟘ᶜ {n = 0} = ε-GLB
  GLBᶜ-nrᵢᶜ-𝟘ᶜ {n = 1+ n} =
    GLBᶜ-pointwise′ GLBᶜ-nrᵢᶜ-𝟘ᶜ GLB-nrᵢ-𝟘

-- Lifting the properties of Has-well-behaved-GLBs to contexts

module _ ⦃ ok : Has-well-behaved-GLBs M semiring-with-meet ⦄ where

  open Has-well-behaved-GLBs ok public

  opaque

    +ᶜ-GLBᶜˡ :
      Greatest-lower-boundᶜ γ γᵢ →
      Greatest-lower-boundᶜ (δ +ᶜ γ) (λ i → δ +ᶜ γᵢ i)
    +ᶜ-GLBᶜˡ = +-GLB→+ᶜ-GLBᶜ +-GLBˡ

  opaque

    ·ᶜ-GLBᶜˡ :
      Greatest-lower-boundᶜ γ γᵢ →
      Greatest-lower-boundᶜ (p ·ᶜ γ) (λ i → p ·ᶜ γᵢ i)
    ·ᶜ-GLBᶜˡ = ·-GLBˡ→·ᶜ-GLBᶜˡ ·-GLBˡ

  opaque

    ·ᶜ-GLBᶜʳ :
      Greatest-lower-bound p pᵢ →
      Greatest-lower-boundᶜ (p ·ᶜ γ) (λ i → pᵢ i ·ᶜ γ)
    ·ᶜ-GLBᶜʳ = ·-GLBʳ→·ᶜ-GLBᶜʳ ·-GLBʳ

  opaque

    +ᶜnrᵢᶜ-GLBᶜ :
      Greatest-lower-boundᶜ γ (nrᵢᶜ r δ η) →
      Greatest-lower-boundᶜ γ′ (nrᵢᶜ r δ′ η′) →
      ∃ λ χ → Greatest-lower-boundᶜ χ (nrᵢᶜ r (δ +ᶜ δ′) (η +ᶜ η′)) ×
          γ +ᶜ γ′ ≤ᶜ χ
    +ᶜnrᵢᶜ-GLBᶜ = +nrᵢ-GLB→+ᶜnrᵢᶜ-GLBᶜ +nrᵢ-GLB


  opaque

    -- A property of greatest lower bounds of nrᵢᶜ sequences.

    nrᵢᶜ-GLBᶜ-≤ᶜ :
      Greatest-lower-boundᶜ γ (nrᵢᶜ r δ η) → γ ≤ᶜ η +ᶜ r ·ᶜ γ
    nrᵢᶜ-GLBᶜ-≤ᶜ γ-glb =
      +ᶜ-GLBᶜˡ (·ᶜ-GLBᶜˡ γ-glb) .proj₂ _ λ i →
        ≤ᶜ-trans (γ-glb .proj₁ (1+ i))
          (≤ᶜ-reflexive nrᵢᶜ-suc)
