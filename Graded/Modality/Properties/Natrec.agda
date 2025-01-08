------------------------------------------------------------------------
-- Properties of nr and nrᵢ
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Modality.Properties.Natrec
  {a} {M : Set a} (𝕄 : Semiring-with-meet M)
  where

open Semiring-with-meet 𝕄

open import Graded.Modality.Properties.Addition 𝕄
open import Graded.Modality.Properties.Greatest-lower-bound 𝕄
open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.Multiplication 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder ≤-poset as RPo
import Tools.Reasoning.PropositionalEquality as RPe

private variable
  p p′ q q′ r r′ z s : M

------------------------------------------------------------------------
-- Properties of nr functions

module _ ⦃ has-nr : Has-nr _ 𝕄 ⦄ where

  open Has-nr has-nr

  opaque

    nr-𝟘 : nr p r 𝟘 𝟘 𝟘 ≡ 𝟘
    nr-𝟘 {p} {r} = ≤-antisym (nr-zero ≤-refl) (begin
      𝟘                               ≡˘⟨ ·-zeroʳ _ ⟩
      nr p r 𝟘 𝟘 𝟘 · 𝟘               ≤⟨ nr-· ⟩
      nr p r (𝟘 · 𝟘) (𝟘 · 𝟘) (𝟘 · 𝟘) ≡⟨ cong (λ x → nr p r x x x) (·-zeroˡ _) ⟩
      nr p r 𝟘 𝟘 𝟘                    ∎)
      where
      open RPo

------------------------------------------------------------------------
-- Properties of factoring nr functions

module _
  ⦃ has-nr : Has-nr _ 𝕄 ⦄
  ⦃ is-factoring-nr : Is-factoring-nr _ has-nr ⦄ where

  open Is-factoring-nr is-factoring-nr
  open Has-nr has-nr

  nr₂≤ : nr₂ p r ≤ p + r · nr₂ p r
  nr₂≤ {p} {r} = begin
    nr₂ p r                              ≡˘⟨ ·-identityʳ _ ⟩
    nr₂ p r · 𝟙                          ≡˘⟨ +-identityʳ _ ⟩
    nr₂ p r · 𝟙 + 𝟘                      ≡˘⟨ +-congˡ nr-𝟘 ⟩
    nr₂ p r · 𝟙 + nr p r 𝟘 𝟘 𝟘           ≡˘⟨ nr-factoring ⟩
    nr p r 𝟘 𝟘 𝟙                         ≤⟨ nr-suc ⟩
    𝟘 + p · 𝟙 + r · nr p r 𝟘 𝟘 𝟙         ≡⟨ +-identityˡ _ ⟩
    p · 𝟙 + r · nr p r 𝟘 𝟘 𝟙             ≡⟨ +-cong (·-identityʳ _) (·-congˡ nr-factoring) ⟩
    p + r · (nr₂ p r · 𝟙 + nr p r 𝟘 𝟘 𝟘) ≡⟨ +-congˡ (·-congˡ (+-cong (·-identityʳ _) nr-𝟘)) ⟩
    p + r · (nr₂ p r + 𝟘)                ≡⟨ +-congˡ (·-congˡ (+-identityʳ _)) ⟩
    p + r · nr₂ p r                      ∎
    where
    open RPo

------------------------------------------------------------------------
-- "Optimal" nr functions

-- A type used to express that there isn't a greatest factoring nr function.

record No-greatest-factoring-nr : Set a where
  no-eta-equality

  field
    -- There are two nr functions
    has-nr₁ : Has-nr M 𝕄
    has-nr₂ : Has-nr M 𝕄
    -- Both nr functions are factoring
    factoring₁ : Is-factoring-nr M has-nr₁
    factoring₂ : Is-factoring-nr M has-nr₂

  open Has-nr has-nr₁ renaming (nr to nr₁)
  open Has-nr has-nr₂ renaming (nr to nr₂)

  field
    -- There is some input to the nr functions...
    p₀ r₀ z₀ s₀ n₀ : M

    -- ...such that their outputs are not equal...
    nr₁≢nr₂ : nr₁ p₀ r₀ z₀ s₀ n₀ ≢ nr₂ p₀ r₀ z₀ s₀ n₀

    -- ...and there is no other possible output that is greater than both
    -- i.e. no other nr function could be greater than both of them.
    nr≰ : ∀ q → nr₁ p₀ r₀ z₀ s₀ n₀ ≤ q → nr₂ p₀ r₀ z₀ s₀ n₀ ≤ q → ⊥

------------------------------------------------------------------------
-- Sequences used to define one of the usage rules for natrec.

opaque

  -- The sequence nrᵢ r 𝟘 𝟘 is constantly 𝟘.

  nrᵢ-𝟘 : ∀ i → nrᵢ r 𝟘 𝟘 i ≡ 𝟘
  nrᵢ-𝟘 0 = refl
  nrᵢ-𝟘 {r} (1+ i) rewrite nrᵢ-𝟘 {r} i =
    trans (+-identityˡ _) (·-zeroʳ r)

opaque

  -- A monotonicity property for nrᵢ

  nrᵢ-monotone : ∀ i → p ≤ p′ → q ≤ q′ → nrᵢ r p q i ≤ nrᵢ r p′ q′ i
  nrᵢ-monotone 0 p≤ q≤ = p≤
  nrᵢ-monotone (1+ i) p≤ q≤ =
    +-monotone q≤ (·-monotoneʳ (nrᵢ-monotone i p≤ q≤))

opaque

  -- The greatest lower bound of the sequence nrᵢ 𝟘 p q is p ∧ q.

  nrᵢ-𝟘-GLB : Greatest-lower-bound (p ∧ q) (λ i → nrᵢ 𝟘 p q i)
  nrᵢ-𝟘-GLB {p} {q} =
    (λ { 0 → ∧-decreasingˡ p q
       ; (1+ i) → ≤-trans (∧-decreasingʳ p q)
                   (≤-reflexive (sym (lemma i)))}) ,
    λ r r≤ →
      ∧-greatest-lower-bound (r≤ 0)
        (≤-trans (r≤ 1) (≤-reflexive (lemma 0)))
    where
    lemma : ∀ i → nrᵢ 𝟘 p q (1+ i) ≡ q
    lemma i = trans (+-congˡ (·-zeroˡ _)) (+-identityʳ q)

opaque

  -- The greatest lower bound of the sequence nrᵢ r 𝟘 𝟘 is 𝟘.

  GLB-nrᵢ-𝟘 : Greatest-lower-bound 𝟘 (nrᵢ r 𝟘 𝟘)
  GLB-nrᵢ-𝟘 = GLB-const nrᵢ-𝟘

opaque

  -- A property of greatest lower bounds of nrᵢ sequences

  nrᵢ-GLB-≤ :
    ⦃ ok : Supports-GLB-for-natrec _ 𝕄 ⦄ →
    Greatest-lower-bound p (nrᵢ r z s) → p ≤ s + r · p
  nrᵢ-GLB-≤ ⦃ ok ⦄ p-glb =
    +-GLBˡ (·-GLBˡ p-glb) .proj₂ _ (λ i → p-glb .proj₁ (1+ i))
    where
    open Supports-GLB-for-natrec ok

opaque

  nrᵢ-+ : ∀ i → nrᵢ r (p + p′) (q + q′) i ≡ nrᵢ r p q i + nrᵢ r p′ q′ i
  nrᵢ-+ 0 = refl
  nrᵢ-+ {r} {p} {p′} {q} {q′} (1+ i) = begin
    (q + q′) + r · nrᵢ r (p + p′) (q + q′) i         ≡⟨ +-congˡ (·-congˡ (nrᵢ-+ i)) ⟩
    (q + q′) + r · (nrᵢ r p q i + nrᵢ r p′ q′ i)     ≡⟨ +-congˡ (·-distribˡ-+ _ _ _) ⟩
    (q + q′) + r · nrᵢ r p q i + r · nrᵢ r p′ q′ i   ≡⟨ +-sub-interchangeable-+ _ _ _ _ ⟩
    (q + r · nrᵢ r p q i) + (q′ + r · nrᵢ r p′ q′ i) ∎
    where
    open RPe

opaque

  -- Multiplication right-distributes over nrᵢ.

  ·-distribʳ-nrᵢ : ∀ i → nrᵢ r p q i · p′ ≡ nrᵢ r (p · p′) (q · p′) i
  ·-distribʳ-nrᵢ 0 = refl
  ·-distribʳ-nrᵢ {r} {p} {q} {p′} (1+ i) = begin
    (q + r · nrᵢ r p q i) · p′             ≡⟨ ·-distribʳ-+ _ _ _ ⟩
    q · p′ + (r · nrᵢ r p q i) · p′        ≡⟨ +-congˡ (·-assoc _ _ _) ⟩
    q · p′ + r · nrᵢ r p q i · p′          ≡⟨ +-congˡ (·-congˡ (·-distribʳ-nrᵢ i)) ⟩
    q · p′ + r · nrᵢ r (p · p′) (q · p′) i ∎
    where
    open RPe
