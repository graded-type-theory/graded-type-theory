------------------------------------------------------------------------
-- Properties of substitution matrices.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Substitution.Properties
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Substitution 𝕄 R
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Weakening 𝕄 R
open import Graded.Mode 𝕄
open import Definition.Untyped M renaming (_[_,_] to _[_,,_])

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private
  variable
    ℓ m n : Nat
    x y : Fin n
    γ γ′ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ η θ χ : Conₘ n
    Ψ : Substₘ m n
    A B t u u′ v w : Term n
    σ : Subst m n
    p q r : M
    mo mo₁ mo₂ mo₃ mo₄ mo′ : Mode
    mos mos₁ mos₂ : Mode-vector n

----------------------
-- Properties of <* --
----------------------

-- Modality substitution application distributes over addition.
-- (γ +ᶜ δ) <* Ψ ≡ γ <* Ψ +ᶜ δ <* Ψ.
-- Proof by induciton on Ψ using identity, commutativity and associtivity of addition
-- and distributivity of multiplication over addition.

<*-distrib-+ᶜ : (Ψ : Substₘ m n) (γ δ : Conₘ n) → (γ +ᶜ δ) <* Ψ ≈ᶜ γ <* Ψ +ᶜ δ <* Ψ
<*-distrib-+ᶜ []       ε       ε      = ≈ᶜ-sym (+ᶜ-identityˡ 𝟘ᶜ)
<*-distrib-+ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) = begin
  ((γ ∙ p) +ᶜ (δ ∙ q)) <* (Ψ ⊙ η)
    ≈⟨ +ᶜ-cong (·ᶜ-distribʳ-+ᶜ p q η) (<*-distrib-+ᶜ Ψ γ δ) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ γ <* Ψ +ᶜ δ <* Ψ
    ≈⟨ +ᶜ-congˡ (+ᶜ-comm (γ <* Ψ) (δ <* Ψ)) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ δ <* Ψ +ᶜ γ <* Ψ
    ≈⟨ +ᶜ-assoc (p ·ᶜ η) (q ·ᶜ η) (δ <* Ψ +ᶜ γ <* Ψ) ⟩
  p ·ᶜ η +ᶜ q ·ᶜ η +ᶜ δ <* Ψ +ᶜ γ <* Ψ
    ≈⟨ +ᶜ-comm (p ·ᶜ η) (q ·ᶜ η +ᶜ δ <* Ψ +ᶜ γ <* Ψ) ⟩
  (q ·ᶜ η +ᶜ δ <* Ψ +ᶜ γ <* Ψ) +ᶜ p ·ᶜ η
    ≈⟨ +ᶜ-assoc _ _ _ ⟩
  q ·ᶜ η +ᶜ (δ <* Ψ +ᶜ γ <* Ψ) +ᶜ p ·ᶜ η
    ≈⟨ +ᶜ-congˡ (+ᶜ-assoc (δ <* Ψ) (γ <* Ψ) (p ·ᶜ η)) ⟩
  q ·ᶜ η +ᶜ δ <* Ψ +ᶜ γ <* Ψ +ᶜ p ·ᶜ η
    ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
  (q ·ᶜ η +ᶜ δ <* Ψ) +ᶜ γ <* Ψ +ᶜ p ·ᶜ η
    ≈⟨ +ᶜ-congˡ (+ᶜ-comm (γ <* Ψ) (p ·ᶜ η)) ⟩
  (q ·ᶜ η +ᶜ δ <* Ψ) +ᶜ p ·ᶜ η +ᶜ γ <* Ψ
    ≈⟨ +ᶜ-comm _ _ ⟩
  ((p ·ᶜ η +ᶜ γ <* Ψ) +ᶜ q ·ᶜ η +ᶜ δ <* Ψ) ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- Modality substitution application distributes over context scaling.
-- (pγ) <* Ψ ≡ p ·ᶜ (γ <* Ψ).
-- Proof by induction on Ψ using zero and associtivity of multiplication,
-- and distributivity of multiplication over addition.

<*-distrib-·ᶜ : (Ψ : Substₘ m n) (p : M) (γ : Conₘ n)
              → (p ·ᶜ γ) <* Ψ ≈ᶜ p ·ᶜ (γ <* Ψ)
<*-distrib-·ᶜ [] p ε = ≈ᶜ-sym (·ᶜ-zeroʳ p)
<*-distrib-·ᶜ (Ψ ⊙ δ) p (γ ∙ q) = begin
  (p · q) ·ᶜ δ +ᶜ (p ·ᶜ γ) <* Ψ  ≈⟨ +ᶜ-cong (·ᶜ-assoc p q δ) (<*-distrib-·ᶜ Ψ p γ) ⟩
  p ·ᶜ (q ·ᶜ δ) +ᶜ p ·ᶜ (γ <* Ψ) ≈˘⟨ ·ᶜ-distribˡ-+ᶜ p (q ·ᶜ δ) (γ <* Ψ) ⟩
  p ·ᶜ (q ·ᶜ δ +ᶜ γ <* Ψ)        ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- Modality substitution application is linear, i.e. distributes over addition and scaling.
-- (pγ +ᶜ qδ) <* Ψ ≡ p ·ᶜ (γ <* Ψ) +ᶜ q ·ᶜ (δ <* Ψ).
-- Follows from the distributivity over addition and multiplication.

<*-linear : (Ψ : Substₘ m n) (p q : M) (γ δ : Conₘ n)
          → (p ·ᶜ γ +ᶜ q ·ᶜ δ) <* Ψ ≈ᶜ p ·ᶜ γ <* Ψ +ᶜ q ·ᶜ δ <* Ψ
<*-linear Ψ p q γ δ = begin
  (p ·ᶜ γ +ᶜ q ·ᶜ δ) <* Ψ        ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) (q ·ᶜ δ) ⟩
  (p ·ᶜ γ) <* Ψ +ᶜ (q ·ᶜ δ) <* Ψ ≈⟨ +ᶜ-cong (<*-distrib-·ᶜ Ψ p γ) (<*-distrib-·ᶜ Ψ q δ) ⟩
  (p ·ᶜ γ <* Ψ +ᶜ q ·ᶜ δ <* Ψ)   ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

<*-sub-distrib-∧ᶜ : (Ψ : Substₘ m n) (γ δ : Conₘ n) → (γ ∧ᶜ δ) <* Ψ ≤ᶜ γ <* Ψ ∧ᶜ δ <* Ψ
<*-sub-distrib-∧ᶜ [] ε ε = begin
  𝟘ᶜ        ≈˘⟨ ∧ᶜ-idem _ ⟩
  𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
<*-sub-distrib-∧ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) = begin
  (p ∧ q) ·ᶜ η +ᶜ (γ ∧ᶜ δ) <* Ψ             ≤⟨ +ᶜ-monotone (≤ᶜ-reflexive (·ᶜ-distribʳ-∧ᶜ _ _ _))
                                                          (<*-sub-distrib-∧ᶜ Ψ γ δ) ⟩
  (p ·ᶜ η ∧ᶜ q ·ᶜ η) +ᶜ (γ <* Ψ ∧ᶜ δ <* Ψ)  ≤⟨ +ᶜ-sub-interchangeable-∧ᶜ _ _ _ _ ⟩
  (p ·ᶜ η +ᶜ γ <* Ψ) ∧ᶜ q ·ᶜ η +ᶜ δ <* Ψ    ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- Modality substitution application sub-distributes over the two first arguments of ⊛ᶜ
-- γ ⊛ᶜ δ ▷ r <* Ψ ≤ (γ <* Ψ) ⊛ (δ <* Ψ) ▷ r
-- Proof by induction on Ψ using sub-distributivity and interchange properties of ⊛ᶜ

<*-sub-distrib-⊛ᶜ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  (Ψ : Substₘ m n) (γ δ : Conₘ n) (r : M) →
  (γ ⊛ᶜ δ ▷ r) <* Ψ ≤ᶜ (γ <* Ψ) ⊛ᶜ (δ <* Ψ) ▷ r
<*-sub-distrib-⊛ᶜ [] ε ε r = ≤ᶜ-reflexive (≈ᶜ-sym (⊛ᶜ-idem-𝟘ᶜ r))
<*-sub-distrib-⊛ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) r = begin
  ((γ ∙ p) ⊛ᶜ (δ ∙ q) ▷ r) <* (Ψ ⊙ η)
      ≡⟨⟩
  (γ ⊛ᶜ δ ▷ r ∙ p ⊛ q ▷ r) <* (Ψ ⊙ η)
      ≡⟨⟩
  p ⊛ q ▷ r ·ᶜ η +ᶜ (γ ⊛ᶜ δ ▷ r) <* Ψ
      ≤⟨ +ᶜ-monotone (·ᶜ-sub-distribʳ-⊛ p q r η) (<*-sub-distrib-⊛ᶜ Ψ γ δ r) ⟩
  (p ·ᶜ η) ⊛ᶜ (q ·ᶜ η) ▷ r +ᶜ (γ <* Ψ) ⊛ᶜ (δ <* Ψ) ▷ r
      ≤⟨ +ᶜ-sub-interchangeable-⊛ᶜ r (p ·ᶜ η) (q ·ᶜ η) (γ <* Ψ) (δ <* Ψ) ⟩
  (p ·ᶜ η +ᶜ γ <* Ψ) ⊛ᶜ (q ·ᶜ η +ᶜ δ <* Ψ) ▷ r
      ≡⟨⟩
  ((γ ∙ p) <* (Ψ ⊙ η)) ⊛ᶜ ((δ ∙ q) <* (Ψ ⊙ η)) ▷ r ∎
  where open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The function _<* Ψ sub-distributes over nrᶜ p r.

<*-sub-distrib-nrᶜ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  nrᶜ p r γ δ η <* Ψ ≤ᶜ nrᶜ p r (γ <* Ψ) (δ <* Ψ) (η <* Ψ)
<*-sub-distrib-nrᶜ {p = p} {r = r} {δ = ε} {η = ε} [] ε = begin
  𝟘ᶜ                ≈˘⟨ nrᶜ-𝟘ᶜ ⟩
  nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
<*-sub-distrib-nrᶜ
  {p = p} {r = r} {δ = δ ∙ s} {η = η ∙ n} (Ψ ⊙ θ) (γ ∙ z) = begin
  nr p r z s n ·ᶜ θ +ᶜ nrᶜ p r γ δ η <* Ψ                           ≤⟨ +ᶜ-monotone nrᶜ-·ᶜ (<*-sub-distrib-nrᶜ Ψ γ) ⟩

  nrᶜ p r (z ·ᶜ θ) (s ·ᶜ θ) (n ·ᶜ θ) +ᶜ
  nrᶜ p r (γ <* Ψ) (δ <* Ψ) (η <* Ψ)                                ≤⟨ nrᶜ-+ᶜ ⟩

  nrᶜ p r (z ·ᶜ θ +ᶜ γ <* Ψ) (s ·ᶜ θ +ᶜ δ <* Ψ) (n ·ᶜ θ +ᶜ η <* Ψ)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

--- The zero-context is a left zero to modality substitution application.
-- 𝟘ᶜ <* Ψ ≡ 𝟘ᶜ.
-- Proof by induction on Ψ using zero of multiplication and identity of addition.

<*-zeroˡ : (Ψ : Substₘ m n) → 𝟘ᶜ <* Ψ ≈ᶜ 𝟘ᶜ
<*-zeroˡ []      = ≈ᶜ-refl
<*-zeroˡ (Ψ ⊙ γ) = begin
  𝟘ᶜ <* (Ψ ⊙ γ)       ≡⟨⟩
  𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ <* Ψ) ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ γ) (<*-zeroˡ Ψ) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ            ≈⟨ +ᶜ-identityˡ 𝟘ᶜ ⟩
  𝟘ᶜ                  ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- The substitution family εₘ is a kind of right zero for _<*_.

<*-zeroʳ : (γ : Conₘ n) → γ <* εₘ ≈ᶜ ε
<*-zeroʳ ε       = ε
<*-zeroʳ (γ ∙ p) = begin
  ε +ᶜ γ <* εₘ  ≈⟨ +ᶜ-congˡ (<*-zeroʳ γ) ⟩
  ε +ᶜ ε        ≈⟨ +ᶜ-identityˡ _ ⟩
  ε             ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

-- Modality substitution application is a monotone function.
-- If γ ≤ᶜ δ, then γ <* Ψ ≤ᶜ δ <* Ψ.
-- Proof by induction on Ψ using monotonicity of addition and multiplication.

<*-monotone : {γ δ : Conₘ n} (Ψ : Substₘ m n) → γ ≤ᶜ δ → γ <* Ψ ≤ᶜ δ <* Ψ
<*-monotone {γ = ε}     {δ = ε}     []      γ≤δ         = ≤ᶜ-refl
<*-monotone {γ = _ ∙ _} {δ = _ ∙ _} (Ψ ⊙ η) (γ≤δ ∙ p≤q) =
  +ᶜ-monotone (·ᶜ-monotoneˡ p≤q) (<*-monotone Ψ γ≤δ)

-- The function  <*_Ψ preserves equivalence.

<*-cong : (Ψ : Substₘ m n) → γ ≈ᶜ δ → γ <* Ψ ≈ᶜ δ <* Ψ
<*-cong Ψ γ≈ᶜδ = ≤ᶜ-antisym
  (<*-monotone Ψ (≤ᶜ-reflexive γ≈ᶜδ))
  (<*-monotone Ψ (≤ᶜ-reflexive (≈ᶜ-sym γ≈ᶜδ)))

-- Matrix/vector multiplication is associative.
-- γ <* (Ψ <*> Φ) ≡ (γ <* Φ) <* Ψ.
-- Proof by induction on γ using linearity of matrix multiplication.

<*-<*>-assoc : {ℓ m n : Nat} (Ψ : Substₘ m n) (Φ : Substₘ n ℓ) (γ : Conₘ ℓ)
             → γ <* (Ψ <*> Φ) ≈ᶜ (γ <* Φ) <* Ψ
<*-<*>-assoc Ψ [] ε = ≈ᶜ-sym (<*-zeroˡ Ψ)
<*-<*>-assoc Ψ (Φ ⊙ δ) (γ ∙ p) = begin
  p ·ᶜ (δ <* Ψ) +ᶜ γ <* (Ψ <*> Φ) ≈⟨ +ᶜ-cong (≈ᶜ-sym (<*-distrib-·ᶜ Ψ p δ)) (<*-<*>-assoc Ψ Φ γ) ⟩
  (p ·ᶜ δ) <* Ψ +ᶜ (γ <* Φ) <* Ψ  ≈˘⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ δ) (γ <* Φ) ⟩
  (p ·ᶜ δ +ᶜ γ <* Φ) <* Ψ        ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- A corollary.

·ᶜ-<*-𝟘ᶜ,≔𝟙 :
  (Ψ : Substₘ m n) →
  p ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ ≈ᶜ (𝟘ᶜ , x ≔ p) <* Ψ
·ᶜ-<*-𝟘ᶜ,≔𝟙 {p = p} {x = x} Ψ = begin
  p ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ      ≈˘⟨ <*-distrib-·ᶜ Ψ _ (𝟘ᶜ , x ≔ 𝟙) ⟩
  (p ·ᶜ (𝟘ᶜ , x ≔ 𝟙)) <* Ψ    ≡˘⟨ cong (_<* Ψ) (update-distrib-·ᶜ 𝟘ᶜ p 𝟙 x) ⟩
  (p ·ᶜ 𝟘ᶜ , x ≔ p · 𝟙) <* Ψ  ≈⟨ <*-cong Ψ (update-cong (·ᶜ-zeroʳ _) (·-identityʳ _)) ⟩
  (𝟘ᶜ , x ≔ p) <* Ψ           ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

------------------------------------------
-- Properties of specific substitutions --
------------------------------------------

-- Application of a shifted substitution.
-- γ <* wk1Substₘ Ψ ≡ (γ <* Ψ) ∙ 𝟘.
-- Proof by induction on γ using identity of addition and zero of multiplication

wk1Substₘ-app : (Ψ : Substₘ m n) (γ : Conₘ n) → γ <* wk1Substₘ Ψ ≈ᶜ (γ <* Ψ) ∙ 𝟘
wk1Substₘ-app [] ε            = ≈ᶜ-refl
wk1Substₘ-app (Ψ ⊙ δ) (γ ∙ p) = begin
  (γ ∙ p) <* wk1Substₘ (Ψ ⊙ δ) ≡⟨⟩
  ((p ·ᶜ δ) ∙ (p · 𝟘)) +ᶜ γ <* wk1Substₘ Ψ
      ≈⟨ +ᶜ-cong (≈ᶜ-refl ∙ (·-zeroʳ p)) (wk1Substₘ-app Ψ γ) ⟩
  ((p ·ᶜ δ) ∙ 𝟘) +ᶜ ((γ <* Ψ) ∙ 𝟘)
      ≡⟨⟩
  (p ·ᶜ δ) +ᶜ (γ <* Ψ) ∙ (𝟘 + 𝟘)
     ≈⟨ ≈ᶜ-refl ∙ (+-identityˡ 𝟘) ⟩
  ((γ ∙ p) <* (Ψ ⊙ δ)) ∙ 𝟘         ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid


-- Application of a lifted substitution.
-- (γ ∙ p) <* liftSubstₘ Ψ ≡ (γ <* Ψ) ∙ p.
-- Proof by induction on γ using lemma on application of a shifted substitution.

liftSubstₘ-app : (Ψ : Substₘ m n) (γ : Conₘ n) (p : M)
               → (γ ∙ p) <* liftSubstₘ Ψ ≈ᶜ (γ <* Ψ) ∙ p
liftSubstₘ-app [] ε p = begin
  (ε ∙ p) <* liftSubstₘ []   ≡⟨⟩
  (ε ∙ p) <* ([] ⊙ (𝟘ᶜ ∙ 𝟙)) ≡⟨⟩
  p ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ 𝟘ᶜ         ≡⟨⟩
  ((p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)) +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ _ ⟩
  (p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)        ≈⟨ (·ᶜ-zeroʳ p) ∙ (·-identityʳ p) ⟩
  𝟘ᶜ ∙ p                     ≡⟨⟩
  (ε <* []) ∙ p ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

liftSubstₘ-app (Ψ ⊙ η) γ p = begin
  (γ ∙ p) <* liftSubstₘ (Ψ ⊙ η)
     ≡⟨⟩
  (γ ∙ p) <* (wk1Substₘ (Ψ ⊙ η) ⊙ (𝟘ᶜ ∙ 𝟙))
     ≡⟨⟩
  p ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ (γ <* wk1Substₘ (Ψ ⊙ η))
     ≈⟨ +ᶜ-cong ((·ᶜ-zeroʳ p) ∙ (·-identityʳ p)) (wk1Substₘ-app (Ψ ⊙ η) γ) ⟩
  (𝟘ᶜ ∙ p) +ᶜ ((γ <* (Ψ ⊙ η)) ∙ 𝟘)
     ≈⟨ (+ᶜ-identityˡ (γ <* (Ψ ⊙ η))) ∙ (+-identityʳ p) ⟩
  (γ <* (Ψ ⊙ η)) ∙ p ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- The identity matrix is a left identity to substitution application.
-- γ <* idSubstₘ ≡ γ.
-- Proof by identity of addition, multiplication and matrix multiplication,
-- zero of multiplication and lemma on the application of shifted substitution matrices.

<*-identityˡ : (γ : Conₘ n) → γ <* idSubstₘ ≈ᶜ γ
<*-identityˡ ε       = ≈ᶜ-refl
<*-identityˡ (γ ∙ p) = begin
  (γ ∙ p) <* idSubstₘ ≡⟨⟩
  ((p ·ᶜ 𝟘ᶜ) ∙ (p · 𝟙)) +ᶜ (γ <* wk1Substₘ idSubstₘ)
    ≈⟨ +ᶜ-cong ((·ᶜ-zeroʳ p) ∙ (·-identityʳ p)) (wk1Substₘ-app idSubstₘ γ) ⟩
  ((𝟘ᶜ ∙ p) +ᶜ ((γ <* idSubstₘ) ∙ 𝟘))
    ≈⟨ (+ᶜ-identityˡ _) ∙ (+-identityʳ p) ⟩
  (γ <* idSubstₘ) ∙ p
    ≈⟨ (<*-identityˡ γ) ∙ refl ⟩
  γ ∙ p ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-------------------------------
-- Well-formed substitutions --
-------------------------------

-- The substitution of a single variable is well-formed if the
-- substituted term is suitably well-resourced.

wf-sgSubstₘ :
  ⌜ mo ⌝ ·ᶜ γ ▸[ mo ] u → sgSubstₘ γ ▶[ consᵐ mo mos ] sgSubst u
wf-sgSubstₘ {mo = mo} {γ = γ} γ▸u x0 = sub
  γ▸u
  (begin
     ⌜ mo ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ <* idSubstₘ  ≈⟨ +ᶜ-congˡ (<*-identityˡ 𝟘ᶜ) ⟩
     ⌜ mo ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ              ≈⟨ +ᶜ-identityʳ _ ⟩
     ⌜ mo ⌝ ·ᶜ γ                    ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wf-sgSubstₘ {γ = γ} {mos = mos} _ (x +1) = sub
  var
  (begin
     𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* idSubstₘ  ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ γ) (<*-identityˡ _) ⟩
     𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝)                  ≈⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ , x ≔ ⌜ mos x ⌝                          ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The one-step weakening of a well-formed substitution is
-- well-formed.

wf-wk1Substₘ : (Ψ : Substₘ m n) (σ : Subst m n)
             → Ψ ▶[ mos ] σ → wk1Substₘ Ψ ▶[ mos ] wk1Subst σ
wf-wk1Substₘ Ψ σ Ψ▶σ x =
  sub (wkUsage (step id) (Ψ▶σ x)) (≤ᶜ-reflexive (wk1Substₘ-app Ψ (𝟘ᶜ , x ≔ _)))

-- The one-step lift of a well-formed substitution is well-formed.

wf-liftSubstₘ :
  {Ψ : Substₘ m n} →
  Ψ ▶[ mos ] σ → liftSubstₘ Ψ ▶[ consᵐ mo mos ] liftSubst σ
wf-liftSubstₘ {mo = mo} {Ψ = Ψ} _ x0 = sub
  var
  (begin
     (⌜ mo ⌝ ·ᶜ 𝟘ᶜ ∙ ⌜ mo ⌝ · 𝟙) +ᶜ 𝟘ᶜ <* wk1Substₘ Ψ  ≈⟨ +ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) (<*-zeroˡ (wk1Substₘ Ψ)) ⟩
     (𝟘ᶜ ∙ ⌜ mo ⌝) +ᶜ 𝟘ᶜ                               ≈⟨ +ᶜ-identityʳ _ ⟩
     𝟘ᶜ ∙ ⌜ mo ⌝                                       ≡⟨⟩
     𝟘ᶜ , x0 ≔ ⌜ mo ⌝                                  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wf-liftSubstₘ {mos = mos} {Ψ = Ψ} Ψ▶σ (x +1) = sub
  (wf-wk1Substₘ Ψ _ Ψ▶σ x)
  (begin
    (𝟘 ·ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟙) +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* wk1Substₘ Ψ  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-zeroˡ _) ⟩
    𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* wk1Substₘ Ψ                 ≈⟨ +ᶜ-identityˡ _ ⟩
    (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* wk1Substₘ Ψ                       ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The extension of a well-formed substitution with a suitably
-- well-resourced term is a well-formed substitution.

wf-consSubstₘ :
  {Ψ : Substₘ m n} {γ : Conₘ m} →
  Ψ ▶[ mos ] σ → ⌜ mo ⌝ ·ᶜ γ ▸[ mo ] t →
  Ψ ⊙ γ ▶[ consᵐ mo mos ] consSubst σ t
wf-consSubstₘ {mo = mo} {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t x0 = sub
  γ▸t
  (begin
     ⌜ mo ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ <* Ψ ≈⟨ +ᶜ-congˡ (<*-zeroˡ Ψ) ⟩
     ⌜ mo ⌝ ·ᶜ γ +ᶜ 𝟘ᶜ       ≈⟨ +ᶜ-identityʳ _ ⟩
     ⌜ mo ⌝ ·ᶜ γ             ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
wf-consSubstₘ {mos = mos} {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t (x +1) = sub
  (Ψ▶σ x)
  (begin
     𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
     𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ     ≈⟨ +ᶜ-identityˡ _ ⟩
     (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ           ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- The tail of a well-formed substitution is a well-formed
-- substitution.

wf-tailSubstₘ :
  {Ψ : Substₘ m n} →
  (Ψ ⊙ γ) ▶[ mos ] σ → Ψ ▶[ tailᵐ mos ] tail σ
wf-tailSubstₘ Ψ▶σ x =
  sub (Ψ▶σ (x +1))
      (≤ᶜ-reflexive (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ _)) (+ᶜ-identityˡ _))))

-- A preservation lemma for _▶[_]_.

▶-cong :
  (Ψ : Substₘ m n) →
  (∀ x → mos₁ x ≡ mos₂ x) → Ψ ▶[ mos₁ ] σ → Ψ ▶[ mos₂ ] σ
▶-cong Ψ mos₁≡mos₂ Ψ▶ x0 =
  PE.subst (λ mo → (𝟘ᶜ ∙ ⌜ mo ⌝) <* Ψ ▸[ mo ] _) (mos₁≡mos₂ x0) (Ψ▶ x0)
▶-cong {mos₁ = mos₁} {mos₂ = mos₂} (Ψ ⊙ γ) mos₁≡mos₂ Ψ⊙▶ (x +1) = sub
  (▶-cong Ψ (λ x → mos₁≡mos₂ (x +1))
    (λ x → sub (Ψ⊙▶ (x +1)) (≤ᶜ-reflexive (≈ᶜ-sym (lemma mos₁ x))))
    x)
  (≤ᶜ-reflexive (lemma mos₂ x))
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

  lemma = λ mos x → begin
     𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝) <* Ψ  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
     𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝) <* Ψ      ≈⟨ +ᶜ-identityˡ _ ⟩
     (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝) <* Ψ            ∎

-- Another preservation lemma for _▶[_]_.

▶-≤ :
  (Ψ : Substₘ m n) →
  γ ≤ᶜ δ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-≤ Ψ γ≤δ Ψ▶ x = sub
  (▸-≤ (lookup-monotone _ γ≤δ)
     (sub (Ψ▶ x) (≤ᶜ-reflexive (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ))))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))

-- A preservation lemma for _▶[_]_ that holds if 𝟘ᵐ is not allowed.

▶-without-𝟘ᵐ :
  (Ψ : Substₘ m n) →
  ¬ T 𝟘ᵐ-allowed →
  Ψ ▶[ mos₁ ] σ → Ψ ▶[ mos₂ ] σ
▶-without-𝟘ᵐ Ψ not-ok =
  ▶-cong Ψ (λ _ → Mode-propositional-without-𝟘ᵐ not-ok)

-- An inversion lemma for _▶[_]_ related to multiplication.

▶-⌞·⌟ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ p ·ᶜ γ ⌟ᶜ ] σ →
  (p ≡ 𝟘 × T 𝟘ᵐ-allowed) ⊎ (Ψ ▶[ ⌞ γ ⌟ᶜ ] σ)
▶-⌞·⌟ {p = p} {σ = σ} Ψ γ Ψ▶ = 𝟘ᵐ-allowed-elim
  (λ ok → case is-𝟘? p of λ where
     (yes p≡𝟘) → inj₁ (p≡𝟘 , ok)
     (no p≢𝟘)  → inj₂ λ x →
       case ▸-⌞·⌟
         (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-·ᶜ γ _ _)) (Ψ▶ x))
            (begin
               ⌜ ⌞ p · γ ⟨ x ⟩ ⌟ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
               (𝟘ᶜ , x ≔ ⌜ ⌞ p · γ ⟨ x ⟩ ⌟ ⌝) <* Ψ      ≡˘⟨ cong (λ p → (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) <* Ψ)
                                                                (lookup-distrib-·ᶜ γ _ _) ⟩
               (𝟘ᶜ , x ≔ ⌜ ⌞ p ·ᶜ γ ⌟ᶜ x ⌝) <* Ψ         ∎))
       of λ where
         (inj₂ ▸γx) → sub ▸γx (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
         (inj₁ ▸p)  → lemma _ _ _ (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸p)
  (λ not-ok → inj₂ (▶-without-𝟘ᵐ Ψ not-ok Ψ▶))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

  lemma :
    ∀ mo₁ mo₂ x →
    mo₁ ≡ 𝟙ᵐ →
    ⌜ mo₁ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ ▸[ mo₁ ] t →
    (𝟘ᶜ , x ≔ ⌜ mo₂ ⌝) <* Ψ ▸[ mo₂ ] t
  lemma 𝟙ᵐ 𝟘ᵐ x _ ▸t = sub (▸-𝟘 ▸t)
    (begin
       (𝟘ᶜ , x ≔ 𝟘) <* Ψ  ≡⟨ cong (_<* Ψ) 𝟘ᶜ,≔𝟘 ⟩
       𝟘ᶜ <* Ψ            ≈⟨ <*-zeroˡ Ψ ⟩
       𝟘ᶜ                 ∎)
  lemma 𝟙ᵐ 𝟙ᵐ x _ ▸t = sub ▸t
    (begin
       (𝟘ᶜ , x ≔ 𝟙) <* Ψ       ≈˘⟨ ·ᶜ-identityˡ _ ⟩
       𝟙 ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ∎)

-- An inversion lemma for _▶[_]_ related to addition.

▶-⌞+ᶜ⌟ˡ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ +ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
▶-⌞+ᶜ⌟ˡ {δ = δ} Ψ γ Ψ▶ x = sub
  (▸-⌞+⌟ˡ
     (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-+ᶜ γ _ _)) (Ψ▶ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ + δ ⟨ x ⟩ ⌟ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⟨ x ⟩ + δ ⟨ x ⟩ ⌟ ⌝) <* Ψ      ≡˘⟨ cong (λ p → (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) <* Ψ)
                                                             (lookup-distrib-+ᶜ γ _ _) ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ γ +ᶜ δ ⌟ᶜ x ⌝) <* Ψ               ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to addition.

▶-⌞+ᶜ⌟ʳ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ +ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-⌞+ᶜ⌟ʳ {δ = δ} Ψ γ Ψ▶ =
  ▶-⌞+ᶜ⌟ˡ Ψ δ (▶-cong Ψ (⌞⌟ᶜ-cong (+ᶜ-comm γ _)) Ψ▶)

-- An inversion lemma for _▸[_]_ related to _<*_.

▸-⌞<*⌟ :
  (Ψ : Substₘ m n) →
  ⌜ ⌞ γ <* Ψ ⌟ᶜ y ⌝ ·ᶜ δ ▸[ ⌞ γ <* Ψ ⌟ᶜ y ] t →
  ⌜ ⌞ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ ⌟ᶜ y ⌝ ·ᶜ δ
    ▸[ ⌞ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ ⌟ᶜ y ] t
▸-⌞<*⌟ {γ = γ ∙ p} {y = y} {δ = δ} {t = t} {x = x0} (Ψ ⊙ η) ▸₁ = ▸₄
  where
  ▸₂ :
    ⌜ ⌞ (p ·ᶜ η) ⟨ y ⟩ + (γ <* Ψ) ⟨ y ⟩ ⌟ ⌝ ·ᶜ δ
      ▸[ ⌞ (p ·ᶜ η) ⟨ y ⟩ + (γ <* Ψ) ⟨ y ⟩ ⌟ ] t
  ▸₂ = PE.subst
    (λ γ → ⌜ ⌞ γ ⌟ ⌝ ·ᶜ _ ▸[ ⌞ γ ⌟ ] _)
    (lookup-distrib-+ᶜ (_ ·ᶜ η) _ _)
    ▸₁

  ▸₃ : ⌜ ⌞ p ·ᶜ η ⌟ᶜ y ⌝ ·ᶜ δ ▸[ ⌞ p ·ᶜ η ⌟ᶜ y ] t
  ▸₃ = ▸-⌞+⌟ˡ ▸₂

  ▸₄ :
    ⌜ ⌞ p ·ᶜ η +ᶜ (𝟘ᶜ <* Ψ) ⌟ᶜ y ⌝ ·ᶜ δ
      ▸[ ⌞ p ·ᶜ η +ᶜ (𝟘ᶜ <* Ψ) ⌟ᶜ y ] t
  ▸₄ = PE.subst
    (λ m → ⌜ m ⌝ ·ᶜ δ ▸[ m ] t)
    (⌞⌟-cong (lookup-cong (begin
       p ·ᶜ η               ≈˘⟨ +ᶜ-identityʳ _ ⟩
       p ·ᶜ η +ᶜ 𝟘ᶜ         ≈˘⟨ +ᶜ-congˡ (<*-zeroˡ Ψ) ⟩
       p ·ᶜ η +ᶜ (𝟘ᶜ <* Ψ)  ∎)))
    ▸₃
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

▸-⌞<*⌟ {γ = γ ∙ p} {y = y} {δ = δ} {t = t} {x = x +1} (Ψ ⊙ η) ▸₁ = ▸₅
  where
  ▸₂ :
    ⌜ ⌞ (p ·ᶜ η) ⟨ y ⟩ + (γ <* Ψ) ⟨ y ⟩ ⌟ ⌝ ·ᶜ δ
      ▸[ ⌞ (p ·ᶜ η) ⟨ y ⟩ + (γ <* Ψ) ⟨ y ⟩ ⌟ ] t
  ▸₂ = PE.subst
    (λ γ → ⌜ ⌞ γ ⌟ ⌝ ·ᶜ _ ▸[ ⌞ γ ⌟ ] _)
    (lookup-distrib-+ᶜ (_ ·ᶜ η) _ _)
    ▸₁

  ▸₃ : ⌜ ⌞ γ <* Ψ ⌟ᶜ y ⌝ ·ᶜ δ ▸[ ⌞ γ <* Ψ ⌟ᶜ y ] t
  ▸₃ = ▸-⌞+⌟ʳ ▸₂

  ▸₄ : ⌜ ⌞ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ ⌟ᶜ y ⌝ ·ᶜ δ
         ▸[ ⌞ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ ⌟ᶜ y ] t
  ▸₄ = ▸-⌞<*⌟ {γ = γ} Ψ ▸₃

  ▸₅ :
    ⌜ ⌞ 𝟘 ·ᶜ η +ᶜ ((𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ) ⌟ᶜ y ⌝ ·ᶜ δ
      ▸[ ⌞ 𝟘 ·ᶜ η +ᶜ ((𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ) ⌟ᶜ y ] t
  ▸₅ = PE.subst
    (λ m → ⌜ m ⌝ ·ᶜ δ ▸[ m ] t)
    (⌞⌟-cong (lookup-cong (begin
       (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ            ≈˘⟨ +ᶜ-identityˡ ((𝟘ᶜ , _ ≔ _) <* Ψ) ⟩
       𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ η) ⟩
       𝟘 ·ᶜ η +ᶜ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ  ∎)))
    ▸₄
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

-- An inversion lemma for _▶[_]_ related to _<*_.

▶-⌞<*⌟ :
  (Ψ : Substₘ ℓ m) {Φ : Substₘ m n} →
  Ψ ▶[ ⌞ γ <* Φ ⌟ᶜ ] σ →
  Ψ ▶[ ⌞ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Φ ⌟ᶜ ] σ
▶-⌞<*⌟ {γ = γ} {x = x} Ψ {Φ = Φ} Ψ▶ y = sub
  (▸-⌞<*⌟ {γ = γ} Φ (sub (Ψ▶ y) (≤ᶜ-reflexive (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ))))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))

-- An inversion lemma for _▶[_]_ related to the meet operation.

▶-⌞∧ᶜ⌟ˡ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ ∧ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
▶-⌞∧ᶜ⌟ˡ {δ = δ} Ψ γ Ψ▶ x = sub
  (▸-⌞∧⌟ˡ
     (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-∧ᶜ γ _ _)) (Ψ▶ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ ∧ δ ⟨ x ⟩ ⌟ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⟨ x ⟩ ∧ δ ⟨ x ⟩ ⌟ ⌝) <* Ψ       ≡˘⟨ cong (λ p → (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) <* Ψ)
                                                                     (lookup-distrib-∧ᶜ γ _ _) ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ γ ∧ᶜ δ ⌟ᶜ x ⌝) <* Ψ               ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to the meet operation.

▶-⌞∧ᶜ⌟ʳ :
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ ∧ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-⌞∧ᶜ⌟ʳ {δ = δ} Ψ γ Ψ▶ =
  ▶-⌞∧ᶜ⌟ˡ Ψ δ (▶-cong Ψ (⌞⌟ᶜ-cong (∧ᶜ-comm γ _)) Ψ▶)

-- An inversion lemma for _▶[_]_ related to the star operation.

▶-⌞⊛ᶜ⌟ˡ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
▶-⌞⊛ᶜ⌟ˡ {δ = δ} {r = r} Ψ γ Ψ▶ x = sub
  (▸-⌞⊛⌟ˡ
     (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-⊛ᶜ γ _ _ _)) (Ψ▶ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ ⊛ δ ⟨ x ⟩ ▷ r ⌟ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ≡˘⟨ cong (λ p → ⌜ ⌞ p ⌟ ⌝ ·ᶜ _)
                                                                  (lookup-distrib-⊛ᶜ γ _ _ _) ⟩
        ⌜ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ          ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ x ⌝) <* Ψ               ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to the star operation.

▶-⌞⊛ᶜ⌟ʳ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-⌞⊛ᶜ⌟ʳ {δ = δ} {r = r} Ψ γ Ψ▶ x = sub
  (▸-⌞⊛⌟ʳ
     (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-⊛ᶜ γ _ _ _)) (Ψ▶ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ ⊛ δ ⟨ x ⟩ ▷ r ⌟ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ≡˘⟨ cong (λ p → ⌜ ⌞ p ⌟ ⌝ ·ᶜ _)
                                                                   (lookup-distrib-⊛ᶜ γ _ _ _) ⟩
        ⌜ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ          ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⊛ᶜ δ ▷ r ⌟ᶜ x ⌝) <* Ψ               ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to the nr function.

▶-⌞nrᶜ⌟₁ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ nrᶜ p r γ δ η ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
▶-⌞nrᶜ⌟₁ {p = p} {r = r} {δ = δ} {η = η} Ψ γ Ψ▶ x = sub
  (▸-⌞nr⌟₁
     (sub (▸-cong (cong ⌞_⌟ (nrᶜ-⟨⟩ γ)) (Ψ▶ x)) (begin
        ⌜ ⌞ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ⌟ ⌝ ·ᶜ
        (𝟘ᶜ , x ≔ 𝟙) <* Ψ                                ≡˘⟨ cong (λ p → ⌜ ⌞ p ⌟ ⌝ ·ᶜ _)
                                                               (nrᶜ-⟨⟩ γ) ⟩
        ⌜ ⌞ nrᶜ p r γ δ η ⌟ᶜ x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ    ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ nrᶜ p r γ δ η ⌟ᶜ x ⌝) <* Ψ         ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to the nr function.

▶-⌞nrᶜ⌟₂ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ nrᶜ p r γ δ η ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
▶-⌞nrᶜ⌟₂ {p = p} {r = r} {δ = δ} {η = η} Ψ γ Ψ▶ x = sub
  (▸-⌞nr⌟₂
     (sub (▸-cong (cong ⌞_⌟ (nrᶜ-⟨⟩ γ)) (Ψ▶ x)) (begin
        ⌜ ⌞ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ⌟ ⌝ ·ᶜ
        (𝟘ᶜ , x ≔ 𝟙) <* Ψ                                ≡˘⟨ cong (λ p → ⌜ ⌞ p ⌟ ⌝ ·ᶜ _)
                                                               (nrᶜ-⟨⟩ γ) ⟩
        ⌜ ⌞ nrᶜ p r γ δ η ⌟ᶜ x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ    ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ nrᶜ p r γ δ η ⌟ᶜ x ⌝) <* Ψ         ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for _▶[_]_ related to the nr function.

▶-⌞nrᶜ⌟₃ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (Ψ : Substₘ m n) (γ : Conₘ n) →
  Ψ ▶[ ⌞ nrᶜ p r γ δ η ⌟ᶜ ] σ → Ψ ▶[ ⌞ η ⌟ᶜ ] σ
▶-⌞nrᶜ⌟₃ {p = p} {r = r} {δ = δ} {η = η} Ψ γ Ψ▶ x = sub
  (▸-⌞nr⌟₃
     (sub (▸-cong (cong ⌞_⌟ (nrᶜ-⟨⟩ γ)) (Ψ▶ x)) (begin
        ⌜ ⌞ nr p r (γ ⟨ x ⟩) (δ ⟨ x ⟩) (η ⟨ x ⟩) ⌟ ⌝ ·ᶜ
        (𝟘ᶜ , x ≔ 𝟙) <* Ψ                                ≡˘⟨ cong (λ p → ⌜ ⌞ p ⌟ ⌝ ·ᶜ _)
                                                               (nrᶜ-⟨⟩ γ) ⟩
        ⌜ ⌞ nrᶜ p r γ δ η ⌟ᶜ x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ    ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ nrᶜ p r γ δ η ⌟ᶜ x ⌝) <* Ψ         ∎)))
  (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

---------------------------------------
-- Substitution lemma for modalities --
---------------------------------------

-- A substitution lemma for the mode 𝟘ᵐ[ ok ]: if σ is well-formed and
-- t is well-resourced with respect to any context and mode, then
-- t [ σ ] is well-resourced with respect to the zero usage context
-- and the mode 𝟘ᵐ[ ok ].
--
-- Proof by induction on t being well resourced.

substₘ-lemma₀ :
  ∀ ⦃ ok ⦄ (Ψ : Substₘ m n) →
  Ψ ▶[ mos ] σ → γ ▸[ mo ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t [ σ ]

private

  -- A lemma which is used in the proof of substₘ-lemma₀.

  substₘ-lemma₀-𝟘ᵐ? :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ (Ψ : Substₘ m n) →
    Ψ ▶[ mos ] σ → γ ▸[ mo ] t → 𝟘ᶜ ▸[ 𝟘ᵐ? ] t [ σ ]
  substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶ γ▸ =
    ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) (substₘ-lemma₀ Ψ Ψ▶ γ▸)

substₘ-lemma₀ _ _ Uₘ =
  Uₘ

substₘ-lemma₀ _ _ ℕₘ =
  ℕₘ

substₘ-lemma₀ _ _ Emptyₘ =
  Emptyₘ

substₘ-lemma₀ _ _ Unitₘ =
  Unitₘ

substₘ-lemma₀ Ψ Ψ▶σ (ΠΣₘ {p = p} γ▸F δ▸G) = sub
  (ΠΣₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸F)
     (sub (substₘ-lemma₀ (liftSubstₘ Ψ) (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ)
             δ▸G)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _))))
  (≤ᶜ-reflexive (≈ᶜ-sym (+ᶜ-identityˡ _)))

substₘ-lemma₀ Ψ Ψ▶σ (var {x = x}) = ▸-𝟘 (Ψ▶σ x)

substₘ-lemma₀ Ψ Ψ▶σ (lamₘ γ▸t) = lamₘ
  (sub (substₘ-lemma₀ (liftSubstₘ Ψ) (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ) γ▸t)
     (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _)))

substₘ-lemma₀ Ψ Ψ▶σ (_∘ₘ_ {p = p} γ▸t δ▸u) = sub
  (substₘ-lemma₀ Ψ Ψ▶σ γ▸t ∘ₘ
   substₘ-lemma₀ Ψ Ψ▶σ δ▸u)
  (begin
     𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
     𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (prodʷₘ {p = p} γ▸t δ▸u) = sub
  (prodʷₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t) (substₘ-lemma₀ Ψ Ψ▶σ δ▸u))
  (begin
     𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
     p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
     p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (prodˢₘ {p = p} γ▸t γ▸u) = sub
  (prodˢₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t) (substₘ-lemma₀ Ψ Ψ▶σ γ▸u))
  (begin
     𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
     𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
     p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (fstₘ m γ▸t PE.refl ok) =
  fstₘ 𝟘ᵐ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t) PE.refl λ ()

substₘ-lemma₀ Ψ Ψ▶σ (sndₘ γ▸t) =
  sndₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t)

substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ (prodrecₘ {r = r} {q = q} γ▸t δ▸u η▸A P) = sub
  (prodrecₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t)
     (sub (substₘ-lemma₀ (liftSubstₘ (liftSubstₘ Ψ))
             (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ))
             δ▸u)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _)))
     (sub (substₘ-lemma₀-𝟘ᵐ? (liftSubstₘ Ψ)
             (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ) η▸A)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
           𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
           𝟘ᶜ                ∎))
     (Prodrec-allowed-·ᵐ P))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
     r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)

substₘ-lemma₀ _ _ zeroₘ =
  zeroₘ

substₘ-lemma₀ Ψ Ψ▶σ (sucₘ γ▸t) =
  sucₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t)

substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ
  (natrecₘ {p = p} {r = r} {q = q} γ▸z δ▸s η▸n θ▸A) = sub
  (natrecₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸z)
     (sub (substₘ-lemma₀ (liftSubstₘ (liftSubstₘ Ψ))
             (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ))
             δ▸s)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _)))
     (substₘ-lemma₀ Ψ Ψ▶σ η▸n)
     (sub (substₘ-lemma₀-𝟘ᵐ? (liftSubstₘ Ψ)
             (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ) θ▸A)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
           𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
           𝟘ᶜ                ∎)))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ                ≈˘⟨ nrᶜ-𝟘ᶜ ⟩
     nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ∎)
  where
  open import Graded.Modality.Dedicated-nr.Instance

substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ
  (natrec-no-nrₘ {p = p} {r = r} {q = q} γ▸z δ▸s η▸n θ▸A _ _ _ _) =
  natrec-no-nrₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸z)
    (sub (substₘ-lemma₀ (liftSubstₘ (liftSubstₘ Ψ))
            (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ))
            δ▸s)
       (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _)))
    (substₘ-lemma₀ Ψ Ψ▶σ η▸n)
    (sub (substₘ-lemma₀-𝟘ᵐ? (liftSubstₘ Ψ)
            (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ) θ▸A)
       (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
          𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
          𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
          𝟘ᶜ                ∎))
    ≤ᶜ-refl
    (λ _ → ≤ᶜ-refl)
    ≤ᶜ-refl
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ                        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ                  ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _) ⟩
       p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
       𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ  ∎)

substₘ-lemma₀ Ψ Ψ▶σ (emptyrecₘ γ▸t δ▸A) =
  sub (emptyrecₘ (substₘ-lemma₀ Ψ Ψ▶σ γ▸t)
         (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ δ▸A))
    (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-zeroʳ _)))

substₘ-lemma₀ _ _ starʷₘ =
  starʷₘ

substₘ-lemma₀ _ _ (starˢₘ _) =
  sub (starˢₘ (λ _ → ≈ᶜ-refl))
      (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-zeroˡ 𝟘ᶜ)))

substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ (unitrecₘ {p = p} {η = η} {q = q} γ▸t δ▸u η▸A ok′) =
  let γ′▸t = substₘ-lemma₀ Ψ Ψ▶σ γ▸t
      δ′▸u = substₘ-lemma₀ Ψ Ψ▶σ δ▸u
      η′▸A = sub (substₘ-lemma₀-𝟘ᵐ? (liftSubstₘ Ψ)
                    (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ) η▸A)
                 (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
                   𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
                   𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ q ⟩
                   𝟘ᶜ                ∎)
  in  sub (unitrecₘ γ′▸t δ′▸u η′▸A (Unitrec-allowed-·ᵐ ok′))
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
            p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎

substₘ-lemma₀ Ψ Ψ▶σ (Idₘ ok ▸A ▸t ▸u) = sub
  (Idₘ ok
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸t)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸u))
  (begin
     𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (Id₀ₘ ok ▸A ▸t ▸u) = Id₀ₘ ok
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸t)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸u)

substₘ-lemma₀ _ _ rflₘ =
  rflₘ

substₘ-lemma₀ Ψ Ψ▶σ (Jₘ {p} {q} _ _ ▸A ▸t ▸B ▸u ▸v ▸w) = sub
  (Jₘ-generalised
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸t)
     (sub
        (substₘ-lemma₀ (liftSubstₘ (liftSubstₘ Ψ))
           (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ)) ▸B)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
           𝟘ᶜ                  ∎))
     (substₘ-lemma₀ Ψ Ψ▶σ ▸u)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸v)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸w))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ                                 ≈˘⟨ ω·ᶜ⋀ᶜ⁵𝟘ᶜ ⟩
     ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎)

substₘ-lemma₀ Ψ Ψ▶σ (J₀ₘ₁ ≡some p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸v ▸w) = sub
  (J₀ₘ₁-generalised
     (≤ᵉᵐ→≡some→≡not-none erased-matches-for-J-≤ᵉᵐ·ᵐ ≡some .proj₂)
     p≡𝟘 q≡𝟘
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸t)
     (substₘ-lemma₀ (liftSubstₘ (liftSubstₘ Ψ))
        (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ)) ▸B)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸u)
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸v)
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸w))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ               ≈˘⟨ ω·ᶜ⋀ᶜ²𝟘ᶜ ⟩
     ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎)

substₘ-lemma₀ ⦃ ok ⦄ Ψ Ψ▶σ (J₀ₘ₂ {p} {q} ≡all ▸A ▸t ▸B ▸u ▸v ▸w) = J₀ₘ₂
  (≤ᵉᵐ→≡all→≡all erased-matches-for-J-≤ᵉᵐ·ᵐ ≡all)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸t)
  (sub
     (substₘ-lemma₀-𝟘ᵐ? (liftSubstₘ (liftSubstₘ Ψ))
        (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ))
        ▸B)
     (begin
        𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
        𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q              ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
        𝟘ᶜ                              ∎))
  (substₘ-lemma₀ Ψ Ψ▶σ ▸u)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸v)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸w)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ (Kₘ {p} _ _ ▸A ▸t ▸B ▸u ▸v) = sub
  (Kₘ-generalised
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸t)
     (sub
        (substₘ-lemma₀ (liftSubstₘ Ψ) (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ)
           ▸B)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
           𝟘ᶜ          ∎))
     (substₘ-lemma₀ Ψ Ψ▶σ ▸u)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸v))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ                           ≈˘⟨ ω·ᶜ⋀ᶜ⁴𝟘ᶜ ⟩
     ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎)

substₘ-lemma₀ Ψ Ψ▶σ (K₀ₘ₁ ≡some p≡𝟘 ▸A ▸t ▸B ▸u ▸v) = sub
  (K₀ₘ₁-generalised
     (≤ᵉᵐ→≡some→≡not-none erased-matches-for-K-≤ᵉᵐ·ᵐ ≡some .proj₂)
     p≡𝟘
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸t)
     (substₘ-lemma₀ (liftSubstₘ Ψ) (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ) ▸B)
     (substₘ-lemma₀ Ψ Ψ▶σ ▸u)
     (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸v))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ               ≈˘⟨ ω·ᶜ⋀ᶜ²𝟘ᶜ ⟩
     ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎)

substₘ-lemma₀ ⦃ ok ⦄ Ψ Ψ▶σ (K₀ₘ₂ {p} ≡all ▸A ▸t ▸B ▸u ▸v) = K₀ₘ₂
  (≤ᵉᵐ→≡all→≡all erased-matches-for-K-≤ᵉᵐ·ᵐ ≡all)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸t)
  (sub
     (substₘ-lemma₀-𝟘ᵐ? (liftSubstₘ Ψ) (wf-liftSubstₘ {mo = 𝟘ᵐ} Ψ▶σ)
        ▸B)
     (begin
        𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
        𝟘ᶜ ∙ 𝟘 · p        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
        𝟘ᶜ                ∎))
  (substₘ-lemma₀ Ψ Ψ▶σ ▸u)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸v)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₀ Ψ Ψ▶σ ([]-congₘ ▸A ▸t ▸u ▸v) = []-congₘ
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸A)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸t)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸u)
  (substₘ-lemma₀-𝟘ᵐ? Ψ Ψ▶σ ▸v)

substₘ-lemma₀ Ψ Ψ▶σ (sub γ▸t _) =
  substₘ-lemma₀ Ψ Ψ▶σ γ▸t

private

  -- Some lemmas used in the proofs of the substitution lemmas below.

  *>∙∙≤liftSubst-listSubst*>∙∙ :
    (Ψ : Substₘ m n) →
    (δ <* Ψ) ∙ p ∙ q ≤ᶜ (δ ∙ p ∙ q) <* liftSubstₘ (liftSubstₘ Ψ)
  *>∙∙≤liftSubst-listSubst*>∙∙ {δ = δ} {p = p} {q = q} Ψ = begin
    (δ <* Ψ) ∙ p ∙ q                           ≈˘⟨ +ᶜ-identityˡ _ ∙ +-identityʳ _ ∙ refl ⟩
    (𝟘ᶜ +ᶜ δ <* Ψ) ∙ (p + 𝟘) ∙ q               ≈˘⟨ (+ᶜ-cong (·ᶜ-zeroʳ _ ∙ ·-identityʳ _) (wk1Substₘ-app Ψ δ)) ∙ refl ⟩
    (p ·ᶜ 𝟘ᶜ ∙ p · 𝟙) +ᶜ δ <* wk1Substₘ Ψ ∙ q  ≈˘⟨ liftSubstₘ-app (liftSubstₘ Ψ) (δ ∙ _) _ ⟩
    (δ ∙ p ∙ q) <* liftSubstₘ (liftSubstₘ Ψ)   ∎
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

  +·+·<*≤ :
    ∀ (Ψ : Substₘ m n) δ →
    (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) <* Ψ ≤ᶜ
    δ <* Ψ +ᶜ p ·ᶜ η <* Ψ +ᶜ r ·ᶜ χ <* Ψ
  +·+·<*≤ {η = η} {χ = χ} Ψ δ =
    ≤ᶜ-reflexive $
    ≈ᶜ-trans (<*-distrib-+ᶜ Ψ δ _) $
    +ᶜ-congˡ $
    ≈ᶜ-trans (<*-distrib-+ᶜ Ψ (_ ·ᶜ η) _) $
    +ᶜ-cong (<*-distrib-·ᶜ Ψ _ η) (<*-distrib-·ᶜ Ψ _ χ)

  ⋀ᶜ⁴-<* :
    ∀ γ₁ →
    (γ₁ ∧ᶜ γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄) <* Ψ ≤ᶜ
    γ₁ <* Ψ ∧ᶜ γ₂ <* Ψ ∧ᶜ γ₃ <* Ψ ∧ᶜ γ₄ <* Ψ
  ⋀ᶜ⁴-<* {γ₂ = γ₂} {γ₃ = γ₃} γ₁ =
    ≤ᶜ-trans (<*-sub-distrib-∧ᶜ _ γ₁ _) $
    ∧ᶜ-monotoneʳ $
    ≤ᶜ-trans (<*-sub-distrib-∧ᶜ _ γ₂ _) $
    ∧ᶜ-monotoneʳ $
    <*-sub-distrib-∧ᶜ _ γ₃ _

  ·ᶜ⋀ᶜ²<* : ∀ γ₁ → (p ·ᶜ (γ₁ ∧ᶜ γ₂)) <* Ψ ≤ᶜ p ·ᶜ (γ₁ <* Ψ ∧ᶜ γ₂ <* Ψ)
  ·ᶜ⋀ᶜ²<* γ₁ =
    ≤ᶜ-trans (≤ᶜ-reflexive $ <*-distrib-·ᶜ _ _ (γ₁ ∧ᶜ _)) $
    ·ᶜ-monotoneʳ $ <*-sub-distrib-∧ᶜ _ γ₁ _

  ·ᶜ⋀ᶜ⁴<* :
    ∀ γ₁ →
    (p ·ᶜ (γ₁ ∧ᶜ γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄)) <* Ψ ≤ᶜ
    p ·ᶜ (γ₁ <* Ψ ∧ᶜ γ₂ <* Ψ ∧ᶜ γ₃ <* Ψ ∧ᶜ γ₄ <* Ψ)
  ·ᶜ⋀ᶜ⁴<* γ₁ =
    ≤ᶜ-trans (≤ᶜ-reflexive $ <*-distrib-·ᶜ _ _ (γ₁ ∧ᶜ _)) $
    ·ᶜ-monotoneʳ $
    ⋀ᶜ⁴-<* γ₁

  ·ᶜ⋀ᶜ⁵<* :
    ∀ γ₁ →
    (p ·ᶜ (γ₁ ∧ᶜ γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄ ∧ᶜ γ₅)) <* Ψ ≤ᶜ
    p ·ᶜ (γ₁ <* Ψ ∧ᶜ γ₂ <* Ψ ∧ᶜ γ₃ <* Ψ ∧ᶜ γ₄ <* Ψ ∧ᶜ γ₅ <* Ψ)
  ·ᶜ⋀ᶜ⁵<* {γ₂ = γ₂} γ₁ =
    ≤ᶜ-trans (≤ᶜ-reflexive $ <*-distrib-·ᶜ _ _ (γ₁ ∧ᶜ _)) $
    ·ᶜ-monotoneʳ $
    ≤ᶜ-trans (<*-sub-distrib-∧ᶜ _ γ₁ _) $
    ∧ᶜ-monotoneʳ $
    ⋀ᶜ⁴-<* γ₂

-- A substitution lemma for the case where the mode 𝟘ᵐ is not allowed.
--
-- Proof by induction on t being well resourced.

substₘ-lemma₁ :
  ¬ T 𝟘ᵐ-allowed →
  (Ψ : Substₘ m n) →
  Ψ ▶[ mos ] σ → γ ▸[ mo ] t → substₘ Ψ γ ▸[ 𝟙ᵐ ] t [ σ ]

private

  -- A variant of substₘ-lemma₁.

  substₘ-lemma₁′ :
    ¬ T 𝟘ᵐ-allowed →
    (Ψ : Substₘ m n) →
    Ψ ▶[ mos ] σ → γ ▸[ mo ] t → substₘ Ψ γ ▸[ mo′ ] t [ σ ]
  substₘ-lemma₁′ not-ok Ψ Ψ▶ γ▸ =
    ▸-without-𝟘ᵐ not-ok (substₘ-lemma₁ not-ok Ψ Ψ▶ γ▸)

substₘ-lemma₁ {mo = 𝟘ᵐ[ ok ]} not-ok = ⊥-elim (not-ok ok)

substₘ-lemma₁ _ Ψ _ Uₘ =
  sub Uₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁ _ Ψ _ ℕₘ =
  sub ℕₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁ _ Ψ _ Emptyₘ =
  sub Emptyₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁ _ Ψ _ Unitₘ =
  sub Unitₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁ {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ (ΠΣₘ {γ = γ} {δ = δ} γ▸F δ▸G) = sub
  (ΠΣₘ (substₘ-lemma₁′ not-ok Ψ Ψ▶σ γ▸F)
     (sub (substₘ-lemma₁ not-ok (liftSubstₘ Ψ)
             (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ)
             δ▸G)
        (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ δ _)))))
  (≤ᶜ-reflexive (<*-distrib-+ᶜ Ψ γ δ))

substₘ-lemma₁ {mos = mos} {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ (var {x = x}) = sub
  (▸-without-𝟘ᵐ not-ok (Ψ▶σ x))
  (begin
     (𝟘ᶜ , x ≔ 𝟙) <* Ψ          ≡˘⟨ cong (λ m → (𝟘ᶜ , x ≔ ⌜ m ⌝) <* Ψ)
                                         (only-𝟙ᵐ-without-𝟘ᵐ {m = mos x} not-ok) ⟩
     (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₁ {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ (lamₘ {γ = γ} {p = p} γ▸t) = lamₘ
  (sub (substₘ-lemma₁ not-ok (liftSubstₘ Ψ)
          (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ)
          γ▸t)
     (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ γ _))))

substₘ-lemma₁ not-ok Ψ Ψ▶σ (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸t δ▸u) = sub
  (substₘ-lemma₁ not-ok Ψ Ψ▶σ γ▸t ∘ₘ
   substₘ-lemma₁′ not-ok Ψ Ψ▶σ δ▸u)
  (begin
     (γ +ᶜ p ·ᶜ δ) <* Ψ       ≈⟨ <*-distrib-+ᶜ Ψ γ (p ·ᶜ δ) ⟩
     γ <* Ψ +ᶜ (p ·ᶜ δ) <* Ψ  ≈⟨ +ᶜ-congˡ (<*-distrib-·ᶜ Ψ _ δ) ⟩
     γ <* Ψ +ᶜ p ·ᶜ δ <* Ψ    ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₁
  not-ok Ψ Ψ▶σ (prodʷₘ {γ = γ} {p = p} {δ = δ} γ▸t δ▸u) = sub
  (prodʷₘ (substₘ-lemma₁′ not-ok Ψ Ψ▶σ γ▸t)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ δ▸u))
  (begin
     (p ·ᶜ γ +ᶜ δ) <* Ψ       ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) δ ⟩
     (p ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ  ≈⟨ +ᶜ-congʳ (<*-distrib-·ᶜ Ψ _ γ) ⟩
     p ·ᶜ γ <* Ψ +ᶜ δ <* Ψ    ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₁
  not-ok Ψ Ψ▶σ (prodˢₘ {γ = γ} {p = p} {δ = δ} γ▸t δ▸u) = sub
  (prodˢₘ (substₘ-lemma₁′ not-ok Ψ Ψ▶σ γ▸t)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ δ▸u))
  (begin
     (p ·ᶜ γ ∧ᶜ δ) <* Ψ       ≤⟨ <*-sub-distrib-∧ᶜ Ψ (p ·ᶜ γ) δ ⟩
     (p ·ᶜ γ) <* Ψ ∧ᶜ δ <* Ψ  ≈⟨ ∧ᶜ-congʳ (<*-distrib-·ᶜ Ψ _ γ) ⟩
     p ·ᶜ γ <* Ψ ∧ᶜ δ <* Ψ    ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma₁ {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ (fstₘ m γ▸t _ ok) =
  fstₘ m (substₘ-lemma₁′ not-ok Ψ Ψ▶σ γ▸t)
    (only-𝟙ᵐ-without-𝟘ᵐ not-ok) ok

substₘ-lemma₁ not-ok Ψ Ψ▶σ (sndₘ γ▸t) =
  sndₘ (substₘ-lemma₁ not-ok Ψ Ψ▶σ γ▸t)

substₘ-lemma₁
  {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ
  (prodrecₘ {γ = γ} {r = r} {δ = δ} {η = η} {q = q}
     γ▸t δ▸u η▸A P) = sub
  (prodrecₘ (substₘ-lemma₁′ not-ok Ψ Ψ▶σ γ▸t)
     (sub (substₘ-lemma₁ not-ok (liftSubstₘ (liftSubstₘ Ψ))
             (wf-liftSubstₘ {mo = 𝟙ᵐ} (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ))
             δ▸u)
        (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = δ} Ψ))
     (sub (substₘ-lemma₁′ not-ok (liftSubstₘ Ψ)
             (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ) η▸A)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           η <* Ψ ∙ ⌜ 𝟘ᵐ? ⌝ · q               ≈˘⟨ liftSubstₘ-app Ψ η _ ⟩
           (η ∙ ⌜ 𝟘ᵐ? ⌝ · q) <* liftSubstₘ Ψ  ∎))
     P)
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     (r ·ᶜ γ +ᶜ δ) <* Ψ       ≈⟨ <*-distrib-+ᶜ Ψ (r ·ᶜ γ) δ ⟩
     (r ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ  ≈⟨ +ᶜ-congʳ (<*-distrib-·ᶜ Ψ _ γ) ⟩
     r ·ᶜ γ <* Ψ +ᶜ δ <* Ψ    ∎)

substₘ-lemma₁ _ Ψ _ zeroₘ =
  sub zeroₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁ not-ok Ψ Ψ▶σ (sucₘ γ▸t) =
  sucₘ (substₘ-lemma₁ not-ok Ψ Ψ▶σ γ▸t)

substₘ-lemma₁
  {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ
  (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {θ = θ} {q = q}
     γ▸z δ▸s η▸n θ▸A) = sub
  (natrecₘ
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ γ▸z)
     (sub
       (substₘ-lemma₁ not-ok (liftSubstₘ (liftSubstₘ Ψ))
          (wf-liftSubstₘ {mo = 𝟙ᵐ} (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ)) δ▸s)
       (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = δ} Ψ))
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ η▸n)
     (sub (substₘ-lemma₁′ not-ok (liftSubstₘ Ψ)
             (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ) θ▸A)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           θ <* Ψ ∙ ⌜ 𝟘ᵐ? ⌝ · q               ≈˘⟨ liftSubstₘ-app Ψ θ _ ⟩
           (θ ∙ ⌜ 𝟘ᵐ? ⌝ · q) <* liftSubstₘ Ψ  ∎)))
  (<*-sub-distrib-nrᶜ Ψ γ)
  where
  open import Graded.Modality.Dedicated-nr.Instance

substₘ-lemma₁
  {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ
  (natrec-no-nrₘ
     {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {θ = θ} {q = q} {χ = χ}
     γ▸z δ▸s η▸n θ▸A χ≤γ χ≤δ χ≤η fix) =
  natrec-no-nrₘ
    (substₘ-lemma₁ not-ok Ψ Ψ▶σ γ▸z)
    (sub
       (substₘ-lemma₁ not-ok (liftSubstₘ (liftSubstₘ Ψ))
          (wf-liftSubstₘ {mo = 𝟙ᵐ} (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ)) δ▸s)
       (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = δ} Ψ))
    (substₘ-lemma₁ not-ok Ψ Ψ▶σ η▸n)
    (sub (substₘ-lemma₁′ not-ok (liftSubstₘ Ψ)
            (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ) θ▸A)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           θ <* Ψ ∙ ⌜ 𝟘ᵐ? ⌝ · q               ≈˘⟨ liftSubstₘ-app Ψ θ _ ⟩
           (θ ∙ ⌜ 𝟘ᵐ? ⌝ · q) <* liftSubstₘ Ψ  ∎))
    (<*-monotone Ψ χ≤γ)
    (<*-monotone Ψ ∘→ χ≤δ)
    (<*-monotone Ψ χ≤η)
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       χ <* Ψ                                ≤⟨ <*-monotone Ψ fix ⟩
       (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) <* Ψ          ≤⟨ +·+·<*≤ Ψ δ ⟩
       δ <* Ψ +ᶜ p ·ᶜ η <* Ψ +ᶜ r ·ᶜ χ <* Ψ  ∎)

substₘ-lemma₁
  {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ
  (emptyrecₘ {γ = γ} {p = p} γ▸t δ▸A) = sub
  (emptyrecₘ (substₘ-lemma₁′ not-ok Ψ Ψ▶σ γ▸t)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ δ▸A))
  (≤ᶜ-reflexive (<*-distrib-·ᶜ Ψ _ γ))

substₘ-lemma₁ _ Ψ _ starʷₘ = sub
  starₘ
  (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁ {mo = 𝟙ᵐ} _ Ψ _ (starˢₘ {γ = γ} prop) = sub
  (starˢₘ (λ ns → ≈ᶜ-trans (≈ᶜ-sym (<*-zeroˡ Ψ)) (<*-cong Ψ (prop ns))))
  (≤ᶜ-reflexive (<*-distrib-·ᶜ Ψ 𝟙 γ ))

substₘ-lemma₁ {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ
              (unitrecₘ {γ = γ} {p = p} {δ = δ} {η = η} {q = q} γ▸t δ▸u η▸A ok) =
  let η′▸A = sub (substₘ-lemma₁′ not-ok (liftSubstₘ Ψ)
                    (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ) η▸A)
                 (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ η _)))
  in  sub (unitrecₘ (substₘ-lemma₁′ not-ok Ψ Ψ▶σ γ▸t)
                    (substₘ-lemma₁ not-ok Ψ Ψ▶σ δ▸u)
                    η′▸A ok)
      let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
        (p ·ᶜ γ +ᶜ δ) <* Ψ       ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) δ ⟩
        (p ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ  ≈⟨ +ᶜ-congʳ (<*-distrib-·ᶜ Ψ p γ) ⟩
        p ·ᶜ γ <* Ψ +ᶜ δ <* Ψ    ∎

substₘ-lemma₁ not-ok Ψ Ψ▶σ (Idₘ {δ = δ} ok ▸A ▸t ▸u) = sub
  (Idₘ ok
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸t)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸u))
  (≤ᶜ-reflexive (<*-distrib-+ᶜ _ δ _))

substₘ-lemma₁ not-ok Ψ Ψ▶σ (Id₀ₘ ok ▸A ▸t ▸u) = sub
  (Id₀ₘ ok
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸t)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸u))
  (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁ _ Ψ _ rflₘ = sub
  rflₘ
  (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁
  {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ (Jₘ {γ₂} {γ₃} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ ▸v) = sub
  (Jₘ ok₁ ok₂
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸t)
     (sub
       (substₘ-lemma₁ not-ok (liftSubstₘ (liftSubstₘ Ψ))
          (wf-liftSubstₘ {mo = 𝟙ᵐ} (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ)) ▸B)
       (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = γ₃} _))
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸u)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸t′)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸v))
  (·ᶜ⋀ᶜ⁵<* γ₂)

substₘ-lemma₁
  {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ (J₀ₘ₁ {γ₃} ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ ▸v) = sub
  (J₀ₘ₁ ok p≡𝟘 q≡𝟘
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸t)
     (sub
       (substₘ-lemma₁ not-ok (liftSubstₘ (liftSubstₘ Ψ))
          (wf-liftSubstₘ {mo = 𝟙ᵐ} (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ)) ▸B)
       (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = γ₃} _))
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸u)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸t′)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸v))
  (·ᶜ⋀ᶜ²<* γ₃)

substₘ-lemma₁ not-ok Ψ Ψ▶σ (J₀ₘ₂ {γ₃} ok ▸A ▸t ▸B ▸u ▸t′ ▸v) = J₀ₘ₂
  (subst ((_≡ all) ∘→ erased-matches-for-J)
     (Mode-propositional-without-𝟘ᵐ not-ok) ok)
  (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
  (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸t)
  (sub
    (substₘ-lemma₁′ not-ok (liftSubstₘ (liftSubstₘ Ψ))
       (wf-liftSubstₘ {mo = 𝟙ᵐ} (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ))
       ▸B)
    (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = γ₃} _))
  (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸u)
  (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸t′)
  (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸v)

substₘ-lemma₁
  {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ (Kₘ {γ₂} {γ₃} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v) = sub
  (Kₘ ok₁ ok₂
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸t)
     (sub
       (substₘ-lemma₁ not-ok (liftSubstₘ Ψ)
          (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ) ▸B)
       (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app _ γ₃ _))))
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸u)
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸v))
  (·ᶜ⋀ᶜ⁴<* γ₂)

substₘ-lemma₁
  {mo = 𝟙ᵐ} not-ok Ψ Ψ▶σ (K₀ₘ₁ {γ₃} ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v) = sub
  (K₀ₘ₁ ok p≡𝟘
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸t)
     (sub
       (substₘ-lemma₁ not-ok (liftSubstₘ Ψ)
          (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ) ▸B)
       (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app _ γ₃ _))))
     (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸u)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸v))
  (·ᶜ⋀ᶜ²<* γ₃)

substₘ-lemma₁ not-ok Ψ Ψ▶σ (K₀ₘ₂ {γ₃} ok ▸A ▸t ▸B ▸u ▸v) = K₀ₘ₂
  (subst ((_≡ all) ∘→ erased-matches-for-K)
     (Mode-propositional-without-𝟘ᵐ not-ok) ok)
  (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
  (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸t)
  (sub
     (substₘ-lemma₁′ not-ok (liftSubstₘ Ψ)
        (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶σ) ▸B)
     (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app _ γ₃ _))))
  (substₘ-lemma₁ not-ok Ψ Ψ▶σ ▸u)
  (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸v)

substₘ-lemma₁ not-ok Ψ Ψ▶σ ([]-congₘ ▸A ▸t ▸u ▸v) = sub
  ([]-congₘ
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸A)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸t)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸u)
     (substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸v))
  (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma₁ not-ok Ψ Ψ▶σ (sub γ▸t γ≤δ) = sub
  (substₘ-lemma₁ not-ok Ψ Ψ▶σ γ▸t)
  (<*-monotone Ψ γ≤δ)

private

  -- Some lemmas used in the proof of the substitution lemma below.

  substₘ-lemma-𝟘ᵐ? :
    (Ψ : Substₘ m n) →
    Ψ ▶[ mos ] σ → γ ▸[ mo ] t →
    ∃ λ δ → δ ▸[ 𝟘ᵐ? ] t [ σ ]
  substₘ-lemma-𝟘ᵐ? Ψ Ψ▶ γ▸ = 𝟘ᵐ-allowed-elim
    (λ ok →
         _
       , substₘ-lemma₀-𝟘ᵐ? ⦃ ok = ok ⦄ Ψ Ψ▶ γ▸)
    (λ not-ok →
         _
       , substₘ-lemma₁′ not-ok Ψ Ψ▶ γ▸)

  substₘ-lemma-∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] :
    (Ψ : Substₘ m n) →
    Ψ ▶[ mos ] σ → γ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ mo ] t →
    ∃ λ δ → δ ∙ ⌜ 𝟘ᵐ? ⌝ · p ▸[ 𝟘ᵐ? ] t [ liftSubst σ ]
  substₘ-lemma-∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] {γ = γ} {p = p} Ψ Ψ▶ γ▸ = 𝟘ᵐ-allowed-elim
    (λ ok →
        _
      , sub (substₘ-lemma₀-𝟘ᵐ? ⦃ ok = ok ⦄ (liftSubstₘ Ψ)
               (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶) γ▸)
          (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
           begin
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
             𝟘ᶜ ∙ 𝟘 · p        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ                ∎))
    (λ not-ok →
        _
      , sub (substₘ-lemma₁′ not-ok (liftSubstₘ Ψ)
               (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶) γ▸)
          (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
           begin
             γ <* Ψ ∙ ⌜ 𝟘ᵐ? ⌝ · p               ≈˘⟨ liftSubstₘ-app Ψ γ _ ⟩
             (γ ∙ ⌜ 𝟘ᵐ? ⌝ · p) <* liftSubstₘ Ψ  ∎))

  substₘ-lemma-∙⌜𝟘ᵐ?⌝·∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] :
    Ψ ▶[ mos ] σ → γ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ mo ] t →
    ∃ λ δ → δ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] t [ liftSubstn σ 2 ]
  substₘ-lemma-∙⌜𝟘ᵐ?⌝·∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] {Ψ} {γ} {p} {q} Ψ▶ γ▸ =
    𝟘ᵐ-allowed-elim
      (λ ok →
          _
        , sub
            (substₘ-lemma₀-𝟘ᵐ? ⦃ ok = ok ⦄
               (liftSubstₘ (liftSubstₘ Ψ))
               (wf-liftSubstₘ {mo = 𝟙ᵐ} (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶))
               γ▸)
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ∙ ·-congʳ (⌜𝟘ᵐ?⌝≡𝟘 ok) ⟩
               𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q              ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
               𝟘ᶜ                              ∎))
      (λ not-ok →
          _
        , sub
            (substₘ-lemma₁′ not-ok
               (liftSubstₘ (liftSubstₘ Ψ))
               (wf-liftSubstₘ {mo = 𝟙ᵐ} (wf-liftSubstₘ {mo = 𝟙ᵐ} Ψ▶))
               γ▸)
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               γ <* Ψ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q               ≈˘⟨ liftSubstₘ-app _ γ _ ∙ refl ⟩

               (γ ∙ ⌜ 𝟘ᵐ? ⌝ · p) <* liftSubstₘ Ψ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈˘⟨ liftSubstₘ-app (liftSubstₘ _) (γ ∙ _) _ ⟩

               (γ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q) <*
                 liftSubstₘ (liftSubstₘ Ψ)                      ∎))

  ≡𝟘→𝟘ᵐ≡ᵐ· : ∀ ⦃ ok ⦄ mo → p ≡ 𝟘 → 𝟘ᵐ[ ok ] ≡ mo ᵐ· p
  ≡𝟘→𝟘ᵐ≡ᵐ· {p = p} mo p≡𝟘 =
    𝟘ᵐ       ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
    𝟘ᵐ?      ≡˘⟨ ᵐ·-zeroʳ mo ⟩
    mo ᵐ· 𝟘  ≡˘⟨ ᵐ·-cong mo p≡𝟘 ⟩
    mo ᵐ· p  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ≡𝟘→·<*≈ᶜ·𝟘 : (Ψ : Substₘ m n) → p ≡ 𝟘 → p ·ᶜ δ <* Ψ ≈ᶜ p ·ᶜ 𝟘ᶜ
  ≡𝟘→·<*≈ᶜ·𝟘 {p = p} {δ = δ} Ψ p≡𝟘 = begin
    p ·ᶜ δ <* Ψ  ≈⟨ ·ᶜ-congʳ p≡𝟘 ⟩
    𝟘 ·ᶜ δ <* Ψ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
    𝟘ᶜ           ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
    p ·ᶜ 𝟘ᶜ      ∎
    where
    open Tools.Reasoning.Equivalence Conₘ-setoid

-- The main substitution lemma.
--
-- Proof by induction on t being well resourced.

substₘ-lemma :
  (Ψ : Substₘ m n) →
  Ψ ▶[ ⌞ γ ⌟ᶜ ] σ → γ ▸[ mo ] t → substₘ Ψ γ ▸[ mo ] t [ σ ]

substₘ-lemma Ψ _ Uₘ =
  sub Uₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma Ψ _ ℕₘ =
  sub ℕₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma Ψ _ Emptyₘ =
  sub Emptyₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma Ψ _ Unitₘ =
  sub Unitₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma Ψ Ψ▶σ (ΠΣₘ {γ = γ} {δ = δ} γ▸F δ▸G) = sub
  (ΠΣₘ (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ˡ Ψ γ Ψ▶σ) γ▸F)
     (sub (substₘ-lemma (liftSubstₘ Ψ)
             (▶-cong (liftSubstₘ Ψ)
                (λ where
                   (_ +1) → PE.refl
                   x0     → PE.refl)
                (wf-liftSubstₘ (▶-⌞+ᶜ⌟ʳ Ψ γ Ψ▶σ)))
             δ▸G)
        (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ δ _)))))
  (≤ᶜ-reflexive (<*-distrib-+ᶜ Ψ γ δ))

substₘ-lemma {σ = σ} {mo = mo} Ψ Ψ▶σ (var {x = x}) = sub
  (▸-cong (let open Tools.Reasoning.PropositionalEquality in
             ⌞ (𝟘ᶜ , x ≔ ⌜ mo ⌝) ⟨ x ⟩ ⌟  ≡⟨ cong ⌞_⌟ (update-lookup 𝟘ᶜ x) ⟩
             ⌞ ⌜ mo ⌝ ⌟                   ≡⟨ ⌞⌜⌝⌟ _ ⟩
             mo                           ∎)
     (Ψ▶σ x))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     (𝟘ᶜ , x ≔ ⌜ mo ⌝) <* Ψ                           ≈˘⟨ <*-cong Ψ (update-congʳ {γ = 𝟘ᶜ} {x = x} (cong ⌜_⌝ (⌞⌜⌝⌟ mo))) ⟩
     (𝟘ᶜ , x ≔ ⌜ ⌞ ⌜ mo ⌝ ⌟ ⌝) <* Ψ                   ≡˘⟨ cong (λ p → (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) <* Ψ) (update-lookup 𝟘ᶜ x) ⟩
     (𝟘ᶜ , x ≔ ⌜ ⌞ (𝟘ᶜ , x ≔ ⌜ mo ⌝) ⟨ x ⟩ ⌟ ⌝) <* Ψ  ∎)

substₘ-lemma {mo = mo} Ψ Ψ▶σ (lamₘ {γ = γ} {p = p} γ▸t) = lamₘ
  (sub (substₘ-lemma (liftSubstₘ Ψ)
          (▶-cong (liftSubstₘ Ψ)
             (λ where
                (_ +1) → PE.refl
                x0     →
                  mo ᵐ· p         ≡˘⟨ ⌞⌜⌝·⌟ mo ⟩
                  ⌞ ⌜ mo ⌝ · p ⌟  ∎)
             (wf-liftSubstₘ Ψ▶σ))
          γ▸t)
     (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app Ψ γ _))))
  where
  open Tools.Reasoning.PropositionalEquality

substₘ-lemma
  {σ = σ} {mo = mo} Ψ Ψ▶σ
  (_∘ₘ_ {γ = γ} {t = t} {δ = δ} {p = p} {u = u} γ▸t δ▸u) =
  case ▶-⌞·⌟ Ψ δ (▶-⌞+ᶜ⌟ʳ Ψ γ Ψ▶σ) of λ where
    (inj₂ Ψ▶σ)        → lemma (substₘ-lemma Ψ Ψ▶σ δ▸u) ≈ᶜ-refl
    (inj₁ (p≡𝟘 , ok)) → lemma
      (▸-cong (≡𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≡𝟘)
         (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ δ▸u))
      (≡𝟘→·<*≈ᶜ·𝟘 {δ = δ} Ψ p≡𝟘)
  where
  lemma :
    η ▸[ mo ᵐ· p ] u [ σ ] →
    p ·ᶜ δ <* Ψ ≈ᶜ p ·ᶜ η →
    (γ +ᶜ p ·ᶜ δ) <* Ψ ▸[ mo ] (t ∘⟨ p ⟩ u) [ σ ]
  lemma {η = η} hyp₁ hyp₂ = sub
    (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ˡ Ψ γ Ψ▶σ) γ▸t ∘ₘ hyp₁)
    (begin
       (γ +ᶜ p ·ᶜ δ) <* Ψ      ≈⟨ <*-distrib-+ᶜ Ψ γ (p ·ᶜ δ) ⟩
       γ <* Ψ +ᶜ (p ·ᶜ δ) <* Ψ  ≈⟨ +ᶜ-congˡ (<*-distrib-·ᶜ Ψ _ δ) ⟩
       γ <* Ψ +ᶜ p ·ᶜ δ <* Ψ    ≈⟨ +ᶜ-congˡ hyp₂ ⟩
       γ <* Ψ +ᶜ p ·ᶜ η         ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma
  {σ = σ} {mo = mo} Ψ Ψ▶σ
  (prodʷₘ {γ = γ} {p = p} {t = t} {δ = δ} {u = u} γ▸t δ▸u) =
  case ▶-⌞·⌟ Ψ γ (▶-⌞+ᶜ⌟ˡ Ψ (_ ·ᶜ γ) Ψ▶σ) of λ where
    (inj₂ Ψ▶σ)        → lemma (substₘ-lemma Ψ Ψ▶σ γ▸t) ≈ᶜ-refl
    (inj₁ (p≡𝟘 , ok)) → lemma
      (▸-cong (≡𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≡𝟘)
         (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ γ▸t))
      (≡𝟘→·<*≈ᶜ·𝟘 {δ = γ} Ψ p≡𝟘)
  where
  lemma :
    η ▸[ mo ᵐ· p ] t [ σ ] →
    p ·ᶜ γ <* Ψ ≈ᶜ p ·ᶜ η →
    (p ·ᶜ γ +ᶜ δ) <* Ψ ▸[ mo ] prodʷ p t u [ σ ]
  lemma {η = η} hyp₁ hyp₂ = sub
    (prodʷₘ hyp₁ (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ʳ Ψ (_ ·ᶜ γ) Ψ▶σ) δ▸u))
    (begin
       (p ·ᶜ γ +ᶜ δ) <* Ψ       ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) δ ⟩
       (p ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ  ≈⟨ +ᶜ-congʳ (<*-distrib-·ᶜ Ψ _ γ) ⟩
       p ·ᶜ γ <* Ψ +ᶜ δ <* Ψ    ≈⟨ +ᶜ-congʳ hyp₂ ⟩
       p ·ᶜ η +ᶜ δ <* Ψ         ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma
  {σ = σ} {mo = mo} Ψ Ψ▶σ
  (prodˢₘ {γ = γ} {p = p} {t = t} {δ = δ} {u = u} γ▸t δ▸u) =
  case ▶-⌞·⌟ Ψ γ (▶-⌞∧ᶜ⌟ˡ Ψ (_ ·ᶜ γ) Ψ▶σ) of λ where
    (inj₂ Ψ▶σ)        → lemma (substₘ-lemma Ψ Ψ▶σ γ▸t) ≈ᶜ-refl
    (inj₁ (p≡𝟘 , ok)) → lemma
      (▸-cong (≡𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≡𝟘)
         (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ γ▸t))
      (≡𝟘→·<*≈ᶜ·𝟘 {δ = γ} Ψ p≡𝟘)
  where
  lemma :
    η ▸[ mo ᵐ· p ] t [ σ ] →
    p ·ᶜ γ <* Ψ ≈ᶜ p ·ᶜ η →
    (p ·ᶜ γ ∧ᶜ δ) <* Ψ ▸[ mo ] prodˢ p t u [ σ ]
  lemma {η = η} hyp₁ hyp₂ = sub
    (prodˢₘ hyp₁ (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ʳ Ψ (_ ·ᶜ γ) Ψ▶σ) δ▸u))
    (begin
       (p ·ᶜ γ ∧ᶜ δ) <* Ψ       ≤⟨ <*-sub-distrib-∧ᶜ Ψ (p ·ᶜ γ) δ ⟩
       (p ·ᶜ γ) <* Ψ ∧ᶜ δ <* Ψ  ≈⟨ ∧ᶜ-congʳ (<*-distrib-·ᶜ Ψ _ γ) ⟩
       p ·ᶜ γ <* Ψ ∧ᶜ δ <* Ψ    ≈⟨ ∧ᶜ-congʳ hyp₂ ⟩
       p ·ᶜ η ∧ᶜ δ <* Ψ         ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma Ψ Ψ▶σ (fstₘ m γ▸t PE.refl ok) =
  fstₘ m (substₘ-lemma Ψ Ψ▶σ γ▸t) PE.refl ok

substₘ-lemma Ψ Ψ▶σ (sndₘ γ▸t) =
  sndₘ (substₘ-lemma Ψ Ψ▶σ γ▸t)

substₘ-lemma
  {σ = σ} {mo = mo} Ψ Ψ▶σ
  (prodrecₘ
     {γ = γ} {r = r} {t = t} {δ = δ} {p = p} {u = u} {η = η} {q = q}
     {A = A} γ▸t δ▸u η▸A P) =
  case ▶-⌞·⌟ Ψ γ (▶-⌞+ᶜ⌟ˡ Ψ (_ ·ᶜ γ) Ψ▶σ) of λ where
    (inj₂ Ψ▶σ)        → lemma (substₘ-lemma Ψ Ψ▶σ γ▸t) ≈ᶜ-refl
    (inj₁ (p≡𝟘 , ok)) → lemma
      (▸-cong (≡𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≡𝟘)
         (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ γ▸t))
      (≡𝟘→·<*≈ᶜ·𝟘 {δ = γ} Ψ p≡𝟘)
  where
  lemma :
    θ ▸[ mo ᵐ· r ] t [ σ ] →
    r ·ᶜ γ <* Ψ ≈ᶜ r ·ᶜ θ →
    (r ·ᶜ γ +ᶜ δ) <* Ψ ▸[ mo ] prodrec r p q A t u [ σ ]
  lemma {θ = θ} hyp₁ hyp₂ = sub
    (prodrecₘ hyp₁
       (sub (substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ))
               (▶-cong (liftSubstₘ (liftSubstₘ Ψ))
                  (λ where
                     x0      → PE.refl
                     (x0 +1) → PE.refl
                     (_ +2)  → PE.refl)
                  (wf-liftSubstₘ
                     (wf-liftSubstₘ (▶-⌞+ᶜ⌟ʳ Ψ (_ ·ᶜ γ) Ψ▶σ))))
               δ▸u)
          (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = δ} Ψ))
       (substₘ-lemma-∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] Ψ Ψ▶σ η▸A .proj₂)
       P)
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       (r ·ᶜ γ +ᶜ δ) <* Ψ       ≈⟨ <*-distrib-+ᶜ Ψ (r ·ᶜ γ) δ ⟩
       (r ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ  ≈⟨ +ᶜ-congʳ (<*-distrib-·ᶜ Ψ _ γ) ⟩
       r ·ᶜ γ <* Ψ +ᶜ δ <* Ψ    ≈⟨ +ᶜ-congʳ hyp₂ ⟩
       r ·ᶜ θ +ᶜ δ <* Ψ         ∎)

substₘ-lemma Ψ _ zeroₘ =
  sub zeroₘ (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma Ψ Ψ▶σ (sucₘ γ▸t) =
  sucₘ (substₘ-lemma Ψ Ψ▶σ γ▸t)

substₘ-lemma
  Ψ Ψ▶σ
  (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {θ = θ} {q = q}
     γ▸z δ▸s η▸n θ▸A) = sub
  (natrecₘ
     (substₘ-lemma Ψ (▶-⌞nrᶜ⌟₁ Ψ γ Ψ▶σ) γ▸z)
     (sub
       (substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ))
          (▶-cong (liftSubstₘ (liftSubstₘ Ψ))
             (λ where
                x0      → PE.refl
                (x0 +1) → PE.refl
                (_ +2)  → PE.refl)
             (wf-liftSubstₘ
                (wf-liftSubstₘ (▶-⌞nrᶜ⌟₂ Ψ γ Ψ▶σ))))
          δ▸s)
       (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = δ} Ψ))
     (substₘ-lemma Ψ (▶-⌞nrᶜ⌟₃ Ψ γ Ψ▶σ) η▸n)
     (substₘ-lemma-∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] Ψ Ψ▶σ θ▸A .proj₂))
  (<*-sub-distrib-nrᶜ Ψ γ)
  where
  open import Graded.Modality.Dedicated-nr.Instance

substₘ-lemma
  Ψ Ψ▶σ
  ▸natrec@(natrec-no-nrₘ
             {γ = γ} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
             ⦃ no-nr = no-nr ⦄ γ▸z δ▸s η▸n θ▸A χ≤γ χ≤δ χ≤η fix) =
  𝟘ᵐ-allowed-elim
    (λ ok →
       natrec-no-nrₘ
         (substₘ-lemma Ψ (▶-≤ Ψ χ≤γ Ψ▶σ) γ▸z)
         (sub
           (substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ))
              (▶-cong (liftSubstₘ (liftSubstₘ Ψ))
                 (λ where
                    x0      → PE.refl
                    (x0 +1) → PE.refl
                    (_ +2)  → PE.refl)
                 (wf-liftSubstₘ $ wf-liftSubstₘ $
                  ▶-≤ Ψ (χ≤δ ok) Ψ▶σ))
              δ▸s)
           (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = δ} Ψ))
         (substₘ-lemma Ψ
            (▶-≤ Ψ (χ≤η ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄) Ψ▶σ)
            η▸n)
         (substₘ-lemma-∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] Ψ Ψ▶σ θ▸A .proj₂)
         (<*-monotone Ψ χ≤γ)
         (<*-monotone Ψ ∘→ χ≤δ)
         (<*-monotone Ψ χ≤η)
         (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            χ <* Ψ                                ≤⟨ <*-monotone Ψ fix ⟩
            (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) <* Ψ          ≤⟨ +·+·<*≤ Ψ δ ⟩
            δ <* Ψ +ᶜ p ·ᶜ η <* Ψ +ᶜ r ·ᶜ χ <* Ψ  ∎))
    (λ not-ok → substₘ-lemma₁′ not-ok Ψ Ψ▶σ ▸natrec)

substₘ-lemma {mo = mo} Ψ Ψ▶σ (emptyrecₘ {γ = γ} {p = p} γ▸t δ▸A) =
  case ▶-⌞·⌟ Ψ γ Ψ▶σ of λ where
    (inj₂ Ψ▶σ) → sub
      (emptyrecₘ (substₘ-lemma Ψ Ψ▶σ γ▸t)
         (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ δ▸A .proj₂))
      (≤ᶜ-reflexive (<*-distrib-·ᶜ Ψ _ γ))
    (inj₁ (p≡𝟘 , ok)) → sub
      (emptyrecₘ (▸-cong (≡𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok ⦄ mo p≡𝟘)
                    (substₘ-lemma₀ ⦃ ok = ok ⦄ Ψ Ψ▶σ γ▸t))
         (substₘ-lemma₀-𝟘ᵐ? ⦃ ok = ok ⦄ Ψ Ψ▶σ δ▸A))
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         (p ·ᶜ γ) <* Ψ  ≈⟨ <*-distrib-·ᶜ Ψ _ γ ⟩
         p ·ᶜ γ <* Ψ    ≈⟨ ≡𝟘→·<*≈ᶜ·𝟘 {δ = γ} Ψ p≡𝟘 ⟩
         p ·ᶜ 𝟘ᶜ        ∎)

substₘ-lemma Ψ Ψ▶σ starʷₘ = sub
  starʷₘ
  (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma Ψ _ (starˢₘ {γ = γ} prop) = sub
  (starˢₘ (λ ns → ≈ᶜ-trans (≈ᶜ-sym (<*-zeroˡ Ψ)) (<*-cong Ψ (prop ns))))
  (≤ᶜ-reflexive (<*-distrib-·ᶜ Ψ _ γ))

substₘ-lemma {mo = mo} Ψ Ψ▶σ (unitrecₘ {γ = γ} {p = p} {δ = δ} {η = η} γ▸t δ▸u η▸A ok) =
  let ▸u = substₘ-lemma Ψ (▶-⌞+ᶜ⌟ʳ Ψ (_ ·ᶜ γ) Ψ▶σ) δ▸u
      ▸A = substₘ-lemma-∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] Ψ Ψ▶σ η▸A .proj₂
      le = begin
        (p ·ᶜ γ +ᶜ δ) <* Ψ       ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) δ ⟩
        (p ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ  ≈⟨ +ᶜ-congʳ (<*-distrib-·ᶜ Ψ p γ) ⟩
        p ·ᶜ γ <* Ψ +ᶜ δ <* Ψ    ∎
  in  case ▶-⌞·⌟ Ψ γ (▶-⌞+ᶜ⌟ˡ Ψ (p ·ᶜ γ) Ψ▶σ) of λ where
    (inj₁ (p≡𝟘 , ok′)) →
      let ▸t = ▸-cong (≡𝟘→𝟘ᵐ≡ᵐ· ⦃ ok = ok′ ⦄ mo p≡𝟘) (substₘ-lemma₀ ⦃ ok = ok′ ⦄ Ψ Ψ▶σ γ▸t)
      in  sub (unitrecₘ ▸t ▸u ▸A ok)
              (begin
                (p ·ᶜ γ +ᶜ δ) <* Ψ     ≤⟨ le ⟩
                p ·ᶜ γ <* Ψ +ᶜ δ <* Ψ  ≡⟨ cong (λ p → p ·ᶜ γ <* Ψ +ᶜ δ <* Ψ) p≡𝟘 ⟩
                𝟘 ·ᶜ γ <* Ψ +ᶜ δ <* Ψ  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
                𝟘ᶜ +ᶜ δ <* Ψ           ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
                p ·ᶜ 𝟘ᶜ +ᶜ δ <* Ψ ∎)
    (inj₂ Ψ▶σ′) →
      let ▸t = substₘ-lemma Ψ Ψ▶σ′ γ▸t
      in  sub (unitrecₘ ▸t ▸u ▸A ok) le
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

substₘ-lemma Ψ Ψ▶σ (Idₘ {δ = δ} ok ▸A ▸t ▸u) = sub
  (Idₘ ok
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
     (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ˡ Ψ δ Ψ▶σ) ▸t)
     (substₘ-lemma Ψ (▶-⌞+ᶜ⌟ʳ Ψ δ Ψ▶σ) ▸u))
  (≤ᶜ-reflexive (<*-distrib-+ᶜ _ δ _))

substₘ-lemma Ψ Ψ▶σ (Id₀ₘ ok ▸A ▸t ▸u) = sub
  (Id₀ₘ ok
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸t .proj₂)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸u .proj₂))
  (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma Ψ _ rflₘ = sub
  rflₘ
  (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma
  Ψ Ψ▶σ (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ ▸v) = sub
  (Jₘ ok₁ ok₂
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ˡ Ψ γ₂ Ψ▶σ′) ▸t)
     (sub
       (substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ))
          (▶-cong (liftSubstₘ (liftSubstₘ Ψ))
             (λ where
                x0      → PE.refl
                (x0 +1) → PE.refl
                (_ +2)  → PE.refl)
             (wf-liftSubstₘ (wf-liftSubstₘ (▶-⌞∧ᶜ⌟ˡ Ψ γ₃ Ψ▶σ″))))
          ▸B)
       (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = γ₃} _))
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ˡ Ψ γ₄ Ψ▶σ‴) ▸u)
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ˡ Ψ γ₅ Ψ▶σ⁗) ▸t′)
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ʳ Ψ γ₅ Ψ▶σ⁗) ▸v))
  (·ᶜ⋀ᶜ⁵<* γ₂)
  where
  Ψ▶σ′ = case ▶-⌞·⌟ Ψ (γ₂ ∧ᶜ _) Ψ▶σ of λ where
           (inj₁ (ω≡𝟘 , ok)) → ⊥-elim (𝟘ᵐ.ω≢𝟘 ok ω≡𝟘)
           (inj₂ Ψ▶σ)        → Ψ▶σ
  Ψ▶σ″ = ▶-⌞∧ᶜ⌟ʳ Ψ γ₂ Ψ▶σ′
  Ψ▶σ‴ = ▶-⌞∧ᶜ⌟ʳ Ψ γ₃ Ψ▶σ″
  Ψ▶σ⁗ = ▶-⌞∧ᶜ⌟ʳ Ψ γ₄ Ψ▶σ‴

substₘ-lemma Ψ Ψ▶σ (J₀ₘ₁ {γ₃} ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ ▸v) = sub
  (J₀ₘ₁ ok p≡𝟘 q≡𝟘
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸t .proj₂)
     (sub
       (substₘ-lemma (liftSubstₘ (liftSubstₘ Ψ))
          (▶-cong (liftSubstₘ (liftSubstₘ Ψ))
             (λ where
                x0      → PE.refl
                (x0 +1) → PE.refl
                (_ +2)  → PE.refl)
             (wf-liftSubstₘ (wf-liftSubstₘ (▶-⌞∧ᶜ⌟ˡ Ψ γ₃ Ψ▶σ′))))
          ▸B)
       (*>∙∙≤liftSubst-listSubst*>∙∙ {δ = γ₃} _))
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ʳ Ψ γ₃ Ψ▶σ′) ▸u)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸t′ .proj₂)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸v .proj₂))
  (·ᶜ⋀ᶜ²<* γ₃)
  where
  Ψ▶σ′ = case ▶-⌞·⌟ Ψ (γ₃ ∧ᶜ _) Ψ▶σ of λ where
           (inj₁ (ω≡𝟘 , ok)) → ⊥-elim (𝟘ᵐ.ω≢𝟘 ok ω≡𝟘)
           (inj₂ Ψ▶σ)        → Ψ▶σ

substₘ-lemma Ψ Ψ▶σ (J₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸t′ ▸v) = J₀ₘ₂ ok
  (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
  (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸t .proj₂)
  (substₘ-lemma-∙⌜𝟘ᵐ?⌝·∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] Ψ▶σ ▸B .proj₂)
  (substₘ-lemma Ψ Ψ▶σ ▸u)
  (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸t′ .proj₂)
  (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸v .proj₂)

substₘ-lemma Ψ Ψ▶σ (Kₘ {γ₂} {γ₃} {γ₄} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v) = sub
  (Kₘ ok₁ ok₂
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ˡ Ψ γ₂ Ψ▶σ′) ▸t)
     (sub
       (substₘ-lemma (liftSubstₘ Ψ)
          (▶-cong (liftSubstₘ Ψ)
             (λ where
                x0     → PE.refl
                (_ +1) → PE.refl)
             (wf-liftSubstₘ (▶-⌞∧ᶜ⌟ˡ Ψ γ₃ Ψ▶σ″)))
          ▸B)
       (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app _ γ₃ _))))
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ˡ Ψ γ₄ Ψ▶σ‴) ▸u)
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ʳ Ψ γ₄ Ψ▶σ‴) ▸v))
  (·ᶜ⋀ᶜ⁴<* γ₂)
  where
  Ψ▶σ′ = case ▶-⌞·⌟ Ψ (γ₂ ∧ᶜ _) Ψ▶σ of λ where
           (inj₁ (ω≡𝟘 , ok)) → ⊥-elim (𝟘ᵐ.ω≢𝟘 ok ω≡𝟘)
           (inj₂ Ψ▶σ)        → Ψ▶σ
  Ψ▶σ″ = ▶-⌞∧ᶜ⌟ʳ Ψ γ₂ Ψ▶σ′
  Ψ▶σ‴ = ▶-⌞∧ᶜ⌟ʳ Ψ γ₃ Ψ▶σ″

substₘ-lemma Ψ Ψ▶σ (K₀ₘ₁ {γ₃} ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v) = sub
  (K₀ₘ₁ ok p≡𝟘
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸t .proj₂)
     (sub
       (substₘ-lemma (liftSubstₘ Ψ)
          (▶-cong (liftSubstₘ Ψ)
             (λ where
                x0      → PE.refl
                (_ +1)  → PE.refl)
             (wf-liftSubstₘ (▶-⌞∧ᶜ⌟ˡ Ψ γ₃ Ψ▶σ′)))
          ▸B)
       (≤ᶜ-reflexive (≈ᶜ-sym (liftSubstₘ-app _ γ₃ _))))
     (substₘ-lemma Ψ (▶-⌞∧ᶜ⌟ʳ Ψ γ₃ Ψ▶σ′) ▸u)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸v .proj₂))
  (·ᶜ⋀ᶜ²<* γ₃)
  where
  Ψ▶σ′ = case ▶-⌞·⌟ Ψ (γ₃ ∧ᶜ _) Ψ▶σ of λ where
           (inj₁ (ω≡𝟘 , ok)) → ⊥-elim (𝟘ᵐ.ω≢𝟘 ok ω≡𝟘)
           (inj₂ Ψ▶σ)        → Ψ▶σ

substₘ-lemma Ψ Ψ▶σ (K₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v) = K₀ₘ₂ ok
  (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
  (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸t .proj₂)
  (substₘ-lemma-∙⌜𝟘ᵐ?⌝·▸[𝟘ᵐ?] _ Ψ▶σ ▸B .proj₂)
  (substₘ-lemma Ψ Ψ▶σ ▸u)
  (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸v .proj₂)

substₘ-lemma Ψ Ψ▶σ ([]-congₘ ▸A ▸t ▸u ▸v) = sub
  ([]-congₘ
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸A .proj₂)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸t .proj₂)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸u .proj₂)
     (substₘ-lemma-𝟘ᵐ? Ψ Ψ▶σ ▸v .proj₂))
  (≤ᶜ-reflexive (<*-zeroˡ Ψ))

substₘ-lemma Ψ Ψ▶σ (sub γ▸t γ≤δ) = sub
  (substₘ-lemma Ψ (▶-≤ Ψ γ≤δ Ψ▶σ) γ▸t)
  (<*-monotone Ψ γ≤δ)

-- A substitution lemma for single substitutions.

sgSubstₘ-lemma₁ :
  γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ᵐ· p ] u →
  γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ ▸[ mo ] t [ u ]₀
sgSubstₘ-lemma₁ {γ = γ} {mo = mo} {p = p} {δ = δ} γ▸t δ▸u = sub
  (substₘ-lemma (sgSubstₘ δ)
     (▶-cong (sgSubstₘ δ)
        (λ where
           (_ +1) → PE.refl
           x0     → PE.sym (⌞⌜⌝·⌟ mo))
        (wf-sgSubstₘ (▸-·′ δ▸u)))
     γ▸t)
  (begin
     γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ              ≈⟨ +ᶜ-comm _ _ ⟩
     (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ γ              ≈˘⟨ +ᶜ-congˡ (<*-identityˡ _) ⟩
     (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ γ <* idSubstₘ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A variant of sgSubstₘ-lemma₁.

sgSubstₘ-lemma₂ :
  γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ᵐ· p ] u →
  γ +ᶜ p ·ᶜ δ ▸[ mo ] t [ u ]₀
sgSubstₘ-lemma₂ {γ = γ} {mo = 𝟙ᵐ} {p = p} {δ = δ} γ▸t δ▸u = sub
  (sgSubstₘ-lemma₁ γ▸t δ▸u)
  (begin
     γ +ᶜ p ·ᶜ δ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (·-identityˡ _)) ⟩
     γ +ᶜ (𝟙 · p) ·ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
sgSubstₘ-lemma₂ {γ = γ} {mo = 𝟘ᵐ} {p = p} {δ = δ} γ▸t δ▸u =
  sub
  (sgSubstₘ-lemma₁ γ▸t δ▸u)
  (begin
     γ +ᶜ p ·ᶜ δ        ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ (▸-𝟘ᵐ δ▸u)) ⟩
     γ +ᶜ p ·ᶜ 𝟘ᶜ       ≈⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
     γ +ᶜ 𝟘ᶜ            ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroˡ _) ⟩
     γ +ᶜ 𝟘 ·ᶜ δ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-congʳ (·-zeroˡ _)) ⟩
     γ +ᶜ (𝟘 · p) ·ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- Another variant of sgSubstₘ-lemma₁.

sgSubstₘ-lemma₃ :
  γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ] u →
  γ +ᶜ p ·ᶜ δ ▸[ mo ] t [ u ]₀
sgSubstₘ-lemma₃ {mo = 𝟘ᵐ} =
  sgSubstₘ-lemma₂
sgSubstₘ-lemma₃ {mo = 𝟙ᵐ} ▸t ▸u =
  case ▸[𝟙ᵐ]→▸[⌞⌟] ▸u of λ where
    (_ , ▸u , eq) → sub
      (sgSubstₘ-lemma₂ ▸t ▸u)
      (≤ᶜ-reflexive (+ᶜ-congˡ eq))

-- A substitution lemma for double substitutions.

doubleSubstₘ-lemma₁ :
  γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
  δ ▸[ mo ᵐ· p ] u → η ▸[ mo ᵐ· q ] u′ →
  γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η ▸[ mo ] t [ u′ ,, u ]
doubleSubstₘ-lemma₁
  {γ = γ} {mo = mo} {q = q} {p = p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = sub
  (substₘ-lemma (consSubstₘ (sgSubstₘ _) _)
     (▶-cong (consSubstₘ (sgSubstₘ _) _)
        (λ where
           x0      → PE.sym (⌞⌜⌝·⌟ mo)
           (x0 +1) → PE.sym (⌞⌜⌝·⌟ mo)
           (_ +2)  → PE.refl)
        (wf-consSubstₘ (wf-sgSubstₘ (▸-·′ η▸u′)) (▸-·′ δ▸u)))
     γ▸t)
  (begin
     γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η              ≈⟨ +ᶜ-comm _ _ ⟩
     ((⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η) +ᶜ γ            ≈⟨ +ᶜ-assoc _ _ _ ⟩
     (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η +ᶜ γ              ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (<*-identityˡ _)) ⟩
     (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η +ᶜ γ <* idSubstₘ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A variant of doubleSubstₘ-lemma₁.

doubleSubstₘ-lemma₂ :
  γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
  δ ▸[ mo ᵐ· p ] u → η ▸[ mo ᵐ· q ] u′ →
  γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η ▸[ mo ] t [ u′ ,, u ]
doubleSubstₘ-lemma₂
  {γ = γ} {mo = 𝟙ᵐ} {q = q} {p = p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = sub
  (doubleSubstₘ-lemma₁ γ▸t δ▸u η▸u′)
  (begin
     γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η              ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-congʳ (·-identityˡ _)) (·ᶜ-congʳ (·-identityˡ _))) ⟩
     γ +ᶜ (𝟙 · p) ·ᶜ δ +ᶜ (𝟙 · q) ·ᶜ η  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
doubleSubstₘ-lemma₂
  {γ = γ} {mo = 𝟘ᵐ} {q = q} {p = p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = sub
  (doubleSubstₘ-lemma₁ γ▸t δ▸u η▸u′)
  (begin
     γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η              ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ δ▸u)) (·ᶜ-monotoneʳ (▸-𝟘ᵐ η▸u′))) ⟩
     γ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ q ·ᶜ 𝟘ᶜ            ≈⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _)) ⟩
     γ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                      ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-zeroˡ _) (·ᶜ-zeroˡ _)) ⟩
     γ +ᶜ 𝟘 ·ᶜ δ +ᶜ 𝟘 ·ᶜ η              ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-congʳ (·-zeroˡ _)) (·ᶜ-congʳ (·-zeroˡ _))) ⟩
     γ +ᶜ (𝟘 · p) ·ᶜ δ +ᶜ (𝟘 · q) ·ᶜ η  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- Another variant of doubleSubstₘ-lemma₁.

doubleSubstₘ-lemma₃ :
  γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
  δ ▸[ mo ] u → η ▸[ mo ] u′ →
  γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η ▸[ mo ] t [ u′ ,, u ]
doubleSubstₘ-lemma₃ {mo = 𝟘ᵐ} =
  doubleSubstₘ-lemma₂
doubleSubstₘ-lemma₃ {mo = 𝟙ᵐ} ▸t ▸u ▸u′ =
  case ▸[𝟙ᵐ]→▸[⌞⌟] ▸u of λ where
    (_ , ▸u , eq) → case ▸[𝟙ᵐ]→▸[⌞⌟] ▸u′ of λ where
      (_ , ▸u′ , eq′) → sub
        (doubleSubstₘ-lemma₂ ▸t ▸u ▸u′)
        (≤ᶜ-reflexive (+ᶜ-congˡ (+ᶜ-cong eq eq′)))

-------------------------------------
-- Substitution matrix inference --
-------------------------------------

-- The inference functions ∥_∥ and ⌈_⌉ are related to each other: the
-- x-th row of ∥ σ ∥ mos is equivalent to ⌈ σ x ⌉ (mos x).

substₘ-calc-row :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (σ : Subst m n) (x : Fin n) →
  (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos ≈ᶜ ⌈ σ x ⌉ (mos x)
substₘ-calc-row {mos = mos} σ x0 = begin
  (𝟘ᶜ , x0 ≔ 𝟙) <* ∥ σ ∥ mos                                 ≡⟨⟩
  (𝟘ᶜ ∙ 𝟙) <* ∥ σ ∥ mos                                      ≡⟨⟩
  𝟙 ·ᶜ ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ <* ∥ tail σ ∥ (tailᵐ mos)  ≈⟨ +ᶜ-cong (·ᶜ-identityˡ _) (<*-zeroˡ (∥ tail σ ∥ _)) ⟩
  ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ                                 ≈⟨ +ᶜ-identityʳ _ ⟩
  ⌈ σ x0 ⌉ (headᵐ mos)                                       ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid
substₘ-calc-row {mos = mos} σ (x +1) = begin
  (𝟘ᶜ , x +1 ≔ 𝟙) <* ∥ σ ∥ mos                                         ≡⟨⟩
  ((𝟘ᶜ , x ≔ 𝟙) ∙ 𝟘) <* ∥ σ ∥ mos                                      ≡⟨⟩
  𝟘 ·ᶜ ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ (𝟘ᶜ , x ≔ 𝟙) <* ∥ tail σ ∥ (tailᵐ mos)  ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (substₘ-calc-row (tail σ) x) ⟩
  𝟘ᶜ +ᶜ ⌈ tail σ x ⌉ (tailᵐ mos x)                                     ≈⟨ +ᶜ-identityˡ _ ⟩
  ⌈ σ (x +1) ⌉ (tailᵐ mos x)                                           ∎
  where open Tools.Reasoning.Equivalence Conₘ-setoid

-- The expression ∥ σ ∥ mos *> (𝟘ᶜ , x ≔ p) has the same value for two
-- potentially different values of p: 𝟙 and ⌜ mos x ⌝.

∥∥-*>-𝟘ᶜ,≔𝟙 :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (σ : Subst m n) →
  (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos ≈ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* ∥ σ ∥ mos
∥∥-*>-𝟘ᶜ,≔𝟙 {x = x} {mos = mos} σ = begin
  (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos               ≈⟨ substₘ-calc-row σ _ ⟩
  ⌈ σ x ⌉ (mos x)                         ≈˘⟨ ·-⌈⌉ (σ x) ⟩
  ⌜ mos x ⌝ ·ᶜ ⌈ σ x ⌉ (mos x)            ≈˘⟨ ·ᶜ-congˡ (substₘ-calc-row σ _) ⟩
  ⌜ mos x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos  ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 (∥ σ ∥ _) ⟩
  (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* ∥ σ ∥ mos       ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

open import Graded.Modality.Dedicated-nr.Instance

-- An inferred substitution matrix is well-formed if all substituted
-- terms are well-resourced (for suitable modes), and there is a
-- dedicated nr function.

substₘ-calc-correct :
  ⦃ has-nr : Dedicated-nr ⦄ →
  (σ : Subst m n) →
  (∀ x → ∃ λ γ → γ ▸[ mos x ] σ x) → ∥ σ ∥ mos ▶[ mos ] σ
substₘ-calc-correct {mos = mos} σ prop x with prop x
... | γ , γ▸σx = sub
  (usage-inf γ▸σx)
  (begin
     (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* ∥ σ ∥ mos       ≈˘⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 (∥ σ ∥ _) ⟩
     ⌜ mos x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos  ≈⟨ ·ᶜ-congˡ (substₘ-calc-row σ _) ⟩
     ⌜ mos x ⌝ ·ᶜ ⌈ σ x ⌉ (mos x)            ≈⟨ ·-⌈⌉ {m = mos x} (σ x) ⟩
     ⌈ σ x ⌉ (mos x)                         ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- If any substitution matrix is well-formed then the inferred
-- substitution matrix is well-formed (for suitable modes) if there is
-- a dedicated nr function.

subst-calc-correct′ :
  ⦃ has-nr : Dedicated-nr ⦄ →
  (Ψ : Substₘ m n) →
  Ψ ▶[ mos ] σ → ∥ σ ∥ mos ▶[ mos ] σ
subst-calc-correct′ {mos = mos} {σ = σ} (Ψ ⊙ γ) Ψ▶σ x0 = sub
  (usage-inf (Ψ▶σ x0))
  (begin
     ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ
     𝟘ᶜ <* ∥ tail σ ∥ (tailᵐ mos)                   ≈⟨ +ᶜ-congˡ (<*-zeroˡ (∥ tail σ ∥ _)) ⟩

     ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩

     ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos)        ≈⟨ ·-⌈⌉ (head σ) ⟩

     ⌈ head σ ⌉ (headᵐ mos)                         ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
subst-calc-correct′ (Ψ ⊙ γ) Ψ▶σ (x +1) =
  sub (subst-calc-correct′ Ψ (wf-tailSubstₘ Ψ▶σ) x)
      (≤ᶜ-reflexive (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ _)) (+ᶜ-identityˡ _)))

-- If there is a dedicated nr function and the strong unit type is not
-- allowed to be used as a sink, then each row of a calculated
-- substitution matrix is an upper bound of the usage contexts (for a
-- suitable mode) of the corresponding substituted term.

substₘ-calc-upper-bound :
  ⦃ has-nr : Dedicated-nr ⦄ →
  ⦃ ¬Starˢ-sink ⦄ →
  {γ : Conₘ m} (σ : Subst m n) (x : Fin n) →
  γ ▸[ mos x ] σ x → γ ≤ᶜ  (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos
substₘ-calc-upper-bound σ x γ▸σx =
  ≤ᶜ-trans (usage-upper-bound γ▸σx)
           (≤ᶜ-reflexive (≈ᶜ-sym (substₘ-calc-row σ x)))

--------------------------------------------------
-- Well-formedness of substitution compositions --
--------------------------------------------------

-- Compositions of suitably well-formed substitutions are well-formed.

wf-compSubst :
  (Ψ : Substₘ m ℓ) {Φ : Substₘ ℓ n} {σ : Subst m ℓ} {σ′ : Subst ℓ n} →
  Ψ ▶[ ⌞ ⌜ mos ⌝ᶜ <* Φ ⌟ᶜ ] σ → Φ ▶[ mos ] σ′ →
  (Ψ <*> Φ) ▶[ mos ] (σ ₛ•ₛ σ′)
wf-compSubst {mos = mos} Ψ {Φ = Φ} {σ = σ} {σ′ = σ′} Ψ▶σ Φ▶σ′ x = sub
  (substₘ-lemma Ψ
     (▶-cong Ψ
        (λ y → cong (λ p → ⌞ (𝟘ᶜ , x ≔ p) <* Φ ⌟ᶜ y) (⌜⌝ᶜ⟨⟩ {ms = mos} x))
        (▶-⌞<*⌟ {γ = ⌜ mos ⌝ᶜ} Ψ {Φ = Φ} Ψ▶σ))
     (Φ▶σ′ x))
  (begin
     (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* (Ψ <*> Φ)       ≈˘⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 (Ψ <*> Φ) ⟩
     ⌜ mos x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* (Ψ <*> Φ)  ≈⟨ ·ᶜ-congˡ (<*-<*>-assoc Ψ Φ (𝟘ᶜ , x ≔ 𝟙)) ⟩
     ⌜ mos x ⌝ ·ᶜ ((𝟘ᶜ , x ≔ 𝟙) <* Φ) <* Ψ   ≈˘⟨ <*-distrib-·ᶜ Ψ _ ((𝟘ᶜ , x ≔ 𝟙) <* Φ) ⟩
     (⌜ mos x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Φ) <* Ψ   ≈⟨ <*-cong Ψ (·ᶜ-<*-𝟘ᶜ,≔𝟙 Φ) ⟩
     ((𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Φ) <* Ψ        ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
