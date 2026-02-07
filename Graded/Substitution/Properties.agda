------------------------------------------------------------------------
-- Properties of substitution matrices.
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Substitution.Properties
  {a b} {M : Set a} {Mode : Set b}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Graded.Mode Mode 𝕄)
  {𝐌 : IsMode}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Substitution R
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Properties R
import Graded.Usage.Restrictions.Instance
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Graded.Usage.Weakening R
open import Definition.Untyped M

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private
  variable
    k ℓ m n i : Nat
    x y : Fin n
    γ γ′ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ η θ χ : Conₘ n
    Ψ : Substₘ m n
    A B t u u′ v w : Term n
    σ : Subst m n
    p q r : M
    mo mo₁ mo₂ mo₃ mo₄ mo′ : Mode
    mos mos₁ mos₂ : Mode-vector n

------------------------------------------------------------------------
-- Properties of <*

opaque

  -- Modality substitution application is a monotone function.
  -- If γ ≤ᶜ δ, then γ <* Ψ ≤ᶜ δ <* Ψ.
  -- Proof by induction on Ψ using monotonicity of addition and multiplication.

  <*-monotone : {γ δ : Conₘ n} (Ψ : Substₘ m n) → γ ≤ᶜ δ → γ <* Ψ ≤ᶜ δ <* Ψ
  <*-monotone {γ = ε}     {δ = ε}     []      γ≤δ         = ≤ᶜ-refl
  <*-monotone {γ = _ ∙ _} {δ = _ ∙ _} (Ψ ⊙ η) (γ≤δ ∙ p≤q) =
    +ᶜ-monotone (·ᶜ-monotoneˡ p≤q) (<*-monotone Ψ γ≤δ)

opaque

  -- The function  <*_Ψ preserves equivalence.

  <*-cong : (Ψ : Substₘ m n) → γ ≈ᶜ δ → γ <* Ψ ≈ᶜ δ <* Ψ
  <*-cong Ψ γ≈ᶜδ = ≤ᶜ-antisym
    (<*-monotone Ψ (≤ᶜ-reflexive γ≈ᶜδ))
    (<*-monotone Ψ (≤ᶜ-reflexive (≈ᶜ-sym γ≈ᶜδ)))

opaque

  -- Modality substitution application distributes over addition.
  -- (γ +ᶜ δ) <* Ψ ≈ᶜ γ <* Ψ +ᶜ δ <* Ψ.
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
    where
    open ≈ᶜ-reasoning

opaque

  -- Modality substitution application distributes over context scaling.
  -- (pγ) <* Ψ ≈ᶜ p ·ᶜ (γ <* Ψ).
  -- Proof by induction on Ψ using zero and associtivity of multiplication,
  -- and distributivity of multiplication over addition.

  <*-distrib-·ᶜ : (Ψ : Substₘ m n) (p : M) (γ : Conₘ n)
                → (p ·ᶜ γ) <* Ψ ≈ᶜ p ·ᶜ (γ <* Ψ)
  <*-distrib-·ᶜ [] p ε = ≈ᶜ-sym (·ᶜ-zeroʳ p)
  <*-distrib-·ᶜ (Ψ ⊙ δ) p (γ ∙ q) = begin
    (p · q) ·ᶜ δ +ᶜ (p ·ᶜ γ) <* Ψ  ≈⟨ +ᶜ-cong (·ᶜ-assoc p q δ) (<*-distrib-·ᶜ Ψ p γ) ⟩
    p ·ᶜ (q ·ᶜ δ) +ᶜ p ·ᶜ (γ <* Ψ) ≈˘⟨ ·ᶜ-distribˡ-+ᶜ p (q ·ᶜ δ) (γ <* Ψ) ⟩
    p ·ᶜ (q ·ᶜ δ +ᶜ γ <* Ψ)        ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- Modality substitution application is linear, i.e. distributes over addition and scaling.
  -- (pγ +ᶜ qδ) <* Ψ ≈ᶜ p ·ᶜ (γ <* Ψ) +ᶜ q ·ᶜ (δ <* Ψ).
  -- Follows from the distributivity over addition and multiplication.

  <*-linear : (Ψ : Substₘ m n) (p q : M) (γ δ : Conₘ n)
            → (p ·ᶜ γ +ᶜ q ·ᶜ δ) <* Ψ ≈ᶜ p ·ᶜ γ <* Ψ +ᶜ q ·ᶜ δ <* Ψ
  <*-linear Ψ p q γ δ = begin
    (p ·ᶜ γ +ᶜ q ·ᶜ δ) <* Ψ        ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) (q ·ᶜ δ) ⟩
    (p ·ᶜ γ) <* Ψ +ᶜ (q ·ᶜ δ) <* Ψ ≈⟨ +ᶜ-cong (<*-distrib-·ᶜ Ψ p γ) (<*-distrib-·ᶜ Ψ q δ) ⟩
    (p ·ᶜ γ <* Ψ +ᶜ q ·ᶜ δ <* Ψ)   ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- Modality substitution application sub-distributes over meet.
  -- (γ ∧ᶜ δ) <* Ψ ≤ᶜ γ <* Ψ ∧ᶜ δ <* Ψ

  <*-sub-distrib-∧ᶜ : (Ψ : Substₘ m n) (γ δ : Conₘ n) → (γ ∧ᶜ δ) <* Ψ ≤ᶜ γ <* Ψ ∧ᶜ δ <* Ψ
  <*-sub-distrib-∧ᶜ [] ε ε = begin
    𝟘ᶜ        ≈˘⟨ ∧ᶜ-idem _ ⟩
    𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎
    where
    open ≤ᶜ-reasoning
  <*-sub-distrib-∧ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) = begin
    (p ∧ q) ·ᶜ η +ᶜ (γ ∧ᶜ δ) <* Ψ             ≤⟨ +ᶜ-monotone (≤ᶜ-reflexive (·ᶜ-distribʳ-∧ᶜ _ _ _))
                                                            (<*-sub-distrib-∧ᶜ Ψ γ δ) ⟩
    (p ·ᶜ η ∧ᶜ q ·ᶜ η) +ᶜ (γ <* Ψ ∧ᶜ δ <* Ψ)  ≤⟨ +ᶜ-sub-interchangeable-∧ᶜ _ _ _ _ ⟩
    (p ·ᶜ η +ᶜ γ <* Ψ) ∧ᶜ (q ·ᶜ η +ᶜ δ <* Ψ)  ∎
    where
    open ≤ᶜ-reasoning

opaque

  -- Modality substitution application sub-distributes over the two first arguments of ⊛ᶜ
  -- γ ⊛ᶜ δ ▷ r <* Ψ ≤ (γ <* Ψ) ⊛ (δ <* Ψ) ▷ r
  -- Proof by induction on Ψ using sub-distributivity and interchange properties of ⊛ᶜ

  <*-sub-distrib-⊛ᶜ :
    ⦃ has-star : Has-star 𝕄 ⦄ →
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
    where
    open ≤ᶜ-reasoning

opaque

  -- The function _<* Ψ sub-distributes over nrᶜ p r.

  <*-sub-distrib-nrᶜ :
    ⦃ has-nr : Has-nr 𝕄 ⦄ →
    (Ψ : Substₘ m n) (γ : Conₘ n) →
    nrᶜ p r γ δ η <* Ψ ≤ᶜ nrᶜ p r (γ <* Ψ) (δ <* Ψ) (η <* Ψ)
  <*-sub-distrib-nrᶜ {p = p} {r = r} {δ = ε} {η = ε} [] ε = begin
    𝟘ᶜ                ≈˘⟨ nrᶜ-𝟘ᶜ ⟩
    nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ∎
    where
    open ≤ᶜ-reasoning
  <*-sub-distrib-nrᶜ
    {p = p} {r = r} {δ = δ ∙ s} {η = η ∙ n} (Ψ ⊙ θ) (γ ∙ z) = begin
    nr p r z s n ·ᶜ θ +ᶜ nrᶜ p r γ δ η <* Ψ                           ≤⟨ +ᶜ-monotone nrᶜ-·ᶜ (<*-sub-distrib-nrᶜ Ψ γ) ⟩

    nrᶜ p r (z ·ᶜ θ) (s ·ᶜ θ) (n ·ᶜ θ) +ᶜ
    nrᶜ p r (γ <* Ψ) (δ <* Ψ) (η <* Ψ)                                ≤⟨ nrᶜ-+ᶜ ⟩

    nrᶜ p r (z ·ᶜ θ +ᶜ γ <* Ψ) (s ·ᶜ θ +ᶜ δ <* Ψ) (n ·ᶜ θ +ᶜ η <* Ψ)  ∎
    where
    open ≤ᶜ-reasoning

opaque

  -- Distributivity of <* over nrᵢ

  <*-distrib-nrᵢᶜ :
    ∀ (Ψ : Substₘ m n) (γ : Conₘ n) →
    nrᵢᶜ r γ δ i <* Ψ ≈ᶜ nrᵢᶜ r (γ <* Ψ) (δ <* Ψ) i
  <*-distrib-nrᵢᶜ {r = r} {(ε)} [] ε = ≈ᶜ-sym nrᵢᶜ-𝟘ᶜ
  <*-distrib-nrᵢᶜ {r = r} {δ ∙ q} {i} (Ψ ⊙ η) (γ ∙ p) = begin
    nrᵢ r p q i ·ᶜ η +ᶜ nrᵢᶜ r γ δ i <* Ψ                    ≈⟨ +ᶜ-cong ·ᶜ-distribʳ-nrᵢᶜ (<*-distrib-nrᵢᶜ Ψ γ) ⟩
    nrᵢᶜ r (p ·ᶜ η) (q ·ᶜ η) i +ᶜ nrᵢᶜ r (γ <* Ψ) (δ <* Ψ) i ≈˘⟨ nrᵢᶜ-+ᶜ ⟩
    nrᵢᶜ r (p ·ᶜ η +ᶜ γ <* Ψ) (q ·ᶜ η +ᶜ δ <* Ψ) i ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- The zero-context is a left zero to modality substitution application.
  -- 𝟘ᶜ <* Ψ ≡ 𝟘ᶜ.
  -- Proof by induction on Ψ using zero of multiplication and identity of addition.

  <*-zeroˡ : (Ψ : Substₘ m n) → 𝟘ᶜ <* Ψ ≈ᶜ 𝟘ᶜ
  <*-zeroˡ []      = ≈ᶜ-refl
  <*-zeroˡ (Ψ ⊙ γ) = begin
    𝟘ᶜ <* (Ψ ⊙ γ)       ≡⟨⟩
    𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ <* Ψ) ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ γ) (<*-zeroˡ Ψ) ⟩
    𝟘ᶜ +ᶜ 𝟘ᶜ            ≈⟨ +ᶜ-identityˡ 𝟘ᶜ ⟩
    𝟘ᶜ                  ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- The substitution family εₘ is a kind of right zero for _<*_.

  <*-zeroʳ : (γ : Conₘ n) → γ <* εₘ ≈ᶜ ε
  <*-zeroʳ ε       = ε
  <*-zeroʳ (γ ∙ p) = begin
    ε +ᶜ γ <* εₘ  ≈⟨ +ᶜ-congˡ (<*-zeroʳ γ) ⟩
    ε +ᶜ ε        ≈⟨ +ᶜ-identityˡ _ ⟩
    ε             ∎
    where
    open ≈ᶜ-reasoning

opaque

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
    where
    open ≈ᶜ-reasoning

opaque

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
    open ≈ᶜ-reasoning

opaque

  -- A kind of "sub-distributivity" property for greatest lower bounds
  -- of nrᵢᶜ sequences.

  nrᵢᶜ-<*-GLBᶜ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    (Ψ : Substₘ m n) →
    Greatest-lower-boundᶜ γ (nrᵢᶜ r δ η) →
    ∃ λ χ → Greatest-lower-boundᶜ χ (λ i → nrᵢᶜ r δ η i <* Ψ) ×
      γ <* Ψ ≤ᶜ χ
  nrᵢᶜ-<*-GLBᶜ {γ = ε} {δ = ε} {η = ε} [] _ =
    𝟘ᶜ , GLBᶜ-const (λ _ → ≈ᶜ-refl) , ≤ᶜ-refl
  nrᵢᶜ-<*-GLBᶜ {γ = γ ∙ p} {r} {δ = δ ∙ q} {η = η ∙ q′} (Ψ ⊙ θ) γp-glb =
    let γ-glb , p-glb = GLBᶜ-pointwise γp-glb
        χ′ , χ′-glb , ≤χ′ = nrᵢᶜ-<*-GLBᶜ Ψ γ-glb
        pθ-glb = GLBᶜ-congˡ (λ _ → ·ᶜ-distribʳ-nrᵢᶜ)
                   (·ᶜ-GLBᶜʳ {γ = θ} p-glb)
        χ , χ-glb , ≤χ = +ᶜnrᵢᶜ-GLBᶜ pθ-glb (GLBᶜ-congˡ (λ _ → <*-distrib-nrᵢᶜ Ψ δ) χ′-glb)
    in  _ , GLBᶜ-congˡ (λ i → ≈ᶜ-trans nrᵢᶜ-+ᶜ (≈ᶜ-sym (+ᶜ-cong ·ᶜ-distribʳ-nrᵢᶜ (<*-distrib-nrᵢᶜ Ψ δ)))) χ-glb ,
        (begin
          (γ ∙ p) <* (Ψ ⊙ θ) ≡⟨⟩
          p ·ᶜ θ +ᶜ γ <* Ψ   ≤⟨ +ᶜ-monotoneʳ ≤χ′ ⟩
          p ·ᶜ θ +ᶜ χ′       ≤⟨ ≤χ ⟩
          χ ∎)
    where
    open ≤ᶜ-reasoning
    open Graded.Usage.Restrictions.Instance R

opaque

  -- A variant of the above

  nrᵢᶜ-<*-GLBᶜ′ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    (Ψ : Substₘ m n) →
    Greatest-lower-boundᶜ γ (nrᵢᶜ r δ η) →
    ∃ λ χ → Greatest-lower-boundᶜ χ (λ i → nrᵢᶜ r (δ <* Ψ) (η <* Ψ) i) ×
      γ <* Ψ ≤ᶜ χ
  nrᵢᶜ-<*-GLBᶜ′ {δ} Ψ γ-GLB =
    let _ , χ-GLB , ≤χ = nrᵢᶜ-<*-GLBᶜ Ψ γ-GLB
    in  _ , GLBᶜ-congˡ (λ _ → <*-distrib-nrᵢᶜ Ψ δ) χ-GLB , ≤χ

------------------------------------------------------------------------
-- Properties of specific substitutions

opaque

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
    where
    open ≈ᶜ-reasoning

opaque

  -- A "reduction rule" for _<*_ and wkSubstₘ′.

  <*-wkSubstₘ′ :
    (γ : Conₘ n) →
    γ <* wkSubstₘ′ k Ψ ≈ᶜ wkConₘ (stepn id k) (γ <* Ψ)
  <*-wkSubstₘ′ {k = 0}        _ = ≈ᶜ-refl
  <*-wkSubstₘ′ {k = 1+ k} {Ψ} γ = begin
    γ <* wk1Substₘ (wkSubstₘ′ k Ψ)    ≈⟨ wk1Substₘ-app _ γ ⟩
    (γ <* wkSubstₘ′ k Ψ) ∙ 𝟘          ≈⟨ <*-wkSubstₘ′ γ ∙ refl ⟩
    wkConₘ (stepn id k) (γ <* Ψ) ∙ 𝟘  ∎
    where
    open ≈ᶜ-reasoning

opaque

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
    where
    open ≈ᶜ-reasoning

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
    where
    open ≈ᶜ-reasoning

opaque

  -- The identity matrix is a left identity to substitution application.
  -- γ <* idSubstₘ ≈ᶜ γ.
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
    where
    open ≈ᶜ-reasoning


opaque

  unfolding replace₁ₘ

  -- A "reduction rule" for _<*_ and replace₁ₘ.

  <*-replace₁ₘ :
    (γ ∙ p) <* replace₁ₘ k δ ≈ᶜ p ·ᶜ δ +ᶜ wkConₘ (stepn id k) γ
  <*-replace₁ₘ {γ} {p} {k} {δ} = begin
    p ·ᶜ δ +ᶜ γ <* wkSubstₘ′ k idSubstₘ            ≈⟨ +ᶜ-congˡ (<*-wkSubstₘ′ γ) ⟩
    p ·ᶜ δ +ᶜ wkConₘ (stepn id k) (γ <* idSubstₘ)  ≈⟨ +ᶜ-congˡ (wk-≈ᶜ (stepn _ k) (<*-identityˡ _)) ⟩
    p ·ᶜ δ +ᶜ wkConₘ (stepn id k) γ                ∎
    where
    open ≈ᶜ-reasoning

opaque
  unfolding replace₂ₘ

  -- A "reduction rule" for _<*_ and replace₂ₘ.

  <*-replace₂ₘ :
    (γ ∙ p ∙ q) <* replace₂ₘ δ η ≈ᶜ
    p ·ᶜ δ +ᶜ q ·ᶜ η +ᶜ wkConₘ (stepn id 2) γ
  <*-replace₂ₘ {γ} {p} {q} {δ} {η} = begin
    q ·ᶜ η +ᶜ p ·ᶜ δ +ᶜ γ <* wkSubstₘ′ 2 idSubstₘ              ≈˘⟨ +ᶜ-assoc _ _ _ ⟩
    (q ·ᶜ η +ᶜ p ·ᶜ δ) +ᶜ γ <* wkSubstₘ′ 2 idSubstₘ            ≈⟨ +ᶜ-cong (+ᶜ-comm _ _) (<*-wkSubstₘ′ {k = 2} γ) ⟩
    (p ·ᶜ δ +ᶜ q ·ᶜ η) +ᶜ wkConₘ (stepn id 2) (γ <* idSubstₘ)  ≈⟨ +ᶜ-congˡ (wk-≈ᶜ (stepn id 2) (<*-identityˡ _)) ⟩
    (p ·ᶜ δ +ᶜ q ·ᶜ η) +ᶜ wkConₘ (stepn id 2) γ                ≈⟨ +ᶜ-assoc _ _ _ ⟩
    p ·ᶜ δ +ᶜ q ·ᶜ η +ᶜ wkConₘ (stepn id 2) γ                  ∎
    where
    open ≈ᶜ-reasoning

------------------------------------------------------------------------
-- Well-formed substitutions

opaque

  -- The identity substitution is well-formed.

  wf-idSubstₘ :
    {mos : Mode-vector n} →
    idSubstₘ ▶[ mos ] idSubst
  wf-idSubstₘ {mos} x = sub var $ begin
    (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* idSubstₘ  ≈⟨ <*-identityˡ _ ⟩
    𝟘ᶜ , x ≔ ⌜ mos x ⌝                ∎
    where
    open ≤ᶜ-reasoning

opaque

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
    open ≤ᶜ-reasoning
  wf-sgSubstₘ {γ = γ} {mos = mos} _ (x +1) = sub
    var
    (begin
       𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* idSubstₘ  ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ γ) (<*-identityˡ _) ⟩
       𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝)                  ≈⟨ +ᶜ-identityˡ _ ⟩
       𝟘ᶜ , x ≔ ⌜ mos x ⌝                          ∎)
    where
    open ≤ᶜ-reasoning

opaque

  -- The one-step weakening of a well-formed substitution is
  -- well-formed.

  wf-wk1Substₘ : (Ψ : Substₘ m n) (σ : Subst m n)
               → Ψ ▶[ mos ] σ → wk1Substₘ Ψ ▶[ mos ] wk1Subst σ
  wf-wk1Substₘ Ψ σ Ψ▶σ x =
    sub-≈ᶜ (wkUsage (step id) (Ψ▶σ x)) (wk1Substₘ-app Ψ (𝟘ᶜ , x ≔ _))

opaque

  -- A well-formedness lemma for wkSubstₘ′.

  wf-wkSubstₘ′ : Ψ ▶[ mos ] σ → wkSubstₘ′ k Ψ ▶[ mos ] wkSubst k σ
  wf-wkSubstₘ′ {k = 0}    = idᶠ
  wf-wkSubstₘ′ {k = 1+ _} = wf-wk1Substₘ _ _ ∘→ wf-wkSubstₘ′

opaque

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
    open ≤ᶜ-reasoning
  wf-liftSubstₘ {mos = mos} {Ψ = Ψ} Ψ▶σ (x +1) = sub
    (wf-wk1Substₘ Ψ _ Ψ▶σ x)
    (begin
      (𝟘 ·ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟙) +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* wk1Substₘ Ψ  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _ ∙ ·-zeroˡ _) ⟩
      𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* wk1Substₘ Ψ                 ≈⟨ +ᶜ-identityˡ _ ⟩
      (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* wk1Substₘ Ψ                       ∎)
    where
    open ≤ᶜ-reasoning

opaque

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
    open ≤ᶜ-reasoning
  wf-consSubstₘ {mos = mos} {Ψ = Ψ} {γ = γ} Ψ▶σ γ▸t (x +1) = sub
    (Ψ▶σ x)
    (begin
       𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
       𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ     ≈⟨ +ᶜ-identityˡ _ ⟩
       (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* Ψ           ∎)
    where
    open ≤ᶜ-reasoning

opaque

  -- The tail of a well-formed substitution is a well-formed
  -- substitution.

  wf-tailSubstₘ :
    {Ψ : Substₘ m n} →
    (Ψ ⊙ γ) ▶[ mos ] σ → Ψ ▶[ tailᵐ mos ] tail σ
  wf-tailSubstₘ Ψ▶σ x =
    sub-≈ᶜ (Ψ▶σ (x +1))
      (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ _)) (+ᶜ-identityˡ _)))

opaque
  unfolding replace₁ₘ

  -- A well-formedness lemma for replace₁ₘ.

  wf-replace₁ₘ :
    ⌜ mo ⌝ ·ᶜ γ ▸[ mo ] t →
    replace₁ₘ k γ ▶[ consᵐ mo mos ] replace₁ k t
  wf-replace₁ₘ = wf-consSubstₘ (wf-wkSubstₘ′ wf-idSubstₘ)

opaque
  unfolding replace₂ replace₂ₘ

  -- A well-formedness lemma for replace₂ₘ.

  wf-replace₂ₘ :
    ⌜ mo₂ ⌝ ·ᶜ γ ▸[ mo₂ ] t →
    ⌜ mo₁ ⌝ ·ᶜ δ ▸[ mo₁ ] u →
    replace₂ₘ γ δ ▶[ consᵐ mo₁ (consᵐ mo₂ mos) ] replace₂ t u
  wf-replace₂ₘ ▸t ▸u =
    wf-consSubstₘ (wf-consSubstₘ (wf-wkSubstₘ′ wf-idSubstₘ) ▸t) ▸u

opaque

  -- A preservation lemma for _▶[_]_.

  ▶-cong :
    (Ψ : Substₘ m n) →
    (∀ x → mos₁ x ≡ mos₂ x) → Ψ ▶[ mos₁ ] σ → Ψ ▶[ mos₂ ] σ
  ▶-cong Ψ mos₁≡mos₂ Ψ▶ x0 =
    PE.subst (λ mo → (𝟘ᶜ ∙ ⌜ mo ⌝) <* Ψ ▸[ mo ] _) (mos₁≡mos₂ x0) (Ψ▶ x0)
  ▶-cong {mos₁ = mos₁} {mos₂ = mos₂} (Ψ ⊙ γ) mos₁≡mos₂ Ψ⊙▶ (x +1) = sub-≈ᶜ
    (▶-cong Ψ (λ x → mos₁≡mos₂ (x +1))
      (λ x → sub-≈ᶜ (Ψ⊙▶ (x +1)) (≈ᶜ-sym (lemma mos₁ x)))
      x)
    (lemma mos₂ x)
    where
    open ≈ᶜ-reasoning
    lemma :
      ∀ (mos : Mode-vector (1+ _)) x →
        𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝) <* Ψ ≈ᶜ
        (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝) <* Ψ
    lemma = λ mos x → begin
       𝟘 ·ᶜ γ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝) <* Ψ  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
       𝟘ᶜ +ᶜ (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝) <* Ψ      ≈⟨ +ᶜ-identityˡ _ ⟩
       (𝟘ᶜ , x ≔ ⌜ mos (x +1) ⌝) <* Ψ            ∎

opaque

  -- Another preservation lemma for _▶[_]_.

  ▶-≤ :
    (Ψ : Substₘ m n) →
    γ ≤ᶜ δ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
  ▶-≤ Ψ γ≤δ Ψ▶ x = sub
    (▸-≤ (lookup-monotone _ γ≤δ)
       (sub-≈ᶜ (Ψ▶ x) (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
    (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))

opaque

  -- A preservation lemma for _▶[_]_ that holds if there is only one mode

  ▶-Trivialᵐ : Trivialᵐ → Ψ ▶[ mos₁ ] σ → Ψ ▶[ mos₂ ] σ
  ▶-Trivialᵐ trivial ▶σ =
    ▶-cong _ (λ _ → ≡-trivialᵐ trivial) ▶σ

opaque

  -- An inversion lemma for _▶[_]_ related to multiplication.

  ▶-⌞·ᶜ⌟ :
    {Ψ : Substₘ m n} (γ : Conₘ n) →
    Ψ ▶[ ⌞ p ·ᶜ γ ⌟ᶜ ] σ →
    Ψ ▶[ ⌞ ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ⌟ᶜ ] σ
  ▶-⌞·ᶜ⌟ {p} {Ψ} γ ▶σ =
    ▶-cong Ψ (λ x → begin
      ⌞ (p ·ᶜ γ) ⟨ x ⟩ ⌟           ≡⟨ ⌞⌟-cong (lookup-distrib-·ᶜ γ _ x) ⟩
      ⌞ p · γ ⟨ x ⟩ ⌟              ≡˘⟨ ⌞⌟·ᵐ ⟩
      ⌞ p ⌟ ·ᵐ ⌞ γ ⟨ x ⟩ ⌟         ≡˘⟨ ·ᵐ-congʳ (⌞⌜⌝⌟ _) ⟩
      ⌞ ⌜ ⌞ p ⌟ ⌝ ⌟ ·ᵐ ⌞ γ ⟨ x ⟩ ⌟ ≡⟨ ⌞⌟·ᵐ ⟩
      ⌞ ⌜ ⌞ p ⌟ ⌝ · γ ⟨ x ⟩ ⌟      ≡˘⟨ ⌞⌟-cong (lookup-distrib-·ᶜ γ _ x) ⟩
      ⌞ (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ) ⟨ x ⟩ ⌟   ∎) ▶σ
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- An inversion lemma for _▶[_]_ related to addition.

  ▶-⌞+ᶜ⌟ˡ :
    {Ψ : Substₘ m n}
    (γ : Conₘ n) →
    Ψ ▶[ ⌞ γ +ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
  ▶-⌞+ᶜ⌟ˡ {δ} {Ψ} γ ▶σ x =
    sub-≈ᶜ (▸-⌞+⌟ˡ (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-+ᶜ γ _ _)) (▶σ x)) (begin
        ⌜ ⌞ γ ⟨ x ⟩ + δ ⟨ x ⟩ ⌟ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⟨ x ⟩ + δ ⟨ x ⟩ ⌟ ⌝) <* Ψ      ≡˘⟨ cong (λ p → (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) <* Ψ)
                                                             (lookup-distrib-+ᶜ γ _ _) ⟩
        (𝟘ᶜ , x ≔ ⌜ ⌞ γ +ᶜ δ ⌟ᶜ x ⌝) <* Ψ               ∎)))
      (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ))
    where
    open ≤ᶜ-reasoning

opaque

  -- An inversion lemma for _▶[_]_ related to addition.

  ▶-⌞+ᶜ⌟ʳ :
    {Ψ : Substₘ m n}
    (γ : Conₘ n) →
    Ψ ▶[ ⌞ γ +ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
  ▶-⌞+ᶜ⌟ʳ {δ} {Ψ} γ ▶σ =
    ▶-⌞+ᶜ⌟ˡ δ (▶-cong Ψ (⌞⌟ᶜ-cong (+ᶜ-comm γ _)) ▶σ)

opaque

  -- An inversion lemma for _▸[_]_ related to _<*_.

  ▸-⌞<*⌟ :
    (Ψ : Substₘ m n) →
    ⌜ ⌞ γ <* Ψ ⌟ᶜ y ⌝ ·ᶜ δ ▸[ ⌞ γ <* Ψ ⌟ᶜ y ] t →
    ⌜ ⌞ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ ⌟ᶜ y ⌝ ·ᶜ δ
      ▸[ ⌞ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Ψ ⌟ᶜ y ] t
  ▸-⌞<*⌟ {γ = ε}                 {x = ()}
  ▸-⌞<*⌟ {γ = γ ∙ p} {y} {δ} {t} {x = x0} (Ψ ⊙ η) ▸₁ = ▸₄
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
      open ≈ᶜ-reasoning

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
      open ≈ᶜ-reasoning

opaque

  -- An inversion lemma for _▶[_]_ related to _<*_.

  ▶-⌞<*⌟ :
    (Ψ : Substₘ ℓ m) {Φ : Substₘ m n} →
    Ψ ▶[ ⌞ γ <* Φ ⌟ᶜ ] σ →
    Ψ ▶[ ⌞ (𝟘ᶜ , x ≔ γ ⟨ x ⟩) <* Φ ⌟ᶜ ] σ
  ▶-⌞<*⌟ {γ = γ} {x = x} Ψ {Φ = Φ} Ψ▶ y = sub
    (▸-⌞<*⌟ {γ = γ} Φ (sub-≈ᶜ (Ψ▶ y) (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
    (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))

opaque

  -- An inversion lemma for _▶[_]_ related to the meet operation.

  ▶-⌞∧ᶜ⌟ˡ :
    {Ψ : Substₘ m n} (γ : Conₘ n) →
    Ψ ▶[ ⌞ γ ∧ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ γ ⌟ᶜ ] σ
  ▶-⌞∧ᶜ⌟ˡ {δ} {Ψ} γ ▶σ x = sub
    (▸-⌞∧⌟ˡ
       (sub (▸-cong (cong ⌞_⌟ (lookup-distrib-∧ᶜ γ _ _)) (▶σ x)) (begin
          ⌜ ⌞ γ ⟨ x ⟩ ∧ δ ⟨ x ⟩ ⌟ ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* Ψ  ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ ⟩
          (𝟘ᶜ , x ≔ ⌜ ⌞ γ ⟨ x ⟩ ∧ δ ⟨ x ⟩ ⌟ ⌝) <* Ψ       ≡˘⟨ cong (λ p → (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) <* Ψ)
                                                                       (lookup-distrib-∧ᶜ γ _ _) ⟩
          (𝟘ᶜ , x ≔ ⌜ ⌞ γ ∧ᶜ δ ⌟ᶜ x ⌝) <* Ψ               ∎)))
    (≤ᶜ-reflexive (≈ᶜ-sym (·ᶜ-<*-𝟘ᶜ,≔𝟙 Ψ)))
    where
    open ≤ᶜ-reasoning

opaque

  -- An inversion lemma for _▶[_]_ related to the meet operation.

  ▶-⌞∧ᶜ⌟ʳ :
    {Ψ : Substₘ m n} (γ : Conₘ n) →
    Ψ ▶[ ⌞ γ ∧ᶜ δ ⌟ᶜ ] σ → Ψ ▶[ ⌞ δ ⌟ᶜ ] σ
  ▶-⌞∧ᶜ⌟ʳ {δ} γ Ψ▶ =
    ▶-⌞∧ᶜ⌟ˡ δ (▶-cong _ (⌞⌟ᶜ-cong (∧ᶜ-comm γ _)) Ψ▶)

opaque

  -- An inversion lemma for _▶[_]_ related to the star operation.

  ▶-⌞⊛ᶜ⌟ˡ :
    ⦃ has-star : Has-star 𝕄 ⦄ →
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
    open ≤ᶜ-reasoning

opaque

  -- An inversion lemma for _▶[_]_ related to the star operation.

  ▶-⌞⊛ᶜ⌟ʳ :
    ⦃ has-star : Has-star 𝕄 ⦄ →
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
    open ≤ᶜ-reasoning

opaque

  -- An inversion lemma for _▶[_]_ related to the nr function.

  ▶-⌞nrᶜ⌟₁ :
    ⦃ has-nr : Nr-available ⦄ →
    let open Graded.Usage.Restrictions.Instance R in
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
    open ≤ᶜ-reasoning
    open Graded.Usage.Restrictions.Instance R

opaque

  -- An inversion lemma for _▶[_]_ related to the nr function.

  ▶-⌞nrᶜ⌟₂ :
    ⦃ has-nr : Has-nr 𝕄 ⦄ →
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
    open ≤ᶜ-reasoning

opaque

  -- An inversion lemma for _▶[_]_ related to the nr function.

  ▶-⌞nrᶜ⌟₃ :
    ⦃ has-nr : Nr-available ⦄ →
    let open Graded.Usage.Restrictions.Instance R in
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
    open ≤ᶜ-reasoning
    open Graded.Usage.Restrictions.Instance R

opaque

  -- If a substitution is well-resourced under some matrix and
  -- mode vector it is also well-resourced under the vector where
  -- all modes are 𝟘.

  ▶-⌞𝟘ᶜ⌟ :
    {Ψ : Substₘ m n} →
    Ψ ▶[ mos ] σ → Ψ ▶[ ⌞ 𝟘ᶜ ⌟ᶜ ] σ
  ▶-⌞𝟘ᶜ⌟ {mos} {Ψ} Ψ▶σ =
    ▶-⌞+ᶜ⌟ˡ 𝟘ᶜ (▶-cong Ψ lemma Ψ▶σ)
    where
    open Tools.Reasoning.PropositionalEquality
    lemma : ∀ x → mos x ≡ ⌞ 𝟘ᶜ +ᶜ ⌜ mos ⌝ᶜ ⌟ᶜ x
    lemma x = begin
      mos x                       ≡˘⟨ ⌞⌜⌝⌟ (mos x) ⟩
      ⌞ ⌜ mos x ⌝ ⌟               ≡˘⟨ ⌞⌟-cong (⌜⌝ᶜ⟨⟩ x) ⟩
      ⌞ ⌜ mos ⌝ᶜ ⟨ x ⟩ ⌟           ≡˘⟨ ⌞⌟-cong (+-identityˡ _) ⟩
      ⌞ 𝟘 + ⌜ mos ⌝ᶜ ⟨ x ⟩ ⌟       ≡˘⟨ ⌞⌟-cong (+-congʳ (𝟘ᶜ-lookup x)) ⟩
      ⌞ 𝟘ᶜ ⟨ x ⟩ + ⌜ mos ⌝ᶜ ⟨ x ⟩ ⌟ ≡˘⟨ ⌞⌟-cong (lookup-distrib-+ᶜ 𝟘ᶜ ⌜ mos ⌝ᶜ x) ⟩
      ⌞ (𝟘ᶜ +ᶜ ⌜ mos ⌝ᶜ) ⟨ x ⟩ ⌟   ∎

opaque

  -- A variant of the above.

  ▶-⌞𝟘ᵐ·ᶜ⌟ :
    {Ψ : Substₘ m n} →
    (γ : Conₘ n) →
    Ψ ▶[ mos ] σ → Ψ ▶[ ⌞ ⌜ 𝟘ᵐ ⌝ ·ᶜ γ ⌟ᶜ ] σ
  ▶-⌞𝟘ᵐ·ᶜ⌟ γ ▶σ =
    ▶-cong _ (λ x → ⌜𝟘ᵐ⌝≡𝟘→ (⌞⌟-cong ∘→ lemma x)) (▶-⌞𝟘ᶜ⌟ ▶σ)
    where
    open Tools.Reasoning.PropositionalEquality
    lemma : ∀ x → ⌜ 𝟘ᵐ ⌝ ≡ 𝟘 → 𝟘ᶜ ⟨ x ⟩ ≡ (⌜ 𝟘ᵐ ⌝ ·ᶜ γ) ⟨ x ⟩
    lemma x ⌜𝟘ᵐ⌝≡𝟘 = begin
      𝟘ᶜ ⟨ x ⟩            ≡⟨ 𝟘ᶜ-lookup x ⟩
      𝟘                  ≡˘⟨ ·-zeroˡ _ ⟩
      𝟘 · γ ⟨ x ⟩         ≡˘⟨ ·-congʳ ⌜𝟘ᵐ⌝≡𝟘 ⟩
      ⌜ 𝟘ᵐ ⌝ · γ ⟨ x ⟩    ≡˘⟨ lookup-distrib-·ᶜ γ _ x ⟩
      (⌜ 𝟘ᵐ ⌝ ·ᶜ γ) ⟨ x ⟩ ∎

------------------------------------------------------------------------
-- Substitution lemma for modalities

private

  -- Some lemmas used in the proofs of the substitution lemmas below.

  +ᶜ⁴-<* :
    ∀ γ₁ →
    (γ₁ +ᶜ γ₂ +ᶜ γ₃ +ᶜ γ₄) <* Ψ ≈ᶜ
    γ₁ <* Ψ +ᶜ γ₂ <* Ψ +ᶜ γ₃ <* Ψ +ᶜ γ₄ <* Ψ
  +ᶜ⁴-<* {γ₂ = γ₂} {γ₃ = γ₃} γ₁ =
    ≈ᶜ-trans (<*-distrib-+ᶜ _ γ₁ _) $
    +ᶜ-congˡ $
    ≈ᶜ-trans (<*-distrib-+ᶜ _ γ₂ _) $
    +ᶜ-congˡ $
    <*-distrib-+ᶜ _ γ₃ _

  ·ᶜ+ᶜ²<* : ∀ γ₁ → (p ·ᶜ (γ₁ +ᶜ γ₂)) <* Ψ ≈ᶜ p ·ᶜ (γ₁ <* Ψ +ᶜ γ₂ <* Ψ)
  ·ᶜ+ᶜ²<* γ₁ =
    ≈ᶜ-trans (<*-distrib-·ᶜ _ _ (γ₁ +ᶜ _)) $
    ·ᶜ-congˡ $ <*-distrib-+ᶜ _ γ₁ _

  ·ᶜ+ᶜ⁴<* :
    ∀ γ₁ →
    (p ·ᶜ (γ₁ +ᶜ γ₂ +ᶜ γ₃ +ᶜ γ₄)) <* Ψ ≈ᶜ
    p ·ᶜ (γ₁ <* Ψ +ᶜ γ₂ <* Ψ +ᶜ γ₃ <* Ψ +ᶜ γ₄ <* Ψ)
  ·ᶜ+ᶜ⁴<* γ₁ =
    ≈ᶜ-trans (<*-distrib-·ᶜ _ _ (γ₁ +ᶜ _)) $
    ·ᶜ-congˡ $
    +ᶜ⁴-<* γ₁

  ·ᶜ+ᶜ⁵<* :
    ∀ γ₁ →
    (p ·ᶜ (γ₁ +ᶜ γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)) <* Ψ ≈ᶜ
    p ·ᶜ (γ₁ <* Ψ +ᶜ γ₂ <* Ψ +ᶜ γ₃ <* Ψ +ᶜ γ₄ <* Ψ +ᶜ γ₅ <* Ψ)
  ·ᶜ+ᶜ⁵<* {γ₂ = γ₂} γ₁ =
    ≈ᶜ-trans (<*-distrib-·ᶜ _ _ (γ₁ +ᶜ _)) $
    ·ᶜ-congˡ $
    ≈ᶜ-trans (<*-distrib-+ᶜ _ γ₁ _) $
    +ᶜ-congˡ $
    +ᶜ⁴-<* γ₂

  ·ᶜ⌜⌝·ᶜ<* : ∀ γ → (p ·ᶜ γ) <* Ψ ≈ᶜ p ·ᶜ (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ) <* Ψ
  ·ᶜ⌜⌝·ᶜ<* {p} {Ψ} γ = let open ≈ᶜ-reasoning in begin
    (p ·ᶜ γ) <* Ψ              ≈⟨ <*-distrib-·ᶜ Ψ _ γ ⟩
    p ·ᶜ γ <* Ψ                ≈˘⟨ ·ᶜ-congʳ ·⌜⌞⌟⌝ ⟩
    (p · ⌜ ⌞ p ⌟ ⌝) ·ᶜ γ <* Ψ  ≈⟨ ·ᶜ-assoc _ _ _ ⟩
    p ·ᶜ ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ <* Ψ   ≈˘⟨ ·ᶜ-congˡ (<*-distrib-·ᶜ Ψ _ γ) ⟩
    p ·ᶜ (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ) <* Ψ ∎

opaque mutual

  substₘ-lemma-ᵐ· :
    Ψ ▶[ ⌞ p ·ᶜ γ ⌟ᶜ ] σ →
    γ ▸[ mo ᵐ· p ] t →
    (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ) <* Ψ ▸[ mo ᵐ· p ] t [ σ ]
  substₘ-lemma-ᵐ· {γ} ▶σ ▸t =
    substₘ-lemma (▶-⌞·ᶜ⌟ γ ▶σ)
      (▸-cong lemma (▸-· ▸t))
    where
    open Tools.Reasoning.PropositionalEquality
    lemma : ⌞ p ⌟ ·ᵐ mo ᵐ· p ≡ mo ᵐ· p
    lemma {p} {mo} = begin
      ⌞ p ⌟ ·ᵐ mo ᵐ· p       ≡⟨⟩
      ⌞ p ⌟ ·ᵐ mo ·ᵐ ⌞ p ⌟   ≡⟨ ·ᵐ-comm _ _ ⟩
      (mo ·ᵐ ⌞ p ⌟) ·ᵐ ⌞ p ⌟ ≡⟨ ·ᵐ-assoc _ _ _ ⟩
      mo ·ᵐ ⌞ p ⌟ ·ᵐ ⌞ p ⌟   ≡⟨ ·ᵐ-congˡ (·ᵐ-idem _) ⟩
      mo ·ᵐ ⌞ p ⌟            ≡⟨⟩
      mo ᵐ· p                ∎

  -- A substitution lemma for the mode 𝟘ᵐ: if σ is well-formed and
  -- t is well-resourced with respect to any context γ and mode, then
  -- t [ σ ] is well-resourced with respect to the context
  -- ⌜ 𝟘ᵐ ⌝ ·ᶜ γ <* Ψ  and the mode 𝟘ᵐ.

  substₘ-lemma-𝟘ᵐ :
    {Ψ : Substₘ m n} →
    Ψ ▶[ mos ] σ → γ ▸[ mo ] t → ⌜ 𝟘ᵐ ⌝ ·ᶜ γ <* Ψ ▸[ 𝟘ᵐ ] t [ σ ]
  substₘ-lemma-𝟘ᵐ {γ} {Ψ} ▶σ ▸t =
    sub-≈ᶜ (substₘ-lemma (▶-⌞𝟘ᵐ·ᶜ⌟ γ ▶σ) (▸-𝟘 ▸t))
      (≈ᶜ-sym (<*-distrib-·ᶜ Ψ _ γ))

  private

    -- A variant of the above

    substₘ-lemma-𝟘ᵐ-⇑ :
      {Ψ : Substₘ m n} →
      Ψ ▶[ mos ] σ → γ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ mo ] t →
      ⌜ 𝟘ᵐ ⌝ ·ᶜ γ <* Ψ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] t [ σ ⇑ ]
    substₘ-lemma-𝟘ᵐ-⇑ {γ} {q} {Ψ} ▶σ ▸t =
      sub-≈ᶜ (substₘ-lemma-𝟘ᵐ (wf-liftSubstₘ {mo = 𝟘ᵐ} ▶σ) ▸t) $ begin
        ⌜ 𝟘ᵐ ⌝ ·ᶜ γ <* Ψ ∙ ⌜ 𝟘ᵐ ⌝ · q              ≈˘⟨ ≈ᶜ-refl ∙ ·-idem-⌜⌝′ ⟩
        ⌜ 𝟘ᵐ ⌝ ·ᶜ (γ <* Ψ ∙ ⌜ 𝟘ᵐ ⌝ · q)            ≈˘⟨ ·ᶜ-congˡ (liftSubstₘ-app Ψ γ _) ⟩
        ⌜ 𝟘ᵐ ⌝ ·ᶜ (γ ∙ ⌜ 𝟘ᵐ ⌝ · q) <* liftSubstₘ Ψ ∎
      where
      open ≈ᶜ-reasoning

    -- A variant of the above

    substₘ-lemma-𝟘ᵐ-⇑² :
      {Ψ : Substₘ m n} →
      Ψ ▶[ mos ] σ → γ ∙ ⌜ 𝟘ᵐ ⌝ · q ∙ ⌜ 𝟘ᵐ ⌝ · p ▸[ mo ] t →
      ⌜ 𝟘ᵐ ⌝ ·ᶜ γ <* Ψ ∙ ⌜ 𝟘ᵐ ⌝ · q ∙ ⌜ 𝟘ᵐ ⌝ · p ▸[ 𝟘ᵐ ] t [ σ ⇑[ 2 ] ]
    substₘ-lemma-𝟘ᵐ-⇑² {γ} {q} {p} {Ψ} ▶σ ▸t =
      sub-≈ᶜ (substₘ-lemma-𝟘ᵐ (wf-liftSubstₘ {mo = 𝟘ᵐ} (wf-liftSubstₘ {mo = 𝟘ᵐ} ▶σ)) ▸t) $ begin
        ⌜ 𝟘ᵐ ⌝ ·ᶜ γ <* Ψ ∙ ⌜ 𝟘ᵐ ⌝ · q ∙ ⌜ 𝟘ᵐ ⌝ · p                           ≈˘⟨ ≈ᶜ-refl ∙ ·-idem-⌜⌝′ ∙ ·-idem-⌜⌝′ ⟩
        ⌜ 𝟘ᵐ ⌝ ·ᶜ (γ <* Ψ ∙ ⌜ 𝟘ᵐ ⌝ · q ∙ ⌜ 𝟘ᵐ ⌝ · p)                         ≈˘⟨ ·ᶜ-congˡ (liftSubstₘ-app Ψ γ _ ∙ refl) ⟩
        ⌜ 𝟘ᵐ ⌝ ·ᶜ ((γ ∙ ⌜ 𝟘ᵐ ⌝ · q) <* liftSubstₘ Ψ ∙ ⌜ 𝟘ᵐ ⌝ · p)            ≈˘⟨ ·ᶜ-congˡ (liftSubstₘ-app (liftSubstₘ Ψ) (γ ∙ _) _) ⟩
        ⌜ 𝟘ᵐ ⌝ ·ᶜ (γ ∙ ⌜ 𝟘ᵐ ⌝ · q ∙ ⌜ 𝟘ᵐ ⌝ · p) <* liftSubstₘ (liftSubstₘ Ψ) ∎
      where
      open ≈ᶜ-reasoning

    -- A variant of the substitution lemma for lifted substitutions

    substₘ-lemma-⇑ :
      Ψ ▶[ ⌞ γ ⌟ᶜ ] σ →
      γ ∙ p ▸[ mo ] t →
      γ <* Ψ ∙ p ▸[ mo ] t [ σ ⇑ ]
    substₘ-lemma-⇑ {γ} {p} ▶σ ▸t =
      sub-≈ᶜ (substₘ-lemma (▶-cong _ lemma (wf-liftSubstₘ ▶σ)) ▸t)
        (≈ᶜ-sym (liftSubstₘ-app _ γ _))
      where
      lemma : ∀ x → consᵐ ⌞ p ⌟ ⌞ γ ⌟ᶜ x ≡ ⌞ γ ∙ p ⌟ᶜ x
      lemma x0 = refl
      lemma (_ +1) = refl

    -- A variant of the substitution lemma for twice lifted substitutions

    substₘ-lemma-⇑² :
      Ψ ▶[ ⌞ γ ⌟ᶜ ] σ →
      γ ∙ p ∙ q ▸[ mo ] t →
      γ <* Ψ ∙ p ∙ q ▸[ mo ] t [ σ ⇑[ 2 ] ]
    substₘ-lemma-⇑² {Ψ} {γ} {p} {q} ▶σ ▸t =
      sub-≈ᶜ (substₘ-lemma (▶-cong _ lemma (wf-liftSubstₘ (wf-liftSubstₘ ▶σ))) ▸t) $ begin
        γ <* Ψ ∙ p ∙ q                           ≈˘⟨ liftSubstₘ-app _ γ _ ∙ refl ⟩
        (γ ∙ p) <* liftSubstₘ Ψ ∙ q              ≈˘⟨ liftSubstₘ-app (liftSubstₘ Ψ) (γ ∙ p) _ ⟩
        (γ ∙ p ∙ q) <* liftSubstₘ (liftSubstₘ Ψ) ∎
      where
      open ≈ᶜ-reasoning
      lemma : ∀ x → consᵐ ⌞ q ⌟ (consᵐ ⌞ p ⌟ ⌞ γ ⌟ᶜ) x ≡ ⌞ γ ∙ p ∙ q ⌟ᶜ x
      lemma x0 = refl
      lemma (_+1 x0) = refl
      lemma (x +2) = refl

  -- The main substitution lemma.
  -- Proof by induction on t being well resourced.

  substₘ-lemma :
    {γ : Conₘ n} {Ψ : Substₘ m n} →
    Ψ ▶[ ⌞ γ ⌟ᶜ ] σ → γ ▸[ mo ] t → substₘ Ψ γ ▸[ mo ] t [ σ ]
  substₘ-lemma {Ψ} ▶σ (sub ▸t γ≤) =
    sub (substₘ-lemma (▶-≤ Ψ γ≤ ▶σ) ▸t)
      (<*-monotone _ γ≤)
  substₘ-lemma {mo} {Ψ} ▶σ (var {x}) =  sub
    (▸-cong (let open Tools.Reasoning.PropositionalEquality in
             ⌞ (𝟘ᶜ , x ≔ ⌜ mo ⌝) ⟨ x ⟩ ⌟  ≡⟨ cong ⌞_⌟ (update-lookup 𝟘ᶜ x) ⟩
             ⌞ ⌜ mo ⌝ ⌟                   ≡⟨ ⌞⌜⌝⌟ _ ⟩
             mo                           ∎)
       (▶σ x))
   (let open ≤ᶜ-reasoning in begin
      (𝟘ᶜ , x ≔ ⌜ mo ⌝) <* Ψ                           ≈˘⟨ <*-cong Ψ (update-congʳ {γ = 𝟘ᶜ} {x = x} (cong ⌜_⌝ (⌞⌜⌝⌟ mo))) ⟩
      (𝟘ᶜ , x ≔ ⌜ ⌞ ⌜ mo ⌝ ⌟ ⌝) <* Ψ                   ≡˘⟨ cong (λ p → (𝟘ᶜ , x ≔ ⌜ ⌞ p ⌟ ⌝) <* Ψ) (update-lookup 𝟘ᶜ x) ⟩
      (𝟘ᶜ , x ≔ ⌜ ⌞ (𝟘ᶜ , x ≔ ⌜ mo ⌝) ⟨ x ⟩ ⌟ ⌝) <* Ψ  ∎)
  substₘ-lemma {Ψ} ▶σ defn =
    sub-≈ᶜ defn (<*-zeroˡ Ψ)
  substₘ-lemma {Ψ} ▶σ (Uₘ ▸t) =
    sub-≈ᶜ (Uₘ (substₘ-lemma-𝟘ᵐ ▶σ ▸t)) (<*-zeroˡ Ψ)
  substₘ-lemma {Ψ} ▶σ Levelₘ =
    sub-≈ᶜ Levelₘ (<*-zeroˡ Ψ)
  substₘ-lemma {Ψ} ▶σ zeroᵘₘ =
    sub-≈ᶜ zeroᵘₘ (<*-zeroˡ Ψ)
  substₘ-lemma ▶σ (sucᵘₘ ▸t) =
    sucᵘₘ (substₘ-lemma ▶σ ▸t)
  substₘ-lemma {Ψ} ▶σ (supᵘₘ {γ} ▸t ▸u) =
    sub-≈ᶜ
      (supᵘₘ (substₘ-lemma (▶-⌞+ᶜ⌟ˡ γ ▶σ) ▸t)
        (substₘ-lemma (▶-⌞+ᶜ⌟ʳ γ ▶σ) ▸u))
      (<*-distrib-+ᶜ Ψ γ _)
  substₘ-lemma ▶σ (Liftₘ ▸t ▸A) =
    Liftₘ (substₘ-lemma-𝟘ᵐ ▶σ ▸t)
      (substₘ-lemma ▶σ ▸A)
  substₘ-lemma ▶σ (liftₘ ▸t) =
    liftₘ (substₘ-lemma ▶σ ▸t)
  substₘ-lemma ▶σ (lowerₘ ▸t) =
    lowerₘ (substₘ-lemma ▶σ ▸t)
  substₘ-lemma {Ψ} ▶σ Emptyₘ =
    sub-≈ᶜ Emptyₘ (<*-zeroˡ Ψ)
  substₘ-lemma ▶σ (emptyrecₘ {γ} {p} ▸t ▸A ok) =
    sub-≈ᶜ
      (emptyrecₘ (substₘ-lemma-ᵐ· ▶σ ▸t)
        (substₘ-lemma-𝟘ᵐ ▶σ ▸A) ok)
      (·ᶜ⌜⌝·ᶜ<* γ)
  substₘ-lemma {Ψ} ▶σ Unitₘ =
    sub-≈ᶜ Unitₘ (<*-zeroˡ Ψ)
  substₘ-lemma {Ψ} ▶σ (starˢₘ {γ} ok) =
    sub-≈ᶜ
      (starˢₘ λ ¬sink → begin
        𝟘ᶜ      ≈˘⟨ <*-zeroˡ Ψ ⟩
        𝟘ᶜ <* Ψ ≈⟨ <*-cong Ψ (ok ¬sink) ⟩
        γ <* Ψ  ∎)
      (<*-distrib-·ᶜ Ψ _ γ)
    where
    open ≈ᶜ-reasoning
  substₘ-lemma {Ψ} ▶σ starʷₘ =
    sub-≈ᶜ starʷₘ (<*-zeroˡ Ψ)
  substₘ-lemma {Ψ} ▶σ (unitrecₘ {γ} {p} {δ} ▸t ▸u ▸A ok) =
    sub-≈ᶜ (unitrecₘ (substₘ-lemma-ᵐ· (▶-⌞+ᶜ⌟ˡ (p ·ᶜ γ) ▶σ) ▸t)
             (substₘ-lemma (▶-⌞+ᶜ⌟ʳ (p ·ᶜ γ) ▶σ) ▸u)
             (substₘ-lemma-𝟘ᵐ-⇑ ▶σ ▸A) ok) $ begin
          (p ·ᶜ γ +ᶜ δ) <* Ψ                   ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) δ ⟩
          (p ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ              ≈⟨ +ᶜ-congʳ (·ᶜ⌜⌝·ᶜ<* γ) ⟩
          p ·ᶜ (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ ∎
    where
    open ≈ᶜ-reasoning
  substₘ-lemma {Ψ} ▶σ (ΠΣₘ {γ} {p} {δ} ▸A ▸B) =
    sub-≈ᶜ
      (ΠΣₘ (substₘ-lemma-ᵐ· (▶-⌞+ᶜ⌟ˡ (p ·ᶜ γ) ▶σ) ▸A)
        (substₘ-lemma-⇑ (▶-⌞+ᶜ⌟ʳ (p ·ᶜ γ) ▶σ) ▸B)) $ begin
        (p ·ᶜ γ +ᶜ δ) <* Ψ                   ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) δ ⟩
        (p ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ              ≈⟨ +ᶜ-congʳ (·ᶜ⌜⌝·ᶜ<* γ) ⟩
        p ·ᶜ (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ ∎
    where
    open ≈ᶜ-reasoning
  substₘ-lemma ▶σ (lamₘ {p} ▸t) =
    lamₘ (substₘ-lemma-⇑ ▶σ ▸t)
  substₘ-lemma {Ψ} ▶σ (_∘ₘ_ {γ} {δ} {p} {u} ▸t ▸u) =
    sub-≈ᶜ (substₘ-lemma (▶-⌞+ᶜ⌟ˡ γ ▶σ) ▸t ∘ₘ substₘ-lemma-ᵐ· (▶-⌞+ᶜ⌟ʳ γ ▶σ) ▸u) $ begin
      (γ +ᶜ p ·ᶜ δ) <* Ψ                   ≈⟨ <*-distrib-+ᶜ Ψ γ (p ·ᶜ δ) ⟩
      γ <* Ψ +ᶜ (p ·ᶜ δ) <* Ψ              ≈⟨ +ᶜ-congˡ (·ᶜ⌜⌝·ᶜ<* δ) ⟩
      γ <* Ψ +ᶜ p ·ᶜ (⌜ ⌞ p ⌟ ⌝ ·ᶜ δ) <* Ψ ∎
    where
    open ≈ᶜ-reasoning
  substₘ-lemma {Ψ} ▶σ (prodˢₘ {γ} {p} {δ} ▸t ▸u) =
    sub (prodˢₘ (substₘ-lemma-ᵐ· (▶-⌞∧ᶜ⌟ˡ (p ·ᶜ γ) ▶σ) ▸t)
          (substₘ-lemma (▶-⌞∧ᶜ⌟ʳ (p ·ᶜ γ) ▶σ) ▸u)) $ begin
      (p ·ᶜ γ ∧ᶜ δ) <* Ψ                   ≤⟨ <*-sub-distrib-∧ᶜ Ψ (p ·ᶜ γ) δ ⟩
      (p ·ᶜ γ) <* Ψ ∧ᶜ δ <* Ψ              ≈⟨ ∧ᶜ-congʳ (·ᶜ⌜⌝·ᶜ<* γ) ⟩
      p ·ᶜ (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ) <* Ψ ∧ᶜ δ <* Ψ ∎
    where
    open ≤ᶜ-reasoning
  substₘ-lemma ▶σ (fstₘ ▸t mp-cond) =
    fstₘ (substₘ-lemma ▶σ ▸t) mp-cond
  substₘ-lemma ▶σ (sndₘ ▸t) =
    sndₘ (substₘ-lemma ▶σ ▸t)
  substₘ-lemma {Ψ} ▶σ (prodʷₘ {γ} {p} {t} {δ} ▸t ▸u) =
    sub-≈ᶜ (prodʷₘ (substₘ-lemma-ᵐ· (▶-⌞+ᶜ⌟ˡ (p ·ᶜ γ) ▶σ) ▸t)
             (substₘ-lemma (▶-⌞+ᶜ⌟ʳ (p ·ᶜ γ) ▶σ) ▸u)) $ begin
      (p ·ᶜ γ +ᶜ δ) <* Ψ                    ≈⟨ <*-distrib-+ᶜ Ψ (p ·ᶜ γ) δ ⟩
      (p ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ               ≈⟨ +ᶜ-congʳ (·ᶜ⌜⌝·ᶜ<* γ) ⟩
      p ·ᶜ (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ  ∎
    where
    open ≈ᶜ-reasoning
  substₘ-lemma {Ψ} ▶σ (prodrecₘ {γ} {r} {δ} ▸t ▸u ▸A ok) =
    sub-≈ᶜ (prodrecₘ (substₘ-lemma-ᵐ· (▶-⌞+ᶜ⌟ˡ (r ·ᶜ γ) ▶σ) ▸t)
             (substₘ-lemma-⇑² (▶-⌞+ᶜ⌟ʳ (r ·ᶜ γ) ▶σ) ▸u)
             (substₘ-lemma-𝟘ᵐ-⇑ ▶σ ▸A) ok) $ begin
      (r ·ᶜ γ +ᶜ δ) <* Ψ                   ≈⟨ <*-distrib-+ᶜ Ψ (r ·ᶜ γ) δ ⟩
      (r ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ              ≈⟨ +ᶜ-congʳ (·ᶜ⌜⌝·ᶜ<* γ) ⟩
      r ·ᶜ (⌜ ⌞ r ⌟ ⌝ ·ᶜ γ) <* Ψ +ᶜ δ <* Ψ ∎
      where
      open ≈ᶜ-reasoning
  substₘ-lemma {Ψ} ▶σ ℕₘ =
    sub-≈ᶜ ℕₘ (<*-zeroˡ Ψ)
  substₘ-lemma {Ψ} ▶σ zeroₘ =
    sub-≈ᶜ zeroₘ (<*-zeroˡ Ψ)
  substₘ-lemma ▶σ (sucₘ ▸t) =
    sucₘ (substₘ-lemma ▶σ ▸t)
  substₘ-lemma {Ψ} ▶σ (natrecₘ {γ} ▸z ▸s ▸n ▸A) =
    sub
      (natrecₘ (substₘ-lemma (▶-⌞nrᶜ⌟₁ Ψ γ ▶σ) ▸z)
        (substₘ-lemma-⇑² (▶-⌞nrᶜ⌟₂ Ψ γ ▶σ) ▸s)
        (substₘ-lemma (▶-⌞nrᶜ⌟₃ Ψ γ ▶σ) ▸n)
        (substₘ-lemma-𝟘ᵐ-⇑ ▶σ ▸A))
      (<*-sub-distrib-nrᶜ Ψ γ)
    where
    open Graded.Usage.Restrictions.Instance R
  substₘ-lemma {σ} {γ = γ₀} {Ψ} ▶σ (natrec-no-nrₘ {γ} {δ} {p} {r} {η} ▸z ▸s ▸n ▸A le₁ le₂ le₃ le₄) =
    natrec-no-nrₘ (substₘ-lemma (▶-≤ Ψ le₁ ▶σ) ▸z)
      (substₘ-lemma-⇑² (▶-⌞+ᶜ⌟ˡ δ (▶-≤ Ψ le₄ ▶σ)) ▸s)
      (substₘ-lemma ▶σ′ ▸n)
      (substₘ-lemma-𝟘ᵐ-⇑ ▶σ ▸A)
      (<*-monotone Ψ le₁)
      (<*-monotone Ψ ∘→ le₂)
      (<*-monotone Ψ ∘→ le₃) $ begin
        γ₀ <* Ψ                                   ≤⟨ <*-monotone Ψ le₄ ⟩
        (δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ γ₀) <* Ψ             ≈⟨ <*-distrib-+ᶜ Ψ δ (p ·ᶜ η +ᶜ r ·ᶜ γ₀) ⟩
        δ <* Ψ +ᶜ (p ·ᶜ η +ᶜ r ·ᶜ γ₀) <* Ψ        ≈⟨ +ᶜ-congˡ (<*-distrib-+ᶜ Ψ (p ·ᶜ η) (r ·ᶜ γ₀)) ⟩
        δ <* Ψ +ᶜ (p ·ᶜ η) <* Ψ +ᶜ (r ·ᶜ γ₀) <* Ψ ≈⟨ +ᶜ-congˡ (+ᶜ-cong (<*-distrib-·ᶜ Ψ _ η) (<*-distrib-·ᶜ Ψ _ γ₀)) ⟩
        δ <* Ψ +ᶜ p ·ᶜ η <* Ψ +ᶜ r ·ᶜ γ₀ <* Ψ     ∎
    where
    open ≤ᶜ-reasoning
    ▶σ′ : Ψ ▶[ ⌞ η ⌟ᶜ ] σ
    ▶σ′ = case trivialᵐ? of λ where
      (yes 𝟙ᵐ≡𝟘ᵐ) → ▶-Trivialᵐ 𝟙ᵐ≡𝟘ᵐ ▶σ
      (no 𝟙ᵐ≢𝟘ᵐ) → ▶-≤ Ψ (le₃ (⊥-elim ∘→ (𝟙ᵐ≢𝟘ᵐ $_))) ▶σ
  substₘ-lemma {Ψ} ▶σ (natrec-no-nr-glbₘ {γ} {δ} {r} {η} {χ} {x} ▸z ▸s ▸n ▸A x-GLB χ-GLB) =
    let open ≤ᶜ-reasoning
        χ′ , χ′-GLB , ≤χ′ = nrᵢᶜ-<*-GLBᶜ′ Ψ χ-GLB
        ▶σ₁ = ▶-≤ Ψ (begin
                       χ            ≤⟨ χ-GLB .proj₁ 0 ⟩
                       nrᵢᶜ r γ δ 0 ≈⟨ nrᵢᶜ-zero ⟩
                       γ            ∎)
                    (▶-⌞+ᶜ⌟ʳ (x ·ᶜ η) ▶σ)
        ▶σ₂ = ▶-⌞+ᶜ⌟ˡ δ (▶-≤ Ψ (begin
                         χ                      ≤⟨ χ-GLB .proj₁ 1 ⟩
                         nrᵢᶜ r γ δ 1           ≈⟨ nrᵢᶜ-suc ⟩
                         δ +ᶜ r ·ᶜ nrᵢᶜ r γ δ 0 ∎)
               (▶-⌞+ᶜ⌟ʳ (x ·ᶜ η) ▶σ))
        ▶σ₃ = ▶-≤ Ψ (begin
                      x ·ᶜ η ≤⟨ ·ᶜ-monotoneˡ (x-GLB .proj₁ 0) ⟩
                      𝟙 ·ᶜ η ≈⟨ ·ᶜ-identityˡ _ ⟩
                      η      ∎)
                (▶-⌞+ᶜ⌟ˡ (x ·ᶜ η) ▶σ)
    in  sub
      (natrec-no-nr-glbₘ
        (substₘ-lemma ▶σ₁ ▸z)
        (substₘ-lemma-⇑² ▶σ₂ ▸s)
        (substₘ-lemma ▶σ₃ ▸n)
        (substₘ-lemma-𝟘ᵐ-⇑ ▶σ ▸A)
        x-GLB χ′-GLB) $ begin
      (x ·ᶜ η +ᶜ χ) <* Ψ      ≈⟨ <*-distrib-+ᶜ Ψ (x ·ᶜ η) χ ⟩
      (x ·ᶜ η) <* Ψ +ᶜ χ <* Ψ ≈⟨ +ᶜ-congʳ (<*-distrib-·ᶜ Ψ _ η) ⟩
      x ·ᶜ η <* Ψ +ᶜ χ <* Ψ   ≤⟨ +ᶜ-monotoneʳ ≤χ′ ⟩
      x ·ᶜ η <* Ψ +ᶜ χ′       ∎
  substₘ-lemma {Ψ} ▶σ (Idₘ {γ} {δ} {η} ok ▸A ▸t ▸u) =
    sub-≈ᶜ (Idₘ ok (substₘ-lemma (▶-⌞+ᶜ⌟ˡ γ ▶σ) ▸A)
              (substₘ-lemma (▶-⌞+ᶜ⌟ˡ δ (▶-⌞+ᶜ⌟ʳ γ ▶σ)) ▸t)
              (substₘ-lemma (▶-⌞+ᶜ⌟ʳ δ (▶-⌞+ᶜ⌟ʳ γ ▶σ)) ▸u)) $ begin
      (γ +ᶜ δ +ᶜ η) <* Ψ         ≈⟨ <*-distrib-+ᶜ Ψ γ _ ⟩
      γ <* Ψ +ᶜ (δ +ᶜ η) <* Ψ    ≈⟨ +ᶜ-congˡ (<*-distrib-+ᶜ Ψ δ η) ⟩
      γ <* Ψ +ᶜ δ <* Ψ +ᶜ η <* Ψ ∎
    where
    open ≈ᶜ-reasoning
  substₘ-lemma {Ψ} ▶σ (Id₀ₘ ok ▸A ▸t ▸u) =
    sub-≈ᶜ (Id₀ₘ ok (substₘ-lemma-𝟘ᵐ ▶σ ▸A)
             (substₘ-lemma-𝟘ᵐ ▶σ ▸t) (substₘ-lemma-𝟘ᵐ ▶σ ▸u))
      (<*-zeroˡ Ψ)
  substₘ-lemma {Ψ} ▶σ rflₘ =
    sub-≈ᶜ rflₘ (<*-zeroˡ Ψ)
  substₘ-lemma {Ψ} ▶σ (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v ▸w) =
    let open ≤ᶜ-reasoning
        ▶σ′ = ▶-≤ Ψ (ω·ᶜ-decreasing {γ = γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆}) ▶σ
        ▶σ₂ = ▶-⌞+ᶜ⌟ˡ γ₂ ▶σ′
        ▶σ₃ = ▶-⌞+ᶜ⌟ˡ γ₃ (▶-⌞+ᶜ⌟ʳ γ₂ ▶σ′)
        ▶σ₄ = ▶-⌞+ᶜ⌟ˡ γ₄ (▶-⌞+ᶜ⌟ʳ γ₃ (▶-⌞+ᶜ⌟ʳ γ₂ ▶σ′))
        ▶σ₅ = ▶-⌞+ᶜ⌟ˡ γ₅ (▶-⌞+ᶜ⌟ʳ γ₄ (▶-⌞+ᶜ⌟ʳ γ₃ (▶-⌞+ᶜ⌟ʳ γ₂ ▶σ′)))
        ▶σ₆ = ▶-⌞+ᶜ⌟ʳ γ₅ (▶-⌞+ᶜ⌟ʳ γ₄ (▶-⌞+ᶜ⌟ʳ γ₃ (▶-⌞+ᶜ⌟ʳ γ₂ ▶σ′)))
    in  sub-≈ᶜ
          (Jₘ ok₁ ok₂
            (substₘ-lemma-𝟘ᵐ ▶σ ▸A)
            (substₘ-lemma ▶σ₂ ▸t)
            (substₘ-lemma-⇑² ▶σ₃ ▸B)
            (substₘ-lemma ▶σ₄ ▸u)
            (substₘ-lemma ▶σ₅ ▸v)
            (substₘ-lemma ▶σ₆ ▸w))
          (·ᶜ+ᶜ⁵<* γ₂)
  substₘ-lemma {Ψ} ▶σ (J₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸v ▸w) =
    let ▶σ′ = ▶-≤ Ψ (ω·ᶜ-decreasing {γ = γ₃ +ᶜ γ₄}) ▶σ
        ▶σ₃ = ▶-⌞+ᶜ⌟ˡ γ₃ ▶σ′
        ▶σ₄ = ▶-⌞+ᶜ⌟ʳ γ₃ ▶σ′
    in  sub-≈ᶜ
          (J₀ₘ₁ ok p≡𝟘 q≡𝟘
            (substₘ-lemma-𝟘ᵐ ▶σ ▸A)
            (substₘ-lemma-𝟘ᵐ ▶σ ▸t)
            (substₘ-lemma-⇑² ▶σ₃ ▸B)
            (substₘ-lemma ▶σ₄ ▸u)
            (substₘ-lemma-𝟘ᵐ ▶σ ▸v)
            (substₘ-lemma-𝟘ᵐ ▶σ ▸w))
          (·ᶜ+ᶜ²<* γ₃)
  substₘ-lemma ▶σ (J₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v ▸w) =
    J₀ₘ₂ ok
      (substₘ-lemma-𝟘ᵐ ▶σ ▸A)
      (substₘ-lemma-𝟘ᵐ ▶σ ▸t)
      (substₘ-lemma-𝟘ᵐ-⇑² ▶σ ▸B)
      (substₘ-lemma ▶σ ▸u)
      (substₘ-lemma-𝟘ᵐ ▶σ ▸v)
      (substₘ-lemma-𝟘ᵐ ▶σ ▸w)
  substₘ-lemma {Ψ} ▶σ (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v) =
    let ▶σ′ = ▶-≤ Ψ (ω·ᶜ-decreasing {γ = γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅}) ▶σ
        ▶σ₂ = ▶-⌞+ᶜ⌟ˡ γ₂ ▶σ′
        ▶σ₃ = ▶-⌞+ᶜ⌟ˡ γ₃ (▶-⌞+ᶜ⌟ʳ γ₂ ▶σ′)
        ▶σ₄ = ▶-⌞+ᶜ⌟ˡ γ₄ (▶-⌞+ᶜ⌟ʳ γ₃ (▶-⌞+ᶜ⌟ʳ γ₂ ▶σ′))
        ▶σ₅ = ▶-⌞+ᶜ⌟ʳ γ₄ (▶-⌞+ᶜ⌟ʳ γ₃ (▶-⌞+ᶜ⌟ʳ γ₂ ▶σ′))
    in  sub-≈ᶜ
          (Kₘ ok₁ ok₂ (substₘ-lemma-𝟘ᵐ ▶σ ▸A)
            (substₘ-lemma ▶σ₂ ▸t)
            (substₘ-lemma-⇑ ▶σ₃ ▸B)
            (substₘ-lemma ▶σ₄ ▸u)
            (substₘ-lemma ▶σ₅ ▸v))
          (·ᶜ+ᶜ⁴<* γ₂)
  substₘ-lemma {Ψ} ▶σ (K₀ₘ₁ {γ₃} {γ₄} ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v) =
    let ▶σ′ = ▶-≤ Ψ (ω·ᶜ-decreasing {γ = γ₃ +ᶜ γ₄}) ▶σ
        ▶σ₃ = ▶-⌞+ᶜ⌟ˡ γ₃ ▶σ′
        ▶σ₄ = ▶-⌞+ᶜ⌟ʳ γ₃ ▶σ′
    in  sub-≈ᶜ
          (K₀ₘ₁ ok p≡𝟘 (substₘ-lemma-𝟘ᵐ ▶σ ▸A)
            (substₘ-lemma-𝟘ᵐ ▶σ ▸t)
            (substₘ-lemma-⇑ ▶σ₃ ▸B)
            (substₘ-lemma ▶σ₄ ▸u)
            (substₘ-lemma-𝟘ᵐ ▶σ ▸v))
          (·ᶜ+ᶜ²<* γ₃)
  substₘ-lemma ▶σ (K₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v) =
    K₀ₘ₂ ok (substₘ-lemma-𝟘ᵐ ▶σ ▸A)
      (substₘ-lemma-𝟘ᵐ ▶σ ▸t)
      (substₘ-lemma-𝟘ᵐ-⇑ ▶σ ▸B)
      (substₘ-lemma ▶σ ▸u)
      (substₘ-lemma-𝟘ᵐ ▶σ ▸v)
  substₘ-lemma {Ψ} ▶σ ([]-congₘ ▸l ▸A ▸t ▸u ▸v ok) =
    sub-≈ᶜ ([]-congₘ (substₘ-lemma-𝟘ᵐ ▶σ ▸l) (substₘ-lemma-𝟘ᵐ ▶σ ▸A)
             (substₘ-lemma-𝟘ᵐ ▶σ ▸t) (substₘ-lemma-𝟘ᵐ ▶σ ▸u)
             (substₘ-lemma-𝟘ᵐ ▶σ ▸v) ok)
      (<*-zeroˡ Ψ)

opaque

  -- A substitution lemma for the mode 𝟘ᵐ and non-trivial mode structures:
  -- if σ is well-formed and t is well-resourced with respect to any context
  -- and mode, then t [ σ ] is well-resourced with respect to the zero usage
  -- context and the mode 𝟘ᵐ.

  substₘ-lemma₀ :
    {Ψ : Substₘ m n} →
    ¬ Trivialᵐ →
    Ψ ▶[ mos ] σ → γ ▸[ mo ] t → 𝟘ᶜ ▸[ 𝟘ᵐ ] t [ σ ]
  substₘ-lemma₀ {γ} {Ψ} not-trivial Ψ▶σ ▸t =
    sub-≈ᶜ (substₘ-lemma-𝟘ᵐ Ψ▶σ ▸t) $ begin
      𝟘ᶜ               ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
      𝟘 ·ᶜ γ <* Ψ      ≈˘⟨ ·ᶜ-congʳ (⌜𝟘ᵐ⌝ not-trivial) ⟩
      ⌜ 𝟘ᵐ ⌝ ·ᶜ γ <* Ψ ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- A substitution lemma for the case where the mode structure is trivial.

  substₘ-lemma₁ :
    {Ψ : Substₘ m n} →
    Trivialᵐ →
    Ψ ▶[ mos ] σ → γ ▸[ mo ] t → substₘ Ψ γ ▸[ 𝟙ᵐ ] t [ σ ]
  substₘ-lemma₁ trivial ▶σ ▸t =
    ▸-trivialᵐ trivial (substₘ-lemma (▶-Trivialᵐ trivial ▶σ) ▸t)

opaque

  -- A variant of substₘ-lemma for closing substitutions.

  substₘ-lemma-closed :
    ((x : Fin n) → ε ▸[ 𝟘ᵐ ] σ x) →
    𝟘ᶜ ▸[ mo ] t →
    ε ▸[ mo ] t [ σ ]
  substₘ-lemma-closed {n} ▸σ ▸t =
    subst (_▸[ _ ] _) (≈ᶜ→≡ $ <*-zeroʳ (𝟘ᶜ {n = n})) $
    substₘ-lemma
      (λ x →
         subst₃ _▸[_]_
           (sym $ ≈ᶜ→≡ $ <*-zeroʳ ((𝟘ᶜ , x ≔ ⌜ ⌞ 𝟘ᶜ ⟨ x ⟩ ⌟ ⌝)))
           (𝟘ᵐ           ≡˘⟨ ⌞𝟘⌟ ⟩
            ⌞ 𝟘 ⌟        ≡˘⟨ cong ⌞_⌟ $ 𝟘ᶜ-lookup x ⟩
            ⌞ 𝟘ᶜ ⟨ x ⟩ ⌟  ∎)
           refl
           (▸σ x))
      ▸t
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A substitution lemma for single substitutions.

  sgSubstₘ-lemma₁ :
    γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ᵐ· p ] u →
    γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ ▸[ mo ] t [ u ]₀
  sgSubstₘ-lemma₁ {γ = γ} {mo = mo} {p = p} {δ = δ} γ▸t δ▸u = sub
    (substₘ-lemma
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
    open ≤ᶜ-reasoning

opaque

  -- A variant of sgSubstₘ-lemma₁.

  sgSubstₘ-lemma₂ :
    γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ᵐ· p ] u →
    γ +ᶜ p ·ᶜ δ ▸[ mo ] t [ u ]₀
  sgSubstₘ-lemma₂ {γ} {mo} {p} {δ} ▸t ▸u =
    sub (sgSubstₘ-lemma₁ ▸t ▸u) $ begin
      γ +ᶜ p ·ᶜ δ             ≤⟨ +ᶜ-monotoneʳ (▸ᵐ-ᵐ· ▸u) ⟩
      γ +ᶜ ⌜ mo ⌝ ·ᶜ p ·ᶜ δ   ≈˘⟨ +ᶜ-congˡ (·ᶜ-assoc _ _ _) ⟩
      γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ  ∎
    where
    open ≤ᶜ-reasoning

opaque

  -- Another variant of sgSubstₘ-lemma₁.

  sgSubstₘ-lemma₃ :
    γ ∙ ⌜ mo ⌝ · p ▸[ mo ] t → δ ▸[ mo ] u →
    γ +ᶜ p ·ᶜ δ ▸[ mo ] t [ u ]₀
  sgSubstₘ-lemma₃ ▸t ▸u =
    case ▸→▸[ᵐ·] ▸u of λ where
      (_ , ▸u , eq) → sub-≈ᶜ
        (sgSubstₘ-lemma₂ ▸t ▸u)
        (+ᶜ-congˡ eq)

opaque

  -- A substitution lemma for double substitutions.

  doubleSubstₘ-lemma₁ :
    γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
    δ ▸[ mo ᵐ· p ] u → η ▸[ mo ᵐ· q ] u′ →
    γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η ▸[ mo ] t [ u′ , u ]₁₀
  doubleSubstₘ-lemma₁
    {γ = γ} {mo = mo} {q = q} {p = p} {δ = δ} {η = η} γ▸t δ▸u η▸u′ = sub
    (substₘ-lemma
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
    open ≤ᶜ-reasoning

opaque

  -- A variant of doubleSubstₘ-lemma₁.

  doubleSubstₘ-lemma₂ :
    γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
    δ ▸[ mo ᵐ· p ] u → η ▸[ mo ᵐ· q ] u′ →
    γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η ▸[ mo ] t [ u′ , u ]₁₀
  doubleSubstₘ-lemma₂ {γ} {mo} {q} {p} {δ} {η} ▸t ▸u ▸u′ =
    sub (doubleSubstₘ-lemma₁ ▸t ▸u ▸u′) $ begin
      γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η                       ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotone (▸ᵐ-ᵐ· ▸u) (▸ᵐ-ᵐ· ▸u′)) ⟩
      γ +ᶜ ⌜ mo ⌝ ·ᶜ p ·ᶜ δ +ᶜ ⌜ mo ⌝ ·ᶜ q ·ᶜ η   ≈˘⟨ +ᶜ-congˡ (+ᶜ-cong (·ᶜ-assoc _ _ _) (·ᶜ-assoc _ _ _)) ⟩
      γ +ᶜ (⌜ mo ⌝ · p) ·ᶜ δ +ᶜ (⌜ mo ⌝ · q) ·ᶜ η ∎
    where
    open ≤ᶜ-reasoning

opaque

  -- Another variant of doubleSubstₘ-lemma₁.

  doubleSubstₘ-lemma₃ :
    γ ∙ ⌜ mo ⌝ · q ∙ ⌜ mo ⌝ · p ▸[ mo ] t →
    δ ▸[ mo ] u → η ▸[ mo ] u′ →
    γ +ᶜ p ·ᶜ δ +ᶜ q ·ᶜ η ▸[ mo ] t [ u′ , u ]₁₀
  doubleSubstₘ-lemma₃ ▸t ▸u ▸u′ =
    case ▸→▸[ᵐ·] ▸u of λ where
      (_ , ▸u , eq) → case ▸→▸[ᵐ·] ▸u′ of λ where
        (_ , ▸u′ , eq′) → sub
          (doubleSubstₘ-lemma₂ ▸t ▸u ▸u′)
          (≤ᶜ-reflexive (+ᶜ-congˡ (+ᶜ-cong eq eq′)))

opaque

  -- A substitution lemma for _[_][_]↑.

  ▸[][]↑ :
    γ ∙ p ▸[ mo ] t →
    ⌜ ⌞ p ⌟ ⌝ ·ᶜ δ ▸[ ⌞ p ⌟ ] u →
    wkConₘ (stepn id k) γ +ᶜ p ·ᶜ δ ▸[ mo ] t [ k ][ u ]↑
  ▸[][]↑ {γ} {p} {k} {δ} ▸t ▸u = sub
    (substₘ-lemma
       (▶-cong _
          (λ where
             x0     → PE.refl
             (_ +1) → PE.refl) $
        wf-consSubstₘ (wf-wkSubstₘ′ wf-idSubstₘ) ▸u)
       ▸t)
    (begin
       wkConₘ (stepn id k) γ +ᶜ p ·ᶜ δ                ≈⟨ +ᶜ-comm _ _ ⟩
       p ·ᶜ δ +ᶜ wkConₘ (stepn id k) γ                ≈˘⟨ +ᶜ-congˡ (wk-≈ᶜ (stepn _ k) (<*-identityˡ _)) ⟩
       p ·ᶜ δ +ᶜ wkConₘ (stepn id k) (γ <* idSubstₘ)  ≈˘⟨ +ᶜ-congˡ (<*-wkSubstₘ′ γ) ⟩
       p ·ᶜ δ +ᶜ γ <* wkSubstₘ′ k idSubstₘ            ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- Substitution matrix inference

opaque

  -- The inference functions ∥_∥ and ⌈_⌉ are related to each other: the
  -- x-th row of ∥ σ ∥ mos is equivalent to ⌈ σ x ⌉ (mos x).

  substₘ-calc-row :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    (σ : Subst m n) (x : Fin n) →
    (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos ≈ᶜ ⌈ σ x ⌉ (mos x)
  substₘ-calc-row {mos = mos} σ x0 = begin
    (𝟘ᶜ , x0 ≔ 𝟙) <* ∥ σ ∥ mos                                 ≡⟨⟩
    (𝟘ᶜ ∙ 𝟙) <* ∥ σ ∥ mos                                      ≡⟨⟩
    𝟙 ·ᶜ ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ <* ∥ tail σ ∥ (tailᵐ mos)  ≈⟨ +ᶜ-cong (·ᶜ-identityˡ _) (<*-zeroˡ (∥ tail σ ∥ _)) ⟩
    ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ                                 ≈⟨ +ᶜ-identityʳ _ ⟩
    ⌈ σ x0 ⌉ (headᵐ mos)                                       ∎
    where
    open ≈ᶜ-reasoning
  substₘ-calc-row {mos = mos} σ (x +1) = begin
    (𝟘ᶜ , x +1 ≔ 𝟙) <* ∥ σ ∥ mos                                         ≡⟨⟩
    ((𝟘ᶜ , x ≔ 𝟙) ∙ 𝟘) <* ∥ σ ∥ mos                                      ≡⟨⟩
    𝟘 ·ᶜ ⌈ σ x0 ⌉ (headᵐ mos) +ᶜ (𝟘ᶜ , x ≔ 𝟙) <* ∥ tail σ ∥ (tailᵐ mos)  ≈⟨ +ᶜ-cong (·ᶜ-zeroˡ _) (substₘ-calc-row (tail σ) x) ⟩
    𝟘ᶜ +ᶜ ⌈ tail σ x ⌉ (tailᵐ mos x)                                     ≈⟨ +ᶜ-identityˡ _ ⟩
    ⌈ σ (x +1) ⌉ (tailᵐ mos x)                                           ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- The expression ∥ σ ∥ mos *> (𝟘ᶜ , x ≔ p) has the same value for two
  -- potentially different values of p: 𝟙 and ⌜ mos x ⌝.

  ∥∥-*>-𝟘ᶜ,≔𝟙 :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    (σ : Subst m n) →
    (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos ≈ᶜ (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* ∥ σ ∥ mos
  ∥∥-*>-𝟘ᶜ,≔𝟙 {x = x} {mos = mos} σ = begin
    (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos               ≈⟨ substₘ-calc-row σ _ ⟩
    ⌈ σ x ⌉ (mos x)                         ≈˘⟨ ·-⌈⌉ (σ x) ⟩
    ⌜ mos x ⌝ ·ᶜ ⌈ σ x ⌉ (mos x)            ≈˘⟨ ·ᶜ-congˡ (substₘ-calc-row σ _) ⟩
    ⌜ mos x ⌝ ·ᶜ (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos  ≈⟨ ·ᶜ-<*-𝟘ᶜ,≔𝟙 (∥ σ ∥ _) ⟩
    (𝟘ᶜ , x ≔ ⌜ mos x ⌝) <* ∥ σ ∥ mos       ∎
    where
    open ≈ᶜ-reasoning

opaque

  -- An inferred substitution matrix is well-formed if all substituted
  -- terms are well-resourced (for suitable modes), and there is a
  -- dedicated nr function.

  substₘ-calc-correct :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
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
    open ≤ᶜ-reasoning

opaque

  -- If any substitution matrix is well-formed then the inferred
  -- substitution matrix is well-formed (for suitable modes) if there is
  -- a dedicated nr function.

  subst-calc-correct′ :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    (Ψ : Substₘ m n) →
    Ψ ▶[ mos ] σ → ∥ σ ∥ mos ▶[ mos ] σ
  subst-calc-correct′           []      _   ()
  subst-calc-correct′ {mos} {σ} (Ψ ⊙ γ) Ψ▶σ x0 = sub
    (usage-inf (Ψ▶σ x0))
    (begin
       ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ
       𝟘ᶜ <* ∥ tail σ ∥ (tailᵐ mos)                   ≈⟨ +ᶜ-congˡ (<*-zeroˡ (∥ tail σ ∥ _)) ⟩

       ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos) +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩

       ⌜ headᵐ mos ⌝ ·ᶜ ⌈ head σ ⌉ (headᵐ mos)        ≈⟨ ·-⌈⌉ (head σ) ⟩

       ⌈ head σ ⌉ (headᵐ mos)                         ∎)
    where
    open ≤ᶜ-reasoning
  subst-calc-correct′ (Ψ ⊙ γ) Ψ▶σ (x +1) =
    sub-≈ᶜ (subst-calc-correct′ Ψ (wf-tailSubstₘ Ψ▶σ) x)
      (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ _)) (+ᶜ-identityˡ _))

opaque

  -- If there is a dedicated nr function, and either strong unit types
  -- are not allowed to be used as sinks or 𝟘 is a greatest grade, then
  -- each row of a calculated substitution matrix is an upper bound of
  -- the usage contexts (for a suitable mode) of the corresponding
  -- substituted term.

  substₘ-calc-upper-bound :
    ⦃ ok : Natrec-mode-supports-usage-inference natrec-mode ⦄ →
    ¬ Starˢ-sink ⊎ (∀ {p} → p ≤ 𝟘) →
    {γ : Conₘ m} (σ : Subst m n) (x : Fin n) →
    γ ▸[ mos x ] σ x → γ ≤ᶜ  (𝟘ᶜ , x ≔ 𝟙) <* ∥ σ ∥ mos
  substₘ-calc-upper-bound ok σ x γ▸σx =
    ≤ᶜ-trans (usage-upper-bound ok γ▸σx)
             (≤ᶜ-reflexive (≈ᶜ-sym (substₘ-calc-row σ x)))

------------------------------------------------------------------------
-- Well-formedness of substitution compositions

opaque

  -- Compositions of suitably well-formed substitutions are well-formed.

  wf-compSubst :
    (Ψ : Substₘ m ℓ) {Φ : Substₘ ℓ n} {σ : Subst m ℓ} {σ′ : Subst ℓ n} →
    Ψ ▶[ ⌞ ⌜ mos ⌝ᶜ <* Φ ⌟ᶜ ] σ → Φ ▶[ mos ] σ′ →
    (Ψ <*> Φ) ▶[ mos ] (σ ₛ•ₛ σ′)
  wf-compSubst {mos = mos} Ψ {Φ = Φ} {σ = σ} {σ′ = σ′} Ψ▶σ Φ▶σ′ x = sub
    (substₘ-lemma
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
    open ≤ᶜ-reasoning
