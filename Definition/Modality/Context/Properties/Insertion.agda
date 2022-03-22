{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.Insertion {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties.Equivalence 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Untyped M using (wkVar; liftn; step; id)

open import Tools.Fin
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.Product
open import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    p q : M

-- Congruence of insertAt
-- If γ ≈ᶜ δ and p ≈ q then insertAt n γ p ≈ᶜ insertAt n δ q

insertAt-cong : {γ δ : Conₘ (n +ⁿ m)} → γ ≈ᶜ δ → p ≈ q → insertAt n γ p ≈ᶜ insertAt n δ q
insertAt-cong {n = 0} γ≈δ p≈q = γ≈δ ∙ p≈q
insertAt-cong {n = 1+ n} (γ≈δ ∙ p′≈q′) p≈q = (insertAt-cong γ≈δ p≈q) ∙ p′≈q′

-- Inserting a zero into a zero-context gives a zero-context
-- insertAt x 𝟘ᶜ 𝟘 ≡ 𝟘ᶜ

insertAt-𝟘 : (n : Nat) → insertAt n (𝟘ᶜ {n = n +ⁿ m}) 𝟘 ≡ 𝟘ᶜ {n = n +ⁿ 1+ m}
insertAt-𝟘 0      = PE.refl
insertAt-𝟘 (1+ n) = cong (_∙ _) (insertAt-𝟘 n)

-- Inserting the sum of two elements distributes over addition
-- insertAt n (γ +ᶜ δ) (p + q) ≡ insertAt n γ p +ᶜ insertAt n δ q

insertAt-distrib-+ᶜ : (n : Nat) (γ δ : Conₘ (n +ⁿ m)) (p q : M)
                    → insertAt n (γ +ᶜ δ) (p + q) ≡ insertAt n γ p +ᶜ insertAt n δ q
insertAt-distrib-+ᶜ 0 γ δ p q = PE.refl
insertAt-distrib-+ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q =
  cong (_∙ _) (insertAt-distrib-+ᶜ n γ δ p q)

-- Inserting a zero into a modality context distributes over addition
-- insertAt n (γ +ᶜ δ) 𝟘 ≈ᶜ insertAt n γ 𝟘 +ᶜ insertAt n δ 𝟘

insertAt-distrib-+ᶜ-𝟘 : (n : Nat) (γ δ : Conₘ (n +ⁿ m))
                      → insertAt n (γ +ᶜ δ) 𝟘 ≈ᶜ insertAt n γ 𝟘 +ᶜ insertAt n δ 𝟘
insertAt-distrib-+ᶜ-𝟘  n γ δ = begin
  insertAt n (γ +ᶜ δ) 𝟘            ≈⟨ insertAt-cong ≈ᶜ-refl (≈-sym (proj₁ +-identity 𝟘)) ⟩
  insertAt n (γ +ᶜ δ) (𝟘 + 𝟘)      ≡⟨ insertAt-distrib-+ᶜ n γ δ 𝟘 𝟘 ⟩
  insertAt n γ 𝟘 +ᶜ insertAt n δ 𝟘 ∎
  where open import Tools.Reasoning.Equivalence Conₘ-setoid

-- Inserting the product of two elements distributes over context scaling
-- insertAt n (p ·ᶜ γ) (p · q) ≡ p ·ᶜ insertAt n γ q

insertAt-distrib-·ᶜ : (n : Nat) (γ : Conₘ (n +ⁿ m)) (p q : M)
                    → insertAt n (p ·ᶜ γ) (p · q) ≡ p ·ᶜ insertAt n γ q
insertAt-distrib-·ᶜ 0 γ p q = PE.refl
insertAt-distrib-·ᶜ (1+ n) (γ ∙ r) p q =
  cong (_∙ _) (insertAt-distrib-·ᶜ n γ p q)

-- Inserting a zero into a modality context distributes over context scaling
-- insertAt n (p ·ᶜ γ) 𝟘 ≈ᶜ p ·ᶜ insertAt n γ 𝟘

insertAt-distrib-·ᶜ-𝟘 : (n : Nat) (p : M) (γ : Conₘ (n +ⁿ m))
                      → insertAt n (p ·ᶜ γ) 𝟘 ≈ᶜ p ·ᶜ insertAt n γ 𝟘
insertAt-distrib-·ᶜ-𝟘 n p γ = begin
  insertAt n (p ·ᶜ γ) 𝟘       ≈⟨ insertAt-cong ≈ᶜ-refl (≈-sym (proj₂ ·-zero p)) ⟩
  insertAt n (p ·ᶜ γ) (p · 𝟘) ≡⟨ insertAt-distrib-·ᶜ n γ p 𝟘 ⟩
  p ·ᶜ insertAt n γ 𝟘         ∎
  where open import Tools.Reasoning.Equivalence Conₘ-setoid

-- Inserting the meet of two elements distributes over meet
-- insertAt n (γ ∧ᶜ δ) (p ∧ q) ≡ insertAt n γ p ∧ᶜ insertAt n δ q

insertAt-distrib-∧ᶜ : (n : Nat) (γ δ : Conₘ (n +ⁿ m)) (p q : M)
                    → insertAt n (γ ∧ᶜ δ) (p ∧ q) ≡ insertAt n γ p ∧ᶜ insertAt n δ q
insertAt-distrib-∧ᶜ 0 γ δ p q = PE.refl
insertAt-distrib-∧ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q =
  cong (_∙ _) (insertAt-distrib-∧ᶜ n γ δ p q)

-- Inserting a zero into a modality context distributes over meet
-- insertAt n (γ ∧ᶜ δ) 𝟘 ≈ᶜ insertAt n γ 𝟘 ∧ᶜ insertAt n δ 𝟘

insertAt-distrib-∧ᶜ-𝟘 : (n : Nat) (γ δ : Conₘ (n +ⁿ m))
                      → insertAt n (γ ∧ᶜ δ) 𝟘 ≈ᶜ insertAt n γ 𝟘 ∧ᶜ insertAt n δ 𝟘
insertAt-distrib-∧ᶜ-𝟘 n γ δ = begin
  insertAt n (γ ∧ᶜ δ) 𝟘            ≈⟨ insertAt-cong ≈ᶜ-refl (≈-sym (∧-idem 𝟘)) ⟩
  insertAt n (γ ∧ᶜ δ) (𝟘 ∧ 𝟘)      ≡⟨ insertAt-distrib-∧ᶜ n γ δ 𝟘 𝟘 ⟩
  insertAt n γ 𝟘 ∧ᶜ insertAt n δ 𝟘 ∎
  where
  open import Tools.Reasoning.Equivalence Conₘ-setoid

-- Inserting a zero into a modality context distributes over nrᶜ
-- insertAt n (nrᶜ γ δ r) 𝟘 ≡ nrᶜ (insertAt n γ 𝟘) (insertAt n δ 𝟘) r

insertAt-distrib-nrᶜ-𝟘 : (n : Nat) (γ δ : Conₘ (n +ⁿ m)) (r : M)
                     → insertAt n (nrᶜ γ δ r) 𝟘 ≈ᶜ nrᶜ (insertAt n γ 𝟘) (insertAt n δ 𝟘) r
insertAt-distrib-nrᶜ-𝟘 0 γ δ r = ≈ᶜ-refl ∙ (≈-sym (nr-idem-𝟘 r))
insertAt-distrib-nrᶜ-𝟘 (1+ n) (γ ∙ p) (δ ∙ q) r = (insertAt-distrib-nrᶜ-𝟘 n γ δ r) ∙ ≈-refl

-- Inserting an element into a modality context is a monotone function
-- If γ ≤ᶜ δ and p ≤ q, then insertAt n γ p ≤ᶜ insertAt n δ q

insertAt-monotone : (n : Nat) (γ δ : Conₘ (n +ⁿ m)) (p q : M)
                  → γ ≤ᶜ δ → p ≤ q → insertAt n γ p ≤ᶜ insertAt n δ q
insertAt-monotone 0 γ δ p q γ≤δ p≤q = γ≤δ ∙ p≤q
insertAt-monotone (1+ n) (γ ∙ p′) (δ ∙ q′) p q (γ≤δ ∙ p′≤q′) p≤q =
  insertAt-monotone n γ δ p q γ≤δ p≤q ∙ p′≤q′

-- Lemma on insertions and lifted variable weakenings
-- 𝟘ᶜ , x[⇑ⁿ(↑id)] ≔ 𝟙 ≡ insertAt n (𝟘ᶜ , x ≔ 𝟙) 𝟘

insertAt-liftn : (n : Nat) (x : Fin (n +ⁿ m))
               → (𝟘ᶜ , wkVar (liftn (step id) n) x ≔ 𝟙) ≡ insertAt n (𝟘ᶜ , x ≔ 𝟙) 𝟘
insertAt-liftn 0 x = PE.refl
insertAt-liftn (1+ n) x0 = cong (_∙ _) (PE.sym (insertAt-𝟘 n))
insertAt-liftn (1+ n) (x +1) = cong (_∙ _) (insertAt-liftn n x)
