{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties.Update {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties.PartialOrder 𝕄
open import Definition.Modality.Properties 𝕄

open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.PropositionalEquality as PE

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

private
  variable
    n : Nat
    p q : M
    γ δ : Conₘ n

-- Updating a context with its own content has no effect
-- (γ , x ≔ (γ ⟨ x ⟩)) ≡ γ

update-self : (γ : Conₘ n) (x : Fin n) → (γ , x ≔ (γ ⟨ x ⟩)) ≡ γ
update-self (γ ∙ p) x0     = PE.refl
update-self (γ ∙ p) (x +1) = cong (_∙ _) (update-self γ x)

-- Context update is a monotone function with regards to the context
-- If γ ≤ᶜ δ then (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)

update-monotoneˡ : (x : Fin n) → γ ≤ᶜ δ → (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)
update-monotoneˡ {γ = γ ∙ p} {δ ∙ q} x0 (γ≤δ ∙ _)        = γ≤δ ∙ ≤-refl
update-monotoneˡ {γ = γ ∙ p} {δ ∙ q} (_+1 x) (γ≤δ ∙ p≤q) = (update-monotoneˡ x γ≤δ) ∙ p≤q

-- Context update is monotone with regards to the inserted element
-- If p ≤ q then( γ , x ≔ p) ≤ᶜ (γ , x ≔ q)

update-monotoneʳ : (x : Fin n) → p ≤ q → (γ , x ≔ p) ≤ᶜ (γ , x ≔ q)
update-monotoneʳ {γ = γ ∙ p} x0 p≤q     = ≤ᶜ-refl ∙ p≤q
update-monotoneʳ {γ = γ ∙ p} (x +1) p≤q = (update-monotoneʳ x p≤q) ∙ ≤-refl

-- Context update distributes over addition
-- (γ +ᶜ δ) , x ≔ (p + q) ≡ (γ , x ≔ p) +ᶜ (δ , x ≔ q)

update-distrib-+ᶜ : (γ δ : Conₘ n) (p q : M) (x : Fin n)
                  → (γ +ᶜ δ) , x ≔ (p + q) ≡ (γ , x ≔ p) +ᶜ (δ , x ≔ q)
update-distrib-+ᶜ (γ ∙ p′) (δ ∙ q′) p q x0     = PE.refl
update-distrib-+ᶜ (γ ∙ p′) (δ ∙ q′) p q (x +1) = cong (_∙ _) (update-distrib-+ᶜ γ δ p q x)

-- Context update distributes over multiplication
-- (p ·ᶜ γ) , x ≔ (p · q) ≡ p ·ᶜ (γ , x ≔ q)

update-distrib-·ᶜ : (γ : Conₘ n) (p q : M) (x : Fin n)
                  → (p ·ᶜ γ) , x ≔ (p · q) ≡ p ·ᶜ (γ , x ≔ q)
update-distrib-·ᶜ (γ ∙ r) p q x0     = PE.refl
update-distrib-·ᶜ (γ ∙ r) p q (x +1) = cong (_∙ _) (update-distrib-·ᶜ γ p q x)

-- Context update distributes over meet
-- (γ ∧ᶜ δ) , x ≔ (p ∧ q) ≡ (γ , x ≔ p) ∧ᶜ (δ , x ≔ q)

update-distrib-∧ᶜ : (γ δ : Conₘ n) (p q : M) (x : Fin n)
                  → (γ ∧ᶜ δ) , x ≔ (p ∧ q) ≡ (γ , x ≔ p) ∧ᶜ (δ , x ≔ q)
update-distrib-∧ᶜ (γ ∙ p′) (δ ∙ q′) p q x0 = PE.refl
update-distrib-∧ᶜ (γ ∙ p′) (δ ∙ q′) p q (x +1) = cong (_∙ _) (update-distrib-∧ᶜ γ δ p q x)

-- Context update distributes over nrᶜ
-- nrᶜ γ δ r , x ≔ nr p q r ≡ nrᶜ (γ , x ≔ p) (δ , x ≔ q) r

update-distrib-nrᶜ : (γ δ : Conₘ n) (r p q : M) (x : Fin n)
                   → nrᶜ γ δ r , x ≔ (nr p q r) ≡ nrᶜ (γ , x ≔ p) (δ , x ≔ q) r
update-distrib-nrᶜ (γ ∙ _) (δ ∙ _) r p q x0 = PE.refl
update-distrib-nrᶜ (γ ∙ _) (δ ∙ _) r p q (x +1) =
  cong (_∙ _) (update-distrib-nrᶜ γ δ r p q x)

-- Updating the head of a context leaves the tail untouched
-- γ , x0 ≔ p ≡ tailₘ γ ∙ p

update-head : (γ : Conₘ (1+ n)) (p : M) → γ , x0 ≔ p ≡ tailₘ γ ∙ p
update-head (γ ∙ q) p = PE.refl

-- Updating the tail of a context leaves the head untouched
-- γ , (x +1) ≔ p ≡ (tailₘ γ , x ≔ p) ∙ headₘ γ

update-step : (γ : Conₘ (1+ n)) (p : M) (x : Fin n)
            → γ , (x +1) ≔ p ≡ (tailₘ γ , x ≔ p) ∙ headₘ γ
update-step (γ ∙ q) p x = PE.refl
