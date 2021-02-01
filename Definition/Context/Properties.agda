{-# OPTIONS --without-K --safe #-}

module Definition.Context.Properties where

open import Definition.Context
open import Definition.Modality
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

-- Modality contexts form a left module

-- 𝟙 is a left identity to modality contex scaling
identity : {A : Set} → (M : Modality A) → (γ : Con A)
                     → M ∷ (Modality.𝟙 M) · γ ≡ γ
identity M  ε      = refl
identity M (γ · p) = cong₂ _·_ γ' p'
  where
    γ' = identity M γ
    p' = (proj₁ (Modality.·-Identity M)) p

-- 𝟘 is a left zero to modality context scaling
leftZero : {A : Set} → (M : Modality A) → (γ : Con A)
                     → ∃ (λ n → 𝟘ᶜ M n ≡ M ∷ (Modality.𝟘 M) · γ)
leftZero M  ε      = (Nat.zero , refl)
leftZero M (γ · p) = (1+ (proj₁ IH)) , (cong₂ _·_ (proj₂ IH) z)
  where
    IH = leftZero M γ
    z = sym (proj₁ (Modality.·-Zero M) p)


-- A zero context is a right zero to modality context scaling
rightZero : {A : Set} → (M : Modality A) → (p : A) → (n : Nat)
                      → 𝟘ᶜ M n ≡ M ∷ p · 𝟘ᶜ M n
rightZero M p  0     = refl
rightZero M p (1+ n) = cong₂ _·_ IH z
  where
    IH = rightZero M p n
    z  = sym (proj₂ (Modality.·-Zero M) p)

-- Modality context scaling is associative
associative : {A : Set} → (M : Modality A) → (p q : A) → (γ : Con A)
                        → M ∷ (Modality._·_ M p q) · γ ≡ M ∷ p · (M ∷ q · γ)
associative M p q  ε      = refl
associative M p q (γ · r) = cong₂ _·_ γ' r'
  where
    γ' = associative M p q γ
    r' = Modality.·-Associative M p q r

-- Modality contex scaling is left distributive over addition
leftDistr+ : {A : Set} → (M : Modality A) → (p : A) → (γ δ : Con A)
                       → M ∷ p · (M ∷ γ + δ) ≡ M ∷ (M ∷ p · γ) + (M ∷ p · δ)
leftDistr+ M p γ ε = refl
leftDistr+ M p  ε      (δ · r) = refl
leftDistr+ M p (γ · q) (δ · r) = cong₂ _·_ IH distr
  where
    IH    = leftDistr+ M p γ δ
    distr = proj₁ (Modality.·Distr+ M) p q r

-- Modality context scaling is right distributive over addition
rightDistr+ : {A : Set} → (M : Modality A) → (p q : A) → (γ : Con A)
                        → M ∷ (Modality._+_ M p q) · γ ≡ M ∷ (M ∷ p · γ) + (M ∷ q · γ)
rightDistr+ M p q  ε      = refl
rightDistr+ M p q (γ · r) = cong₂ _·_ IH distr
  where
    IH    = rightDistr+ M p q γ
    distr = proj₂ (Modality.·Distr+ M) r p q

-- Modality contex scaling is left distributive over meet
leftDistr∧ : {A : Set} → (M : Modality A) → (p : A) → (γ δ : Con A)
                       → M ∷ p · (M ∷ γ ∧ δ) ≡ M ∷ (M ∷ p · γ) ∧ (M ∷ p · δ)
leftDistr∧ M p γ        ε      = refl
leftDistr∧ M p ε       (δ · r) = refl
leftDistr∧ M p (γ · q) (δ · r) = cong₂ _·_ IH distr
  where
    IH    = leftDistr∧ M p γ δ
    distr = proj₁ (Modality.·Distr∧ M) p q r

-- Modality context scaling is right distributive over meet
rightDistr∧ : {A : Set} → (M : Modality A) → (p q : A) → (γ : Con A)
                        → M ∷ (Modality._∧_ M p q) · γ ≡ M ∷ (M ∷ p · γ) ∧ (M ∷ q · γ)
rightDistr∧ M p q  ε      = refl
rightDistr∧ M p q (γ · r) = cong₂ _·_ IH distr
  where
    IH    = rightDistr∧ M p q γ
    distr = proj₂ (Modality.·Distr∧ M) r p q
