{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Context.Properties where

open import Definition.Modality
open import Definition.Modality.Context

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    n : Nat
    M : Set
    𝕄 : Modality M

-- Modality contexts form a left module

-- 𝟙 is a left identity to modality contex scaling
identity : (γ : ConM 𝕄 n) → (Modality.𝟙 𝕄) ·ᶜ γ ≡ γ
identity           ε      = refl
identity {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ γ' p'
  where
  γ' = identity γ
  p' = (proj₁ (Modality.·-Identity 𝕄)) p


-- 𝟘 is a left zero to modality context scaling
leftZero : (γ : ConM 𝕄 n) → (Modality.𝟘 𝕄) ·ᶜ γ ≡ 𝟘ᶜ
leftZero           ε      = refl
leftZero {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ IH z
  where
  IH = leftZero γ
  z  = proj₁ (Modality.·-Zero 𝕄) p


-- A zero context is a right zero to modality context scaling
rightZero : {𝕄 : Modality M} → (p : M) → p ·ᶜ 𝟘ᶜ ≡ 𝟘ᶜ {𝕄 = 𝕄} {n = n}
rightZero {n = 0}    p = refl
rightZero {n = 1+ n} {𝕄 = 𝕄} p = cong₂ _∙_ IH z
  where
  IH = rightZero p
  z  = proj₂ (Modality.·-Zero 𝕄) p

-- Modality context scaling is associative
associative : (p q : M) → (γ : ConM 𝕄 n) → (Modality._·_ 𝕄 p q) ·ᶜ γ ≡ p ·ᶜ (q ·ᶜ γ)
associative          p q  ε      = refl
associative {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ γ' r'
  where
  γ' = associative p q γ
  r' = Modality.·-Associative 𝕄 p q r

-- Modality contex scaling is left distributive over addition
leftDistr+ : (p : M) → (γ δ : ConM 𝕄 n) → p ·ᶜ (γ +ᶜ δ) ≡ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)
leftDistr+          p  ε       ε      = refl
leftDistr+ {𝕄 = 𝕄} p (γ ∙ q) (δ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = leftDistr+ p γ δ
  distr = proj₁ (Modality.·Distr+ 𝕄) p q r

-- Modality context scaling is right distributive over addition
rightDistr+ : (p q : M) → (γ : ConM 𝕄 n) → (Modality._+_ 𝕄 p q) ·ᶜ γ ≡ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)
rightDistr+          p q  ε      = refl
rightDistr+ {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = rightDistr+ p q γ
  distr = proj₂ (Modality.·Distr+ 𝕄) r p q

-- Modality contex scaling is left distributive over meet
leftDistr∧ : (p : M) → (γ δ : ConM 𝕄 n) → p ·ᶜ (γ ∧ᶜ δ) ≡ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)
leftDistr∧          p  ε       ε      = refl
leftDistr∧ {𝕄 = 𝕄} p (γ ∙ q) (δ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = leftDistr∧ p γ δ
  distr = proj₁ (Modality.·Distr∧ 𝕄) p q r

-- Modality context scaling is right distributive over meet
rightDistr∧ : (p q : M) → (γ : ConM 𝕄 n) → (Modality._∧_ 𝕄 p q) ·ᶜ γ ≡ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)
rightDistr∧          p q  ε      = refl
rightDistr∧ {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = rightDistr∧ p q γ
  distr = proj₂ (Modality.·Distr∧ 𝕄) r p q
