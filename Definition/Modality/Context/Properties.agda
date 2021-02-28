{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Context.Properties where

open import Definition.Modality
open import Definition.Modality.Properties
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

-------------

-- 𝟘ᶜ is left unit for addition
leftUnit : (γ : ConM 𝕄 n) → 𝟘ᶜ +ᶜ γ ≡ γ
leftUnit           ε      = refl
leftUnit {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ γ' p'
  where
  γ' = leftUnit γ
  p' = proj₁ (Modality.+-Identity 𝕄) p

-- 𝟘ᶜ is right unit for addition
rightUnit : (γ : ConM 𝕄 n) → γ +ᶜ 𝟘ᶜ ≡ γ
rightUnit           ε      = refl
rightUnit {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ γ' p'
  where
  γ' = rightUnit γ
  p' = proj₂ (Modality.+-Identity 𝕄) p


≤ᶜ-reflexive : {γ : ConM 𝕄 n} → γ ≤ᶜ γ
≤ᶜ-reflexive {γ = ε} = refl
≤ᶜ-reflexive {𝕄 = 𝕄} {γ = γ ∙ p} = cong₂ _∙_ ≤ᶜ-reflexive (≤-reflexive {𝕄 = 𝕄})

≤ᶜ-transitive : {γ δ η : ConM 𝕄 n} → γ ≤ᶜ δ → δ ≤ᶜ η → γ ≤ᶜ η
≤ᶜ-transitive {γ = ε} {ε} {ε} x y = refl
≤ᶜ-transitive {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} x y = cong₂ _∙_
  (≤ᶜ-transitive (cong tailₘ x) (cong tailₘ y))
  (≤-transitive {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))

≤ᶜ-antisymmetric : {γ δ : ConM 𝕄 n} → γ ≤ᶜ δ → δ ≤ᶜ γ → γ ≡ δ
≤ᶜ-antisymmetric {γ = ε} {ε} refl refl = refl
≤ᶜ-antisymmetric {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} x y = cong₂ _∙_
  (≤ᶜ-antisymmetric (cong tailₘ x) (cong tailₘ y))
  (≤-antisymmetric {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))

+ᶜ-monotone : {γ δ η : ConM 𝕄 n} → γ ≤ᶜ δ → γ +ᶜ η ≤ᶜ δ +ᶜ η
+ᶜ-monotone {γ = ε} {ε} {ε} refl = refl
+ᶜ-monotone {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} x = cong₂ _∙_
  (+ᶜ-monotone (cong tailₘ x))
  (+-monotone {𝕄 = 𝕄} (cong headₘ x))

+ᶜ-monotone₂ : {γ γ′ δ δ′ : ConM 𝕄 n} → γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → (γ +ᶜ δ) ≤ᶜ (γ′ +ᶜ δ′)
+ᶜ-monotone₂ {γ = ε} {ε} {ε} {ε} refl refl = refl
+ᶜ-monotone₂ {𝕄 = 𝕄} {γ = γ ∙ p} {γ′ ∙ p′} {δ ∙ q} {δ′ ∙ q′} x y = cong₂ _∙_
  (+ᶜ-monotone₂ (cong tailₘ x) (cong tailₘ y))
  (+-monotone₂ {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))

·ᶜ-monotone : {p : M} {γ δ : ConM 𝕄 n} → γ ≤ᶜ δ → p ·ᶜ γ ≤ᶜ p ·ᶜ δ
·ᶜ-monotone {γ = ε} {ε} refl = refl
·ᶜ-monotone {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} x = cong₂ _∙_
  (·ᶜ-monotone (cong tailₘ x))
  (·-monotone {𝕄 = 𝕄} (cong headₘ x))

tail-linear∧ : {γ δ : ConM 𝕄 (1+ n)} → tailₘ (γ ∧ᶜ δ) ≡ (tailₘ γ) ∧ᶜ (tailₘ δ)
tail-linear∧ {γ = γ ∙ p} {δ ∙ q} = refl
