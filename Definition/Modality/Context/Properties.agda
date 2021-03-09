{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Context.Properties where

open import Definition.Untyped
open import Definition.Modality
open import Definition.Modality.Properties
open import Definition.Modality.Context

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    n : Nat
    M : Set
    𝕄 : Modality M
    p q : M
    γ δ : Conₘ 𝕄 n

-- Modality contexts form a left module

-- 𝟙 is a left identity to modality contex scaling
identity : {γ : Conₘ 𝕄 n} → (Modality.𝟙 𝕄) ·ᶜ γ ≡ γ
identity           {γ = ε}      = refl
identity {𝕄 = 𝕄} {γ = γ ∙ p} = cong₂ _∙_ γ' p'
  where
  γ' = identity
  p' = (proj₁ (Modality.·-Identity 𝕄)) p


-- 𝟘 is a left zero to modality context scaling
leftZero : {γ : Conₘ 𝕄 n} → (Modality.𝟘 𝕄) ·ᶜ γ ≡ 𝟘ᶜ
leftZero           {γ = ε}      = refl
leftZero {𝕄 = 𝕄} {γ = γ ∙ p} = cong₂ _∙_ IH z
  where
  IH = leftZero
  z  = proj₁ (Modality.·-Zero 𝕄) p


-- A zero context is a right zero to modality context scaling
rightZero : {𝕄 : Modality M} → (p : M) → p ·ᶜ 𝟘ᶜ ≡ 𝟘ᶜ {𝕄 = 𝕄} {n = n}
rightZero {n = 0}    p = refl
rightZero {n = 1+ n} {𝕄 = 𝕄} p = cong₂ _∙_ IH z
  where
  IH = rightZero p
  z  = proj₂ (Modality.·-Zero 𝕄) p

-- Modality context scaling is associative
associative : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._·_ 𝕄 p q) ·ᶜ γ ≡ p ·ᶜ (q ·ᶜ γ)
associative          p q  ε      = refl
associative {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ γ' r'
  where
  γ' = associative p q γ
  r' = Modality.·-Associative 𝕄 p q r

-- Modality contex scaling is left distributive over addition
leftDistr+ : (p : M) → (γ δ : Conₘ 𝕄 n) → p ·ᶜ (γ +ᶜ δ) ≡ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)
leftDistr+          p  ε       ε      = refl
leftDistr+ {𝕄 = 𝕄} p (γ ∙ q) (δ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = leftDistr+ p γ δ
  distr = proj₁ (Modality.·Distr+ 𝕄) p q r

-- Modality context scaling is right distributive over addition
rightDistr+ : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._+_ 𝕄 p q) ·ᶜ γ ≡ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)
rightDistr+          p q  ε      = refl
rightDistr+ {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = rightDistr+ p q γ
  distr = proj₂ (Modality.·Distr+ 𝕄) r p q

-- Modality contex scaling is left distributive over meet
leftDistr∧ : (p : M) → (γ δ : Conₘ 𝕄 n) → p ·ᶜ (γ ∧ᶜ δ) ≡ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)
leftDistr∧          p  ε       ε      = refl
leftDistr∧ {𝕄 = 𝕄} p (γ ∙ q) (δ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = leftDistr∧ p γ δ
  distr = proj₁ (Modality.·Distr∧ 𝕄) p q r

-- Modality context scaling is right distributive over meet
rightDistr∧ : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._∧_ 𝕄 p q) ·ᶜ γ ≡ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)
rightDistr∧          p q  ε      = refl
rightDistr∧ {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = rightDistr∧ p q γ
  distr = proj₂ (Modality.·Distr∧ 𝕄) r p q

-------------

-- 𝟘ᶜ is left unit for addition
leftUnit : (γ : Conₘ 𝕄 n) → 𝟘ᶜ +ᶜ γ ≡ γ
leftUnit            ε      = refl
leftUnit {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ γ' p'
  where
  γ' = leftUnit γ
  p' = proj₁ (Modality.+-Identity 𝕄) p

-- 𝟘ᶜ is right unit for addition
rightUnit : {γ : Conₘ 𝕄 n} → γ +ᶜ 𝟘ᶜ ≡ γ
rightUnit           {γ = ε}      = refl
rightUnit {𝕄 = 𝕄} {γ = γ ∙ p} = cong₂ _∙_ γ' p'
  where
  γ' = rightUnit
  p' = proj₂ (Modality.+-Identity 𝕄) p


≤ᶜ-reflexive : {γ : Conₘ 𝕄 n} → γ ≤ᶜ γ
≤ᶜ-reflexive {γ = ε} = refl
≤ᶜ-reflexive {𝕄 = 𝕄} {γ = γ ∙ p} = cong₂ _∙_ ≤ᶜ-reflexive (≤-reflexive {𝕄 = 𝕄})

≤ᶜ-transitive : {γ δ η : Conₘ 𝕄 n} → γ ≤ᶜ δ → δ ≤ᶜ η → γ ≤ᶜ η
≤ᶜ-transitive {γ = ε} {ε} {ε} x y = refl
≤ᶜ-transitive {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} x y = cong₂ _∙_
  (≤ᶜ-transitive (cong tailₘ x) (cong tailₘ y))
  (≤-transitive {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))

≤ᶜ-antisymmetric : {γ δ : Conₘ 𝕄 n} → γ ≤ᶜ δ → δ ≤ᶜ γ → γ ≡ δ
≤ᶜ-antisymmetric {γ = ε} {ε} refl refl = refl
≤ᶜ-antisymmetric {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} x y = cong₂ _∙_
  (≤ᶜ-antisymmetric (cong tailₘ x) (cong tailₘ y))
  (≤-antisymmetric {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))

+ᶜ-monotone : {γ δ η : Conₘ 𝕄 n} → γ ≤ᶜ δ → γ +ᶜ η ≤ᶜ δ +ᶜ η
+ᶜ-monotone {γ = ε} {ε} {ε} refl = refl
+ᶜ-monotone {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} x = cong₂ _∙_
  (+ᶜ-monotone (cong tailₘ x))
  (+-monotone {𝕄 = 𝕄} (cong headₘ x))

+ᶜ-monotone₂ : {γ γ′ δ δ′ : Conₘ 𝕄 n} → γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → (γ +ᶜ δ) ≤ᶜ (γ′ +ᶜ δ′)
+ᶜ-monotone₂ {γ = ε} {ε} {ε} {ε} refl refl = refl
+ᶜ-monotone₂ {𝕄 = 𝕄} {γ = γ ∙ p} {γ′ ∙ p′} {δ ∙ q} {δ′ ∙ q′} x y = cong₂ _∙_
  (+ᶜ-monotone₂ (cong tailₘ x) (cong tailₘ y))
  (+-monotone₂ {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))

·ᶜ-monotone : {p : M} {γ δ : Conₘ 𝕄 n} → γ ≤ᶜ δ → p ·ᶜ γ ≤ᶜ p ·ᶜ δ
·ᶜ-monotone {γ = ε} {ε} refl = refl
·ᶜ-monotone {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} x = cong₂ _∙_
  (·ᶜ-monotone (cong tailₘ x))
  (·-monotoneˡ {𝕄 = 𝕄} (cong headₘ x))

·ᶜ-monotone₂ : {p q : M} {γ δ : Conₘ 𝕄 n} → γ ≤ᶜ δ → Modality._≤_ 𝕄 p q → p ·ᶜ γ ≤ᶜ q ·ᶜ δ
·ᶜ-monotone₂ {γ = ε} {ε} γ≤δ p≤q = refl
·ᶜ-monotone₂ {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} γ≤δ p≤q = cong₂ _∙_
  (·ᶜ-monotone₂ (cong tailₘ γ≤δ) p≤q)
  (·-monotone₂ {𝕄 = 𝕄} p≤q (cong headₘ γ≤δ))

tail-linear∧ : {γ δ : Conₘ 𝕄 (1+ n)} → tailₘ (γ ∧ᶜ δ) ≡ (tailₘ γ) ∧ᶜ (tailₘ δ)
tail-linear∧ {γ = γ ∙ p} {δ ∙ q} = refl

+ᶜ-associative : (γ δ η : Conₘ 𝕄 n) → (γ +ᶜ δ) +ᶜ η ≡ γ +ᶜ (δ +ᶜ η)
+ᶜ-associative ε ε ε = refl
+ᶜ-associative {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) (η ∙ r) = cong₂ _∙_ (+ᶜ-associative γ δ η) (Modality.+-Associative 𝕄 p q r)

+ᶜ-comm : (γ δ : Conₘ 𝕄 n) → γ +ᶜ δ ≡ δ +ᶜ γ
+ᶜ-comm ε ε = refl
+ᶜ-comm {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = cong₂ _∙_ (+ᶜ-comm γ δ) (Modality.+-Commutative 𝕄 p q)

insertAt-𝟘 : {m : Nat} (n : Nat)
           → 𝟘ᶜ {𝕄 = 𝕄} {n = n + 1+ m} ≡ insertAt n (𝟘ᶜ {n = n + m}) (Modality.𝟘 𝕄)
insertAt-𝟘 0      = refl
insertAt-𝟘 (1+ n) = cong₂ _∙_ (insertAt-𝟘 n) refl

insertAt-distrib-+ᶜ : {𝕄 : Modality M} {m : Nat} (n : Nat) (γ δ : Conₘ 𝕄 (n + m)) (p q : M)
                    → insertAt n γ p +ᶜ insertAt n δ q ≡ insertAt n (γ +ᶜ δ) (Modality._+_ 𝕄 p q)
insertAt-distrib-+ᶜ 0      γ δ p q = refl
insertAt-distrib-+ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q = cong₂ _∙_ (insertAt-distrib-+ᶜ n γ δ p q) refl

insertAt-distrib-+ᶜ-𝟘 : {𝕄 : Modality M} {m : Nat} (n : Nat) (γ δ : Conₘ 𝕄 (n + m))
                      → insertAt n γ (Modality.𝟘 𝕄) +ᶜ insertAt n δ (Modality.𝟘 𝕄)
                      ≡ insertAt n (γ +ᶜ δ) (Modality.𝟘 𝕄)
insertAt-distrib-+ᶜ-𝟘 {𝕄 = 𝕄} n γ δ = begin
  insertAt n γ (Modality.𝟘 𝕄) +ᶜ insertAt n δ (Modality.𝟘 𝕄)
    ≡⟨ insertAt-distrib-+ᶜ n γ δ (Modality.𝟘 𝕄) (Modality.𝟘 𝕄) ⟩
  insertAt n (γ +ᶜ δ) ((𝕄 Modality.+ Modality.𝟘 𝕄) (Modality.𝟘 𝕄))
    ≡⟨ cong (insertAt n (γ +ᶜ δ)) (proj₁ (Modality.+-Identity 𝕄) (Modality.𝟘 𝕄)) ⟩
  insertAt n (γ +ᶜ δ) (Modality.𝟘 𝕄) ∎  

insertAt-distrib-·ᶜ : {𝕄 : Modality M} {m : Nat} (n : Nat) (γ δ : Conₘ 𝕄 (n + m)) (p q : M)
                    → p ·ᶜ insertAt n γ q ≡ insertAt n (p ·ᶜ γ) (Modality._·_ 𝕄 p q)
insertAt-distrib-·ᶜ 0 γ δ p q = refl
insertAt-distrib-·ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q = cong₂ _∙_ (insertAt-distrib-·ᶜ n γ δ p q) refl

insertAt-monotone : {𝕄 : Modality M} {m : Nat} (n : Nat) (γ δ : Conₘ 𝕄 (n + m)) (p q : M)
                  → γ ≤ᶜ δ → Modality._≤_ 𝕄 p q → insertAt n γ p ≤ᶜ insertAt n δ q
insertAt-monotone Nat.zero γ δ p q γ≤δ p≤q = cong₂ _∙_ γ≤δ p≤q
insertAt-monotone (1+ n) (γ ∙ p′) (δ ∙ q′) p q γ≤δ p≤q = cong₂ _∙_ (insertAt-monotone n γ δ p q (cong tailₘ γ≤δ) p≤q) (cong headₘ γ≤δ)

insertAt-liftn : {m : Nat} (n : Nat) (x : Fin (n + m))
              → (𝟘ᶜ {𝕄 = 𝕄} , wkVar (liftn (step id) n) x ≔ Modality.𝟙 𝕄) ≡
                insertAt n (𝟘ᶜ , x ≔ Modality.𝟙 𝕄) (Modality.𝟘 𝕄)
insertAt-liftn 0 x = refl
insertAt-liftn (1+ n) x0 = cong₂ _∙_ (insertAt-𝟘 n) refl
insertAt-liftn (1+ n) (_+1 x) = cong₂ _∙_ (insertAt-liftn n x) refl


