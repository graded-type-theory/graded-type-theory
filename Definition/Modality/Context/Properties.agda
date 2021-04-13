{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Context.Properties where

open import Definition.Untyped
open import Definition.Modality
open import Definition.Modality.Properties
open import Definition.Modality.Context

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE

private
  variable
    n m : Nat
    M : Set
    𝕄 : Modality M
    p q : M
    γ γ′ δ δ′ η : Conₘ 𝕄 n

------------------------------------------
-- Modality contexts form a left module --
------------------------------------------

-- 𝟙 is a left identity to modality contex scaling
-- 𝟙 ·ᶜ γ ≡ γ

·ᶜ-identityˡ : (γ : Conₘ 𝕄 n) → (Modality.𝟙 𝕄) ·ᶜ γ ≡ γ
·ᶜ-identityˡ            ε      = refl
·ᶜ-identityˡ {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ (·ᶜ-identityˡ γ) ((proj₁ (Modality.·-Identity 𝕄)) p)

-- 𝟘 is a left zero to modality context scaling
-- 𝟘 ·ᶜ γ ≡ 𝟘ᶜ

·ᶜ-zeroˡ : (γ : Conₘ 𝕄 n) → (Modality.𝟘 𝕄) ·ᶜ γ ≡ 𝟘ᶜ
·ᶜ-zeroˡ            ε      = refl
·ᶜ-zeroˡ {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ (·ᶜ-zeroˡ γ) (proj₁ (Modality.·-Zero 𝕄) p)

-- A zero context is a right zero to modality context scaling
-- p ·ᶜ 𝟘ᶜ ≡ 𝟘ᶜ

·ᶜ-zeroʳ : {n : Nat} {𝕄 : Modality M} (p : M) → p ·ᶜ 𝟘ᶜ ≡ 𝟘ᶜ {𝕄 = 𝕄} {n = n}
·ᶜ-zeroʳ {n = 0}              p = refl
·ᶜ-zeroʳ {n = 1+ n} {𝕄 = 𝕄} p = cong₂ _∙_ (·ᶜ-zeroʳ p) (proj₂ (Modality.·-Zero 𝕄) p)

-- Modality context scaling is associative
-- (p · q) ·ᶜ γ ≡ p ·ᶜ (q ·ᶜ γ)

·ᶜ-assoc : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._·_ 𝕄 p q) ·ᶜ γ ≡ p ·ᶜ (q ·ᶜ γ)
·ᶜ-assoc           p q  ε      = refl
·ᶜ-assoc {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_
  (·ᶜ-assoc p q γ)
  (Modality.·-Associative 𝕄 p q r)

-- Modality contex scaling is left distributive over addition
-- p ·ᶜ (γ +ᶜ δ) ≡ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)

·ᶜ-distribˡ-+ᶜ : (p : M) → (γ δ : Conₘ 𝕄 n) → p ·ᶜ (γ +ᶜ δ) ≡ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)
·ᶜ-distribˡ-+ᶜ          p  ε       ε      = refl
·ᶜ-distribˡ-+ᶜ {𝕄 = 𝕄} p (γ ∙ q) (δ ∙ r) = cong₂ _∙_
  (·ᶜ-distribˡ-+ᶜ p γ δ)
  (proj₁ (Modality.·Distr+ 𝕄) p q r)


-- Modality context scaling is right distributive over addition
-- (p + q) ·ᶜ γ ≡ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)

·ᶜ-distribʳ-+ᶜ : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._+_ 𝕄 p q) ·ᶜ γ ≡ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-+ᶜ          p q  ε      = refl
·ᶜ-distribʳ-+ᶜ {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_
  (·ᶜ-distribʳ-+ᶜ p q γ)
  (proj₂ (Modality.·Distr+ 𝕄) r p q)

-- Modality contex scaling is left distributive over meet
-- p ·ᶜ (γ ∧ᶜ δ) ≡ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)

·ᶜ-distribˡ-∧ᶜ : (p : M) → (γ δ : Conₘ 𝕄 n) → p ·ᶜ (γ ∧ᶜ δ) ≡ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)
·ᶜ-distribˡ-∧ᶜ          p  ε       ε      = refl
·ᶜ-distribˡ-∧ᶜ {𝕄 = 𝕄} p (γ ∙ q) (δ ∙ r) = cong₂ _∙_
  (·ᶜ-distribˡ-∧ᶜ p γ δ)
  (proj₁ (Modality.·Distr∧ 𝕄) p q r)

-- Modality context scaling is right distributive over meet
-- (p ∧ q) ·ᶜ γ ≡ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)

·ᶜ-distribʳ-∧ᶜ : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._∧_ 𝕄 p q) ·ᶜ γ ≡ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-∧ᶜ          p q  ε      = refl
·ᶜ-distribʳ-∧ᶜ {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_
  (·ᶜ-distribʳ-∧ᶜ p q γ)
  (proj₂ (Modality.·Distr∧ 𝕄) r p q)

----------------------
-- Properties of +ᶜ --
----------------------

-- 𝟘ᶜ is left unit for addition
-- 𝟘ᶜ +ᶜ γ ≡ γ

+ᶜ-identityˡ : (γ : Conₘ 𝕄 n) → 𝟘ᶜ +ᶜ γ ≡ γ
+ᶜ-identityˡ            ε      = refl
+ᶜ-identityˡ {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_
  (+ᶜ-identityˡ γ)
  (proj₁ (Modality.+-Identity 𝕄) p)

-- 𝟘ᶜ is right unit for addition
-- γ +ᶜ 𝟘ᶜ ≡ γ

+ᶜ-identityʳ : (γ : Conₘ 𝕄 n) → γ +ᶜ 𝟘ᶜ ≡ γ
+ᶜ-identityʳ            ε     = refl
+ᶜ-identityʳ {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_
  (+ᶜ-identityʳ γ)
  (proj₂ (Modality.+-Identity 𝕄) p)

-- Addition is associative
-- (γ +ᶜ δ) +ᶜ η ≡ γ +ᶜ (δ +ᶜ η)

+ᶜ-assoc : (γ δ η : Conₘ 𝕄 n) → (γ +ᶜ δ) +ᶜ η ≡ γ +ᶜ (δ +ᶜ η)
+ᶜ-assoc ε ε ε = refl
+ᶜ-assoc {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) (η ∙ r) = cong₂ _∙_
  (+ᶜ-assoc γ δ η)
  (Modality.+-Associative 𝕄 p q r)

-- Addition is commutative
-- γ +ᶜ δ ≡ δ +ᶜ γ

+ᶜ-comm : (γ δ : Conₘ 𝕄 n) → γ +ᶜ δ ≡ δ +ᶜ γ
+ᶜ-comm ε ε = refl
+ᶜ-comm {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = cong₂ _∙_
  (+ᶜ-comm γ δ)
  (Modality.+-Commutative 𝕄 p q)

-- The module of modality contexts is positive
-- If 𝟘ᶜ ≤ᶜ γ +ᶜ δ then 𝟘ᶜ ≤ᶜ γ and 𝟘ᶜ ≤ δ

+ᶜ-Positive : (γ δ : Conₘ 𝕄 n) → 𝟘ᶜ ≤ᶜ γ +ᶜ δ → 𝟘ᶜ ≤ᶜ γ × 𝟘ᶜ ≤ᶜ δ
+ᶜ-Positive ε ε eq = refl , refl
+ᶜ-Positive {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) eq =
  cong₂ _∙_ (proj₁ 0≤γ+δ) (proj₁ 0≤p+q) , cong₂ _∙_ (proj₂ 0≤γ+δ) (proj₂ 0≤p+q)
  where
  0≤γ+δ = +ᶜ-Positive γ δ (cong tailₘ eq)
  0≤p+q = Modality.+-Positive 𝕄 p q (cong headₘ eq)

----------------------
-- Properties of ∧ᶜ --
----------------------

-- Meet is idempotent
-- γ ∧ᶜ γ ≡ γ

∧ᶜ-Idempotent : (γ : Conₘ 𝕄 n) → γ ∧ᶜ γ ≡ γ
∧ᶜ-Idempotent ε = refl
∧ᶜ-Idempotent {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_
  (∧ᶜ-Idempotent γ)
  (Modality.∧-Idempotent 𝕄 p)

-- Meet is commutative
-- γ ∧ᶜ δ ≡ δ ∧ᶜ γ

∧ᶜ-comm : (γ δ : Conₘ 𝕄 n) → γ ∧ᶜ δ ≡ δ ∧ᶜ γ
∧ᶜ-comm ε ε = refl
∧ᶜ-comm {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = cong₂ _∙_
  (∧ᶜ-comm γ δ)
  (Modality.∧-Commutative 𝕄 p q)

-- Meet is associative
-- (γ ∧ᶜ δ) ∧ᶜ η ≡ γ ∧ᶜ (δ ∧ᶜ η)

∧ᶜ-assoc : (γ δ η : Conₘ 𝕄 n) → (γ ∧ᶜ δ) ∧ᶜ η ≡ γ ∧ᶜ (δ ∧ᶜ η)
∧ᶜ-assoc ε ε ε = refl
∧ᶜ-assoc {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) (η ∙ r) = cong₂ _∙_
 (∧ᶜ-assoc γ δ η)
 (Modality.∧-Associative 𝕄 p q r)

----------------------
-- Properties of ≤ᶜ --
----------------------

-- ≤ᶜ is reflexive
-- γ ≤ᶜ γ

≤ᶜ-reflexive : {γ : Conₘ 𝕄 n} → γ ≤ᶜ γ
≤ᶜ-reflexive {γ = ε} = refl
≤ᶜ-reflexive {𝕄 = 𝕄} {γ = γ ∙ p} = cong₂ _∙_ ≤ᶜ-reflexive (≤-reflexive {𝕄 = 𝕄})

-- ≤ᶜ is transitive
-- If γ ≤ᶜ δ and δ ≤ᶜ η then γ ≤ᶜ η

≤ᶜ-transitive : {γ δ η : Conₘ 𝕄 n} → γ ≤ᶜ δ → δ ≤ᶜ η → γ ≤ᶜ η
≤ᶜ-transitive {γ = ε} {ε} {ε} x y = refl
≤ᶜ-transitive {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} x y = cong₂ _∙_
  (≤ᶜ-transitive (cong tailₘ x) (cong tailₘ y))
  (≤-transitive {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))

-- ≤ᶜ is antisymmetric
-- If γ ≤ᶜ δ and δ ≤ᶜ γ then γ ≡ δ

≤ᶜ-antisymmetric : {γ δ : Conₘ 𝕄 n} → γ ≤ᶜ δ → δ ≤ᶜ γ → γ ≡ δ
≤ᶜ-antisymmetric {γ = ε} {ε} refl refl = refl
≤ᶜ-antisymmetric {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} x y = cong₂ _∙_
  (≤ᶜ-antisymmetric (cong tailₘ x) (cong tailₘ y))
  (≤-antisymmetric {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))

-----------------------------
-- Monotonicity properties --
-----------------------------

-- Addition on the left is monotone
-- If γ ≤ᶜ δ then γ +ᶜ η ≤ᶜ δ +ᶜ η

+ᶜ-monotoneˡ : {γ δ η : Conₘ 𝕄 n} → γ ≤ᶜ δ → γ +ᶜ η ≤ᶜ δ +ᶜ η
+ᶜ-monotoneˡ {γ = ε} {ε} {ε} refl = refl
+ᶜ-monotoneˡ {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} γ≤δ = cong₂ _∙_
  (+ᶜ-monotoneˡ (cong tailₘ γ≤δ))
  (+-monotoneˡ {𝕄 = 𝕄} (cong headₘ γ≤δ))

-- Addition on the right is monotone
-- If γ ≤ᶜ δ then η +ᶜ γ ≤ᶜ η +ᶜ δ

+ᶜ-monotoneʳ : {γ δ η : Conₘ 𝕄 n} → γ ≤ᶜ δ → η +ᶜ γ ≤ᶜ η +ᶜ δ
+ᶜ-monotoneʳ {γ = ε} {ε} {ε} refl = refl
+ᶜ-monotoneʳ {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} γ≤δ = cong₂ _∙_
  (+ᶜ-monotoneʳ (cong tailₘ γ≤δ))
  (+-monotoneʳ {𝕄 = 𝕄} (cong headₘ γ≤δ))

-- Addition is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ + δ ≤ᶜ γ′ +ᶜ δ′

+ᶜ-monotone : {γ γ′ δ δ′ : Conₘ 𝕄 n} → γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → γ +ᶜ δ ≤ᶜ γ′ +ᶜ δ′
+ᶜ-monotone {𝕄 = 𝕄} γ≤γ′ δ≤δ′ = ≤ᶜ-transitive (+ᶜ-monotoneˡ γ≤γ′) (+ᶜ-monotoneʳ δ≤δ′)

-- Multiplication on the left is monotone
-- If p ≤ q then p ·ᶜ γ ≤ᶜ q ·ᶜ γ

·ᶜ-monotoneˡ : {γ : Conₘ 𝕄 n} → (Modality._≤_ 𝕄 p q) → p ·ᶜ γ ≤ᶜ q ·ᶜ γ
·ᶜ-monotoneˡ           {γ = ε}     p≤q = refl
·ᶜ-monotoneˡ {𝕄 = 𝕄} {γ = γ ∙ r} p≤q = cong₂ _∙_
  (·ᶜ-monotoneˡ p≤q)
  (·-monotoneˡ {𝕄 = 𝕄} p≤q)

-- Multiplication on the right is monotone
-- If γ ≤ᶜ δ then p ·ᶜ γ ≤ᶜ p ·ᶜ δ

·ᶜ-monotoneʳ : {p : M} {γ δ : Conₘ 𝕄 n} → γ ≤ᶜ δ → p ·ᶜ γ ≤ᶜ p ·ᶜ δ
·ᶜ-monotoneʳ {γ = ε} {ε} refl = refl
·ᶜ-monotoneʳ {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} x = cong₂ _∙_
  (·ᶜ-monotoneʳ (cong tailₘ x))
  (·-monotoneʳ {𝕄 = 𝕄} (cong headₘ x))

-- Multiplication is monotone
-- If γ ≤ᶜ δ and p ≤ q then p ·ᶜ γ ≤ᶜ q ·ᶜ δ

·ᶜ-monotone : {p q : M} {γ δ : Conₘ 𝕄 n} → γ ≤ᶜ δ → Modality._≤_ 𝕄 p q → p ·ᶜ γ ≤ᶜ q ·ᶜ δ
·ᶜ-monotone {γ = ε} {ε} γ≤δ p≤q = refl
·ᶜ-monotone {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} γ≤δ p≤q = cong₂ _∙_
  (·ᶜ-monotone (cong tailₘ γ≤δ) p≤q)
  (·-monotone {𝕄 = 𝕄} p≤q (cong headₘ γ≤δ))

-- Meet on the left is monotone
-- If γ ≤ᶜ δ then γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η

∧ᶜ-monotoneˡ : {γ δ η : Conₘ 𝕄 n} → γ ≤ᶜ δ → γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η
∧ᶜ-monotoneˡ {γ = ε} {ε} {ε} refl = refl
∧ᶜ-monotoneˡ {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} γ≤δ = cong₂ _∙_
  (∧ᶜ-monotoneˡ (cong tailₘ γ≤δ))
  (∧-monotoneˡ {𝕄 = 𝕄} (cong headₘ γ≤δ))

-- Meet on the right is monotone
-- If γ ≤ᶜ δ then γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η

∧ᶜ-monotoneʳ : {γ δ η : Conₘ 𝕄 n} → γ ≤ᶜ δ → η ∧ᶜ γ ≤ᶜ η ∧ᶜ δ
∧ᶜ-monotoneʳ {γ = ε} {ε} {ε} refl = refl
∧ᶜ-monotoneʳ {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} γ≤δ = cong₂ _∙_
  (∧ᶜ-monotoneʳ (cong tailₘ γ≤δ))
  (∧-monotoneʳ {𝕄 = 𝕄} (cong headₘ γ≤δ))

-- Meet is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ ∧ᶜ δ ≤ᶜ γ′ ∧ᶜ δ′

∧ᶜ-monotone : {γ γ′ δ δ′ : Conₘ 𝕄 n} → γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → (γ ∧ᶜ δ) ≤ᶜ (γ′ ∧ᶜ δ′)
∧ᶜ-monotone γ≤γ′ δ≤δ′ = ≤ᶜ-transitive (∧ᶜ-monotoneˡ γ≤γ′) (∧ᶜ-monotoneʳ δ≤δ′)

-- Meet on the left is a decreasing function
-- γ ∧ᶜ δ ≤ᶜ γ

∧ᶜ-decreasingˡ : (γ δ : Conₘ 𝕄 n) → γ ∧ᶜ δ ≤ᶜ γ
∧ᶜ-decreasingˡ γ δ = begin
          γ ∧ᶜ δ          ≡⟨ cong₂ _∧ᶜ_ (sym (∧ᶜ-Idempotent _)) refl ⟩
          (γ ∧ᶜ γ) ∧ᶜ δ   ≡⟨ ∧ᶜ-assoc _ _ _ ⟩
          γ ∧ᶜ γ ∧ᶜ δ     ≡⟨ ∧ᶜ-comm _ _ ⟩
          (γ ∧ᶜ δ) ∧ᶜ γ   ∎

-- Meet on the right is a decreasing function
-- γ ∧ᶜ δ ≤ᶜ δ

∧ᶜ-decreasingʳ : (γ δ : Conₘ 𝕄 n) → γ ∧ᶜ δ ≤ᶜ δ
∧ᶜ-decreasingʳ γ δ = begin
          γ ∧ᶜ δ          ≡⟨ cong₂ _∧ᶜ_ refl (sym (∧ᶜ-Idempotent _)) ⟩
          γ ∧ᶜ (δ ∧ᶜ δ)   ≡⟨ sym (∧ᶜ-assoc _ _ _) ⟩
          (γ ∧ᶜ δ) ∧ᶜ δ   ∎

----------------------------------
-- Propeties of headₘ and tailₘ --
----------------------------------

-- tailₘ distributes over meet
-- tailₘ (γ ∧ᶜ δ) ≡ tailₘ γ ∧ᶜ tailₘ δ

tail-distrib-∧ : {γ δ : Conₘ 𝕄 (1+ n)} → tailₘ (γ ∧ᶜ δ) ≡ (tailₘ γ) ∧ᶜ (tailₘ δ)
tail-distrib-∧ {γ = γ ∙ p} {δ ∙ q} = refl

-- headₘ distributes over meet
-- headₘ (γ ∧ᶜ δ) ≡ headₘ γ ∧ headₘ δ

head-distrib-∧ : {γ δ : Conₘ 𝕄 (1+ n)} → headₘ (γ ∧ᶜ δ)
             ≡ Modality._∧_ 𝕄 (headₘ γ) (headₘ δ)
head-distrib-∧ {γ = γ ∙ p} {δ ∙ q} = refl

-- The headₘ and tailₘ functions correctly give the head and tail of the context
-- tailₘ γ ∙ headₘ γ ≡ γ

headₘ-tailₘ-correct : (γ : Conₘ 𝕄 (1+ n)) → tailₘ γ ∙ headₘ γ ≡ γ
headₘ-tailₘ-correct (γ ∙ p) = refl

----------------------------------------------
-- Properties of context updates and lookup --
----------------------------------------------

-- Inserting a zero into a zero-context gives a zero-context
-- insertAt x 𝟘ᶜ 𝟘 ≡ 𝟘ᶜ

insertAt-𝟘 : {m : Nat} (n : Nat)
           → insertAt n (𝟘ᶜ {n = n + m}) (Modality.𝟘 𝕄) ≡ 𝟘ᶜ {𝕄 = 𝕄} {n = n + 1+ m}
insertAt-𝟘 0      = refl
insertAt-𝟘 (1+ n) = cong₂ _∙_ (insertAt-𝟘 n) refl

-- Inserting the sum of two elements distributes over addition
-- insertAt n (γ +ᶜ δ) (p + q) ≡ insertAt n γ p +ᶜ insertAt n δ q

insertAt-distrib-+ᶜ : {𝕄 : Modality M} {m : Nat} (n : Nat) (γ δ : Conₘ 𝕄 (n + m)) (p q : M)
                    →  insertAt n (γ +ᶜ δ) (Modality._+_ 𝕄 p q) ≡ insertAt n γ p +ᶜ insertAt n δ q
insertAt-distrib-+ᶜ 0      γ δ p q = refl
insertAt-distrib-+ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q = cong₂ _∙_ (insertAt-distrib-+ᶜ n γ δ p q) refl

-- Inserting a zero into a modality context distributes over addition
-- insertAt n (γ +ᶜ δ) 𝟘 ≡ insertAt n γ 𝟘 +ᶜ insertAt n δ 𝟘

insertAt-distrib-+ᶜ-𝟘 : {𝕄 : Modality M} {m : Nat} (n : Nat) (γ δ : Conₘ 𝕄 (n + m))
                      → insertAt n (γ +ᶜ δ) (Modality.𝟘 𝕄)
                      ≡ insertAt n γ (Modality.𝟘 𝕄) +ᶜ insertAt n δ (Modality.𝟘 𝕄)
insertAt-distrib-+ᶜ-𝟘 {𝕄 = 𝕄} n γ δ = begin
   insertAt n (γ +ᶜ δ) (Modality.𝟘 𝕄)
     ≡⟨ cong (insertAt n (γ +ᶜ δ)) (sym (proj₁ (Modality.+-Identity 𝕄) (Modality.𝟘 𝕄))) ⟩
   insertAt n (γ +ᶜ δ) ((𝕄 Modality.+ Modality.𝟘 𝕄) (Modality.𝟘 𝕄))
     ≡⟨ insertAt-distrib-+ᶜ n γ δ (Modality.𝟘 𝕄) (Modality.𝟘 𝕄) ⟩
   insertAt n γ (Modality.𝟘 𝕄) +ᶜ insertAt n δ (Modality.𝟘 𝕄) ∎

-- Inserting the product of two elements distributes over context scaling
-- insertAt n (p ·ᶜ γ) (p · q) ≡ p ·ᶜ insertAt n γ q

insertAt-distrib-·ᶜ : {𝕄 : Modality M} {m : Nat} (n : Nat) (γ δ : Conₘ 𝕄 (n + m)) (p q : M)
                    → insertAt n (p ·ᶜ γ) (Modality._·_ 𝕄 p q) ≡ p ·ᶜ insertAt n γ q
insertAt-distrib-·ᶜ 0 γ δ p q = refl
insertAt-distrib-·ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q = cong₂ _∙_
  (insertAt-distrib-·ᶜ n γ δ p q) refl

-- Inserting the meet of two elements distributes over meet
-- insertAt n (γ ∧ᶜ δ) (p ∧ q) ≡ insertAt n γ p ∧ᶜ insertAt n δ q

insertAt-distrib-∧ᶜ : {𝕄 : Modality M} (n : Nat) (γ δ : Conₘ 𝕄 (n + m)) (p q : M)
                    → insertAt n (γ ∧ᶜ δ) (Modality._∧_ 𝕄 p q) ≡ insertAt n γ p ∧ᶜ insertAt n δ q
insertAt-distrib-∧ᶜ 0 γ δ p q = refl
insertAt-distrib-∧ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q = cong₂ _∙_
  (insertAt-distrib-∧ᶜ n γ δ p q) refl

-- Inserting a zero into a modality context distributes over meet
-- insertAt n (γ ∧ᶜ δ) 𝟘 ≡ insertAt n γ 𝟘 ∧ᶜ insertAt n δ 𝟘

insertAt-distrib-∧ᶜ-𝟘 : (n : Nat) (γ δ : Conₘ 𝕄 (n + m))
                      → insertAt n (γ ∧ᶜ δ) (Modality.𝟘 𝕄)
                      ≡ insertAt n γ (Modality.𝟘 𝕄) ∧ᶜ insertAt n δ (Modality.𝟘 𝕄)
insertAt-distrib-∧ᶜ-𝟘 {𝕄 = 𝕄} n γ δ = begin
  insertAt n (γ ∧ᶜ δ) (Modality.𝟘 𝕄)
    ≡⟨ cong (insertAt n (γ ∧ᶜ δ)) (sym (Modality.∧-Idempotent 𝕄 (Modality.𝟘 𝕄))) ⟩
  insertAt n (γ ∧ᶜ δ) ((𝕄 Modality.∧ Modality.𝟘 𝕄) (Modality.𝟘 𝕄))
    ≡⟨ insertAt-distrib-∧ᶜ n γ δ (Modality.𝟘 𝕄) (Modality.𝟘 𝕄) ⟩
  insertAt n γ (Modality.𝟘 𝕄) ∧ᶜ insertAt n δ (Modality.𝟘 𝕄) ∎

-- Inserting an element into a modality context is a monotone function
-- If γ ≤ᶜ δ and p ≤ q, then insertAt n γ p ≤ᶜ insertAt n δ q

insertAt-monotone : {𝕄 : Modality M} {m : Nat} (n : Nat) (γ δ : Conₘ 𝕄 (n + m)) (p q : M)
                  → γ ≤ᶜ δ → Modality._≤_ 𝕄 p q → insertAt n γ p ≤ᶜ insertAt n δ q
insertAt-monotone Nat.zero γ δ p q γ≤δ p≤q = cong₂ _∙_ γ≤δ p≤q
insertAt-monotone (1+ n) (γ ∙ p′) (δ ∙ q′) p q γ≤δ p≤q = cong₂ _∙_ (insertAt-monotone n γ δ p q (cong tailₘ γ≤δ) p≤q) (cong headₘ γ≤δ)

-- Lemma on insertions and lifted variable weakenings
-- 𝟘ᶜ , x[⇑ⁿ(↑id)] ≔ 𝟙 ≡ insertAt n (𝟘ᶜ , x ≔ 𝟙) 𝟘

insertAt-liftn : {m : Nat} (n : Nat) (x : Fin (n + m))
              → (𝟘ᶜ {𝕄 = 𝕄} , wkVar (liftn (step id) n) x ≔ Modality.𝟙 𝕄) ≡
                insertAt n (𝟘ᶜ , x ≔ Modality.𝟙 𝕄) (Modality.𝟘 𝕄)
insertAt-liftn 0 x = refl
insertAt-liftn (1+ n) x0 = cong₂ _∙_ (PE.sym (insertAt-𝟘 n)) refl
insertAt-liftn (1+ n) (_+1 x) = cong₂ _∙_ (insertAt-liftn n x) refl

-- Every lookup in a zero-context is zero
-- 𝟘ᶜ ⟨ x ⟩ ≡ 𝟘

𝟘ᶜ-lookup : {𝕄 : Modality M} (x : Fin n) → 𝟘ᶜ {𝕄 = 𝕄} ⟨ x ⟩ ≡ Modality.𝟘 𝕄
𝟘ᶜ-lookup x0     = refl
𝟘ᶜ-lookup (x +1) = 𝟘ᶜ-lookup x

-- Lookup is consistent with context updates
-- (γ , x ≔ p) ⟨ x ⟩ ≡ p

update-lookup : (x : Fin n) → (γ , x ≔ p) ⟨ x ⟩ ≡ p
update-lookup {γ = γ ∙ p} x0 = refl
update-lookup {γ = γ ∙ p} (_+1 x) = update-lookup {γ = γ} x

-- Updating a context with its own content has no effect
-- (γ , x ≔ (γ ⟨ x ⟩)) ≡ γ

update-self : (γ : Conₘ 𝕄 n) (x : Fin n) → (γ , x ≔ (γ ⟨ x ⟩)) ≡ γ
update-self (γ ∙ p) x0 = refl
update-self (γ ∙ p) (x +1) = cong₂ _∙_ (update-self γ x) refl

-- Context update is a monotone function with regards to the context
-- If γ ≤ᶜ δ then (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)

update-monotoneˡ : {𝕄 : Modality M} {γ δ : Conₘ 𝕄 n} {p : M}
                  (x : Fin n) → γ ≤ᶜ δ → (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)
update-monotoneˡ {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} x0 γ≤δ =
  cong₂ _∙_ (cong tailₘ γ≤δ) (≤-reflexive {𝕄 = 𝕄})
update-monotoneˡ {γ = γ ∙ p} {δ ∙ q} (_+1 x) γ≤δ =
  cong₂ _∙_ (update-monotoneˡ x (cong tailₘ γ≤δ)) (cong headₘ γ≤δ)

-- Context update is monotone with regards to the inserted element
-- If p ≤ q then( γ , x ≔ p) ≤ᶜ (γ , x ≔ q)

update-monotoneʳ : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {p q : M}
                     → (x : Fin n) → Modality._≤_ 𝕄 p q
                     → γ , x ≔ p ≤ᶜ γ , x ≔ q
update-monotoneʳ {γ = γ ∙ p} x0 p≤q = cong₂ _∙_ ≤ᶜ-reflexive p≤q
update-monotoneʳ {𝕄 = 𝕄} {γ = γ ∙ p} (x +1) p≤q =
  cong₂ _∙_ (update-monotoneʳ x p≤q) (≤-reflexive {𝕄 = 𝕄})

-- Context lookup is a monotone function
-- If γ ≤ᶜ δ then γ⟨x⟩ ≤ δ⟨x⟩

lookup-monotone : {𝕄 : Modality M} {γ δ : Conₘ 𝕄 n}
                → (x : Fin n) → γ ≤ᶜ δ → Modality._≤_ 𝕄 (γ ⟨ x ⟩) (δ ⟨ x ⟩)
lookup-monotone {γ = γ ∙ p} {δ ∙ q} x0 γ≤δ = cong headₘ γ≤δ
lookup-monotone {γ = γ ∙ p} {δ ∙ q} (x +1) γ≤δ =
  lookup-monotone x (cong tailₘ γ≤δ)

-- Context update distributes over addition
-- (γ +ᶜ δ) , x ≔ (p + q) ≡ (γ , x ≔ p) +ᶜ (δ , x ≔ q)

update-distrib-+ᶜ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (p q : M) (x : Fin n)
                  → (γ +ᶜ δ) , x ≔ (Modality._+_ 𝕄 p q) ≡ (γ , x ≔ p) +ᶜ (δ , x ≔ q)
update-distrib-+ᶜ (γ ∙ p′) (δ ∙ q′) p q x0 = refl
update-distrib-+ᶜ (γ ∙ p′) (δ ∙ q′) p q (x +1) =
  cong₂ _∙_ (update-distrib-+ᶜ γ δ p q x) refl

-- Context update distributes over multiplication
-- (p ·ᶜ γ) , x ≔ (p · q) ≡ p ·ᶜ (γ , x ≔ q)

update-distrib-·ᶜ : {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (p q : M) (x : Fin n)
                  → (p ·ᶜ γ) , x ≔ (Modality._·_ 𝕄 p q) ≡ p ·ᶜ (γ , x ≔ q)
update-distrib-·ᶜ (γ ∙ r) p q x0 = refl
update-distrib-·ᶜ (γ ∙ r) p q (x +1) =
  cong₂ _∙_ (update-distrib-·ᶜ γ p q x) refl

-- Context update distributes over meet
-- (γ ∧ᶜ δ) , x ≔ (p ∧ q) ≡ (γ , x ≔ p) ∧ᶜ (δ , x ≔ q)

update-distrib-∧ᶜ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (p q : M) (x : Fin n)
                  → (γ ∧ᶜ δ) , x ≔ (Modality._∧_ 𝕄 p q) ≡ (γ , x ≔ p) ∧ᶜ (δ , x ≔ q)
update-distrib-∧ᶜ (γ ∙ p′) (δ ∙ q′) p q x0 = refl
update-distrib-∧ᶜ (γ ∙ p′) (δ ∙ q′) p q (x +1) =
  cong₂ _∙_ (update-distrib-∧ᶜ γ δ p q x) refl

-- Context update distributes over nrᶜ
-- nrᶜ γ δ r , x ≔ nr p q r ≡  nrᶜ (γ , x ≔ p) (δ , x ≔ q) r

update-distrib-nrᶜ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (r p q : M) (x : Fin n)
                   → nrᶜ γ δ r , x ≔ (Modality.nr 𝕄 p q r) ≡ nrᶜ (γ , x ≔ p) (δ , x ≔ q) r
update-distrib-nrᶜ (γ ∙ _) (δ ∙ _) r p q x0 = refl
update-distrib-nrᶜ (γ ∙ _) (δ ∙ _) r p q (x +1) =
  cong₂ _∙_ (update-distrib-nrᶜ γ δ r p q x) refl

-- Context lookup distributes over addition
-- (γ +ᶜ δ)⟨x⟩ ≡ γ⟨x⟩ + δ⟨x⟩

lookup-distrib-+ᶜ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (x : Fin n)
                  → (γ +ᶜ δ) ⟨ x ⟩ ≡ Modality._+_ 𝕄 (γ ⟨ x ⟩) (δ ⟨ x ⟩)
lookup-distrib-+ᶜ (γ ∙ p) (δ ∙ q) x0     = refl
lookup-distrib-+ᶜ (γ ∙ p) (δ ∙ q) (x +1) = lookup-distrib-+ᶜ γ δ x

-- Context lookup distributes over multiplication
-- (p ·ᶜ γ)⟨x⟩ ≡ p · γ⟨x⟩

lookup-distrib-·ᶜ : {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (p : M) (x : Fin n)
                  → (p ·ᶜ γ) ⟨ x ⟩ ≡ Modality._·_ 𝕄 p (γ ⟨ x ⟩)
lookup-distrib-·ᶜ (γ ∙ q) p x0 = refl
lookup-distrib-·ᶜ (γ ∙ q) p (x +1) = lookup-distrib-·ᶜ γ p x

-- Context lookup distributes over meet
-- (γ ∧ᶜ δ)⟨x⟩ ≡ γ⟨x⟩ ∧ δ⟨x⟩

lookup-distrib-∧ᶜ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (x : Fin n)
                  → (γ ∧ᶜ δ) ⟨ x ⟩ ≡ Modality._∧_ 𝕄 (γ ⟨ x ⟩) (δ ⟨ x ⟩)
lookup-distrib-∧ᶜ (γ ∙ p) (δ ∙ q) x0     = refl
lookup-distrib-∧ᶜ (γ ∙ p) (δ ∙ q) (x +1) = lookup-distrib-∧ᶜ γ δ x

-- Context lookup distributes over nrᶜ
-- (nrᶜ γ δ r)⟨x⟩ ≡ nr γ⟨x⟩ δ⟨x⟩ r

lookup-distrib-nrᶜ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (r : M) (x : Fin n)
                   → (nrᶜ γ δ r) ⟨ x ⟩ ≡ Modality.nr 𝕄 (γ ⟨ x ⟩) (δ ⟨ x ⟩) r
lookup-distrib-nrᶜ (γ ∙ p) (δ ∙ q) r x0     = refl
lookup-distrib-nrᶜ (γ ∙ p) (δ ∙ q) r (x +1) = lookup-distrib-nrᶜ γ δ r x

-- Updating the head of a context leaves the tail untouched
-- γ , x0 ≔ p ≡ tailₘ γ ∙ p

update-head : {𝕄 : Modality M} (γ : Conₘ 𝕄 (1+ n)) (p : M)
            → γ , x0 ≔ p ≡ tailₘ γ ∙ p
update-head (γ ∙ q) p = refl

-- Updating the tail of a context leaves the head untouched
-- γ , (x +1) ≔ p ≡ (tailₘ γ , x ≔ p) ∙ headₘ γ

update-step : {𝕄 : Modality M} (γ : Conₘ 𝕄 (1+ n)) (p : M) (x : Fin n)
            → γ , (x +1) ≔ p ≡ (tailₘ γ , x ≔ p) ∙ headₘ γ
update-step (γ ∙ q) p x = refl


nr-thm : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (r : M) →
         nrᶜ γ δ r ≡ γ ∧ᶜ (δ +ᶜ r ·ᶜ nrᶜ γ δ r)
nr-thm ε ε r = refl
nr-thm {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) r = cong₂ _∙_ (nr-thm γ δ r) (Modality.nr-rec 𝕄 p q r)
