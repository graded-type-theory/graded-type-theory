{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Context.Properties
  {M : Set} {_≈_ : Rel M _}
  (𝕄 : Modality M _≈_)
  where

open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Context {M} {_≈_} 𝕄
-- open import Definition.Untyped

open import Tools.Fin
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.Product
import Tools.PropositionalEquality as PE

open Modality 𝕄

private
  variable
    n : Nat
    p q : M
    γ γ′ δ δ′ η : Conₘ n

------------------------------------------
-- Modality contexts form a left module --
------------------------------------------

-- 𝟙 is a left identity to modality contex scaling
-- 𝟙 ·ᶜ γ ≈ᶜ γ

·ᶜ-identityˡ : (γ : Conₘ n) → 𝟙 ·ᶜ γ ≈ᶜ γ
·ᶜ-identityˡ  ε      = ε
·ᶜ-identityˡ (γ ∙ p) = (·ᶜ-identityˡ γ) ∙ (proj₁ ·-identity p)

-- 𝟘 is a left zero to modality context scaling
-- 𝟘 ·ᶜ γ ≈ᶜ 𝟘ᶜ

·ᶜ-zeroˡ : (γ : Conₘ n) → 𝟘 ·ᶜ γ ≈ᶜ 𝟘ᶜ
·ᶜ-zeroˡ  ε      = ε
·ᶜ-zeroˡ (γ ∙ p) = (·ᶜ-zeroˡ γ) ∙ (proj₁ ·-zero p)

-- A zero context is a right zero to modality context scaling
-- p ·ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ

·ᶜ-zeroʳ : {n : Nat} (p : M) → p ·ᶜ 𝟘ᶜ ≈ᶜ 𝟘ᶜ {n = n}
·ᶜ-zeroʳ {n = 0}    p = ε
·ᶜ-zeroʳ {n = 1+ n} p = (·ᶜ-zeroʳ p) ∙ (proj₂ ·-zero p)

-- Modality context scaling is associative
-- (p · q) ·ᶜ γ ≈ᶜ p ·ᶜ (q ·ᶜ γ)

·ᶜ-assoc : (p q : M) → (γ : Conₘ n) → (p · q) ·ᶜ γ ≈ᶜ p ·ᶜ (q ·ᶜ γ)
·ᶜ-assoc p q  ε      = ε
·ᶜ-assoc p q (γ ∙ r) = (·ᶜ-assoc p q γ) ∙ (·-assoc p q r)

-- Modality contex scaling is left distributive over addition
-- p ·ᶜ (γ +ᶜ δ) ≈ᶜ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)

·ᶜ-distribˡ-+ᶜ : (p : M) → (γ δ : Conₘ n) → (p ·ᶜ (γ +ᶜ δ)) ≈ᶜ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)
·ᶜ-distribˡ-+ᶜ p  ε       ε      = ε
·ᶜ-distribˡ-+ᶜ p (γ ∙ q) (δ ∙ r) = (·ᶜ-distribˡ-+ᶜ p γ δ) ∙ (proj₁ ·-distrib-+ p q r)


-- Modality context scaling is right distributive over addition
-- (p + q) ·ᶜ γ ≈ᶜ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)

·ᶜ-distribʳ-+ᶜ : (p q : M) → (γ : Conₘ n) → (p + q) ·ᶜ γ ≈ᶜ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-+ᶜ p q  ε      = ε
·ᶜ-distribʳ-+ᶜ p q (γ ∙ r) = (·ᶜ-distribʳ-+ᶜ p q γ) ∙ (proj₂ ·-distrib-+ r p q)

-- Modality contex scaling is left distributive over meet
-- p ·ᶜ (γ ∧ᶜ δ) ≈ᶜ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)

·ᶜ-distribˡ-∧ᶜ : (p : M) → (γ δ : Conₘ n) → p ·ᶜ (γ ∧ᶜ δ) ≈ᶜ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)
·ᶜ-distribˡ-∧ᶜ p  ε       ε      = ε
·ᶜ-distribˡ-∧ᶜ p (γ ∙ q) (δ ∙ r) = (·ᶜ-distribˡ-∧ᶜ p γ δ) ∙ (proj₁ ·-distrib-∧ p q r)

-- Modality context scaling is right distributive over meet
-- (p ∧ q) ·ᶜ γ ≈ᶜ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)

·ᶜ-distribʳ-∧ᶜ : (p q : M) → (γ : Conₘ n) → (p ∧ q) ·ᶜ γ ≈ᶜ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-∧ᶜ p q  ε      = ε
·ᶜ-distribʳ-∧ᶜ p q (γ ∙ r) = (·ᶜ-distribʳ-∧ᶜ p q γ) ∙ (proj₂ ·-distrib-∧ r p q)

----------------------
-- Properties of +ᶜ --
----------------------

-- 𝟘ᶜ is left unit for addition
-- 𝟘ᶜ +ᶜ γ ≈ᶜ γ

+ᶜ-identityˡ : (γ : Conₘ n) → 𝟘ᶜ +ᶜ γ ≈ᶜ γ
+ᶜ-identityˡ  ε      = ε
+ᶜ-identityˡ (γ ∙ p) = (+ᶜ-identityˡ γ) ∙ (proj₁ +-identity p)

-- 𝟘ᶜ is right unit for addition
-- γ +ᶜ 𝟘ᶜ ≈ᶜ γ

+ᶜ-identityʳ : (γ : Conₘ n) → γ +ᶜ 𝟘ᶜ ≈ᶜ γ
+ᶜ-identityʳ ε       = ε
+ᶜ-identityʳ (γ ∙ p) = (+ᶜ-identityʳ γ) ∙ (proj₂ +-identity p)

-- Addition is associative
-- (γ +ᶜ δ) +ᶜ η ≈ᶜ γ +ᶜ (δ +ᶜ η)

+ᶜ-assoc : (γ δ η : Conₘ n) → (γ +ᶜ δ) +ᶜ η ≈ᶜ γ +ᶜ (δ +ᶜ η)
+ᶜ-assoc ε ε ε = ε
+ᶜ-assoc (γ ∙ p) (δ ∙ q) (η ∙ r) = (+ᶜ-assoc γ δ η) ∙ (+-assoc p q r)

-- Addition is commutative
-- γ +ᶜ δ ≈ᶜ δ +ᶜ γ

+ᶜ-comm : (γ δ : Conₘ n) → γ +ᶜ δ ≈ᶜ δ +ᶜ γ
+ᶜ-comm ε ε = ε
+ᶜ-comm (γ ∙ p) (δ ∙ q) = (+ᶜ-comm γ δ) ∙ (+-comm p q)

-- The module of modality contexts is positive
-- If 𝟘ᶜ ≤ᶜ γ +ᶜ δ then 𝟘ᶜ ≤ᶜ γ and 𝟘ᶜ ≤ δ

+ᶜ-positive : (γ δ : Conₘ n) → 𝟘ᶜ ≤ᶜ γ +ᶜ δ → 𝟘ᶜ ≤ᶜ γ × 𝟘ᶜ ≤ᶜ δ
+ᶜ-positive ε ε ε = ε , ε
+ᶜ-positive  (γ ∙ p) (δ ∙ q) (0≤γ+δ ∙ 0≤p+q) =
  (proj₁ (+ᶜ-positive γ δ 0≤γ+δ) ∙ proj₁ (+-positive p q 0≤p+q)) ,
  (proj₂ (+ᶜ-positive γ δ 0≤γ+δ) ∙ proj₂ (+-positive p q 0≤p+q))

----------------------
-- Properties of ∧ᶜ --
----------------------

-- Meet is idempotent
-- γ ∧ᶜ γ ≈ᶜ γ

∧ᶜ-idem : (γ : Conₘ n) → γ ∧ᶜ γ ≈ᶜ γ
∧ᶜ-idem ε = ε
∧ᶜ-idem (γ ∙ p) = (∧ᶜ-idem γ) ∙ (∧-idem p)

-- Meet is commutative
-- γ ∧ᶜ δ ≈ᶜ δ ∧ᶜ γ

∧ᶜ-comm : (γ δ : Conₘ n) → γ ∧ᶜ δ ≈ᶜ δ ∧ᶜ γ
∧ᶜ-comm ε ε = ε
∧ᶜ-comm  (γ ∙ p) (δ ∙ q) = (∧ᶜ-comm γ δ) ∙ (∧-comm p q)

-- Meet is associative
-- (γ ∧ᶜ δ) ∧ᶜ η ≈ᶜ γ ∧ᶜ (δ ∧ᶜ η)

∧ᶜ-assoc : (γ δ η : Conₘ n) → (γ ∧ᶜ δ) ∧ᶜ η ≈ᶜ γ ∧ᶜ (δ ∧ᶜ η)
∧ᶜ-assoc ε ε ε = ε
∧ᶜ-assoc (γ ∙ p) (δ ∙ q) (η ∙ r) = (∧ᶜ-assoc γ δ η) ∙ (∧-assoc p q r)

----------------------
-- Properties of ≈ᶜ --
----------------------

-- ≈ᶜ is reflexive
-- γ ≈ᶜ γ

≈ᶜ-refl : {γ : Conₘ n} → γ ≈ᶜ γ
≈ᶜ-refl {γ = ε} = ε
≈ᶜ-refl {γ = γ ∙ p} = ≈ᶜ-refl ∙ ≈-refl

-- ≈ᶜ is transitive
-- If γ ≈ᶜ δ and δ ≈ᶜ η then γ ≈ᶜ η

≈ᶜ-trans : {γ δ η : Conₘ n} → γ ≈ᶜ δ → δ ≈ᶜ η → γ ≈ᶜ η
≈ᶜ-trans {γ = ε} {ε} {ε} _ _ = ε
≈ᶜ-trans {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≈δ ∙ p≈q) (δ≈η ∙ q≈r) =
  (≈ᶜ-trans γ≈δ δ≈η) ∙ (≈-trans p≈q q≈r)

-- ≈ᶜ is symmetric
-- If γ ≈ᶜ δ and δ ≈ᶜ γ then γ ≈ᶜ δ

≈ᶜ-sym : {γ δ : Conₘ n} → γ ≈ᶜ δ → δ ≈ᶜ γ
≈ᶜ-sym {γ = ε} {ε} a = ε
≈ᶜ-sym {γ = γ ∙ p} {δ ∙ q} (γ≈δ ∙ p≈q) = (≈ᶜ-sym γ≈δ) ∙ (≈-sym p≈q)

-- Congruence of +ᶜ
-- If γ ≈ᶜ γ′ and δ ≈ᶜ δ′ then γ +ᶜ δ ≈ᶜ γ′ +ᶜ δ′

≈ᶜ-cong-+ᶜ : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → γ +ᶜ δ ≈ᶜ γ′ +ᶜ δ′
≈ᶜ-cong-+ᶜ ε ε = ε
≈ᶜ-cong-+ᶜ (γ≈γ′ ∙ p≈p′) (δ≈δ′ ∙ q≈q′) =
  (≈ᶜ-cong-+ᶜ γ≈γ′ δ≈δ′) ∙ (≈-cong-+ p≈p′ q≈q′)

-- Congruence of ·ᶜ
-- If p ≈ q and γ ≈ᶜ δ then p ·ᶜ γ ≈ᶜ q ·ᶜ δ

≈ᶜ-cong-·ᶜ : p ≈ q → γ ≈ᶜ δ → p ·ᶜ γ ≈ᶜ q ·ᶜ δ
≈ᶜ-cong-·ᶜ p≈q ε = ε
≈ᶜ-cong-·ᶜ p≈q (γ≈δ ∙ p′≈q′) = (≈ᶜ-cong-·ᶜ p≈q γ≈δ) ∙ (≈-cong-· p≈q p′≈q′)

-- Congruence of ∧ᶜ
-- If γ ≈ᶜ γ′ and δ ≈ᶜ δ′ then γ ∧ᶜ δ ≈ᶜ γ′ ∧ᶜ δ′

≈ᶜ-cong-∧ᶜ : γ ≈ᶜ γ′ → δ ≈ᶜ δ′ → γ ∧ᶜ δ ≈ᶜ γ′ ∧ᶜ δ′
≈ᶜ-cong-∧ᶜ ε ε = ε
≈ᶜ-cong-∧ᶜ (γ≈γ′ ∙ p≈p′) (δ≈δ′ ∙ q≈q′) =
  (≈ᶜ-cong-∧ᶜ γ≈γ′ δ≈δ′) ∙ (≈-cong-∧ p≈p′ q≈q′)

----------------------
-- Properties of ≤ᶜ --
----------------------

-- ≤ᶜ is reflexive
-- γ ≤ᶜ γ

≤ᶜ-refl : {γ : Conₘ n} → γ ≤ᶜ γ
≤ᶜ-refl {γ = ε} = ε
≤ᶜ-refl {γ = γ ∙ p} = ≤ᶜ-refl ∙ ≤-refl

-- ≤ᶜ is transitive
-- If γ ≤ᶜ δ and δ ≤ᶜ η then γ ≤ᶜ η

≤ᶜ-trans : {γ δ η : Conₘ n} → γ ≤ᶜ δ → δ ≤ᶜ η → γ ≤ᶜ η
≤ᶜ-trans {γ = ε} {ε} {ε} _ _ = ε
≤ᶜ-trans {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) (δ≤η ∙ q≤r) =
  (≤ᶜ-trans γ≤δ δ≤η) ∙ (≤-trans p≤q q≤r)

-- ≤ᶜ is antisymmetric
-- If γ ≤ᶜ δ and δ ≤ᶜ γ then γ ≈ᶜ δ

≤ᶜ-antisym : {γ δ : Conₘ n} → γ ≤ᶜ δ → δ ≤ᶜ γ → γ ≈ᶜ δ
≤ᶜ-antisym {γ = ε} {ε} a b = ε
≤ᶜ-antisym {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) (δ≤γ ∙ q≤p) = ≤ᶜ-antisym γ≤δ δ≤γ ∙ ≤-antisym p≤q q≤p

-----------------------------
-- Monotonicity properties --
-----------------------------

-- Addition on the left is monotone
-- If γ ≤ᶜ δ then γ +ᶜ η ≤ᶜ δ +ᶜ η

+ᶜ-monotoneˡ : {γ δ η : Conₘ n} → γ ≤ᶜ δ → γ +ᶜ η ≤ᶜ δ +ᶜ η
+ᶜ-monotoneˡ {γ = ε} {ε} {ε} ε = ε
+ᶜ-monotoneˡ  {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) = (+ᶜ-monotoneˡ γ≤δ) ∙ (+-monotoneˡ p≤q)

-- Addition on the right is monotone
-- If γ ≤ᶜ δ then η +ᶜ γ ≤ᶜ η +ᶜ δ

+ᶜ-monotoneʳ : {γ δ η : Conₘ n} → γ ≤ᶜ δ → η +ᶜ γ ≤ᶜ η +ᶜ δ
+ᶜ-monotoneʳ {γ = ε} {ε} {ε} refl = refl
+ᶜ-monotoneʳ  {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) = (+ᶜ-monotoneʳ γ≤δ) ∙ (+-monotoneʳ p≤q)

-- Addition is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ + δ ≤ᶜ γ′ +ᶜ δ′

+ᶜ-monotone : {γ γ′ δ δ′ : Conₘ n} → γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → γ +ᶜ δ ≤ᶜ γ′ +ᶜ δ′
+ᶜ-monotone γ≤γ′ δ≤δ′ = ≤ᶜ-trans (+ᶜ-monotoneˡ γ≤γ′) (+ᶜ-monotoneʳ δ≤δ′)

-- Multiplication on the left is monotone
-- If p ≤ q then p ·ᶜ γ ≤ᶜ q ·ᶜ γ

·ᶜ-monotoneˡ : {γ : Conₘ n} → p ≤ q → p ·ᶜ γ ≤ᶜ q ·ᶜ γ
·ᶜ-monotoneˡ {γ = ε}     p≤q = ε
·ᶜ-monotoneˡ {γ = γ ∙ r} p≤q = (·ᶜ-monotoneˡ p≤q) ∙ (·-monotoneˡ p≤q)

-- Multiplication on the right is monotone
-- If γ ≤ᶜ δ then p ·ᶜ γ ≤ᶜ p ·ᶜ δ

·ᶜ-monotoneʳ : {p : M} {γ δ : Conₘ n} → γ ≤ᶜ δ → p ·ᶜ γ ≤ᶜ p ·ᶜ δ
·ᶜ-monotoneʳ {γ = ε} {ε} ε = ε
·ᶜ-monotoneʳ  {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) = (·ᶜ-monotoneʳ γ≤δ) ∙ (·-monotoneʳ p≤q)

-- Multiplication is monotone
-- If γ ≤ᶜ δ and p ≤ q then p ·ᶜ γ ≤ᶜ q ·ᶜ δ

·ᶜ-monotone : {p q : M} {γ δ : Conₘ n} → γ ≤ᶜ δ → p ≤ q → p ·ᶜ γ ≤ᶜ q ·ᶜ δ
·ᶜ-monotone {γ = ε} {ε} ε p≤q = ε
·ᶜ-monotone  {γ = γ ∙ p} {δ ∙ q} (γ≤δ ∙ p≤q) p′≤q′ = (·ᶜ-monotone γ≤δ p′≤q′) ∙ (·-monotone p′≤q′ p≤q)

-- Meet on the left is monotone
-- If γ ≤ᶜ δ then γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η

∧ᶜ-monotoneˡ : {γ δ η : Conₘ n} → γ ≤ᶜ δ → γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η
∧ᶜ-monotoneˡ {γ = ε} {ε} {ε} ε = ε
∧ᶜ-monotoneˡ  {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) = (∧ᶜ-monotoneˡ γ≤δ) ∙ (∧-monotoneˡ p≤q)

-- Meet on the right is monotone
-- If γ ≤ᶜ δ then γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η

∧ᶜ-monotoneʳ : {γ δ η : Conₘ n} → γ ≤ᶜ δ → η ∧ᶜ γ ≤ᶜ η ∧ᶜ δ
∧ᶜ-monotoneʳ {γ = ε} {ε} {ε} refl = refl
∧ᶜ-monotoneʳ  {γ = γ ∙ p} {δ ∙ q} {η ∙ r} (γ≤δ ∙ p≤q) =
  (∧ᶜ-monotoneʳ γ≤δ) ∙ (∧-monotoneʳ p≤q)

-- Meet is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ ∧ᶜ δ ≤ᶜ γ′ ∧ᶜ δ′

∧ᶜ-monotone : {γ γ′ δ δ′ : Conₘ n} → γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → (γ ∧ᶜ δ) ≤ᶜ (γ′ ∧ᶜ δ′)
∧ᶜ-monotone γ≤γ′ δ≤δ′ = ≤ᶜ-trans (∧ᶜ-monotoneˡ γ≤γ′) (∧ᶜ-monotoneʳ δ≤δ′)

-- Meet on the left is a decreasing function
-- γ ∧ᶜ δ ≤ᶜ γ

∧ᶜ-decreasingˡ : (γ δ : Conₘ n) → γ ∧ᶜ δ ≤ᶜ γ
∧ᶜ-decreasingˡ ε ε = ε
∧ᶜ-decreasingˡ (γ ∙ p) (δ ∙ q) = (∧ᶜ-decreasingˡ γ δ) ∙ (∧-decreasingˡ p q)

-- Meet on the right is a decreasing function
-- γ ∧ᶜ δ ≤ᶜ δ

∧ᶜ-decreasingʳ : (γ δ : Conₘ n) → γ ∧ᶜ δ ≤ᶜ δ
∧ᶜ-decreasingʳ ε ε = ε
∧ᶜ-decreasingʳ (γ ∙ p) (δ ∙ q) = (∧ᶜ-decreasingʳ γ δ) ∙ (∧-decreasingʳ p q)

----------------------------------
-- Propeties of headₘ and tailₘ --
----------------------------------

-- tailₘ distributes over meet
-- tailₘ (γ ∧ᶜ δ) ≈ᶜ tailₘ γ ∧ᶜ tailₘ δ

tail-distrib-∧ : (γ δ : Conₘ (1+ n)) → tailₘ (γ ∧ᶜ δ) ≈ᶜ (tailₘ γ) ∧ᶜ (tailₘ δ)
tail-distrib-∧ (ε ∙ p) (ε ∙ q) = ε
tail-distrib-∧ (γ ∙ p′ ∙ p) (δ ∙ q′ ∙ q) = (tail-distrib-∧ (γ ∙ p′) (δ ∙ q′)) ∙ ≈-refl

-- headₘ distributes over meet
-- headₘ (γ ∧ᶜ δ) ≈ᶜ headₘ γ ∧ headₘ δ

head-distrib-∧ : (γ δ : Conₘ (1+ n)) → headₘ (γ ∧ᶜ δ) ≈ (headₘ γ) ∧ (headₘ δ)
head-distrib-∧ (γ ∙ p) (δ ∙ q) = ≈-refl

-- The headₘ and tailₘ functions correctly give the head and tail of the context
-- tailₘ γ ∙ headₘ γ ≈ᶜ γ

headₘ-tailₘ-correct : (γ : Conₘ (1+ n)) → tailₘ γ ∙ headₘ γ ≈ᶜ γ
headₘ-tailₘ-correct (γ ∙ p) = ≈ᶜ-refl

----------------------------------------------
-- Properties of context updates and lookup --
----------------------------------------------

-- Congruence of insertAt
-- If γ ≈ᶜ δ and p ≈ q then insertAt n γ p ≈ᶜ insertAt n δ q

insertAt-cong : {m : Nat} {n : Nat} {γ δ : Conₘ (n +ⁿ m)} {p q : M}
              → γ ≈ᶜ δ → p ≈ q → insertAt n γ p ≈ᶜ insertAt n δ q
insertAt-cong {n = 0} γ≈δ p≈q = γ≈δ ∙ p≈q
insertAt-cong {n = 1+ n} (γ≈δ ∙ p′≈q′) p≈q = (insertAt-cong γ≈δ p≈q) ∙ p′≈q′

-- Inserting a zero into a zero-context gives a zero-context
-- insertAt x 𝟘ᶜ 𝟘 ≈ᶜ 𝟘ᶜ

insertAt-𝟘 : {m : Nat} (n : Nat)
           → insertAt n (𝟘ᶜ {n = n +ⁿ m}) 𝟘 ≈ᶜ 𝟘ᶜ {n = n +ⁿ 1+ m}
insertAt-𝟘 0      = ≈ᶜ-refl
insertAt-𝟘 (1+ n) = (insertAt-𝟘 n) ∙ ≈-refl

-- Inserting the sum of two elements distributes over addition
-- insertAt n (γ +ᶜ δ) (p + q) ≈ᶜ insertAt n γ p +ᶜ insertAt n δ q

insertAt-distrib-+ᶜ : {m : Nat} (n : Nat) (γ δ : Conₘ (n +ⁿ m)) (p q : M)
                    → insertAt n (γ +ᶜ δ) (p + q) ≈ᶜ insertAt n γ p +ᶜ insertAt n δ q
insertAt-distrib-+ᶜ 0      γ δ p q = ≈ᶜ-refl
insertAt-distrib-+ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q = (insertAt-distrib-+ᶜ n γ δ p q) ∙ ≈-refl

-- Inserting a zero into a modality context distributes over addition
-- insertAt n (γ +ᶜ δ) 𝟘 ≈ᶜ insertAt n γ 𝟘 +ᶜ insertAt n δ 𝟘

insertAt-distrib-+ᶜ-𝟘 : {m : Nat} (n : Nat) (γ δ : Conₘ (n +ⁿ m))
                      → insertAt n (γ +ᶜ δ) 𝟘 ≈ᶜ insertAt n γ 𝟘 +ᶜ insertAt n δ 𝟘
insertAt-distrib-+ᶜ-𝟘  n γ δ = begin
  insertAt n (γ +ᶜ δ) 𝟘            ∼⟨ insertAt-cong ≈ᶜ-refl (≈-sym (proj₁ +-identity 𝟘)) ⟩
  insertAt n (γ +ᶜ δ) (𝟘 + 𝟘)      ∼⟨ insertAt-distrib-+ᶜ n γ δ 𝟘 𝟘 ⟩
  insertAt n γ 𝟘 +ᶜ insertAt n δ 𝟘 ∎⟨ ≈ᶜ-refl ⟩
  where open import Tools.Reasoning _≈ᶜ_ ≈ᶜ-trans

-- Inserting the product of two elements distributes over context scaling
-- insertAt n (p ·ᶜ γ) (p · q) ≈ᶜ p ·ᶜ insertAt n γ q

insertAt-distrib-·ᶜ : {m : Nat} (n : Nat) (γ δ : Conₘ (n +ⁿ m)) (p q : M)
                    → insertAt n (p ·ᶜ γ) (p · q) ≈ᶜ p ·ᶜ insertAt n γ q
insertAt-distrib-·ᶜ 0 γ δ p q = ≈ᶜ-refl
insertAt-distrib-·ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q = (insertAt-distrib-·ᶜ n γ δ p q) ∙ ≈-refl

-- Inserting the meet of two elements distributes over meet
-- insertAt n (γ ∧ᶜ δ) (p ∧ q) ≈ᶜ insertAt n γ p ∧ᶜ insertAt n δ q

insertAt-distrib-∧ᶜ : {m : Nat} (n : Nat) (γ δ : Conₘ (n +ⁿ m)) (p q : M)
                    → insertAt n (γ ∧ᶜ δ) (p ∧ q) ≈ᶜ insertAt n γ p ∧ᶜ insertAt n δ q
insertAt-distrib-∧ᶜ 0 γ δ p q = ≈ᶜ-refl
insertAt-distrib-∧ᶜ (1+ n) (γ ∙ p′) (δ ∙ q′) p q = (insertAt-distrib-∧ᶜ n γ δ p q) ∙ ≈-refl

-- Inserting a zero into a modality context distributes over meet
-- insertAt n (γ ∧ᶜ δ) 𝟘 ≈ᶜ insertAt n γ 𝟘 ∧ᶜ insertAt n δ 𝟘

insertAt-distrib-∧ᶜ-𝟘 : {m : Nat} (n : Nat) (γ δ : Conₘ (n +ⁿ m))
                      → insertAt n (γ ∧ᶜ δ) 𝟘 ≈ᶜ insertAt n γ 𝟘 ∧ᶜ insertAt n δ 𝟘
insertAt-distrib-∧ᶜ-𝟘  n γ δ = begin
  insertAt n (γ ∧ᶜ δ) 𝟘            ∼⟨ insertAt-cong ≈ᶜ-refl (≈-sym (∧-idem 𝟘)) ⟩
  insertAt n (γ ∧ᶜ δ) (𝟘 ∧ 𝟘)      ∼⟨ insertAt-distrib-∧ᶜ n γ δ 𝟘 𝟘 ⟩
  insertAt n γ 𝟘 ∧ᶜ insertAt n δ 𝟘 ∎⟨ ≈ᶜ-refl ⟩
  where
  open import Tools.Reasoning _≈ᶜ_ ≈ᶜ-trans

-- Inserting an element into a modality context is a monotone function
-- If γ ≤ᶜ δ and p ≤ q, then insertAt n γ p ≤ᶜ insertAt n δ q

insertAt-monotone : {m : Nat} (n : Nat) (γ δ : Conₘ (n +ⁿ m)) (p q : M)
                  → γ ≤ᶜ δ → p ≤ q → insertAt n γ p ≤ᶜ insertAt n δ q
insertAt-monotone 0 γ δ p q γ≤δ p≤q = γ≤δ ∙ p≤q
insertAt-monotone (1+ n) (γ ∙ p′) (δ ∙ q′) p q (γ≤δ ∙ p′≤q′) p≤q =
  insertAt-monotone n γ δ p q γ≤δ p≤q ∙ p′≤q′

-- Lemma on insertions and lifted variable weakenings
-- 𝟘ᶜ , x[⇑ⁿ(↑id)] ≔ 𝟙 ≈ᶜ insertAt n (𝟘ᶜ , x ≔ 𝟙) 𝟘

-- insertAt-liftn : {m : Nat} (n : Nat) (x : Fin (n +ⁿ m))
--                → (𝟘ᶜ  , wkVar (liftn (step id) n) x ≔ 𝟙) ≈ᶜ
--                 insertAt n (𝟘ᶜ , x ≔ 𝟙) 𝟘
-- insertAt-liftn 0 x = ? --refl
-- insertAt-liftn (1+ n) x0 = ? --cong₂ _∙_ (PE.sym (insertAt-𝟘 n)) refl
-- insertAt-liftn (1+ n) (_+1 x) = ? --cong₂ _∙_ (insertAt-liftn n x) refl

-- Every lookup in a zero-context is zero
-- 𝟘ᶜ ⟨ x ⟩ ≈ 𝟘

𝟘ᶜ-lookup : (x : Fin n) → 𝟘ᶜ ⟨ x ⟩ ≈ 𝟘
𝟘ᶜ-lookup x0     = ≈-refl
𝟘ᶜ-lookup (x +1) = 𝟘ᶜ-lookup x

-- Lookup is consistent with context updates
-- (γ , x ≔ p) ⟨ x ⟩ ≈ p

update-lookup : (x : Fin n) → (γ , x ≔ p) ⟨ x ⟩ ≈ p
update-lookup {γ = γ ∙ p} x0 = ≈-refl
update-lookup {γ = γ ∙ p} (x +1) = update-lookup {γ = γ} x

-- Updating a context with its own content has no effect
-- (γ , x ≔ (γ ⟨ x ⟩)) ≈ᶜ γ

update-self : (γ : Conₘ n) (x : Fin n) → (γ , x ≔ (γ ⟨ x ⟩)) ≈ᶜ γ
update-self (γ ∙ p) x0 = ≈ᶜ-refl
update-self (γ ∙ p) (x +1) = (update-self γ x) ∙ ≈-refl

-- Context update is a monotone function with regards to the context
-- If γ ≤ᶜ δ then (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)

update-monotoneˡ :(x : Fin n) → γ ≤ᶜ δ → (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)
update-monotoneˡ {γ = γ ∙ p} {δ ∙ q} x0 (γ≤δ ∙ _) = γ≤δ ∙ ≤-refl
update-monotoneˡ {γ = γ ∙ p} {δ ∙ q} (_+1 x) (γ≤δ ∙ p≤q) = (update-monotoneˡ x γ≤δ) ∙ p≤q

-- Context update is monotone with regards to the inserted element
-- If p ≤ q then( γ , x ≔ p) ≤ᶜ (γ , x ≔ q)

update-monotoneʳ : (x : Fin n) → p ≤ q → (γ , x ≔ p) ≤ᶜ (γ , x ≔ q)
update-monotoneʳ {γ = γ ∙ p} x0 p≤q = ≤ᶜ-refl ∙ p≤q
update-monotoneʳ {γ = γ ∙ p} (x +1) p≤q = (update-monotoneʳ x p≤q) ∙ ≤-refl

-- Context lookup is a monotone function
-- If γ ≤ᶜ δ then γ⟨x⟩ ≤ δ⟨x⟩

lookup-monotone : (x : Fin n) → γ ≤ᶜ δ → (γ ⟨ x ⟩) ≤ (δ ⟨ x ⟩)
lookup-monotone {γ = γ ∙ p} {δ ∙ q} x0     (γ≤δ ∙ p≤q) = p≤q
lookup-monotone {γ = γ ∙ p} {δ ∙ q} (x +1) (γ≤δ ∙ p≤q) = lookup-monotone x γ≤δ

-- Context update distributes over addition
-- (γ +ᶜ δ) , x ≔ (p + q) ≈ᶜ (γ , x ≔ p) +ᶜ (δ , x ≔ q)

update-distrib-+ᶜ : (γ δ : Conₘ n) (p q : M) (x : Fin n)
                  → (γ +ᶜ δ) , x ≔ (p + q) ≈ᶜ (γ , x ≔ p) +ᶜ (δ , x ≔ q)
update-distrib-+ᶜ (γ ∙ p′) (δ ∙ q′) p q x0     = ≈ᶜ-refl
update-distrib-+ᶜ (γ ∙ p′) (δ ∙ q′) p q (x +1) = (update-distrib-+ᶜ γ δ p q x) ∙ ≈-refl

-- Context update distributes over multiplication
-- (p ·ᶜ γ) , x ≔ (p · q) ≈ᶜ p ·ᶜ (γ , x ≔ q)

update-distrib-·ᶜ : (γ : Conₘ n) (p q : M) (x : Fin n)
                  → (p ·ᶜ γ) , x ≔ (p · q) ≈ᶜ p ·ᶜ (γ , x ≔ q)
update-distrib-·ᶜ (γ ∙ r) p q x0     = ≈ᶜ-refl
update-distrib-·ᶜ (γ ∙ r) p q (x +1) = (update-distrib-·ᶜ γ p q x) ∙ ≈-refl

-- Context lookup distributes over addition
-- (γ +ᶜ δ)⟨x⟩ ≈ᶜ γ⟨x⟩ + δ⟨x⟩

lookup-distrib-+ᶜ : (γ δ : Conₘ n) (x : Fin n) → (γ +ᶜ δ) ⟨ x ⟩ ≈ γ ⟨ x ⟩ + δ ⟨ x ⟩
lookup-distrib-+ᶜ (γ ∙ p) (δ ∙ q) x0     = ≈-refl
lookup-distrib-+ᶜ (γ ∙ p) (δ ∙ q) (x +1) = lookup-distrib-+ᶜ γ δ x

-- Context lookup distributes over multiplication
-- (p ·ᶜ γ)⟨x⟩ ≈ᶜ p · γ⟨x⟩

lookup-distrib-·ᶜ : (γ : Conₘ n) (p : M) (x : Fin n) → (p ·ᶜ γ) ⟨ x ⟩ ≈ p · γ ⟨ x ⟩
lookup-distrib-·ᶜ (γ ∙ q) p x0     = ≈-refl
lookup-distrib-·ᶜ (γ ∙ q) p (x +1) = lookup-distrib-·ᶜ γ p x

-- Updating the head of a context leaves the tail untouched
-- γ , x0 ≔ p ≈ᶜ tailₘ γ ∙ p

update-head : (γ : Conₘ (1+ n)) (p : M) → γ , x0 ≔ p ≈ᶜ tailₘ γ ∙ p
update-head (γ ∙ q) p = ≈ᶜ-refl

-- Updating the tail of a context leaves the head untouched
-- γ , (x +1) ≔ p ≈ᶜ (tailₘ γ , x ≔ p) ∙ headₘ γ

update-step : (γ : Conₘ (1+ n)) (p : M) (x : Fin n)
            → γ , (x +1) ≔ p ≈ᶜ (tailₘ γ , x ≔ p) ∙ headₘ γ
update-step (γ ∙ q) p x = ≈ᶜ-refl
