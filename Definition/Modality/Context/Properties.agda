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
·ᶜ-identityˡ : (γ : Conₘ 𝕄 n) → (Modality.𝟙 𝕄) ·ᶜ γ ≡ γ
·ᶜ-identityˡ       ε      = refl
·ᶜ-identityˡ {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ γ' p'
  where
  γ' = ·ᶜ-identityˡ γ
  p' = (proj₁ (Modality.·-Identity 𝕄)) p


-- 𝟘 is a left zero to modality context scaling
·ᶜ-zeroˡ : (γ : Conₘ 𝕄 n) → (Modality.𝟘 𝕄) ·ᶜ γ ≡ 𝟘ᶜ
·ᶜ-zeroˡ            ε     = refl
·ᶜ-zeroˡ {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ IH z
  where
  IH = ·ᶜ-zeroˡ γ
  z  = proj₁ (Modality.·-Zero 𝕄) p


-- A zero context is a right zero to modality context scaling
·ᶜ-zeroʳ : {𝕄 : Modality M} → (p : M) → p ·ᶜ 𝟘ᶜ ≡ 𝟘ᶜ {𝕄 = 𝕄} {n = n}
·ᶜ-zeroʳ {n = 0}    p = refl
·ᶜ-zeroʳ {n = 1+ n} {𝕄 = 𝕄} p = cong₂ _∙_ IH z
  where
  IH = ·ᶜ-zeroʳ p
  z  = proj₂ (Modality.·-Zero 𝕄) p

-- Modality context scaling is associative
·ᶜ-assoc : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._·_ 𝕄 p q) ·ᶜ γ ≡ p ·ᶜ (q ·ᶜ γ)
·ᶜ-assoc          p q  ε      = refl
·ᶜ-assoc {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ γ' r'
  where
  γ' = ·ᶜ-assoc p q γ
  r' = Modality.·-Associative 𝕄 p q r

-- Modality contex scaling is left distributive over addition
·ᶜ-distribˡ-+ᶜ : (p : M) → (γ δ : Conₘ 𝕄 n) → p ·ᶜ (γ +ᶜ δ) ≡ (p ·ᶜ γ) +ᶜ (p ·ᶜ δ)
·ᶜ-distribˡ-+ᶜ          p  ε       ε      = refl
·ᶜ-distribˡ-+ᶜ {𝕄 = 𝕄} p (γ ∙ q) (δ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = ·ᶜ-distribˡ-+ᶜ p γ δ
  distr = proj₁ (Modality.·Distr+ 𝕄) p q r

-- Modality context scaling is right distributive over addition
·ᶜ-distribʳ-+ᶜ : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._+_ 𝕄 p q) ·ᶜ γ ≡ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-+ᶜ          p q  ε      = refl
·ᶜ-distribʳ-+ᶜ {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = ·ᶜ-distribʳ-+ᶜ p q γ
  distr = proj₂ (Modality.·Distr+ 𝕄) r p q

-- Modality contex scaling is left distributive over meet
·ᶜ-distribˡ-∧ᶜ : (p : M) → (γ δ : Conₘ 𝕄 n) → p ·ᶜ (γ ∧ᶜ δ) ≡ (p ·ᶜ γ) ∧ᶜ (p ·ᶜ δ)
·ᶜ-distribˡ-∧ᶜ          p  ε       ε      = refl
·ᶜ-distribˡ-∧ᶜ {𝕄 = 𝕄} p (γ ∙ q) (δ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = ·ᶜ-distribˡ-∧ᶜ p γ δ
  distr = proj₁ (Modality.·Distr∧ 𝕄) p q r

-- Modality context scaling is right distributive over meet
·ᶜ-distribʳ-∧ᶜ : (p q : M) → (γ : Conₘ 𝕄 n) → (Modality._∧_ 𝕄 p q) ·ᶜ γ ≡ (p ·ᶜ γ) ∧ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-∧ᶜ          p q  ε      = refl
·ᶜ-distribʳ-∧ᶜ {𝕄 = 𝕄} p q (γ ∙ r) = cong₂ _∙_ IH distr
  where
  IH    = ·ᶜ-distribʳ-∧ᶜ p q γ
  distr = proj₂ (Modality.·Distr∧ 𝕄) r p q


-- Properties of +ᶜ

-- 𝟘ᶜ is left unit for addition
+ᶜ-identityˡ : (γ : Conₘ 𝕄 n) → 𝟘ᶜ +ᶜ γ ≡ γ
+ᶜ-identityˡ            ε      = refl
+ᶜ-identityˡ {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ γ' p'
  where
  γ' = +ᶜ-identityˡ γ
  p' = proj₁ (Modality.+-Identity 𝕄) p

-- 𝟘ᶜ is right unit for addition
+ᶜ-identityʳ : (γ : Conₘ 𝕄 n) → γ +ᶜ 𝟘ᶜ ≡ γ
+ᶜ-identityʳ            ε     = refl
+ᶜ-identityʳ {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_ γ' p'
  where
  γ' = +ᶜ-identityʳ γ
  p' = proj₂ (Modality.+-Identity 𝕄) p

+ᶜ-assoc : (γ δ η : Conₘ 𝕄 n) → (γ +ᶜ δ) +ᶜ η ≡ γ +ᶜ (δ +ᶜ η)
+ᶜ-assoc ε ε ε = refl
+ᶜ-assoc {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) (η ∙ r) = cong₂ _∙_
  (+ᶜ-assoc γ δ η)
  (Modality.+-Associative 𝕄 p q r)

+ᶜ-comm : (γ δ : Conₘ 𝕄 n) → γ +ᶜ δ ≡ δ +ᶜ γ
+ᶜ-comm ε ε = refl
+ᶜ-comm {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = cong₂ _∙_
  (+ᶜ-comm γ δ)
  (Modality.+-Commutative 𝕄 p q)

+ᶜ-noInverse : (γ δ : Conₘ 𝕄 n) → γ +ᶜ δ ≡ 𝟘ᶜ → γ ≡ 𝟘ᶜ × δ ≡ 𝟘ᶜ
+ᶜ-noInverse ε ε eq = refl , refl
+ᶜ-noInverse {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) eq =
  cong₂ _∙_ (proj₁ γ+δ=0) (proj₁ p+q=0) , cong₂ _∙_ (proj₂ γ+δ=0) (proj₂ p+q=0)
  where
  γ+δ=0 = +ᶜ-noInverse γ δ (cong tailₘ eq)
  p+q=0 = Modality.+-noInverse 𝕄 p q (cong headₘ eq)

-- Properties of ∧ᶜ

∧ᶜ-Idempotent : (γ : Conₘ 𝕄 n) → γ ∧ᶜ γ ≡ γ
∧ᶜ-Idempotent ε = refl
∧ᶜ-Idempotent {𝕄 = 𝕄} (γ ∙ p) = cong₂ _∙_
  (∧ᶜ-Idempotent γ)
  (Modality.∧-Idempotent 𝕄 p)

-- Properties of ≤ᶜ

-- ≤ᶜ forms a parital order

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

-- +ᶜ, ∧ᶜ and ·ᶜ are monotone owht reggards to ≤ᶜ

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


∧ᶜ-monotone : {γ δ η : Conₘ 𝕄 n} → γ ≤ᶜ δ → γ ∧ᶜ η ≤ᶜ δ ∧ᶜ η
∧ᶜ-monotone {γ = ε} {ε} {ε} refl = refl
∧ᶜ-monotone {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} {η ∙ r} x = cong₂ _∙_
  (∧ᶜ-monotone (cong tailₘ x))
  (∧-monotone {𝕄 = 𝕄} (cong headₘ x))

∧ᶜ-monotone₂ : {γ γ′ δ δ′ : Conₘ 𝕄 n} → γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → (γ ∧ᶜ δ) ≤ᶜ (γ′ ∧ᶜ δ′)
∧ᶜ-monotone₂ {γ = ε} {ε} {ε} {ε} refl refl = refl
∧ᶜ-monotone₂ {𝕄 = 𝕄} {γ = γ ∙ p} {γ′ ∙ p′} {δ ∙ q} {δ′ ∙ q′} x y = cong₂ _∙_
  (∧ᶜ-monotone₂ (cong tailₘ x) (cong tailₘ y))
  (∧-monotone₂ {𝕄 = 𝕄} (cong headₘ x) (cong headₘ y))


-- Propeties of headₘ and tailₘ


tail-linear∧ : {γ δ : Conₘ 𝕄 (1+ n)} → tailₘ (γ ∧ᶜ δ) ≡ (tailₘ γ) ∧ᶜ (tailₘ δ)
tail-linear∧ {γ = γ ∙ p} {δ ∙ q} = refl

head-linear∧ : {γ δ : Conₘ 𝕄 (1+ n)} → headₘ (γ ∧ᶜ δ)
             ≡ Modality._∧_ 𝕄 (headₘ γ) (headₘ δ)
head-linear∧ {γ = γ ∙ p} {δ ∙ q} = refl

headₘ-tailₘ-correct : (γ : Conₘ 𝕄 (1+ n)) → γ ≡ tailₘ γ ∙ headₘ γ
headₘ-tailₘ-correct (γ ∙ p) = refl


-- Properties of context updates and lookup

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

𝟘ᶜ-lookup : {𝕄 : Modality M} (x : Fin n) → 𝟘ᶜ {𝕄 = 𝕄} ⟨ x ⟩ ≡ Modality.𝟘 𝕄
𝟘ᶜ-lookup x0     = refl
𝟘ᶜ-lookup (x +1) = 𝟘ᶜ-lookup x

update-lookup : (x : Fin n) → (γ , x ≔ p) ⟨ x ⟩ ≡ p
update-lookup {γ = γ ∙ p} x0 = refl
update-lookup {γ = γ ∙ p} (_+1 x) = update-lookup {γ = γ} x

update-self : (γ : Conₘ 𝕄 n) (x : Fin n) → (γ , x ≔ (γ ⟨ x ⟩)) ≡ γ
update-self (γ ∙ p) x0 = refl
update-self (γ ∙ p) (x +1) = cong₂ _∙_ (update-self γ x) refl

update-monotoneˡ : {𝕄 : Modality M} {γ δ : Conₘ 𝕄 n} {p : M}
                  (x : Fin n) → γ ≤ᶜ δ → (γ , x ≔ p) ≤ᶜ (δ , x ≔ p)
update-monotoneˡ {𝕄 = 𝕄} {γ = γ ∙ p} {δ ∙ q} x0 γ≤δ =
  cong₂ _∙_ (cong tailₘ γ≤δ) (≤-reflexive {𝕄 = 𝕄})
update-monotoneˡ {γ = γ ∙ p} {δ ∙ q} (_+1 x) γ≤δ =
  cong₂ _∙_ (update-monotoneˡ x (cong tailₘ γ≤δ)) (cong headₘ γ≤δ)

update-monotoneʳ : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {p q : M}
                     → (x : Fin n) → Modality._≤_ 𝕄 p q
                     → γ , x ≔ p ≤ᶜ γ , x ≔ q
update-monotoneʳ {γ = γ ∙ p} x0 p≤q = cong₂ _∙_ ≤ᶜ-reflexive p≤q
update-monotoneʳ {𝕄 = 𝕄} {γ = γ ∙ p} (x +1) p≤q =
  cong₂ _∙_ (update-monotoneʳ x p≤q) (≤-reflexive {𝕄 = 𝕄})

lookup-monotone : {𝕄 : Modality M} {γ δ : Conₘ 𝕄 n}
                → (x : Fin n) → γ ≤ᶜ δ → Modality._≤_ 𝕄 (γ ⟨ x ⟩) (δ ⟨ x ⟩)
lookup-monotone {γ = γ ∙ p} {δ ∙ q} x0 γ≤δ = cong headₘ γ≤δ
lookup-monotone {γ = γ ∙ p} {δ ∙ q} (x +1) γ≤δ =
  lookup-monotone x (cong tailₘ γ≤δ)

update-linear-+ᶜ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (p q : M) (x : Fin n)
                 → (γ , x ≔ p) +ᶜ (δ , x ≔ q) ≡ (γ +ᶜ δ) , x ≔ (Modality._+_ 𝕄 p q)
update-linear-+ᶜ (γ ∙ p′) (δ ∙ q′) p q x0 = refl
update-linear-+ᶜ (γ ∙ p′) (δ ∙ q′) p q (x +1) =
  cong₂ _∙_ (update-linear-+ᶜ γ δ p q x) refl

update-linear-·ᶜ : {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (p q : M) (x : Fin n)
                 → p ·ᶜ (γ , x ≔ q) ≡ (p ·ᶜ γ) , x ≔ (Modality._·_ 𝕄 p q)
update-linear-·ᶜ (γ ∙ r) p q x0 = refl
update-linear-·ᶜ (γ ∙ r) p q (x +1) =
  cong₂ _∙_ (update-linear-·ᶜ γ p q x) refl

lookup-linear-+ᶜ : {𝕄 : Modality M} (γ δ : Conₘ 𝕄 n) (x : Fin n)
                 → (γ +ᶜ δ) ⟨ x ⟩ ≡ Modality._+_ 𝕄 (γ ⟨ x ⟩) (δ ⟨ x ⟩)
lookup-linear-+ᶜ (γ ∙ p) (δ ∙ q) x0     = refl
lookup-linear-+ᶜ (γ ∙ p) (δ ∙ q) (x +1) = lookup-linear-+ᶜ γ δ x

lookup-linear-·ᶜ : {𝕄 : Modality M} (γ : Conₘ 𝕄 n) (p : M) (x : Fin n)
                 → (p ·ᶜ γ) ⟨ x ⟩ ≡ Modality._·_ 𝕄 p (γ ⟨ x ⟩)
lookup-linear-·ᶜ (γ ∙ q) p x0 = refl
lookup-linear-·ᶜ (γ ∙ q) p (x +1) = lookup-linear-·ᶜ γ p x
