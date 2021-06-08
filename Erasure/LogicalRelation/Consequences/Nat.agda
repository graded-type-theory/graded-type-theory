{-# OPTIONS --without-K  #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Consequences.Nat {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure hiding (_∷_)
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
open import Definition.LogicalRelation Erasure

open import Erasure.LogicalRelation
open import Erasure.Extraction
import Erasure.Target as T

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

private
  variable
    n : Nat
    t t′ : Term n
    v : T.Term n

sucᵏ : (k : Nat) → Term n
sucᵏ 0      = zero
sucᵏ (1+ k) = suc (sucᵏ k)

sucᵏₙ : {k : Nat} → Whnf (sucᵏ k)
sucᵏₙ {0}    = zeroₙ
sucᵏₙ {1+ k} = sucₙ

sucᵏ′ : (k : Nat) → T.Term n
sucᵏ′ 0      = T.zero
sucᵏ′ (1+ k) = T.suc (sucᵏ′ k)

suc-injective : suc t ≡ suc t′ → t ≡ t′
suc-injective refl = refl

zeroCase : {n : Nat} → zero ≡ sucᵏ n → n ≡ 0
zeroCase {0} _ = refl

sucCase : {n : Nat} → suc t′ ≡ sucᵏ n → ∃ λ m → n ≡ (1+ m)
sucCase {n = 0} ()
sucCase {n = 1+ n} eq = n , refl

-- invℕ : t ® v ∷ℕ

-- lem : ε ⊢ t ⇒* sucᵏ (1+ n) ∷ ℕ → ε ⊢ suc t

thm : t ® v ∷ℕ → ε ⊢ t ⇒* sucᵏ n ∷ ℕ → v T.⇒* sucᵏ′ n
thm (zeroᵣ x x₁) t⇒t′ with whrDet*Term (x , zeroₙ) (t⇒t′ , sucᵏₙ)
... | Z rewrite zeroCase Z = x₁
thm (sucᵣ x x₁ t®v) t⇒t′ with whrDet*Term (x , sucₙ) (t⇒t′ , sucᵏₙ)
... | X with sucCase X
... | m , refl with thm t®v {!!}
... | Q = {!!}

thm2 : t ® erase t ∷ℕ → ε ⊢ t ⇒* sucᵏ n ∷ ℕ → erase t T.⇒* sucᵏ′ n
thm2 (zeroᵣ x x₁) t⇒t′ rewrite zeroCase (whrDet*Term (x , zeroₙ) (t⇒t′ , sucᵏₙ)) = x₁
thm2 (sucᵣ x x₁ t®v) t⇒t′ =
  let IH = thm2 {!!} {!!}
  in  {!!}

thm3 : sucᵏ (1+ n) ® sucᵏ′ (1+ n) ∷ℕ → sucᵏ n ® sucᵏ′ n ∷ℕ
thm3 (zeroᵣ x x₁) = {!!}
thm3 {Nat.zero} (sucᵣ x x₁ x₂) = zeroᵣ (id (zeroⱼ ε)) T.refl
thm3 {1+ n} (sucᵣ x x₁ x₂) = {!!}

thm4 : t ® v ∷ℕ → ε ⊢ t ⇒* sucᵏ n ∷ ℕ → v T.⇒* sucᵏ′ n
thm4 (zeroᵣ x₁ x₂) (id x) = {!!}
thm4 (sucᵣ x₁ x₂ t®v) (id x) = {!!}
thm4 t®v (x ⇨ t⇒t′) = {!!}

escape : ∀ {l A} → ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
       → ∃ λ w → erase t T.⇒* w × v T.⇒* w
escape (Uᵣ x) (Uᵣ x₁ x₂) = T.undefined , ({!!} , x₂)
escape (ℕᵣ x) (zeroᵣ x₁ x₂) = T.zero , ({!t in WHNF!} , x₂)
escape (ℕᵣ x) (sucᵣ x₁ x₂ t®v) = (T.suc v′) , ({!escape _ t®v!} , x₂)
escape (Unitᵣ x) t®v = {!!}
escape (ne x) t®v = {!!}
escape (Bᵣ W x) t®v = {!!}
escape (emb l< [A]) t®v = {!!}
