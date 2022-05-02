{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Typed.Consequences.Equality {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.EqRelInstance M′
open import Definition.Typed.Consequences.Inequality M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.ShapeView M′
open import Definition.LogicalRelation.Fundamental.Reducibility M′

open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

U≡A′ : ∀ {A l} ([U] : Γ ⊩⟨ l ⟩U)
    → Γ ⊩⟨ l ⟩ U ≡ A / (U-intr [U])
    → A PE.≡ U
U≡A′ (noemb [U]) (lift A≡U) = A≡U
U≡A′ (emb 0<1 [U]) [U≡A] = U≡A′ [U] [U≡A]

-- If A is judgmentally equal to U, then A is propositionally equal to U.
U≡A : ∀ {A}
    → Γ ⊢ U ≡ A
    → A PE.≡ U
U≡A {A} U≡A with reducibleEq U≡A
U≡A {A} U≡A | [U] , [A] , [U≡A] =
  U≡A′ (U-elim [U]) (irrelevanceEq [U] (U-intr (U-elim [U])) [U≡A])

ℕ≡A′ : ∀ {A l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
    → Γ ⊩⟨ l ⟩ ℕ ≡ A / (ℕ-intr [ℕ])
    → Whnf A
    → A PE.≡ ℕ
ℕ≡A′ (noemb x) [ℕ≡A] whnfA = whnfRed* [ℕ≡A] whnfA
ℕ≡A′ (emb 0<1 [ℕ]) [ℕ≡A] whnfA = ℕ≡A′ [ℕ] [ℕ≡A] whnfA

-- If A in WHNF is judgmentally equal to ℕ, then A is propositionally equal to ℕ.
ℕ≡A : ∀ {A}
    → Γ ⊢ ℕ ≡ A
    → Whnf A
    → A PE.≡ ℕ
ℕ≡A {A} ℕ≡A whnfA with reducibleEq ℕ≡A
ℕ≡A {A} ℕ≡A whnfA | [ℕ] , [A] , [ℕ≡A] =
  ℕ≡A′ (ℕ-elim [ℕ]) (irrelevanceEq [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [ℕ≡A]) whnfA

-- If A in WHNF is judgmentally equal to Empty, then A is propositionally equal to Empty.
Empty≡A′ : ∀ {A l} ([Empty] : Γ ⊩⟨ l ⟩Empty Empty)
    → Γ ⊩⟨ l ⟩ Empty ≡ A / (Empty-intr [Empty])
    → Whnf A
    → A PE.≡ Empty
Empty≡A′ (noemb x) [Empty≡A] whnfA = whnfRed* [Empty≡A] whnfA
Empty≡A′ (emb 0<1 [Empty]) [Empty≡A] whnfA = Empty≡A′ [Empty] [Empty≡A] whnfA

Empty≡A : ∀ {A}
    → Γ ⊢ Empty ≡ A
    → Whnf A
    → A PE.≡ Empty
Empty≡A {A} Empty≡A whnfA with reducibleEq Empty≡A
Empty≡A {A} Empty≡A whnfA | [Empty] , [A] , [Empty≡A] =
  Empty≡A′ (Empty-elim [Empty]) (irrelevanceEq [Empty] (Empty-intr (Empty-elim [Empty])) [Empty≡A]) whnfA

Unit≡A′ : ∀ {A l} ([Unit] : Γ ⊩⟨ l ⟩Unit Unit)
    → Γ ⊩⟨ l ⟩ Unit ≡ A / (Unit-intr [Unit])
    → Whnf A
    → A PE.≡ Unit
Unit≡A′ (noemb x) [Unit≡A] whnfA = whnfRed* [Unit≡A] whnfA
Unit≡A′ (emb 0<1 [Unit]) [Unit≡A] whnfA = Unit≡A′ [Unit] [Unit≡A] whnfA

Unit≡A : ∀ {A}
    → Γ ⊢ Unit ≡ A
    → Whnf A
    → A PE.≡ Unit
Unit≡A {A} Unit≡A whnfA with reducibleEq Unit≡A
Unit≡A {A} Unit≡A whnfA | [Unit] , [A] , [Unit≡A] =
  Unit≡A′ (Unit-elim [Unit]) (irrelevanceEq [Unit] (Unit-intr (Unit-elim [Unit])) [Unit≡A]) whnfA

ne≡A′ : ∀ {A K l}
     → ([K] : Γ ⊩⟨ l ⟩ne K)
     → Γ ⊩⟨ l ⟩ K ≡ A / (ne-intr [K])
     → Whnf A
     → ∃ λ M → Neutral M × A PE.≡ M
ne≡A′ (noemb [K]) (ne₌ M D′ neM K≡M) whnfA =
  M , neM , (whnfRed* (red D′) whnfA)
ne≡A′ (emb 0<1 [K]) [K≡A] whnfA = ne≡A′ [K] [K≡A] whnfA

-- If A in WHNF is judgmentally equal to K, then there exists a M such that
-- A is propositionally equal to M.
ne≡A : ∀ {A K}
    → Neutral K
    → Γ ⊢ K ≡ A
    → Whnf A
    → ∃ λ M → Neutral M × A PE.≡ M
ne≡A {A} neK ne≡A whnfA with reducibleEq ne≡A
ne≡A {A} neK ne≡A whnfA | [ne] , [A] , [ne≡A] =
  ne≡A′ (ne-elim neK [ne])
        (irrelevanceEq [ne] (ne-intr (ne-elim neK [ne])) [ne≡A]) whnfA

B≡A′ : ∀ {A F G l} W ([W] : Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G)
    → Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G ≡ A / (B-intr W [W])
    → Whnf A
    → ∃₃ λ W′ H E → A PE.≡ ⟦ W′ ⟧ H ▹ E
B≡A′ W (noemb [W]) (B₌ F′ G′ W′ D′ W≋W′ A≡B [F≡F′] [G≡G′]) whnfA =
  W′ , F′ , G′ , whnfRed* D′ whnfA
B≡A′ W (emb 0<1 [W]) [W≡A] whnfA = B≡A′ W [W] [W≡A] whnfA

Π≡A′ : ∀ {Γ : Con Term n} {A F G l p q} → _
Π≡A′ {Γ = Γ} {A} {F} {G} {l} {p} {q} = B≡A′ {Γ = Γ} {A} {F} {G} {l} (BΠ p q)
Σ≡A′ : ∀ {Γ : Con Term n} {A F G l q m} → _
Σ≡A′ {Γ = Γ} {A} {F} {G} {l} {q} {m} = B≡A′ {Γ = Γ} {A} {F} {G} {l} (BΣ q m)

-- If A is judgmentally equal to Π F ▹ G, then there exists H and E such that
-- A is propositionally equal to  Π H ▹ E.
B≡A : ∀ {A F G} W
    → Γ ⊢ ⟦ W ⟧ F ▹ G ≡ A
    → Whnf A
    → ∃₃ λ W′ H E → A PE.≡ ⟦ W′ ⟧ H ▹ E
B≡A {A} W W≡A whnfA with reducibleEq W≡A
B≡A {A} W W≡A whnfA | [W] , [A] , [W≡A] =
  B≡A′ W (B-elim W [W]) (irrelevanceEq [W] (B-intr W (B-elim W [W])) [W≡A]) whnfA

Π≡A : ∀ {Γ : Con Term n} {A F G p q} → Γ ⊢ ⟦ BΠ p q ⟧ F ▹ G ≡ A
    → Whnf A → ∃₄ λ p′ q′ H E → A PE.≡ ⟦ BΠ p′ q′ ⟧ H ▹ E
Π≡A {Γ = Γ} {A} {F} {G} {p} {q} x y with B≡A {Γ = Γ} {A} {F} {G} (BΠ p q) x y
... | BΠ p₁ q₁ , H , E , A≡ΠHE = p₁ , q₁ , H , E , A≡ΠHE
... | BΣ q₁ m , H , E , PE.refl = PE.⊥-elim (Π≢Σ x)
Σ≡A : ∀ {Γ : Con Term n} {A F G q m} → Γ ⊢ ⟦ BΣ q m ⟧ F ▹ G ≡ A
    → Whnf A → ∃₃ λ q′ H E → A PE.≡ ⟦ BΣ q′ m ⟧ H ▹ E
Σ≡A {Γ = Γ} {A} {F} {G} {q} {m} x y with B≡A {Γ = Γ} {A} {F} {G} (BΣ q m) x y
Σ≡A {Γ = Γ} {A} {F} {G} {q} {m} x y | BΠ p q₁ , H , E , PE.refl = PE.⊥-elim (Π≢Σ (sym x))
Σ≡A {Γ = Γ} {A} {F} {G} {q} {Σₚ} x y | BΣ q₁ Σₚ , H , E , A≡ΣHE = q₁ , H , E , A≡ΣHE
Σ≡A {Γ = Γ} {A} {F} {G} {q} {Σₚ} x y | BΣ q₁ Σᵣ , H , E , PE.refl = PE.⊥-elim (Σₚ≢Σᵣ x)
Σ≡A {Γ = Γ} {A} {F} {G} {q} {Σᵣ} x y | BΣ q₁ Σₚ , H , E , PE.refl = PE.⊥-elim (Σₚ≢Σᵣ (sym x))
Σ≡A {Γ = Γ} {A} {F} {G} {q} {Σᵣ} x y | BΣ q₁ Σᵣ , H , E , A≡ΣHE = q₁ , H , E , A≡ΣHE
