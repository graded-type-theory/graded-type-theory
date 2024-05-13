------------------------------------------------------------------------
-- Equality lemmata.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Equality
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n             : Nat
    Γ             : Con Term n
    A B F G t u v : Term _
    b             : BinderMode
    p q           : M
    l             : TypeLevel
    s             : Strength

U≡A′ : ∀ {A l} ([U] : Γ ⊩⟨ l ⟩U)
    → Γ ⊩⟨ l ⟩ U ≡ A / (U-intr [U])
    → A PE.≡ U
U≡A′ (noemb [U]) A≡U = A≡U
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

Unit≡A′ : ∀ {A l} ([Unit] : Γ ⊩⟨ l ⟩Unit⟨ s ⟩ Unit s)
    → Γ ⊩⟨ l ⟩ Unit! ≡ A / (Unit-intr [Unit])
    → Whnf A
    → A PE.≡ Unit s
Unit≡A′ (noemb x) [Unit≡A] whnfA = whnfRed* [Unit≡A] whnfA
Unit≡A′ (emb 0<1 [Unit]) [Unit≡A] whnfA = Unit≡A′ [Unit] [Unit≡A] whnfA

Unit≡A : ∀ {A}
    → Γ ⊢ Unit s ≡ A
    → Whnf A
    → A PE.≡ Unit s
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
    → ∃₂ λ H E → A PE.≡ ⟦ W ⟧ H ▹ E
B≡A′ W (noemb [W]) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) whnfA =
  F′ , G′ , whnfRed* D′ whnfA
B≡A′ W (emb 0<1 [W]) [W≡A] whnfA = B≡A′ W [W] [W≡A] whnfA

Π≡A′ : ∀ {Γ : Con Term n} {A F G l p q} → _
Π≡A′ {Γ = Γ} {A} {F} {G} {l} {p} {q} = B≡A′ {Γ = Γ} {A} {F} {G} {l} (BΠ p q)
Σ≡A′ : ∀ {Γ : Con Term n} {A F G l p q m} → _
Σ≡A′ {Γ = Γ} {A} {F} {G} {l} {p} {q} {m} =
  B≡A′ {Γ = Γ} {A} {F} {G} {l} (BΣ m p q)

-- If A is judgmentally equal to Π F ▹ G, then there exists H and E such that
-- A is propositionally equal to  Π H ▹ E.
B≡A : ∀ {A F G} W
    → Γ ⊢ ⟦ W ⟧ F ▹ G ≡ A
    → Whnf A
    → ∃₂ λ H E → A PE.≡ ⟦ W ⟧ H ▹ E
B≡A {A} W W≡A whnfA with reducibleEq W≡A
B≡A {A} W W≡A whnfA | [W] , [A] , [W≡A] =
  B≡A′ W (B-elim W [W]) (irrelevanceEq [W] (B-intr W (B-elim W [W])) [W≡A]) whnfA

Π≡A : ∀ {Γ : Con Term n} {A F G p q} → Γ ⊢ ⟦ BΠ p q ⟧ F ▹ G ≡ A
    → Whnf A → ∃₂ λ H E → A PE.≡ ⟦ BΠ p q ⟧ H ▹ E
Π≡A {Γ = Γ} {A} {F} {G} {p} {q} x y with B≡A {Γ = Γ} {A} {F} {G} (BΠ p q) x y
... | H , E , A≡ΠHE = H , E , A≡ΠHE

Σ≡A : ∀ {Γ : Con Term n} {A F G p q m} → Γ ⊢ ⟦ BΣ m p q ⟧ F ▹ G ≡ A
    → Whnf A → ∃₂ λ H E → A PE.≡ ⟦ BΣ m p q ⟧ H ▹ E
Σ≡A {p = p} {q} {m} x y with B≡A (BΣ m p q) x y
Σ≡A _ _ | H , E , A≡ΣHE   = H , E , A≡ΣHE

-- If a WHNF A is definitionally equal to ΠΣ⟨ b ⟩ p , q ▷ F ▹ G, then
-- A has the shape ΠΣ⟨ b ⟩ p , q ▷ _ ▹ _.

ΠΣ≡Whnf :
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡ A → Whnf A →
  ∃₂ λ H E → A PE.≡ ΠΣ⟨ b ⟩ p , q ▷ H ▹ E
ΠΣ≡Whnf {b = BMΠ}   = Π≡A
ΠΣ≡Whnf {b = BMΣ _} = Σ≡A

opaque

  -- If the WHNF B is judgmentally equal to Id A t u, then there are
  -- A′, t′ and u′ such that B is propositionally equal to
  -- Id A′ t′ u′.

  Id≡Whnf :
    Γ ⊢ Id A t u ≡ B → Whnf B →
    ∃₃ λ A′ t′ u′ → B PE.≡ Id A′ t′ u′
  Id≡Whnf {Γ} {A} {t} {u} {B} Id≡B B-whnf =
    case reducibleEq Id≡B of λ {
      (⊩Id , ⊩B , ⊩Id≡B) →
      helper (Id-elim ⊩Id)
        (irrelevanceEq ⊩Id (Id-intr (Id-elim ⊩Id)) ⊩Id≡B) }
    where
    helper :
      (⊩Id : Γ ⊩⟨ l ⟩Id Id A t u) →
      Γ ⊩⟨ l ⟩ Id A t u ≡ B / Id-intr ⊩Id →
      ∃₃ λ A′ t′ u′ → B PE.≡ Id A′ t′ u′
    helper (emb 0<1 ⊩Id) ⊩Id≡B = helper ⊩Id ⊩Id≡B
    helper (noemb ⊩Id)   ⊩Id≡B =
      _ , _ , _ , whnfRed* (red (_⊩ₗId_≡_/_.⇒*Id′ ⊩Id≡B)) B-whnf

opaque

  -- If t is definitionally equal to rfl, then t reduces to rfl.

  rfl-norm : Γ ⊢ t ≡ rfl ∷ A → Γ ⊢ t ⇒* rfl ∷ A
  rfl-norm {Γ} {t} t≡rfl =
    case inversion-rfl (syntacticEqTerm t≡rfl .proj₂ .proj₂) of λ {
      (_ , _ , _ , _ , A≡Id) →
    case reducibleEqTerm (conv t≡rfl A≡Id) of λ {
      (⊩Id , ⊩t≡rfl) →
    conv*
      (helper (Id-elim ⊩Id)
         (irrelevanceEqTerm ⊩Id (Id-intr (Id-elim ⊩Id)) ⊩t≡rfl))
      (sym A≡Id) }}
    where
    helper :
      (⊩Id : Γ ⊩⟨ l ⟩Id Id B u v) →
      Γ ⊩⟨ l ⟩ t ≡ rfl ∷ Id B u v / Id-intr ⊩Id →
      Γ ⊢ t ⇒* rfl ∷ Id B u v
    helper (emb 0<1 ⊩Id) ⊩t≡rfl =
      helper ⊩Id ⊩t≡rfl
    helper {B} {u} {v} (noemb ⊩Id) ⊩t≡rfl@(t′ , _ , t⇒*t′ , _) =
      case PE.subst (_⊢_⇒*_∷_ _ _ _)
             (PE.sym $ whnfRed* (red (_⊩ₗId_.⇒*Id ⊩Id)) Idₙ)
             (redₜ t⇒*t′) of λ {
        t⇒*t′ →
      case ⊩Id≡∷-view-inhabited ⊩Id ⊩t≡rfl of λ where
        (rfl₌ _)       → t⇒*t′
        (ne t′-ne _ _) →           $⟨ t⇒*t′ ⟩
          Γ ⊢ t ⇒* t′ ∷ Id B u v   →⟨ subset*Term ⟩
          Γ ⊢ t ≡ t′ ∷ Id B u v    →⟨ trans (sym (escapeTermEq (Idᵣ ⊩Id) ⊩t≡rfl)) ⟩
          Γ ⊢ rfl ≡ t′ ∷ Id B u v  →⟨ I.rfl≢ne t′-ne ⟩
          ⊥                        →⟨ ⊥-elim ⟩
          Γ ⊢ t ⇒* rfl ∷ Id B u v  □ }

opaque

  -- If the WHNF t is judgmentally equal to rfl, then t is
  -- propositionally equal to rfl.

  whnf≡rfl : Γ ⊢ t ≡ rfl ∷ A → Whnf t → t PE.≡ rfl
  whnf≡rfl = whnfRed*Term ∘→ rfl-norm
