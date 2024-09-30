------------------------------------------------------------------------
-- Inequality lemmata.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Inequality
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant as U
  using (Neutral; No-η-equality; Whnf)
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.Typed.Consequences.Syntactic R

open import Tools.Function
open import Tools.Nat as Nat using (Nat)
open import Tools.Product
open import Tools.Relation
open import Tools.Empty
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    n : Nat
    Γ : Con Term n
    A B C D F G H t u v : Term n
    p p′ q q′ : M
    b : BinderMode
    b′ : BindingType
    m : Strength
    s : Strength
    l l′ : Universe-level

opaque
  unfolding _⊩⟨_⟩_≡_

  A≢B :
    (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Con Term n → Universe-level → Term n → Set a)
    (A-intr : ∀ {l} → Γ ⊩′⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A)
    (B-intr : ∀ {l} → Γ ⊩′⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B) →
    (∀ {l} → Γ ⊩⟨ l ⟩ A → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩A A) →
    (∀ {l} → Γ ⊩⟨ l ⟩ B → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩B B) →
    (∀ {l₁ l₂} (⊩A : Γ ⊩′⟨ l₁ ⟩A A) (⊩B : Γ ⊩′⟨ l₂ ⟩B B) →
     ¬ ShapeView Γ l₁ l₂ A B (A-intr ⊩A) (B-intr ⊩B)) →
    ¬ Γ ⊢ A ≡ B
  A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B
    with reducible-⊩≡ A≡B
  … | _ , ⊩A , ⊩B , A≡B =
    let _ , ⊩A′ = A-elim ⊩A
        _ , ⊩B′ = B-elim ⊩B
        A≡B′    = irrelevanceEq ⊩A (A-intr ⊩A′) A≡B
    in  A≢B′ ⊩A′ ⊩B′ (goodCases (A-intr ⊩A′) (B-intr ⊩B′) A≡B′)

U≢ℕ′ :
  (⊩U : Γ ⊩′⟨ l ⟩U A)
  (⊩ℕ : Γ ⊩ℕ B) →
  ShapeView Γ l l′ _ _ (Uᵣ ⊩U) (ℕᵣ ⊩ℕ) → ⊥
U≢ℕ′ _ _ ()

U≢ℕ-red : Γ ⊢ B ⇒* ℕ → Γ ⊢ U l ≡ B → ⊥
U≢ℕ-red D =
  A≢B _⊩′⟨_⟩U_ (λ Γ _ B → Γ ⊩ℕ B) Uᵣ ℕᵣ
    (extractMaybeEmb ∘→ U-elim)
    (extractMaybeEmb ∘→ ℕ-elim′ D)
    U≢ℕ′

-- U and ℕ cannot be judgmentally equal.
U≢ℕ : Γ ⊢ U l ≡ ℕ → ⊥
U≢ℕ U≡ℕ =
  let _ , ⊢ℕ = syntacticEq U≡ℕ
  in  U≢ℕ-red (id ⊢ℕ) U≡ℕ

-- U and Empty
U≢Empty′ :
  (⊩U : Γ ⊩′⟨ l ⟩U A)
  (⊩Empty : Γ ⊩Empty B) →
  ShapeView Γ l l′ _ _ (Uᵣ ⊩U) (Emptyᵣ ⊩Empty) → ⊥
U≢Empty′ _ _ ()

U≢Empty-red : Γ ⊢ B ⇒* Empty → Γ ⊢ U l ≡ B → ⊥
U≢Empty-red D =
  A≢B _⊩′⟨_⟩U_ (λ Γ _ B → Γ ⊩Empty B) Uᵣ Emptyᵣ
    (extractMaybeEmb ∘→ U-elim)
    (extractMaybeEmb ∘→ Empty-elim′ D)
    U≢Empty′

U≢Emptyⱼ : Γ ⊢ U l ≡ Empty → ⊥
U≢Emptyⱼ U≡Empty =
  let _ , ⊢Empty = syntacticEq U≡Empty
  in  U≢Empty-red (id ⊢Empty) U≡Empty

-- U and Unit
U≢Unit′ :
  (⊩U : Γ ⊩′⟨ l ⟩U A)
  (⊩Unit : Γ ⊩Unit⟨ s ⟩ B) →
  ShapeView Γ l l′ _ _ (Uᵣ ⊩U) (Unitᵣ ⊩Unit) → ⊥
U≢Unit′ _ _ ()

U≢Unit-red : Γ ⊢ B ⇒* Unit s → Γ ⊢ U l ≡ B → ⊥
U≢Unit-red D =
  A≢B _⊩′⟨_⟩U_ (λ Γ _ B → Γ ⊩Unit⟨ _ ⟩ B) Uᵣ Unitᵣ
    (extractMaybeEmb ∘→ U-elim)
    (extractMaybeEmb ∘→ Unit-elim′ D)
    U≢Unit′

U≢Unitⱼ : Γ ⊢ U l ≡ Unit s → ⊥
U≢Unitⱼ U≡Unit =
  let _ , ⊢Unit = syntacticEq U≡Unit
  in  U≢Unit-red (id ⊢Unit) U≡Unit

-- ℕ and Empty

ℕ≢Empty′ : ∀ {B l l'}
           ([ℕ] : Γ ⊩ℕ ℕ)
           ([Empty] : Γ ⊩Empty B)
           → ShapeView Γ l l' _ _ (ℕᵣ [ℕ]) (Emptyᵣ [Empty]) → ⊥
ℕ≢Empty′ a b ()

ℕ≢Empty-red : ∀ {B} → Γ ⊢ B ⇒* Empty → Γ ⊢ ℕ ≡ B → ⊥
ℕ≢Empty-red D = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩Empty B) ℕᵣ Emptyᵣ
                (λ x → extractMaybeEmb (ℕ-elim x))
                (λ x → extractMaybeEmb (Empty-elim′ D x))
                ℕ≢Empty′

ℕ≢Emptyⱼ : Γ ⊢ ℕ ≡ Empty → ⊥
ℕ≢Emptyⱼ ℕ≡Empty =
  let _ , ⊢Empty = syntacticEq ℕ≡Empty
  in  ℕ≢Empty-red (id ⊢Empty) ℕ≡Empty

-- ℕ and Unit

ℕ≢Unit′ : ∀ {B l l'}
           ([ℕ] : Γ ⊩ℕ ℕ)
           ([Unit] : Γ ⊩Unit⟨ s ⟩ B)
           → ShapeView Γ l l' _ _ (ℕᵣ [ℕ]) (Unitᵣ [Unit]) → ⊥
ℕ≢Unit′ a b ()

ℕ≢Unit-red : ∀ {B} → Γ ⊢ B ⇒* Unit s → Γ ⊢ ℕ ≡ B → ⊥
ℕ≢Unit-red D = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩Unit⟨ _ ⟩ B) ℕᵣ Unitᵣ
                (λ x → extractMaybeEmb (ℕ-elim x))
                (λ x → extractMaybeEmb (Unit-elim′ D x))
                ℕ≢Unit′

ℕ≢Unitⱼ : Γ ⊢ ℕ ≡ Unit s → ⊥
ℕ≢Unitⱼ ℕ≡Unit =
  let _ , ⊢Unit = syntacticEq ℕ≡Unit
  in  ℕ≢Unit-red (id ⊢Unit) ℕ≡Unit

-- Empty and Unit

Empty≢Unit′ : ∀ {B l l'}
           ([Empty] : Γ ⊩Empty Empty)
           ([Unit] : Γ ⊩Unit⟨ s ⟩ B)
           → ShapeView Γ l l' _ _ (Emptyᵣ [Empty]) (Unitᵣ [Unit]) → ⊥
Empty≢Unit′ a b ()

Empty≢Unit-red : ∀ {B} → Γ ⊢ B ⇒* Unit s → Γ ⊢ Empty ≡ B → ⊥
Empty≢Unit-red D = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩Unit⟨ _ ⟩ B) Emptyᵣ Unitᵣ
                (λ x → extractMaybeEmb (Empty-elim x))
                (λ x → extractMaybeEmb (Unit-elim′ D x))
                Empty≢Unit′

Empty≢Unitⱼ : Γ ⊢ Empty ≡ Unit s → ⊥
Empty≢Unitⱼ Empty≡Unit =
  let _ , ⊢Unit = syntacticEq Empty≡Unit
  in  Empty≢Unit-red (id ⊢Unit) Empty≡Unit

-- Universe and binding types

U≢B′ :
  ∀ W
  (⊩U : Γ ⊩′⟨ l ⟩U A)
  (⊩W : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B) →
  ShapeView Γ l l′ _ _ (Uᵣ ⊩U) (Bᵣ W ⊩W) → ⊥
U≢B′ _ _ _ ()

U≢B-red : ∀ W → Γ ⊢ B ⇒* ⟦ W ⟧ C ▹ D → Γ ⊢ U l ≡ B → ⊥
U≢B-red _ D =
  A≢B _⊩′⟨_⟩U_ _⊩′⟨_⟩B⟨ _ ⟩_ Uᵣ (Bᵣ _)
    (extractMaybeEmb ∘→ U-elim)
    (extractMaybeEmb ∘→ B-elim′ _ D)
    (U≢B′ _)

-- The type U l is not definitionally equal to any Π- or Σ-type.

U≢B : ∀ W → Γ ⊢ U l ≡ ⟦ W ⟧ A ▹ B → ⊥
U≢B _ U≡W =
  let _ , ⊢W = syntacticEq U≡W in
  U≢B-red _ (id ⊢W) U≡W

U≢Π : Γ ⊢ U l ≡ Π p , q ▷ A ▹ B → ⊥
U≢Π = U≢B _
U≢Σ : Γ ⊢ U l ≡ Σ⟨ s ⟩ p , q ▷ A ▹ B → ⊥
U≢Σ = U≢B _

U≢ΠΣⱼ : Γ ⊢ U l ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B → ⊥
U≢ΠΣⱼ {b = BMΠ}   = U≢Π
U≢ΠΣⱼ {b = BMΣ _} = U≢Σ

U≢ne′ :
  (⊩U : Γ ⊩′⟨ l ⟩U A)
  (⊩B : Γ ⊩ne B) →
  ShapeView Γ l l′ _ _ (Uᵣ ⊩U) (ne ⊩B) → ⊥
U≢ne′ _ _ ()

U≢ne-red : Γ ⊢ B ⇒* C → Neutral C → Γ ⊢ U l ≡ B → ⊥
U≢ne-red D C-ne =
  A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩ne A) Uᵣ ne
    (extractMaybeEmb ∘→ U-elim)
    (extractMaybeEmb ∘→ ne-elim′ D C-ne)
    U≢ne′

-- U l is not definitionally equal to any neutral term.

U≢ne : Neutral A → Γ ⊢ U l ≡ A → ⊥
U≢ne A-ne U≡A =
  let _ , ⊢A = syntacticEq U≡A in
  U≢ne-red (id ⊢A) A-ne U≡A

ℕ≢B′ : ∀ {A B l l′} W
       ([ℕ] : Γ ⊩ℕ A)
       ([W] : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B)
     → ShapeView Γ l l′ _ _ (ℕᵣ [ℕ]) (Bᵣ W [W]) → ⊥
ℕ≢B′ W a b ()

ℕ≢B-red : ∀ {A B F G} W → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ A ≡ B → ⊥
ℕ≢B-red W D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
                     (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A) ℕᵣ (Bᵣ W)
                     (λ x → extractMaybeEmb (ℕ-elim′ D x))
                     (λ x → extractMaybeEmb (B-elim′ W D′ x))
                     (ℕ≢B′ W)

-- ℕ and B F ▹ G for any F and G cannot be judgmentally equal.
ℕ≢B : ∀ {F G} W → Γ ⊢ ℕ ≡ ⟦ W ⟧ F ▹ G → ⊥
ℕ≢B W ℕ≡W =
  let ⊢ℕ , ⊢W = syntacticEq ℕ≡W
  in  ℕ≢B-red W (id ⊢ℕ) (id ⊢W) ℕ≡W

ℕ≢Π : ∀ {Γ : Con Term n} {F G p q} → _
ℕ≢Π {Γ = Γ} {F} {G} {p} {q} = ℕ≢B {Γ = Γ} {F} {G} (BΠ p q)
ℕ≢Σ : ∀ {Γ : Con Term n} {F G p q m} → _
ℕ≢Σ {Γ = Γ} {F} {G} {p} {q} {m} = ℕ≢B {Γ = Γ} {F} {G} (BΣ m p q)

ℕ≢ΠΣⱼ : Γ ⊢ ℕ ≡ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G → ⊥
ℕ≢ΠΣⱼ {b = BMΠ}   = ℕ≢Π
ℕ≢ΠΣⱼ {b = BMΣ _} = ℕ≢Σ

-- Empty and Π
Empty≢B′ : ∀ {A B l l′} W
       ([Empty] : Γ ⊩Empty A)
       ([W] : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B)
     → ShapeView Γ l l′ _ _ (Emptyᵣ [Empty]) (Bᵣ W [W]) → ⊥
Empty≢B′ W a b ()

Empty≢B-red : ∀ {A B F G} W → Γ ⊢ A ⇒* Empty → Γ ⊢ B ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ A ≡ B → ⊥
Empty≢B-red W D D′ = A≢B (λ Γ l A → Γ ⊩Empty A)
                         (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A) Emptyᵣ (Bᵣ W)
                         (λ x → extractMaybeEmb (Empty-elim′ D x))
                         (λ x → extractMaybeEmb (B-elim′ W D′ x))
                         (Empty≢B′ W)

Empty≢Bⱼ : ∀ {F G} W → Γ ⊢ Empty ≡ ⟦ W ⟧ F ▹ G → ⊥
Empty≢Bⱼ W Empty≡W =
  let ⊢Empty , ⊢W = syntacticEq Empty≡W
  in  Empty≢B-red W (id ⊢Empty) (id ⊢W) Empty≡W

Empty≢Πⱼ : ∀ {Γ : Con Term n} {F G p q} → _
Empty≢Πⱼ {Γ = Γ} {F} {G} {p} {q} = Empty≢Bⱼ {Γ = Γ} {F} {G} (BΠ p q)
Empty≢Σⱼ : ∀ {Γ : Con Term n} {F G p q m} → _
Empty≢Σⱼ {Γ = Γ} {F} {G} {p} {q} {m} =
  Empty≢Bⱼ {Γ = Γ} {F} {G} (BΣ m p q)

Empty≢ΠΣⱼ : Γ ⊢ Empty ≡ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G → ⊥
Empty≢ΠΣⱼ {b = BMΠ}   = Empty≢Πⱼ
Empty≢ΠΣⱼ {b = BMΣ _} = Empty≢Σⱼ

-- Unit and Π
Unit≢B′ : ∀ {A B l l′} W
       ([Unit] : Γ ⊩Unit⟨ s ⟩ A)
       ([W] : Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ B)
     → ShapeView Γ l l′ _ _ (Unitᵣ [Unit]) (Bᵣ W [W]) → ⊥
Unit≢B′ W a b ()

Unit≢B-red : ∀ {A B F G} W → Γ ⊢ A ⇒* Unit s → Γ ⊢ B ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ A ≡ B → ⊥
Unit≢B-red W D D′ = A≢B (λ Γ l A → Γ ⊩Unit⟨ _ ⟩ A)
                    (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A) Unitᵣ (Bᵣ W)
                    (λ x → extractMaybeEmb (Unit-elim′ D x))
                    (λ x → extractMaybeEmb (B-elim′ W D′ x))
                    (Unit≢B′ W)

Unit≢Bⱼ : ∀ {F G} W → Γ ⊢ Unit s ≡ ⟦ W ⟧ F ▹ G → ⊥
Unit≢Bⱼ W Unit≡W =
  let ⊢Unit , ⊢W = syntacticEq Unit≡W
  in  Unit≢B-red W (id ⊢Unit) (id ⊢W) Unit≡W

Unit≢Πⱼ : ∀ {Γ : Con Term n} {F G p q s} → _
Unit≢Πⱼ {Γ = Γ} {F} {G} {p} {q} {s} = Unit≢Bⱼ {Γ = Γ} {s} {F} {G} (BΠ p q)
Unit≢Σⱼ : ∀ {Γ : Con Term n} {F G p q m s} → _
Unit≢Σⱼ {Γ = Γ} {F} {G} {p} {q} {m} {s} = Unit≢Bⱼ {Γ = Γ} {s} {F} {G} (BΣ m p q)

Unit≢ΠΣⱼ : Γ ⊢ Unit s ≡ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G → ⊥
Unit≢ΠΣⱼ {b = BMΠ}   = Unit≢Πⱼ
Unit≢ΠΣⱼ {b = BMΣ _} = Unit≢Σⱼ

ℕ≢ne′ : ∀ {A K l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (ℕᵣ [ℕ]) (ne [K]) → ⊥
ℕ≢ne′ a b ()

ℕ≢ne-red : ∀ {A B K} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
ℕ≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B) ℕᵣ ne
                        (λ x → extractMaybeEmb (ℕ-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        ℕ≢ne′

-- ℕ and K for any neutral K cannot be judgmentally equal.
ℕ≢ne : ∀ {K} → Neutral K → Γ ⊢ ℕ ≡ K → ⊥
ℕ≢ne neK ℕ≡K =
  let ⊢ℕ , ⊢K = syntacticEq ℕ≡K
  in  ℕ≢ne-red (id ⊢ℕ) (id ⊢K) neK ℕ≡K

-- Empty and neutral
Empty≢ne′ : ∀ {A K l l′}
       ([Empty] : Γ ⊩Empty A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Emptyᵣ [Empty]) (ne [K]) → ⊥
Empty≢ne′ a b ()

Empty≢ne-red : ∀ {A B K} → Γ ⊢ A ⇒* Empty → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
Empty≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩ne B) Emptyᵣ ne
                        (λ x → extractMaybeEmb (Empty-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        Empty≢ne′

Empty≢neⱼ : ∀ {K} → Neutral K → Γ ⊢ Empty ≡ K → ⊥
Empty≢neⱼ neK Empty≡K =
  let ⊢Empty , ⊢K = syntacticEq Empty≡K
  in  Empty≢ne-red (id ⊢Empty) (id ⊢K) neK Empty≡K

-- Unit and neutral
Unit≢ne′ : ∀ {A K l l′}
       ([Unit] : Γ ⊩Unit⟨ s ⟩ A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Unitᵣ [Unit]) (ne [K]) → ⊥
Unit≢ne′ a b ()

Unit≢ne-red : ∀ {A B K} → Γ ⊢ A ⇒* Unit s → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
Unit≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Unit⟨ _ ⟩ A) (λ Γ l B → Γ ⊩ne B) Unitᵣ ne
                        (λ x → extractMaybeEmb (Unit-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        Unit≢ne′

Unit≢neⱼ : ∀ {K} → Neutral K → Γ ⊢ Unit s ≡ K → ⊥
Unit≢neⱼ neK Unit≡K =
  let ⊢Unit , ⊢K = syntacticEq Unit≡K
  in  Unit≢ne-red (id ⊢Unit) (id ⊢K) neK Unit≡K

B≢ne′ : ∀ {A K l l′} W
       ([W] : Γ ⊩′⟨ l ⟩B⟨ W ⟩ A)
       ([K] : Γ ⊩ne K)
     → ShapeView Γ l l′ _ _ (Bᵣ W [W]) (ne [K]) → ⊥
B≢ne′ W a b ()

B≢ne-red : ∀ {A B F G K} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ ⊢ B ⇒* K → Neutral K
     → Γ ⊢ A ≡ B → ⊥
B≢ne-red W D D′ neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ W ⟩ A)
                          (λ Γ l B → Γ ⊩ne B) (Bᵣ W) ne
                          (λ x → extractMaybeEmb (B-elim′ W D x))
                          (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                          (B≢ne′ W)

-- ⟦ W ⟧ F ▹ G and K for any W, F, G and neutral K cannot be judgmentally equal.
B≢ne : ∀ {F G K} W → Neutral K → Γ ⊢ ⟦ W ⟧ F ▹ G ≡ K → ⊥
B≢ne W neK W≡K =
  let ⊢W , ⊢K = syntacticEq W≡K
  in  B≢ne-red W (id ⊢W) (id ⊢K) neK W≡K

Π≢ne : ∀ {Γ : Con Term n} {F G H p q} → _
Π≢ne {Γ = Γ} {F} {G} {H} {p} {q} = B≢ne {Γ = Γ} {F} {G} {H} (BΠ p q)
Σ≢ne : ∀ {Γ : Con Term n} {F G H p q m} → _
Σ≢ne {Γ = Γ} {F} {G} {H} {p} {q} {m} =
  B≢ne {Γ = Γ} {F} {G} {H} (BΣ m p q)

ΠΣ≢ne : Neutral H → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡ H → ⊥
ΠΣ≢ne {b = BMΠ}   = B≢ne (BΠ _ _)
ΠΣ≢ne {b = BMΣ _} = B≢ne (BΣ _ _ _)

-- Π and Σ
Π≢Σ′ : ∀ {A B l l′ p q q′ m}
       ([A] : Γ ⊩′⟨ l ⟩B⟨ BΠ p q ⟩ A)
       ([B] : Γ ⊩′⟨ l′ ⟩B⟨ BΣ m p′ q′ ⟩ B)
     → ShapeView Γ l l′ _ _ (Bᵣ (BΠ p q) [A]) (Bᵣ (BΣ m p′ q′) [B]) → ⊥
Π≢Σ′ _ _ ()

Π≢Σ-red : ∀ {A B F G H E m} → Γ ⊢ A ⇒* Π p , q ▷ F ▹ G
         → Γ ⊢ B ⇒* Σ⟨ m ⟩ p′ , q′ ▷ H ▹ E → Γ ⊢ A ≡ B → ⊥
Π≢Σ-red {p′ = p′} {q′ = q′} {m = m} D D′ = A≢B
  (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ BΠ! ⟩ A)
  (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ BΣ m p′ q′ ⟩ A) (Bᵣ BΠ!) (Bᵣ BΣ!)
  (λ x → extractMaybeEmb (B-elim′ BΠ! D x))
  (λ x → extractMaybeEmb (B-elim′ BΣ! D′ x))
  Π≢Σ′

Π≢Σⱼ : ∀ {F G H E m} → Γ ⊢ Π p , q ▷ F ▹ G ≡ Σ⟨ m ⟩ p′ , q′ ▷ H ▹ E → ⊥
Π≢Σⱼ Π≡Σ =
  let ⊢Π , ⊢Σ = syntacticEq Π≡Σ
  in  Π≢Σ-red (id ⊢Π) (id ⊢Σ) Π≡Σ

Σˢ≢Σʷ′ :
  ∀ {A B l l′ q q′}
  ([A] : Γ ⊩′⟨ l ⟩B⟨ BΣ 𝕤 p q ⟩ A)
  ([B] : Γ ⊩′⟨ l′ ⟩B⟨ BΣ 𝕨 p′ q′ ⟩ B) →
  ShapeView Γ l l′ _ _ (Bᵣ (BΣ 𝕤 p q) [A]) (Bᵣ (BΣ 𝕨 p′ q′) [B]) → ⊥
Σˢ≢Σʷ′ _ _ ()

Σˢ≢Σʷ-red : ∀ {A B F G H E} → Γ ⊢ A ⇒* Σˢ p , q ▷ F ▹ G
          → Γ ⊢ B ⇒* Σʷ p′ , q′ ▷ H ▹ E → Γ ⊢ A ≡ B → ⊥
Σˢ≢Σʷ-red D D′ = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩B⟨ BΣˢ ⟩ A)
                     (λ Γ l B → Γ ⊩′⟨ l ⟩B⟨ BΣʷ ⟩ B)
                     (Bᵣ BΣ!) (Bᵣ BΣ!)
                     (λ x → extractMaybeEmb (B-elim′ BΣ! D x))
                     (λ x → extractMaybeEmb (B-elim′ BΣ! D′ x))
                     Σˢ≢Σʷ′

Σˢ≢Σʷⱼ : ∀ {F G H E} → Γ ⊢ Σˢ p , q ▷ F ▹ G ≡ Σʷ p′ , q′ ▷ H ▹ E → ⊥
Σˢ≢Σʷⱼ Σˢ≡Σʷ =
  let ⊢Σˢ , ⊢Σʷ = syntacticEq Σˢ≡Σʷ
  in  Σˢ≢Σʷ-red (id ⊢Σˢ) (id ⊢Σʷ) Σˢ≡Σʷ

-- Weak and strong unit types

Unitʷ≢Unitˢ′ : ([A] : Γ ⊩Unit⟨ 𝕨 ⟩ A)
               ([B] : Γ ⊩Unit⟨ 𝕤 ⟩ B)
             → ShapeView Γ l l′ A B (Unitᵣ [A]) (Unitᵣ [B]) → ⊥
Unitʷ≢Unitˢ′ [A] [B] ()

Unitʷ≢Unitˢ-red : Γ ⊢ A ⇒* Unitʷ
                → Γ ⊢ B ⇒* Unitˢ
                → Γ ⊢ A ≡ B → ⊥
Unitʷ≢Unitˢ-red D D′ = A≢B (λ Γ l A → Γ ⊩Unit⟨ 𝕨 ⟩ A)
                           (λ Γ l B → Γ ⊩Unit⟨ 𝕤 ⟩ B)
                           Unitᵣ Unitᵣ
                           (λ x → extractMaybeEmb (Unit-elim′ D x))
                           (λ x → extractMaybeEmb (Unit-elim′ D′ x))
                           Unitʷ≢Unitˢ′

Unitʷ≢Unitˢ : Γ ⊢ Unitʷ ≡ Unitˢ → ⊥
Unitʷ≢Unitˢ Unitʷ≡Unitˢ =
  let ⊢Unitʷ , ⊢Unitˢ = syntacticEq Unitʷ≡Unitˢ
  in  Unitʷ≢Unitˢ-red (id ⊢Unitʷ) (id ⊢Unitˢ) Unitʷ≡Unitˢ

opaque

  -- Applications of Id are not definitionally equal to neutral types.

  Id≢ne : Neutral B → Γ ⊢ Id A t u ≡ B → ⊥
  Id≢ne B-ne =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩ne A) Idᵣ ne
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ ne-elim B-ne)
      (λ _ _ ())

  -- Applications of Id are not definitionally equal to U.

  Id≢U : Γ ⊢ Id A t u ≡ U l → ⊥
  Id≢U =
    A≢B _⊩′⟨_⟩Id_ _⊩′⟨_⟩U_ Idᵣ Uᵣ
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ U-elim)
      (λ _ _ ())

  -- Applications of Id are not definitionally equal to ℕ.

  Id≢ℕ : Γ ⊢ Id A t u ≡ ℕ → ⊥
  Id≢ℕ =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩ℕ A) Idᵣ ℕᵣ
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ ℕ-elim)
      (λ _ _ ())

  -- Applications of Id are not definitionally equal to Unit.

  Id≢Unit : Γ ⊢ Id A t u ≡ Unit s → ⊥
  Id≢Unit {s = s} =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) Idᵣ Unitᵣ
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ Unit-elim)
      (λ _ _ ())

  -- Applications of Id are not definitionally equal to Empty.

  Id≢Empty : Γ ⊢ Id A t u ≡ Empty → ⊥
  Id≢Empty =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩Empty A) Idᵣ Emptyᵣ
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ Empty-elim)
      (λ _ _ ())

  -- Applications of Id are not definitionally equal to applications of
  -- Π or Σ.

  Id≢⟦⟧▷ : Γ ⊢ Id A t u ≡ ⟦ b′ ⟧ B ▹ C → ⊥
  Id≢⟦⟧▷ =
    A≢B _⊩′⟨_⟩Id_ _⊩′⟨_⟩B⟨ _ ⟩_ Idᵣ (Bᵣ _)
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ B-elim _)
      (λ _ _ ())

  -- Applications of Id are not definitionally equal to applications
  -- of Π.

  Id≢Π : Γ ⊢ Id A t u ≡ Π p , q ▷ B ▹ C → ⊥
  Id≢Π = Id≢⟦⟧▷ {b′ = BΠ _ _}

  -- Applications of Id are not definitionally equal to applications
  -- of Σ.

  Id≢Σ : Γ ⊢ Id A t u ≡ Σ⟨ m ⟩ p , q ▷ B ▹ C → ⊥
  Id≢Σ = Id≢⟦⟧▷ {b′ = BΣ _ _ _}

  -- Applications of Id are not definitionally equal to applications
  -- of Π or Σ.

  Id≢ΠΣ : Γ ⊢ Id A t u ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C → ⊥
  Id≢ΠΣ {b = BMΠ}   = Id≢Π
  Id≢ΠΣ {b = BMΣ _} = Id≢Σ

-- If No-η-equality A holds, then A is not a Π-type.

No-η-equality→≢Π : No-η-equality A → Γ ⊢ A ≡ Π p , q ▷ B ▹ C → ⊥
No-η-equality→≢Π = λ where
  U.Uₙ         U≡Π     → U≢ΠΣⱼ U≡Π
  U.Σʷₙ        Σʷ≡Π    → Π≢Σⱼ (sym Σʷ≡Π)
  U.Emptyₙ     Empty≡Π → Empty≢ΠΣⱼ Empty≡Π
  U.ℕₙ         ℕ≡Π     → ℕ≢ΠΣⱼ ℕ≡Π
  U.Idₙ        Id≡Π    → Id≢ΠΣ Id≡Π
  (U.Unitʷₙ _) Unit≡Π  → Unit≢ΠΣⱼ Unit≡Π
  (U.neₙ A-ne) A≡Π     → ΠΣ≢ne A-ne (sym A≡Π)

-- If No-η-equality A holds, then A is not a Σ-type with η-equality.

No-η-equality→≢Σˢ : No-η-equality A → Γ ⊢ A ≡ Σˢ p , q ▷ B ▹ C → ⊥
No-η-equality→≢Σˢ = λ where
  U.Uₙ         U≡Σ     → U≢ΠΣⱼ U≡Σ
  U.Σʷₙ        Σʷ≡Σ    → Σˢ≢Σʷⱼ (sym Σʷ≡Σ)
  U.Emptyₙ     Empty≡Σ → Empty≢ΠΣⱼ Empty≡Σ
  U.ℕₙ         ℕ≡Σ     → ℕ≢ΠΣⱼ ℕ≡Σ
  U.Idₙ        Id≡Σ    → Id≢ΠΣ Id≡Σ
  (U.Unitʷₙ _) Unit≡Σ  → Unit≢ΠΣⱼ Unit≡Σ
  (U.neₙ A-ne) A≡Σ     → ΠΣ≢ne A-ne (sym A≡Σ)

-- If No-η-equality A holds, then A is not a unit type with
-- η-equality.

No-η-equality→≢Unit : No-η-equality A → Γ ⊢ A ≡ Unit s → ¬ Unit-with-η s
No-η-equality→≢Unit = λ where
  U.Uₙ            U≡Unit      _              → U≢Unitⱼ U≡Unit
  U.Σʷₙ           Σʷ≡Unit     _              → Unit≢ΠΣⱼ (sym Σʷ≡Unit)
  U.Emptyₙ        Empty≡Unit  _              → Empty≢Unitⱼ Empty≡Unit
  U.ℕₙ            ℕ≡Unit      _              → ℕ≢Unitⱼ ℕ≡Unit
  U.Idₙ           Id≡Unit     _              → Id≢Unit Id≡Unit
  (U.Unitʷₙ _)    Unitʷ≡Unitˢ (inj₁ PE.refl) → Unitʷ≢Unitˢ Unitʷ≡Unitˢ
  (U.Unitʷₙ no-η) _           (inj₂ η)       → no-η η
  (U.neₙ A-ne)    A≡Unit      _              → Unit≢neⱼ A-ne
                                                 (sym A≡Unit)

-- If A is a type without η-equality, then a non-neutral WHNF is not
-- definitionally equal at type A to any neutral term.

whnf≢ne :
  No-η-equality A → Whnf t → ¬ Neutral t → Neutral u →
  ¬ Γ ⊢ t ≡ u ∷ A
whnf≢ne {A} {t} {u} ¬-A-η t-whnf ¬-t-ne u-ne t≡u =
  case reducible-⊩≡∷ t≡u of λ
    (_ , t≡u) →
  case wf-⊩∷ $ wf-⊩≡∷ t≡u .proj₁ of λ
    ⊩A →
  lemma ⊩A (⊩≡∷→⊩≡∷/ ⊩A t≡u)
  where
  A⇒*no-η : Γ ⊢ A :⇒*: B → No-η-equality B
  A⇒*no-η [ _ , _ , A⇒*B ] =
    case whnfRed* A⇒*B (U.No-η-equality→Whnf ¬-A-η) of λ {
      PE.refl →
    ¬-A-η }

  ¬t⇒*ne : Γ ⊢ t :⇒*: v ∷ B → ¬ Neutral v
  ¬t⇒*ne [ _ , _ , t⇒*v ] v-ne =
    case whnfRed*Term t⇒*v t-whnf of λ {
      PE.refl →
    ¬-t-ne v-ne }

  u⇒*ne : Γ ⊢ u :⇒*: v ∷ B → Neutral v
  u⇒*ne [ _ , _ , u⇒*v ] =
    case whnfRed*Term u⇒*v (U.ne u-ne) of λ {
      PE.refl →
    u-ne }

  lemma : ([A] : Γ ⊩⟨ l ⟩ A) → ¬ Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
  lemma = λ where
    (ℕᵣ _) (ℕₜ₌ _ _ _ u⇒*zero _ zeroᵣ) →
      U.zero≢ne (u⇒*ne u⇒*zero) PE.refl
    (ℕᵣ _) (ℕₜ₌ _ _ _ u⇒*suc _ (sucᵣ _)) →
      U.suc≢ne (u⇒*ne u⇒*suc) PE.refl
    (ℕᵣ _) (ℕₜ₌ _ _ t⇒*v _ _ (ne (neNfₜ₌ v-ne _ _))) →
      ¬t⇒*ne t⇒*v v-ne
    (Emptyᵣ _) (Emptyₜ₌ _ _ t⇒*v _ _ (ne (neNfₜ₌ v-ne _ _))) →
      ¬t⇒*ne t⇒*v v-ne
    (Unitᵣ (Unitₜ A⇒*Unit _)) [t≡u] →
      case A⇒*no-η A⇒*Unit of λ where
        (U.neₙ ())
        (U.Unitʷₙ not-ok) → case [t≡u] of λ where
          (Unitₜ₌ʷ _ _ _ d′ _ starᵣ _) →
            U.star≢ne (u⇒*ne d′) PE.refl
          (Unitₜ₌ʷ _ _ d _ _ (ne (neNfₜ₌ neK _ _)) _) →
            ¬t⇒*ne d neK
          (Unitₜ₌ˢ _ _ (inj₂ ok)) →
            not-ok ok
    (ne _) (neₜ₌ _ _ t⇒*v _ (neNfₜ₌ v-ne _ _)) →
      ¬t⇒*ne t⇒*v v-ne
    (Bᵣ BΠ! (Bᵣ _ _ A⇒*Π _ _ _ _ _ _ _)) _ →
      case A⇒*no-η A⇒*Π of λ where
        (U.neₙ ())
    (Bᵣ BΣˢ (Bᵣ _ _ A⇒*Σ _ _ _ _ _ _ _)) _ →
      case A⇒*no-η A⇒*Σ of λ where
        (U.neₙ ())
    (Bᵣ BΣʷ _) (_ , _ , _ , u⇒*w , _ , _ , _ , _ , U.prodₙ , _) →
      U.prod≢ne (u⇒*ne u⇒*w) PE.refl
    (Bᵣ BΣʷ _) (_ , _ , t⇒*v , _ , _ , _ , _ , U.ne v-ne , _) →
      ¬t⇒*ne t⇒*v v-ne
    (Bᵣ BΣʷ _) (_ , _ , _ , _ , _ , _ , _ , U.prodₙ , U.ne _  , ())
    (Idᵣ ⊩Id) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) →
      case ⊩Id≡∷-view-inhabited ⊩Id t≡u of λ where
        (ne t′-ne _ _) → ¬t⇒*ne t⇒*t′ t′-ne
        (rfl₌ _)       → U.rfl≢ne (u⇒*ne u⇒*u′) PE.refl
    (Uᵣ _) (Uₜ₌ _ _ t⇒*A u⇒*B A-type B-type A≡B _ _ _) →
      case B-type of λ where
        U.Uₙ        → U.U≢ne     (u⇒*ne u⇒*B) PE.refl
        U.ΠΣₙ       → U.ΠΣ≢ne _  (u⇒*ne u⇒*B) PE.refl
        U.ℕₙ        → U.ℕ≢ne     (u⇒*ne u⇒*B) PE.refl
        U.Emptyₙ    → U.Empty≢ne (u⇒*ne u⇒*B) PE.refl
        U.Unitₙ     → U.Unit≢ne  (u⇒*ne u⇒*B) PE.refl
        U.Idₙ       → U.Id≢ne    (u⇒*ne u⇒*B) PE.refl
        (U.ne B-ne) → case A-type of λ where
          (U.ne A-ne) → ⊥-elim (¬t⇒*ne t⇒*A A-ne)
          U.Uₙ        → U≢ne      B-ne (univ A≡B)
          U.ΠΣₙ       → ΠΣ≢ne     B-ne (univ A≡B)
          U.ℕₙ        → ℕ≢ne      B-ne (univ A≡B)
          U.Emptyₙ    → Empty≢neⱼ B-ne (univ A≡B)
          U.Unitₙ     → Unit≢neⱼ  B-ne (univ A≡B)
          U.Idₙ       → Id≢ne     B-ne (univ A≡B)
    (emb ≤ᵘ-refl     [A]) → lemma [A]
    (emb (≤ᵘ-step p) [A]) → lemma (emb p [A])

-- The term zero is not definitionally equal (at type ℕ) to any
-- neutral term.

zero≢ne :
  Neutral t →
  ¬ Γ ⊢ zero ≡ t ∷ ℕ
zero≢ne = whnf≢ne U.ℕₙ U.zeroₙ (λ ())

-- The term suc t is not definitionally equal (at type ℕ) to any
-- neutral term.

suc≢ne :
  Neutral u →
  ¬ Γ ⊢ suc t ≡ u ∷ ℕ
suc≢ne = whnf≢ne U.ℕₙ U.sucₙ (λ ())

-- The term prodʷ p t u is not definitionally equal (at type
-- Σʷ p , q ▷ A ▹ B) to any neutral term.

prodʷ≢ne :
  Neutral v →
  ¬ Γ ⊢ prodʷ p t u ≡ v ∷ Σʷ p , q ▷ A ▹ B
prodʷ≢ne = whnf≢ne U.Σʷₙ U.prodₙ (λ ())

-- The term rfl is not definitionally equal (at type Id A t u) to any
-- neutral term.

rfl≢ne :
  Neutral v →
  ¬ Γ ⊢ rfl ≡ v ∷ Id A t u
rfl≢ne = whnf≢ne U.Idₙ U.rflₙ (λ ())
