------------------------------------------------------------------------
-- ShapeView: A view for constructor equality for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.ShapeView
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (K)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Reflexivity R

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B C t u : Term n
    p q : M
    l l′ l″ : TypeLevel

-- Type for maybe embeddings of reducible types
data MaybeEmb {ℓ′} (l : TypeLevel) (⊩⟨_⟩ : TypeLevel → Set ℓ′) : Set ℓ′ where
  noemb : ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : ∀ {l′} → l′ < l → MaybeEmb l′ ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

transparent

  -- Specific reducible types with possible embedding

  _⊩⟨_⟩U : (Γ : Con Term n) (l : TypeLevel) → Set a
  Γ ⊩⟨ l ⟩U = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U)

  _⊩⟨_⟩ℕ_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set a
  Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

  _⊩⟨_⟩Empty_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set a
  Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

  _⊩⟨_⟩Unit_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set a
  Γ ⊩⟨ l ⟩Unit A = MaybeEmb l (λ l′ → Γ ⊩Unit A)

  _⊩⟨_⟩ne_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set a
  Γ ⊩⟨ l ⟩ne A = MaybeEmb l (λ l′ → Γ ⊩ne A)

  _⊩⟨_⟩B⟨_⟩_ : Con Term n → TypeLevel → BindingType → Term n → Set a
  Γ ⊩⟨ l ⟩B⟨ W ⟩ A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ A)

  _⊩⟨_⟩Id_ : Con Term n → TypeLevel → Term n → Set a
  Γ ⊩⟨ l ⟩Id A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Id A)

-- Construct a general reducible type from a specific

U-intr : ∀ {l} → Γ ⊩⟨ l ⟩U → Γ ⊩⟨ l ⟩ U
U-intr (noemb x) = Uᵣ x
U-intr (emb 0<1 x) = emb 0<1 (U-intr x)

ℕ-intr : ∀ {A l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb 0<1 x) = emb 0<1 (ℕ-intr x)

Empty-intr : ∀ {A l} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr (emb 0<1 x) = emb 0<1 (Empty-intr x)

Unit-intr : ∀ {A l} → Γ ⊩⟨ l ⟩Unit A → Γ ⊩⟨ l ⟩ A
Unit-intr (noemb x) = Unitᵣ x
Unit-intr (emb 0<1 x) = emb 0<1 (Unit-intr x)

ne-intr : ∀ {A l} → Γ ⊩⟨ l ⟩ne A → Γ ⊩⟨ l ⟩ A
ne-intr (noemb x) = ne x
ne-intr (emb 0<1 x) = emb 0<1 (ne-intr x)

B-intr : ∀ {A l} W → Γ ⊩⟨ l ⟩B⟨ W ⟩ A → Γ ⊩⟨ l ⟩ A
B-intr W (noemb x) = Bᵣ W x
B-intr W (emb 0<1 x) = emb 0<1 (B-intr W x)

Id-intr : Γ ⊩⟨ l ⟩Id A → Γ ⊩⟨ l ⟩ A
Id-intr (noemb ⊩A)   = Idᵣ ⊩A
Id-intr (emb 0<1 ⊩A) = emb 0<1 (Id-intr ⊩A)

-- Construct a specific reducible type from a general with some criterion

U-elim : ∀ {l} → Γ ⊩⟨ l ⟩ U → Γ ⊩⟨ l ⟩U
U-elim (Uᵣ′ l′ l< ⊢Γ) = noemb (Uᵣ l′ l< ⊢Γ)
U-elim (ℕᵣ D) with whnfRed* (red D) Uₙ
... | ()
U-elim (Emptyᵣ D) with whnfRed* (red D) Uₙ
... | ()
U-elim (Unitᵣ (Unitₜ D _)) with whnfRed* (red D) Uₙ
... | ()
U-elim (ne′ K D neK K≡K) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-elim (Bᵣ′ W _ _ D _ _ _ _ _ _ _) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
U-elim (Idᵣ ⊩A) =
  case whnfRed* (red (_⊩ₗId_.⇒*Id ⊩A)) Uₙ of λ ()
U-elim (emb 0<1 x) with U-elim x
U-elim (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
U-elim (emb 0<1 x) | emb () x₁

ℕ-elim′ : ∀ {A l} → Γ ⊢ A ⇒* ℕ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ l′ l< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ℕₙ)
... | ()
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (ℕ≢B W (whrDet* (D , ℕₙ) (red D′ , ⟦ W ⟧ₙ)))
ℕ-elim′ D (Emptyᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Emptyₙ)
... | ()
ℕ-elim′ D (Unitᵣ (Unitₜ D′ _)) with whrDet* (D , ℕₙ) (red D′ , Unitₙ)
... | ()
ℕ-elim′ A⇒*Nat (Idᵣ ⊩A) =
  case whrDet* (A⇒*Nat , ℕₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
ℕ-elim′ D (emb 0<1 x) with ℕ-elim′ D x
ℕ-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim′ D (emb 0<1 x) | emb () x₂

ℕ-elim : ∀ {l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

Empty-elim′ : ∀ {A l} → Γ ⊢ A ⇒* Empty → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Uᵣ′ l′ l< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Emptyₙ)
... | ()
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (Unitᵣ (Unitₜ D′ _))
  with whrDet* (D , Emptyₙ) (red D′ , Unitₙ)
... | ()
Empty-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (Empty≢B W (whrDet* (D , Emptyₙ) (red D′ , ⟦ W ⟧ₙ)))
Empty-elim′ D (ℕᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , ℕₙ)
... | ()
Empty-elim′ A⇒*Empty (Idᵣ ⊩A) =
  case whrDet* (A⇒*Empty , Emptyₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
Empty-elim′ D (emb 0<1 x) with Empty-elim′ D x
Empty-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Empty-elim′ D (emb 0<1 x) | emb () x₂

Empty-elim : ∀ {l} → Γ ⊩⟨ l ⟩ Empty → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

Unit-elim′ : ∀ {A l} → Γ ⊢ A ⇒* Unit → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Unit A
Unit-elim′ D (Uᵣ′ l′ l< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Unitₙ)
... | ()
Unit-elim′ D (Unitᵣ D′) = noemb D′
Unit-elim′ D (Emptyᵣ D′) with whrDet* (D , Unitₙ) (red D′ , Emptyₙ)
... | ()
Unit-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (red D′ , ne neK)))
Unit-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (Unit≢B W (whrDet* (D , Unitₙ) (red D′ , ⟦ W ⟧ₙ)))
Unit-elim′ D (ℕᵣ D′) with whrDet* (D , Unitₙ) (red D′ , ℕₙ)
... | ()
Unit-elim′ A⇒*Unit (Idᵣ ⊩A) =
  case whrDet* (A⇒*Unit , Unitₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
Unit-elim′ D (emb 0<1 x) with Unit-elim′ D x
Unit-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Unit-elim′ D (emb 0<1 x) | emb () x₂

Unit-elim : ∀ {l} → Γ ⊩⟨ l ⟩ Unit → Γ ⊩⟨ l ⟩Unit Unit
Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

ne-elim′ : ∀ {A l K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ne A
ne-elim′ D neK (Uᵣ′ l′ l< ⊢Γ) =
  ⊥-elim (U≢ne neK (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (Unitᵣ (Unitₜ D′ _)) =
  ⊥-elim (Unit≢ne neK (whrDet* (red D′ , Unitₙ) (D , ne neK)))
ne-elim′ D neK (ne′ K D′ neK′ K≡K) = noemb (ne K D′ neK′ K≡K)
ne-elim′ D neK (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (B≢ne W neK (whrDet* (red D′ , ⟦ W ⟧ₙ) (D , ne neK)))
ne-elim′ A⇒*ne n (Idᵣ ⊩A) =
  ⊥-elim (Id≢ne n (whrDet* (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) (A⇒*ne , ne n)))
ne-elim′ D neK (emb 0<1 x) with ne-elim′ D neK x
ne-elim′ D neK (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ne-elim′ D neK (emb 0<1 x) | emb () x₂

ne-elim : ∀ {l K} → Neutral K  → Γ ⊩⟨ l ⟩ K → Γ ⊩⟨ l ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

B-elim′ : ∀ {A F G l} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩B⟨ W ⟩ A
B-elim′ W D (Uᵣ′ l′ l< ⊢Γ) =
  ⊥-elim (U≢B W (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ℕᵣ D′) =
  ⊥-elim (ℕ≢B W (whrDet* (red D′ , ℕₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Emptyᵣ D′) =
  ⊥-elim (Empty≢B W (whrDet* (red D′ , Emptyₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Unitᵣ (Unitₜ D′ _)) =
  ⊥-elim (Unit≢B W (whrDet* (red D′ , Unitₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ne′ K D′ neK K≡K) =
  ⊥-elim (B≢ne W neK (whrDet* (D , ⟦ W ⟧ₙ) (red D′ , ne neK)))
B-elim′ BΠ! D (Bᵣ′ BΣ! _ _ D′ _ _ _ _ _ _ _)
  with whrDet* (D , ΠΣₙ) (red D′ , ΠΣₙ)
... | ()
B-elim′ BΣ! D (Bᵣ′ BΠ! _ _ D′ _ _ _ _ _ _ _)
  with whrDet* (D , ΠΣₙ) (red D′ , ΠΣₙ)
... | ()
B-elim′ BΠ! D (Bᵣ′ BΠ! F G D′ ⊢F ⊢G A≡A [F] [G] G-ext ok)
  with whrDet* (D , ΠΣₙ) (red D′ , ΠΣₙ)
... | PE.refl = noemb (Bᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext ok)
B-elim′ BΣ! D (Bᵣ′ BΣ! F G D′ ⊢F ⊢G A≡A [F] [G] G-ext ok)
  with whrDet* (D , ΠΣₙ) (red D′ , ΠΣₙ)
... | PE.refl = noemb (Bᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext ok)
B-elim′ _ A⇒*B (Idᵣ ⊩A) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) (A⇒*B , ⟦ _ ⟧ₙ)
B-elim′ W D (emb 0<1 x) with B-elim′ W D x
B-elim′ W D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
B-elim′ W D (emb 0<1 x) | emb () x₂

B-elim : ∀ {F G l} W → Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G
B-elim W [Π] = B-elim′ W (id (escape [Π])) [Π]

Π-elim : ∀ {F G l} → Γ ⊩⟨ l ⟩ Π p , q ▷ F ▹ G → Γ ⊩⟨ l ⟩B⟨ BΠ p q ⟩ Π p , q ▷ F ▹ G
Π-elim [Π] = B-elim′ BΠ! (id (escape [Π])) [Π]

Σ-elim :
  ∀ {F G m l} →
  Γ ⊩⟨ l ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G →
  Γ ⊩⟨ l ⟩B⟨ BΣ m p q ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G
Σ-elim [Σ] = B-elim′ BΣ! (id (escape [Σ])) [Σ]

Id-elim′ : Γ ⊢ A ⇒* Id B t u → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Id A
Id-elim′ ⇒*Id (Uᵣ′ _ _ ⊢Γ) =
  case whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (ℕᵣ ⇒*ℕ) =
  case whrDet* (red ⇒*ℕ , ℕₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Emptyᵣ ⇒*Empty) =
  case whrDet* (red ⇒*Empty , Emptyₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Unitᵣ ⊩Unit) =
  case whrDet* (red (_⊩Unit_.⇒*-Unit ⊩Unit) , Unitₙ) (⇒*Id , Idₙ)
  of λ ()
Id-elim′ ⇒*Id (ne′ _ ⇒*ne n _) =
  ⊥-elim (Id≢ne n (whrDet* (⇒*Id , Idₙ) (red ⇒*ne , ne n)))
Id-elim′ ⇒*Id (Bᵣ′ _ _ _ ⇒*B _ _ _ _ _ _ _) =
  ⊥-elim (Id≢⟦⟧▷ _ (whrDet* (⇒*Id , Idₙ) (red ⇒*B , ⟦ _ ⟧ₙ)))
Id-elim′ _ (Idᵣ ⊩A) =
  noemb ⊩A
Id-elim′ ⇒*Id (emb 0<1 ⊩A) with Id-elim′ ⇒*Id ⊩A
… | noemb ⊩A = emb 0<1 (noemb ⊩A)
… | emb () _

opaque

  Id-elim : Γ ⊩⟨ l ⟩ Id A t u → Γ ⊩⟨ l ⟩Id Id A t u
  Id-elim ⊩Id = Id-elim′ (id (escape ⊩Id)) ⊩Id

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb {ℓ′ = a} l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

-- A view for constructor equality of types where embeddings are ignored
data ShapeView (Γ : Con Term n) : ∀ l l′ A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ B) → Set a where
  Uᵥ : ∀ {l l′} UA UB → ShapeView Γ l l′ U U (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  Unitᵥ : ∀ {A B l l′} UnitA UnitB → ShapeView Γ l l′ A B (Unitᵣ UnitA) (Unitᵣ UnitB)
  ne  : ∀ {A B l l′} neA neB
      → ShapeView Γ l l′ A B (ne neA) (ne neB)
  Bᵥ : ∀ {A B l l′} W BA BB
    → ShapeView Γ l l′ A B (Bᵣ W BA) (Bᵣ W BB)
  Idᵥ : ∀ ⊩A ⊩B → ShapeView Γ l l′ A B (Idᵣ ⊩A) (Idᵣ ⊩B)
  emb⁰¹ : ∀ {A B l p q}
        → ShapeView Γ ⁰ l A B p q
        → ShapeView Γ ¹ l A B (emb 0<1 p) q
  emb¹⁰ : ∀ {A B l p q}
        → ShapeView Γ l ⁰ A B p q
        → ShapeView Γ l ¹ A B p (emb 0<1 q)

-- Construct an shape view from an equality (aptly named)
goodCases : ∀ {l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → ShapeView Γ l l′ A B [A] [B]
-- Diagonal cases
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Unitᵣ UnitA) (Unitᵣ UnitB) A≡B = Unitᵥ UnitA UnitB
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (Bᵣ BΠ! ΠA) (Bᵣ′ BΠ! F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
  with whrDet* (red D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = Bᵥ BΠ! ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
goodCases (Bᵣ BΣ! ΣA) (Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
  with whrDet* (red D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = Bᵥ BΣ! ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
goodCases (Idᵣ ⊩A) (Idᵣ ⊩B) _ = Idᵥ ⊩A ⊩B


goodCases {l = l} [A] (emb 0<1 x) A≡B =
  emb¹⁰ (goodCases {l = l} {⁰} [A] x A≡B)
goodCases {l′ = l} (emb 0<1 x) [B] A≡B =
  emb⁰¹ (goodCases {l = ⁰} {l} x [B] A≡B)

-- Refutable cases
-- U ≡ _
goodCases (Uᵣ′ _ _ ⊢Γ) (ℕᵣ D) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (Emptyᵣ D) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (Unitᵣ (Unitₜ D _)) PE.refl
  with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (ne′ K D neK K≡K) PE.refl =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _) (Bᵣ′ W _ _ D _ _ _ _ _ _ _) PE.refl =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
goodCases (Uᵣ _) (Idᵣ ⊩B) PE.refl =
  case whnfRed* (red (_⊩ₗId_.⇒*Id ⊩B)) Uₙ of λ ()

-- ℕ ≡ _
goodCases (ℕᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (ℕᵣ _) (Emptyᵣ D') D with whrDet* (D , ℕₙ) (red D' , Emptyₙ)
... | ()
goodCases (ℕᵣ x) (Unitᵣ (Unitₜ D' _)) D
  with whrDet* (D , ℕₙ) (red D' , Unitₙ)
... | ()
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _ _ _) A≡B =
  ⊥-elim (ℕ≢B W (whrDet* (A≡B , ℕₙ) (red D , ⟦ W ⟧ₙ)))
goodCases (ℕᵣ _) (Idᵣ ⊩B) ⇒*ℕ =
  case whrDet* (⇒*ℕ , ℕₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- Empty ≢ _
goodCases (Emptyᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (Emptyᵣ _) (Unitᵣ (Unitₜ D' _)) D
  with whrDet* (red D' , Unitₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _ _ _) A≡B =
  ⊥-elim (Empty≢B W (whrDet* (A≡B , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
goodCases (Emptyᵣ _) (Idᵣ ⊩B) ⇒*Empty =
  case whrDet* (⇒*Empty , Emptyₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- Unit ≡ _
goodCases (Unitᵣ _) (Uᵣ x₁) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (Unitᵣ _) (Emptyᵣ D') D with whrDet* (red D' , Emptyₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Unit≢ne neK (whrDet* (A≡B , Unitₙ) (red D₁ , ne neK)))
goodCases (Unitᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _ _ _) A≡B =
  ⊥-elim (Unit≢B W (whrDet* (A≡B , Unitₙ) (red D , ⟦ W ⟧ₙ)))
goodCases (Unitᵣ _) (Idᵣ ⊩B) ⇒*Unit =
  case whrDet* (⇒*Unit , Unitₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- ne ≡ _
goodCases (ne′ K D neK K≡K) (Uᵣ ⊢Γ) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Unitᵣ (Unitₜ D₁ _)) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Unit≢ne neM (whrDet* (red D₁ , Unitₙ) (red D′ , ne neM)))
goodCases (ne′ _ _ _ _) (Bᵣ′ W _ _ D₁ _ _ _ _ _ _ _) (ne₌ _ D₂ neM _) =
  ⊥-elim (B≢ne W neM (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D₂ , ne neM)))
goodCases (ne _) (Idᵣ ⊩B) A≡B =
  ⊥-elim $ Id≢ne N.neM $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red N.D′ , ne N.neM)
  where
  module N = _⊩ne_≡_/_ A≡B

-- B ≡ _
goodCases (Bᵣ W x) (Uᵣ ⊢Γ) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢B W (whnfRed* D′ Uₙ))
goodCases (Bᵣ W x) (ℕᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢B W (whrDet* (red D₁ , ℕₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (Emptyᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢B W (whrDet* (red D₁ , Emptyₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases
  (Bᵣ W x) (Unitᵣ (Unitₜ D₁ _)) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Unit≢B W (whrDet* (red D₁ , Unitₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ne′ K D neK K≡K) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (B≢ne W neK (whrDet* (D′ , ⟦ W ⟧ₙ) (red D , ne neK)))
goodCases (Bᵣ′ BΠ! _ _ _ _ _ _ _ _ _ _)
          (Bᵣ′ BΣ! _ _ D₁ _ _ _ _ _ _ _)
          (B₌ _ _ D₂ _ _ _) =
  ⊥-elim (Π≢Σ (whrDet* (D₂ , ΠΣₙ) (red D₁ , ΠΣₙ)))
goodCases (Bᵣ′ BΣ! _ _ _ _ _ _ _ _ _ _)
          (Bᵣ′ BΠ! _ _ D₁ _ _ _ _ _ _ _)
          (B₌ _ _ D₂ _ _ _) =
  ⊥-elim (Π≢Σ (whrDet* (red D₁ , ΠΣₙ) (D₂ , ΠΣₙ)))
goodCases (Bᵣ _ _) (Idᵣ ⊩B) A≡B =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (_⊩ₗB⟨_⟩_≡_/_.D′ A≡B , ⟦ _ ⟧ₙ)

-- Id ≡ _
goodCases (Idᵣ _) (Uᵣ _) A≡B =
  case whnfRed* (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B)) Uₙ of λ ()
goodCases (Idᵣ _) (ℕᵣ ⇒*ℕ) A≡B =
  case whrDet* (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ) (red ⇒*ℕ , ℕₙ)
  of λ ()
goodCases (Idᵣ _) (Emptyᵣ ⇒*Empty) A≡B =
  case
    whrDet* (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ) (red ⇒*Empty , Emptyₙ)
  of λ ()
goodCases (Idᵣ _) (Unitᵣ ⊩B) A≡B =
  case
    whrDet*
      (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ)
      (red (_⊩Unit_.⇒*-Unit ⊩B) , Unitₙ)
  of λ ()
goodCases (Idᵣ _) (ne ⊩B) A≡B =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ) (red N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B
goodCases (Idᵣ _) (Bᵣ _ ⊩B) A≡B =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet*
    (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ) (red (_⊩ₗB⟨_⟩_.D ⊩B) , ⟦ _ ⟧ₙ)

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A′] : Γ ⊩⟨ l′ ⟩ A)
              → ShapeView Γ l l′ A A [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ (Γ : Con Term n) : ∀ l l′ l″ A B C
                 (p : Γ ⊩⟨ l  ⟩ A)
                 (q : Γ ⊩⟨ l′ ⟩ B)
                 (r : Γ ⊩⟨ l″ ⟩ C) → Set a where
  Uᵥ : ∀ {l l′ l″} UA UB UC → ShapeView₃ Γ l l′ l″ U U U (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C l l′ l″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  Unitᵥ : ∀ {A B C l l′ l″} UnitA UnitB UnitC
    → ShapeView₃ Γ l l′ l″ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ UnitC)
  ne  : ∀ {A B C l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C (ne neA) (ne neB) (ne neC)
  Bᵥ : ∀ {A B C l l′ l″} W W′ W″ BA BB BC
    → ShapeView₃ Γ l l′ l″ A B C (Bᵣ W BA) (Bᵣ W′ BB) (Bᵣ W″ BC)
  Idᵥ :
    ∀ ⊩A ⊩B ⊩C → ShapeView₃ Γ l l′ l″ A B C (Idᵣ ⊩A) (Idᵣ ⊩B) (Idᵣ ⊩C)
  emb⁰¹¹ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ ⁰ l l′ A B C p q r
         → ShapeView₃ Γ ¹ l l′ A B C (emb 0<1 p) q r
  emb¹⁰¹ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ l ⁰ l′ A B C p q r
         → ShapeView₃ Γ l ¹ l′ A B C p (emb 0<1 q) r
  emb¹¹⁰ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ l l′ ⁰ A B C p q r
         → ShapeView₃ Γ l l′ ¹ A B C p q (emb 0<1 r)

-- Combines two two-way views into a three-way view
combine : ∀ {l l′ l″ l‴ A B C [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B [A] [B]
        → ShapeView Γ l″ l‴ B C [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C [A] [B] [C]
-- Diagonal cases
combine (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine (Unitᵥ UnitA₁ UnitB₁) (Unitᵥ UnitA UnitB) = Unitᵥ UnitA₁ UnitB₁ UnitB
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (Bᵥ BΠ! ΠA₁ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok))
        (Bᵥ BΠ! (Bᵣ _ _ D′ _ _ _ _ _ _ _) ΠB)
        with whrDet* (red D , ΠΣₙ) (red D′ , ΠΣₙ)
... | PE.refl =
  Bᵥ BΠ! BΠ! BΠ! ΠA₁ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok) ΠB
combine (Bᵥ BΣ! ΣA₁ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok))
        (Bᵥ BΣ! (Bᵣ _ _ D′ _ _ _ _ _ _ _) ΣB)
        with whrDet* (red D , ΠΣₙ) (red D′ , ΠΣₙ)
... | PE.refl =
  Bᵥ BΣ! BΣ! BΣ! ΣA₁ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok) ΣB
combine (Idᵥ ⊩A ⊩B) (Idᵥ _ ⊩C) =
  Idᵥ ⊩A ⊩B ⊩C
combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])

-- Refutable cases
-- U ≡ _
combine (Uᵥ UA UB) (ℕᵥ ℕA ℕB) with whnfRed* (red ℕA) Uₙ
... | ()
combine (Uᵥ UA UB) (Emptyᵥ EmptyA EmptyB) with whnfRed* (red EmptyA) Uₙ
... | ()
combine (Uᵥ UA UB) (Unitᵥ (Unitₜ UnA _) UnB) with whnfRed* (red UnA) Uₙ
... | ()
combine (Uᵥ UA UB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (Uᵥ _ _) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
combine (Uᵥ _ _) (Idᵥ ⊩B _) =
  case whnfRed* (red (_⊩ₗId_.⇒*Id ⊩B)) Uₙ of λ ()

-- ℕ ≡ _
combine (ℕᵥ ℕA ℕB) (Uᵥ UA UB) with whnfRed* (red ℕB) Uₙ
... | ()
combine (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Unitᵥ (Unitₜ UnA _) UnB)
  with whrDet* (red ℕB , ℕₙ) (red UnA , Unitₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine (ℕᵥ _ ℕB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕB , ℕₙ) (red D , ⟦ W ⟧ₙ)))
combine (ℕᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case whrDet* (red ⊩B , ℕₙ) (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) of λ ()

-- Empty ≡ _
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) with whnfRed* (red EmptyB) Uₙ
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Unitᵥ (Unitₜ UnA _) UnB)
  with whrDet* (red EmptyB , Emptyₙ) (red UnA , Unitₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine
  (Emptyᵥ _ EmptyB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyB , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
combine (Emptyᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case whrDet* (red ⊩B , Emptyₙ) (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) of λ ()

-- Unit ≡ _
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (Uᵥ UA UB)
  with whnfRed* (red UnitB) Uₙ
... | ()
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (ℕᵥ ℕA ℕB)
  with whrDet* (red UnitB , Unitₙ) (red ℕA , ℕₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (Emptyᵥ EmptyA EmptyB)
  with whrDet* (red UnitB , Unitₙ) (red EmptyA , Emptyₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnitB , Unitₙ) (red D , ne neK)))
combine (Unitᵥ _ (Unitₜ UnitB _)) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (Unit≢B W (whrDet* (red UnitB , Unitₙ) (red D , ⟦ W ⟧ₙ)))
combine (Unitᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case
    whrDet*
      (red (_⊩Unit_.⇒*-Unit ⊩B) , Unitₙ)
      (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ)
  of λ ()

-- ne ≡ _
combine (ne neA (ne K D neK K≡K)) (Uᵥ UA UB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Unitᵥ (Unitₜ UnA _) UnB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnA , Unitₙ) (red D , ne neK)))
combine (ne _ (ne _ D neK _)) (Bᵥ W (Bᵣ _ _ D′ _ _ _ _ _ _ _) _) =
  ⊥-elim (B≢ne W neK (whrDet* (red D′ , ⟦ W ⟧ₙ) (red D , ne neK)))
combine (ne _ ⊩B) (Idᵥ ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) (red N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B

-- Π/Σ ≡ _
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (Uᵥ _ _) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (ℕᵥ ℕA _) =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕA , ℕₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (Emptyᵥ EmptyA _) =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyA , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (Unitᵥ (Unitₜ UnitA _) _) =
  ⊥-elim (Unit≢B W (whrDet* (red UnitA , Unitₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D₁ _ _ _ _ _ _ _)) (ne (ne _ D neK _) _) =
  ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))
combine
  (Bᵥ BΠ! _ (Bᵣ _ _ D _ _ _ _ _ _ _))
  (Bᵥ BΣ! (Bᵣ _ _ D′ _ _ _ _ _ _ _) _)
  with whrDet* (red D , ΠΣₙ) (red D′ , ΠΣₙ)
... | ()
combine
  (Bᵥ BΣ! _ (Bᵣ _ _ D _ _ _ _ _ _ _))
  (Bᵥ BΠ! (Bᵣ _ _ D′ _ _ _ _ _ _ _) _)
  with whrDet* (red D , ΠΣₙ) (red D′ , ΠΣₙ)
... | ()
combine (Bᵥ _ _ ⊩B) (Idᵥ ⊩B′ _) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) (red (_⊩ₗB⟨_⟩_.D ⊩B) , ⟦ _ ⟧ₙ)

-- Id ≡ _
combine (Idᵥ _ ⊩B) (Uᵥ _ _) =
  case whnfRed* (red (_⊩ₗId_.⇒*Id ⊩B)) Uₙ of λ ()
combine (Idᵥ _ ⊩B) (ℕᵥ ⊩B′ _) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⊩B′ , ℕₙ) of λ ()
combine (Idᵥ _ ⊩B) (Emptyᵥ ⊩B′ _) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⊩B′ , Emptyₙ) of λ ()
combine (Idᵥ _ ⊩B) (Unitᵥ ⊩B′ _) =
  case
    whrDet*
      (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ)
      (red (_⊩Unit_.⇒*-Unit ⊩B′) , Unitₙ)
  of λ ()
combine (Idᵥ _ ⊩B) (ne ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B′
combine (Idᵥ _ ⊩B) (Bᵥ _ ⊩B′ _) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red (_⊩ₗB⟨_⟩_.D ⊩B′) , ⟦ _ ⟧ₙ)
