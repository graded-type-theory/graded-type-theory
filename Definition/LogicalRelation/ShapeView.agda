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
open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Kit R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Reflexivity R

open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+; s≤s; n<1+n; ≤′-refl; ≤′-step)
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE

private
  variable
    ℓ : Level
    n : Nat
    Γ : Con Term n
    A B C t u : Term n
    p q : M
    l l′ l″ : TypeLevel

-- Type for maybe embeddings of reducible types
data MaybeEmb {ℓ′} (l : TypeLevel) (⊩⟨_⟩ : TypeLevel → Set ℓ′) : Set ℓ′ where
  noemb : ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : ∀ {l′} → l′ < l → MaybeEmb l′ ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

-- Specific reducible types with possible embedding

_⊩⟨_⟩U_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set a
Γ ⊩⟨ l ⟩U A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U A)

_⊩⟨_⟩ℕ_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set a
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩Empty_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set a
Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

_⊩⟨_⟩Unit⟨_⟩_ : (Γ : Con Term n) (l : TypeLevel) (s : Strength) (A : Term n) → Set a
Γ ⊩⟨ l ⟩Unit⟨ s ⟩ A = MaybeEmb l (λ l′ → Γ ⊩Unit⟨ s ⟩ A)

_⊩⟨_⟩ne_ : (Γ : Con Term n) (l : TypeLevel) (A : Term n) → Set a
Γ ⊩⟨ l ⟩ne A = MaybeEmb l (λ l′ → Γ ⊩ne⟨ l′ ⟩ A)

_⊩⟨_⟩B⟨_⟩_ : (Γ : Con Term n) (l : TypeLevel) (W : BindingType) (A : Term n) → Set a
Γ ⊩⟨ l ⟩B⟨ W ⟩ A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ A)

_⊩⟨_⟩Id_ : Con Term n → TypeLevel → Term n → Set a
Γ ⊩⟨ l ⟩Id A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Id A)

-- Construct a general reducible type from a specific

U-intr : ∀ {A l} → Γ ⊩⟨ l ⟩U A → Γ ⊩⟨ l ⟩ A
U-intr (noemb x) = Uᵣ x
U-intr (emb p x) = emb-⊩ p (U-intr x)

ℕ-intr : ∀ {A l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb p x) = emb-⊩ p (ℕ-intr x)


Empty-intr : ∀ {A l} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr (emb p x) = emb-⊩ p (Empty-intr x)

Unit-intr : ∀ {A l s} → Γ ⊩⟨ l ⟩Unit⟨ s ⟩ A → Γ ⊩⟨ l ⟩ A
Unit-intr (noemb x) = Unitᵣ x
Unit-intr (emb p x) = emb-⊩ p (Unit-intr x)

ne-intr : ∀ {A l} → Γ ⊩⟨ l ⟩ne A → Γ ⊩⟨ l ⟩ A
ne-intr (noemb x) = ne x
ne-intr (emb p x) = emb-⊩ p (ne-intr x)

B-intr : ∀ {A l} W → Γ ⊩⟨ l ⟩B⟨ W ⟩ A → Γ ⊩⟨ l ⟩ A
B-intr W (noemb x) = Bᵣ W x
B-intr W (emb p x) = emb-⊩ p (B-intr W x)

Id-intr : Γ ⊩⟨ l ⟩Id A → Γ ⊩⟨ l ⟩ A
Id-intr (noemb ⊩A)   = Idᵣ ⊩A
Id-intr (emb p ⊩A) = emb-⊩ p (Id-intr ⊩A)

-- Construct a specific reducible type from a general with some criterion

U-elim : ∀ {l} → Γ ⊢ A ⇒* U l′ →  Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩U A
U-elim _ (Uᵣ ⊩U) = noemb ⊩U
U-elim A⇒U (ℕᵣ D) with whrDet* (A⇒U , Uₙ) (red D , ℕₙ)
... | ()
U-elim A⇒U (Emptyᵣ D) with whrDet* (A⇒U , Uₙ) (red D , Emptyₙ)
... | ()
U-elim A⇒U (Unitᵣ (Unitₜ D _)) with whrDet* (A⇒U , Uₙ) (red D , Unitₙ)
... | ()
U-elim A⇒U (ne′ K D neK K≡K) =
  ⊥-elim (U≢ne neK (whrDet* (A⇒U , Uₙ) (red D , ne neK)))
U-elim A⇒U (Bᵣ′ W _ _ D _ _ _ _ _ _ _) =
  ⊥-elim (U≢B W (whrDet* (A⇒U , Uₙ) (red D , ⟦ W ⟧ₙ)))
U-elim A⇒U (Idᵣ ⊩A) =
  case whrDet* (A⇒U , Uₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
U-elim A⇒U (emb ≤′-refl x) with U-elim  A⇒U x
U-elim A⇒U (emb ≤′-refl x) | noemb x₁ =  emb ≤′-refl (noemb x₁)
U-elim A⇒U (emb ≤′-refl x) | emb x1 k = emb ≤′-refl (emb x1 k)
U-elim A⇒U (emb (≤′-step p) x) = emb ≤′-refl (U-elim A⇒U (emb p x))

ℕ-elim′ : ∀ {A l} → Γ ⊢ A ⇒* ℕ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ l′ l< D') with whrDet* (D , ℕₙ) (red  D' , Uₙ)
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
ℕ-elim′ A⇒ℕ (emb ≤′-refl x) with ℕ-elim′  A⇒ℕ x
ℕ-elim′ A⇒ℕ (emb ≤′-refl x) | noemb x₁ =  emb ≤′-refl (noemb x₁)
ℕ-elim′ A⇒ℕ (emb ≤′-refl x) | emb x1 k = emb ≤′-refl (emb x1 k)
ℕ-elim′ A⇒ℕ (emb (≤′-step p) x) = emb ≤′-refl (ℕ-elim′ A⇒ℕ (emb p x))

ℕ-elim : ∀ {l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

Empty-elim′ : ∀ {A l} → Γ ⊢ A ⇒* Empty → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Uᵣ′ l′ l< D') with whrDet* (D , Emptyₙ) (red  D' , Uₙ)
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
Empty-elim′ A⇒E (emb ≤′-refl x) with Empty-elim′  A⇒E x
Empty-elim′ A⇒E (emb ≤′-refl x) | noemb x₁ =  emb ≤′-refl (noemb x₁)
Empty-elim′ A⇒E (emb ≤′-refl x) | emb x1 k = emb ≤′-refl (emb x1 k)
Empty-elim′ A⇒E (emb (≤′-step p) x) = emb ≤′-refl (Empty-elim′ A⇒E (emb p x))

Empty-elim : ∀ {l} → Γ ⊩⟨ l ⟩ Empty → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

Unit-elim′ : ∀ {A l s} → Γ ⊢ A ⇒* Unit s → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Unit⟨ s ⟩ A
Unit-elim′ D (Uᵣ′ l′ l< D') with whrDet* (D , Unitₙ) (red  D' , Uₙ)
... | ()
Unit-elim′ D (Unitᵣ (Unitₜ D′ ok))
  with whrDet* (red D′ , Unitₙ) (D , Unitₙ)
... | PE.refl = noemb (Unitₜ D′ ok)
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
Unit-elim′ A⇒U (emb ≤′-refl x) with Unit-elim′  A⇒U x
Unit-elim′ A⇒U (emb ≤′-refl x) | noemb x₁ =  emb ≤′-refl (noemb x₁)
Unit-elim′ A⇒U (emb ≤′-refl x) | emb x1 k = emb ≤′-refl (emb x1 k)
Unit-elim′ A⇒U (emb (≤′-step p) x) = emb ≤′-refl (Unit-elim′ A⇒U (emb p x))

Unit-elim : ∀ {l s} → Γ ⊩⟨ l ⟩ Unit s → Γ ⊩⟨ l ⟩Unit⟨ s ⟩ Unit s
Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

ne-elim′ : ∀ {A l K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ne A
ne-elim′ D neK (Uᵣ′ l′ l< D') =
  ⊥-elim (U≢ne neK (whrDet* (red D' , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (Unitᵣ (Unitₜ D′ _)) =
  ⊥-elim (Unit≢ne neK (whrDet* (red D′ , Unitₙ) (D , ne neK)))
ne-elim′ D neK (ne′ K D′ neK′ K≡K) = noemb (ne K D′ neK′ K≡K)
ne-elim′ D neK (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (B≢ne W neK (whrDet* (red D′ , ⟦ W ⟧ₙ) (D , ne neK)))
ne-elim′ A⇒*ne n (Idᵣ ⊩A) =
  ⊥-elim (Id≢ne n (whrDet* (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) (A⇒*ne , ne n)))
ne-elim′ A⇒n neK (emb ≤′-refl x) with ne-elim′ A⇒n neK x
ne-elim′ A⇒n neK (emb ≤′-refl x) | noemb x₁ =  emb ≤′-refl (noemb x₁)
ne-elim′ A⇒n neK (emb ≤′-refl x) | emb x1 k = emb ≤′-refl (emb x1 k)
ne-elim′ A⇒n neK (emb (≤′-step p) x) = emb ≤′-refl (ne-elim′ A⇒n neK (emb p x))

ne-elim : ∀ {l K} → Neutral K  → Γ ⊩⟨ l ⟩ K → Γ ⊩⟨ l ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

B-elim′ : ∀ {A F G l} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩B⟨ W ⟩ A
B-elim′ W D (Uᵣ′ l′ l< D') = ⊥-elim (U≢B W (whrDet* (red D' , Uₙ) (D ,  ⟦ W ⟧ₙ)))
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
B-elim′ W A⇒B (emb ≤′-refl x) with B-elim′ W A⇒B x
B-elim′ W A⇒B (emb ≤′-refl x) | noemb x₁ =  emb ≤′-refl (noemb x₁)
B-elim′ W A⇒B (emb ≤′-refl x) | emb x1 k = emb ≤′-refl (emb x1 k)
B-elim′ W A⇒B (emb (≤′-step p) x) = emb ≤′-refl (B-elim′ W A⇒B (emb p x))

B-elim : ∀ {F G l} W → Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G
B-elim W [Π] = B-elim′ W (id (escape [Π])) [Π]

Π-elim : ∀ {F G l} → Γ ⊩⟨ l ⟩ Π p , q ▷ F ▹ G → Γ ⊩⟨ l ⟩B⟨ BΠ p q ⟩ Π p , q ▷ F ▹ G
Π-elim [Π] = B-elim′ BΠ! (id (escape [Π])) [Π]

Σ-elim :
  ∀ {F G m l} →
  Γ ⊩⟨ l ⟩ Σ p , q ▷ F ▹ G → Γ ⊩⟨ l ⟩B⟨ BΣ m p q ⟩ Σ p , q ▷ F ▹ G
Σ-elim [Σ] = B-elim′ BΣ! (id (escape [Σ])) [Σ]

Id-elim′ : Γ ⊢ A ⇒* Id B t u → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Id A
Id-elim′ ⇒*Id (Uᵣ′ _′ _ D') with whrDet* (⇒*Id , Idₙ) (red  D' , Uₙ)
... | ()
Id-elim′ ⇒*Id (ℕᵣ ⇒*ℕ) =
  case whrDet* (red ⇒*ℕ , ℕₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Emptyᵣ ⇒*Empty) =
  case whrDet* (red ⇒*Empty , Emptyₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Unitᵣ ⊩Unit) =
  case whrDet* (red (_⊩Unit⟨_⟩_.⇒*-Unit ⊩Unit) , Unitₙ) (⇒*Id , Idₙ)
  of λ ()
Id-elim′ ⇒*Id (ne′ _ ⇒*ne n _) =
  ⊥-elim (Id≢ne n (whrDet* (⇒*Id , Idₙ) (red ⇒*ne , ne n)))
Id-elim′ ⇒*Id (Bᵣ′ _ _ _ ⇒*B _ _ _ _ _ _ _) =
  ⊥-elim (Id≢⟦⟧▷ _ (whrDet* (⇒*Id , Idₙ) (red ⇒*B , ⟦ _ ⟧ₙ)))
Id-elim′ _ (Idᵣ ⊩A) =
  noemb ⊩A
Id-elim′ ⇒*Id (emb ≤′-refl x) with Id-elim′ ⇒*Id x
Id-elim′ ⇒*Id (emb ≤′-refl x) | noemb x₁ =  emb ≤′-refl (noemb x₁)
Id-elim′ ⇒*Id (emb ≤′-refl x) | emb x1 k = emb ≤′-refl (emb x1 k)
Id-elim′ ⇒*Id (emb (≤′-step p) x) = emb ≤′-refl (Id-elim′ ⇒*Id (emb p x))

opaque

  Id-elim : Γ ⊩⟨ l ⟩ Id A t u → Γ ⊩⟨ l ⟩Id Id A t u
  Id-elim ⊩Id = Id-elim′ (id (escape ⊩Id)) ⊩Id

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb {ℓ′ = a} l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb _ x) = extractMaybeEmb x


data ShapeEmb (Γ : Con Term n) : ∀ l′ l A (p : l′ < l) → Γ ⊩⟨ l′ ⟩ A
                            → LogRelKit._⊩_ (kit′ p) Γ A → Set a where
  refl-emb : ∀ {A l′} PA → ShapeEmb Γ l′ (1+ l′) A ≤′-refl PA PA
  step-emb : ∀ {A l′ l l<} PA PB → ShapeEmb Γ l′ l A l< PA PB
                            → ShapeEmb Γ l′ (1+ l) A (≤′-step l<) PA PB

helperToShapeEmb : {l′ l : TypeLevel} → (p : l′ < l )
  → (x : LogRelKit._⊩_ (kit′ p) Γ A) → (ShapeEmb Γ l′ l A p (kitToLogRel p x) x)
helperToShapeEmb ≤′-refl x = refl-emb x
helperToShapeEmb (≤′-step p) x =
                step-emb (kitToLogRel (≤′-step p) x) x (helperToShapeEmb p x)


opaque

  -- If MaybeEmb l P holds, then P l′ holds for some l′ ≤ l.

  extractMaybeEmb′ :
    {P : TypeLevel → Set ℓ} →
    MaybeEmb l P → ∃ λ l′ → l′ ≤ l × P l′
  extractMaybeEmb′ (noemb p)   = _ , ≤′-refl , p
  extractMaybeEmb′ (emb ≤′-refl p) =
    case extractMaybeEmb′ p of λ where
      (l , ≤′-refl , p) →
        l , ≤′-step ≤′-refl , p
      (l , ≤′-step l< , p) → l , (≤′-step (≤′-step l<) , p)
  extractMaybeEmb′ (emb (≤′-step s) p) =
    let (l , a , p) = extractMaybeEmb′ (emb s p)
    in l , (lemma a , p)
    where
      lemma : l ≤ n → l ≤ Nat.suc n
      lemma ≤′-refl = ≤′-step ≤′-refl
      lemma (≤′-step x) = ≤′-step (≤′-step x)

-- A view for constructor equality of types where embeddings are ignored
data ShapeView (Γ : Con Term n) : ∀ l l′ A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ B) → Set a where
  Uᵥ : ∀ {A B l l′} UA UB → ShapeView Γ l l′ A B (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  Unitᵥ : ∀ {A B l l′ s} UnitA UnitB → ShapeView Γ l l′ A B (Unitᵣ {s = s} UnitA) (Unitᵣ {s = s} UnitB)
  ne  : ∀ {A B l l′} neA neB
      → ShapeView Γ l l′ A B (ne neA) (ne neB)
  Bᵥ : ∀ {A B l l′} W BA BB
    → ShapeView Γ l l′ A B (Bᵣ W BA) (Bᵣ W BB)
  Idᵥ : ∀ ⊩A ⊩B → ShapeView Γ l l′ A B (Idᵣ ⊩A) (Idᵣ ⊩B)
  embl- : ∀ {A B l l′′ l′ p q} (l< : l′′ < l) {p′}
        → ShapeEmb Γ l′′ l A l< p p′
        → ShapeView Γ l′′ l′ A B p q
        → ShapeView Γ l l′ A B (emb l< p′) q
  emb-l : ∀ {A B l l′′ l′ p q} (l< : l′′ < l′) {q′}
        → ShapeEmb Γ l′′ l′ B l< q q′
        → ShapeView Γ l l′′ A B p q
        → ShapeView Γ l l′ A B p (emb l< q′)

-- Construct an shape view from an equality (aptly named)
goodCases : ∀ {l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → ShapeView Γ l l′ A B [A] [B]
-- Diagonal cases
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Unitᵣ UnitA) (Unitᵣ  UnitB@(Unitₜ D _)) D′
  with whrDet* (red D , Unitₙ) (D′ , Unitₙ)
... | PE.refl = Unitᵥ UnitA UnitB
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (Bᵣ BΠ! ΠA) (Bᵣ′ BΠ! F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
  with whrDet* (red D , ΠΣₙ) (red D′ , ΠΣₙ)
... | PE.refl = Bᵥ BΠ! ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
goodCases (Bᵣ BΣ! ΣA) (Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
  with whrDet* (red D , ΠΣₙ) (red D′ , ΠΣₙ)
... | PE.refl = Bᵥ BΣ! ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
goodCases (Idᵣ ⊩A) (Idᵣ ⊩B) _ = Idᵥ ⊩A ⊩B

goodCases [A] (emb {l′ = l′₁} p x) A≡B = emb-l p (helperToShapeEmb p x) (v p x)
  where
    v : {l l′ : TypeLevel} (p : l < l′) → (x : LogRelKit._⊩_ (kit′ p) _ _ )
                                  → ShapeView _ _ _ _ _ [A] (kitToLogRel p x)
    v ≤′-refl x = goodCases [A] x A≡B
    v (≤′-step p) x = v p x
goodCases (emb {l′ = l′₁} p x) [B] A≡B = embl- p (helperToShapeEmb p x) (v p x A≡B )
  where
    v : {l l′ : TypeLevel} (p : l < l′) → (x : LogRelKit._⊩_ (kit′ p) _ _ )
        →  _ ⊩⟨ l′ ⟩ _ ≡ _ / emb p x → ShapeView _ _ _ _ _ (kitToLogRel p x) [B]
    v ≤′-refl x A≡B = goodCases x [B] A≡B
    v (≤′-step p) x A≡B = v p x A≡B

-- Refutable cases
-- U ≡ _
goodCases (Uᵣ _) (ℕᵣ D') [ _ , _ , D ] with whrDet* (D , Uₙ) (red D' , ℕₙ)
... | ()
goodCases (Uᵣ _) (Emptyᵣ D') [ _ , _ , D ] with whrDet* (D , Uₙ) (red D' , Emptyₙ)
... | ()
goodCases (Uᵣ _) (Unitᵣ (Unitₜ D' _)) [ _ , _ , D ] with whrDet* (D , Uₙ) (red D' , Unitₙ)
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (ne′ K D' neK K≡K) [ _ , _ , D ] =
  ⊥-elim (U≢ne neK (whrDet* ( D , Uₙ ) ( red D' , ne neK)))
goodCases (Uᵣ′ _ _ _) (Bᵣ′ W _ _ D' _ _ _ _ _ _ _) [ _ , _ , D ] =
  ⊥-elim (U≢B W (whrDet* ( D , Uₙ ) ( red D' , ⟦ W ⟧ₙ )))
goodCases (Uᵣ _) (Idᵣ ⊩B) [ _ , _ , D ] =
  case whrDet* (D , Uₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- ℕ ≡ _
goodCases (ℕᵣ _) (Uᵣ (Uᵣ _ _ D')) D with whrDet* (D , ℕₙ) (red  D' , Uₙ)
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
goodCases (Emptyᵣ _) (Uᵣ (Uᵣ _ _ D')) D with whrDet* (D , Emptyₙ) (red  D' , Uₙ)
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
goodCases (Unitᵣ _) (Uᵣ (Uᵣ _ _ D')) D with whrDet* (D , Unitₙ) (red  D' , Uₙ)
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
goodCases (ne′ K D neK K≡K) (Uᵣ (Uᵣ _ _ D')) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whrDet* (red D' , Uₙ) (red D′ , ne neM)))
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
  module N = _⊩ne⟨_⟩_≡_/_ A≡B

-- B ≡ _
goodCases (Bᵣ W x) (Uᵣ (Uᵣ _ _ D')) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢B W (whrDet* (red D' , Uₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ℕᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢B W (whrDet* (red D₁ , ℕₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (Emptyᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢B W (whrDet* (red D₁ , Emptyₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases
  (Bᵣ W x) (Unitᵣ (Unitₜ D₁ _)) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Unit≢B W (whrDet* (red D₁ , Unitₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ne′ K D neK K≡K) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (B≢ne W neK (whrDet* (red D′ , ⟦ W ⟧ₙ) (red D , ne neK)))
goodCases (Bᵣ′ BΠ! _ _ _ _ _ _ _ _ _ _)
          (Bᵣ′ BΣ! _ _ D₁ _ _ _ _ _ _ _)
          (B₌ _ _ D₂ _ _ _) =
  ⊥-elim (Π≢Σ (whrDet* (red D₂ , ΠΣₙ) (red D₁ , ΠΣₙ)))
goodCases (Bᵣ′ BΣ! _ _ _ _ _ _ _ _ _ _)
          (Bᵣ′ BΠ! _ _ D₁ _ _ _ _ _ _ _)
          (B₌ _ _ D₂ _ _ _) =
  ⊥-elim (Π≢Σ (whrDet* (red D₁ , ΠΣₙ) (red D₂ , ΠΣₙ)))
goodCases (Bᵣ _ _) (Idᵣ ⊩B) A≡B =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ)
    (red (_⊩ₗB⟨_⟩_≡_/_.D′ A≡B) , ⟦ _ ⟧ₙ)

-- Id ≡ _
goodCases (Idᵣ _) (Uᵣ (Uᵣ _ _ D')) A≡B =
  case whrDet* (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ) (red D' , Uₙ)
  of λ ()
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
      (red (_⊩Unit⟨_⟩_.⇒*-Unit ⊩B) , Unitₙ)
  of λ ()
goodCases (Idᵣ _) (ne ⊩B) A≡B =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ) (red N.D , ne N.neK)
  where
  module N = _⊩ne⟨_⟩_ ⊩B
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
  Uᵥ : ∀ {A B C l l′ l″} UA UB UC → ShapeView₃ Γ l l′ l″ A B C (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C l l′ l″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  Unitᵥ : ∀ {A B C l l′ l″ s} UnitA UnitB UnitC
    → ShapeView₃ Γ l l′ l″ A B C (Unitᵣ {s = s} UnitA)
                 (Unitᵣ {s = s} UnitB) (Unitᵣ {s = s} UnitC)
  ne  : ∀ {A B C l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C (ne neA) (ne neB) (ne neC)
  Bᵥ : ∀ {A B C l l′ l″} W W′ W″ BA BB BC
    → ShapeView₃ Γ l l′ l″ A B C (Bᵣ W BA) (Bᵣ W′ BB) (Bᵣ W″ BC)
  Idᵥ :
    ∀ ⊩A ⊩B ⊩C → ShapeView₃ Γ l l′ l″ A B C (Idᵣ ⊩A) (Idᵣ ⊩B) (Idᵣ ⊩C)
  embl-- : ∀ {A B C l l′ l' l'' p q r} (l< : l' < l'' ) {p′}
         → ShapeEmb Γ l' l'' A l< p p′
         → ShapeView₃ Γ l' l l′ A B C p q r
         → ShapeView₃ Γ l'' l l′ A B C (emb l< p′) q r
  emb-l- : ∀ {A B C l l′ l' l'' p q r} (l< : l' < l'' ) {q′}
         → ShapeEmb Γ l' l'' B l< q q′
         → ShapeView₃ Γ l l' l′ A B C p q r
         → ShapeView₃ Γ l l'' l′ A B C p (emb l< q′) r
  emb--l : ∀ {A B C l l′ l' l'' p q r} (l< : l' < l'' ) {r′}
         → ShapeEmb Γ l' l'' C l< r r′
         → ShapeView₃ Γ l l′ l' A B C p q r
         → ShapeView₃ Γ l l′ l'' A B C p q (emb l< r′)

-- Combines two two-way views into a three-way view
combine : ∀ {l l′ l″ l‴ A B C [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B [A] [B]
        → ShapeView Γ l″ l‴ B C [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C [A] [B] [C]
-- Diagonal cases
combine (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine (Unitᵥ UnitA₁ UnitB₁@(Unitₜ D _)) (Unitᵥ (Unitₜ D′ _) UnitB)
  with whrDet* (red D , Unitₙ) (red D′ , Unitₙ)
... | PE.refl = Unitᵥ UnitA₁ UnitB₁ UnitB
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
combine (embl- l< se [AB]) [BC] = embl-- l< se (combine [AB] [BC])
combine (emb-l l< se [AB]) [BC] = emb-l- l< se (combine [AB] [BC])
combine [AB] (embl- l< se [BC]) = combine [AB] [BC]
combine [AB] (emb-l l< se [BC]) = emb--l l< se (combine [AB] [BC])

-- Refutable cases
-- U ≡ _
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (ℕᵥ ℕA ℕB) with whrDet* (red ⇒*U , Uₙ) (red ℕA , ℕₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (Emptyᵥ EA EB) with whrDet* (red ⇒*U , Uₙ) (red EA , Emptyₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (Unitᵥ (Unitₜ UnA _) UnB) with whrDet* (red ⇒*U , Uₙ) (red UnA , Unitₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whrDet* (red ⇒*U , Uₙ) (red D , ne neK)))
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (U≢B W (whrDet* (red ⇒*U , Uₙ) (red D , ⟦ W ⟧ₙ)))
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (Idᵥ ⊩B′ _) =
  case whrDet* (red ⇒*U , Uₙ) (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) of λ ()

-- ℕ ≡ _
combine (ℕᵥ ℕA ℕB) (Uᵥ (Uᵣ _ _ ⇒*U) UB) with whrDet* (red ℕB , ℕₙ)  (red ⇒*U , Uₙ)
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
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ (Uᵣ _ _ ⇒*U) UB) with whrDet* (red EmptyB , Emptyₙ)  (red ⇒*U , Uₙ)
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
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (Uᵥ (Uᵣ _ _ ⇒*U) UB) with whrDet* (red UnitB , Unitₙ)  (red ⇒*U , Uₙ)
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
      (red (_⊩Unit⟨_⟩_.⇒*-Unit ⊩B) , Unitₙ)
      (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ)
  of λ ()

-- ne ≡ _
combine (ne neA (ne K D neK K≡K)) (Uᵥ (Uᵣ _ _ ⇒*U) UB) =
  ⊥-elim (U≢ne neK (whrDet* (red ⇒*U , Uₙ) (red D , ne neK)))
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
  module N = _⊩ne⟨_⟩_ ⊩B

-- Π/Σ ≡ _
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (Uᵥ (Uᵣ _ _ ⇒*U) UB) =
  ⊥-elim (U≢B W (whrDet* (red ⇒*U , Uₙ) (red D , ⟦ W ⟧ₙ)))
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
combine (Idᵥ _ ⊩B) (Uᵥ (Uᵣ _ _ ⇒*U) UB) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⇒*U , Uₙ) of λ ()
combine (Idᵥ _ ⊩B) (ℕᵥ ⊩B′ _) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⊩B′ , ℕₙ) of λ ()
combine (Idᵥ _ ⊩B) (Emptyᵥ ⊩B′ _) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⊩B′ , Emptyₙ) of λ ()
combine (Idᵥ _ ⊩B) (Unitᵥ ⊩B′ _) =
  case
    whrDet*
      (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ)
      (red (_⊩Unit⟨_⟩_.⇒*-Unit ⊩B′) , Unitₙ)
  of λ ()
combine (Idᵥ _ ⊩B) (ne ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red N.D , ne N.neK)
  where
  module N = _⊩ne⟨_⟩_ ⊩B′
combine (Idᵥ _ ⊩B) (Bᵥ _ ⊩B′ _) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red (_⊩ₗB⟨_⟩_.D ⊩B′) , ⟦ _ ⟧ₙ)
