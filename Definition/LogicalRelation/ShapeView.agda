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
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.Properties.Reflexivity R

open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
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
    l l′ l″ l₁ l₁′ l₂ l₂′ l₃ l₃′ : Universe-level
    s : Strength

-- Type for maybe embeddings of reducible types
data MaybeEmb
       {ℓ′} (l : Universe-level) (⊩⟨_⟩ : Universe-level → Set ℓ′) :
       Set ℓ′ where
  noemb : ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : l′ <ᵘ l → MaybeEmb l′ ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

-- Specific reducible types with possible embedding

_⊩⟨_⟩U_ : (Γ : Con Term n) (l : Universe-level) (A : Term n) → Set a
Γ ⊩⟨ l ⟩U A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U A)

_⊩⟨_⟩ℕ_ : (Γ : Con Term n) (l : Universe-level) (A : Term n) → Set a
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩Empty_ : (Γ : Con Term n) (l : Universe-level) (A : Term n) → Set a
Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

_⊩⟨_⟩Unit⟨_⟩_ :
  (Γ : Con Term n) (l : Universe-level) (s : Strength) (A : Term n) →
  Set a
Γ ⊩⟨ l ⟩Unit⟨ s ⟩ A = MaybeEmb l (λ l′ → Γ ⊩Unit⟨ l′ , s ⟩ A)

_⊩⟨_⟩ne_ : (Γ : Con Term n) (l : Universe-level) (A : Term n) → Set a
Γ ⊩⟨ l ⟩ne A = MaybeEmb l (λ _ → Γ ⊩ne A)

_⊩⟨_⟩B⟨_⟩_ :
  (Γ : Con Term n) (l : Universe-level) (W : BindingType) (A : Term n) →
  Set a
Γ ⊩⟨ l ⟩B⟨ W ⟩ A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩B⟨ W ⟩ A)

_⊩⟨_⟩Id_ : Con Term n → Universe-level → Term n → Set a
Γ ⊩⟨ l ⟩Id A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Id A)

-- Construct a general reducible type from a specific

U-intr : ∀ {A l} → Γ ⊩⟨ l ⟩U A → Γ ⊩⟨ l ⟩ A
U-intr (noemb x) = Uᵣ x
U-intr (emb p x) = emb-<-⊩ p (U-intr x)

ℕ-intr : ∀ {A l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb p x) = emb-<-⊩ p (ℕ-intr x)


Empty-intr : ∀ {A l} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr (emb p x) = emb-<-⊩ p (Empty-intr x)

Unit-intr : ∀ {A l s} → Γ ⊩⟨ l ⟩Unit⟨ s ⟩ A → Γ ⊩⟨ l ⟩ A
Unit-intr (noemb x) = Unitᵣ x
Unit-intr (emb p x) = emb-<-⊩ p (Unit-intr x)

ne-intr : ∀ {A l} → Γ ⊩⟨ l ⟩ne A → Γ ⊩⟨ l ⟩ A
ne-intr (noemb x) = ne x
ne-intr (emb p x) = emb-<-⊩ p (ne-intr x)

B-intr : ∀ {A l} W → Γ ⊩⟨ l ⟩B⟨ W ⟩ A → Γ ⊩⟨ l ⟩ A
B-intr W (noemb x) = Bᵣ W x
B-intr W (emb p x) = emb-<-⊩ p (B-intr W x)

Id-intr : Γ ⊩⟨ l ⟩Id A → Γ ⊩⟨ l ⟩ A
Id-intr (noemb ⊩A)   = Idᵣ ⊩A
Id-intr (emb p ⊩A) = emb-<-⊩ p (Id-intr ⊩A)

-- Construct a specific reducible type from a general with some criterion

U-elim′ : Γ ⊢ A ⇒* U l′ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩U A
U-elim′ _ (Uᵣ ⊩U) = noemb ⊩U
U-elim′ A⇒U (ℕᵣ D) with whrDet* (A⇒U , Uₙ) (D , ℕₙ)
... | ()
U-elim′ A⇒U (Emptyᵣ D) with whrDet* (A⇒U , Uₙ) (D , Emptyₙ)
... | ()
U-elim′ A⇒U (Unitᵣ (Unitₜ D _)) with whrDet* (A⇒U , Uₙ) (D , Unitₙ)
... | ()
U-elim′ A⇒U (ne′ _ D neK K≡K) =
  ⊥-elim (U≢ne neK (whrDet* (A⇒U , Uₙ) (D , ne neK)))
U-elim′ A⇒U (Bᵣ′ W _ _ D _ _ _ _ _) =
  ⊥-elim (U≢B W (whrDet* (A⇒U , Uₙ) (D , ⟦ W ⟧ₙ)))
U-elim′ A⇒U (Idᵣ ⊩A) =
  case whrDet* (A⇒U , Uₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()
U-elim′ A⇒U (emb ≤ᵘ-refl x) with U-elim′  A⇒U x
U-elim′ A⇒U (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
U-elim′ A⇒U (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
U-elim′ A⇒U (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (U-elim′ A⇒U (emb p x))

U-elim : Γ ⊩⟨ l ⟩ U l′ → Γ ⊩⟨ l ⟩U U l′
U-elim ⊩U = U-elim′ (id (escape ⊩U)) ⊩U

ℕ-elim′ : ∀ {A l} → Γ ⊢ A ⇒* ℕ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ l′ l< D') with whrDet* (D , ℕₙ) (D' , Uₙ)
... | ()
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (D′ , ne neK)))
ℕ-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (ℕ≢B W (whrDet* (D , ℕₙ) (D′ , ⟦ W ⟧ₙ)))
ℕ-elim′ D (Emptyᵣ D′) with whrDet* (D , ℕₙ) (D′ , Emptyₙ)
... | ()
ℕ-elim′ D (Unitᵣ (Unitₜ D′ _)) with whrDet* (D , ℕₙ) (D′ , Unitₙ)
... | ()
ℕ-elim′ A⇒*Nat (Idᵣ ⊩A) =
  case whrDet* (A⇒*Nat , ℕₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()
ℕ-elim′ A⇒ℕ (emb ≤ᵘ-refl x) with ℕ-elim′  A⇒ℕ x
ℕ-elim′ A⇒ℕ (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
ℕ-elim′ A⇒ℕ (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
ℕ-elim′ A⇒ℕ (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (ℕ-elim′ A⇒ℕ (emb p x))

ℕ-elim : ∀ {l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

Empty-elim′ : ∀ {A l} → Γ ⊢ A ⇒* Empty → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Uᵣ′ l′ l< D') with whrDet* (D , Emptyₙ) (D' , Uₙ)
... | ()
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (Unitᵣ (Unitₜ D′ _))
  with whrDet* (D , Emptyₙ) (D′ , Unitₙ)
... | ()
Empty-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (D′ , ne neK)))
Empty-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (Empty≢B W (whrDet* (D , Emptyₙ) (D′ , ⟦ W ⟧ₙ)))
Empty-elim′ D (ℕᵣ D′) with whrDet* (D , Emptyₙ) (D′ , ℕₙ)
... | ()
Empty-elim′ A⇒*Empty (Idᵣ ⊩A) =
  case whrDet* (A⇒*Empty , Emptyₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()
Empty-elim′ A⇒E (emb ≤ᵘ-refl x) with Empty-elim′  A⇒E x
Empty-elim′ A⇒E (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
Empty-elim′ A⇒E (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
Empty-elim′ A⇒E (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (Empty-elim′ A⇒E (emb p x))

Empty-elim : ∀ {l} → Γ ⊩⟨ l ⟩ Empty → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

Unit-elim′ : Γ ⊢ A ⇒* Unit s l → Γ ⊩⟨ l′ ⟩ A → Γ ⊩⟨ l′ ⟩Unit⟨ s ⟩ A
Unit-elim′ D (Uᵣ′ l′ l< D') with whrDet* (D , Unitₙ) (D' , Uₙ)
... | ()
Unit-elim′ D (Unitᵣ (Unitₜ D′ ok))
  with whrDet* (D′ , Unitₙ) (D , Unitₙ)
... | PE.refl = noemb (Unitₜ D′ ok)
Unit-elim′ D (Emptyᵣ D′) with whrDet* (D , Unitₙ) (D′ , Emptyₙ)
... | ()
Unit-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (D′ , ne neK)))
Unit-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (Unit≢B W (whrDet* (D , Unitₙ) (D′ , ⟦ W ⟧ₙ)))
Unit-elim′ D (ℕᵣ D′) with whrDet* (D , Unitₙ) (D′ , ℕₙ)
... | ()
Unit-elim′ A⇒*Unit (Idᵣ ⊩A) =
  case whrDet* (A⇒*Unit , Unitₙ) (_⊩ₗId_.⇒*Id ⊩A , Idₙ) of λ ()
Unit-elim′ A⇒U (emb ≤ᵘ-refl x) with Unit-elim′  A⇒U x
Unit-elim′ A⇒U (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
Unit-elim′ A⇒U (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
Unit-elim′ A⇒U (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (Unit-elim′ A⇒U (emb p x))

Unit-elim : Γ ⊩⟨ l′ ⟩ Unit s l → Γ ⊩⟨ l′ ⟩Unit⟨ s ⟩ Unit s l
Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

ne-elim′ : ∀ {A l K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ne A
ne-elim′ D neK (Uᵣ′ l′ l< D') =
  ⊥-elim (U≢ne neK (whrDet* (D' , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (Unitᵣ (Unitₜ D′ _)) =
  ⊥-elim (Unit≢ne neK (whrDet* (D′ , Unitₙ) (D , ne neK)))
ne-elim′ D neK (ne′ _ D′ neK′ K≡K) = noemb (ne _ D′ neK′ K≡K)
ne-elim′ D neK (Bᵣ′ W _ _ D′ _ _ _ _ _) =
  ⊥-elim (B≢ne W neK (whrDet* (D′ , ⟦ W ⟧ₙ) (D , ne neK)))
ne-elim′ A⇒*ne n (Idᵣ ⊩A) =
  ⊥-elim (Id≢ne n (whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (A⇒*ne , ne n)))
ne-elim′ A⇒n neK (emb ≤ᵘ-refl x) with ne-elim′ A⇒n neK x
ne-elim′ A⇒n neK (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
ne-elim′ A⇒n neK (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
ne-elim′ A⇒n neK (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (ne-elim′ A⇒n neK (emb p x))

ne-elim : ∀ {l K} → Neutral K  → Γ ⊩⟨ l ⟩ K → Γ ⊩⟨ l ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

B-elim′ : ∀ {A F G l} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩B⟨ W ⟩ A
B-elim′ W D (Uᵣ′ l′ l< D') = ⊥-elim (U≢B W (whrDet* (D' , Uₙ) (D ,  ⟦ W ⟧ₙ)))
B-elim′ W D (ℕᵣ D′) =
  ⊥-elim (ℕ≢B W (whrDet* (D′ , ℕₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Emptyᵣ D′) =
  ⊥-elim (Empty≢B W (whrDet* (D′ , Emptyₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Unitᵣ (Unitₜ D′ _)) =
  ⊥-elim (Unit≢B W (whrDet* (D′ , Unitₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ne′ _ D′ neK K≡K) =
  ⊥-elim (B≢ne W neK (whrDet* (D , ⟦ W ⟧ₙ) (D′ , ne neK)))
B-elim′ BΠ! D (Bᵣ′ BΣ! _ _ D′ _ _ _ _ _)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | ()
B-elim′ BΣ! D (Bᵣ′ BΠ! _ _ D′ _ _ _ _ _)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | ()
B-elim′ BΠ! D (Bᵣ′ BΠ! F G D′ A≡A [F] [G] G-ext ok)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = noemb (Bᵣ F G D′ A≡A [F] [G] G-ext ok)
B-elim′ BΣ! D (Bᵣ′ BΣ! F G D′ A≡A [F] [G] G-ext ok)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = noemb (Bᵣ F G D′ A≡A [F] [G] G-ext ok)
B-elim′ _ A⇒*B (Idᵣ ⊩A) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (A⇒*B , ⟦ _ ⟧ₙ)
B-elim′ W A⇒B (emb ≤ᵘ-refl x) with B-elim′ W A⇒B x
B-elim′ W A⇒B (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
B-elim′ W A⇒B (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
B-elim′ W A⇒B (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (B-elim′ W A⇒B (emb p x))

B-elim : ∀ {F G l} W → Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G
B-elim W [Π] = B-elim′ W (id (escape [Π])) [Π]

Π-elim : ∀ {F G l} → Γ ⊩⟨ l ⟩ Π p , q ▷ F ▹ G → Γ ⊩⟨ l ⟩B⟨ BΠ p q ⟩ Π p , q ▷ F ▹ G
Π-elim [Π] = B-elim′ BΠ! (id (escape [Π])) [Π]

Σ-elim :
  ∀ {F G m l} →
  Γ ⊩⟨ l ⟩ Σ p , q ▷ F ▹ G → Γ ⊩⟨ l ⟩B⟨ BΣ m p q ⟩ Σ p , q ▷ F ▹ G
Σ-elim [Σ] = B-elim′ BΣ! (id (escape [Σ])) [Σ]

Id-elim′ : Γ ⊢ A ⇒* Id B t u → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Id A
Id-elim′ ⇒*Id (Uᵣ′ _′ _ D') with whrDet* (⇒*Id , Idₙ) (D' , Uₙ)
... | ()
Id-elim′ ⇒*Id (ℕᵣ ⇒*ℕ) =
  case whrDet* (⇒*ℕ , ℕₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Emptyᵣ ⇒*Empty) =
  case whrDet* (⇒*Empty , Emptyₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Unitᵣ ⊩Unit) =
  case whrDet* (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩Unit , Unitₙ) (⇒*Id , Idₙ)
  of λ ()
Id-elim′ ⇒*Id (ne′ _ ⇒*ne n _) =
  ⊥-elim (Id≢ne n (whrDet* (⇒*Id , Idₙ) (⇒*ne , ne n)))
Id-elim′ ⇒*Id (Bᵣ′ _ _ _ ⇒*B _ _ _ _ _) =
  ⊥-elim (Id≢⟦⟧▷ _ (whrDet* (⇒*Id , Idₙ) (⇒*B , ⟦ _ ⟧ₙ)))
Id-elim′ _ (Idᵣ ⊩A) =
  noemb ⊩A
Id-elim′ ⇒*Id (emb ≤ᵘ-refl x) with Id-elim′ ⇒*Id x
Id-elim′ ⇒*Id (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
Id-elim′ ⇒*Id (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
Id-elim′ ⇒*Id (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (Id-elim′ ⇒*Id (emb p x))

opaque

  Id-elim : Γ ⊩⟨ l ⟩ Id A t u → Γ ⊩⟨ l ⟩Id Id A t u
  Id-elim ⊩Id = Id-elim′ (id (escape ⊩Id)) ⊩Id

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb {ℓ′ = a} l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb _ x) = extractMaybeEmb x

opaque

  -- If MaybeEmb l P holds, then P l′ holds for some l′ ≤ᵘ l.

  extractMaybeEmb′ :
    {P : Universe-level → Set ℓ} →
    MaybeEmb l P → ∃ λ l′ → l′ ≤ᵘ l × P l′
  extractMaybeEmb′ (noemb p)   = _ , ≤ᵘ-refl , p
  extractMaybeEmb′ (emb ≤ᵘ-refl p) =
    case extractMaybeEmb′ p of λ where
      (l , ≤ᵘ-refl , p) →
        l , ≤ᵘ-step ≤ᵘ-refl , p
      (l , ≤ᵘ-step l< , p) → l , (≤ᵘ-step (≤ᵘ-step l<) , p)
  extractMaybeEmb′ (emb (≤ᵘ-step s) p) =
    let (l , a , p) = extractMaybeEmb′ (emb s p)
    in l , (lemma a , p)
    where
    lemma : l ≤ᵘ l′ → l ≤ᵘ 1+ l′
    lemma = flip ≤ᵘ-trans ≤ᵘ1+

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
  embᵥ₁ : ∀ p {⊩A ⊩B} →
          ShapeView Γ l₁′ l₂ A B (⊩<⇔⊩ p .proj₁ ⊩A) ⊩B →
          ShapeView Γ l₁ l₂ A B (emb p ⊩A) ⊩B
  embᵥ₂ : ∀ p {⊩A ⊩B} →
          ShapeView Γ l₁ l₂′ A B ⊩A (⊩<⇔⊩ p .proj₁ ⊩B) →
          ShapeView Γ l₁ l₂ A B ⊩A (emb p ⊩B)

-- Construct an shape view from an equality (aptly named)
goodCases : ∀ {l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → ShapeView Γ l l′ A B [A] [B]
-- Diagonal cases
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Unitᵣ UnitA) (Unitᵣ  UnitB@(Unitₜ D _)) D′
  with whrDet* (D , Unitₙ) (D′ , Unitₙ)
... | PE.refl = Unitᵥ UnitA UnitB
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (Bᵣ BΠ! ΠA) (Bᵣ′ BΠ! F G D A≡A [F] [G] G-ext _)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = Bᵥ BΠ! ΠA (Bᵣ F G D A≡A [F] [G] G-ext _)
goodCases (Bᵣ BΣ! ΣA) (Bᵣ′ BΣ! F G D A≡A [F] [G] G-ext ok)
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl = Bᵥ BΣ! ΣA (Bᵣ F G D A≡A [F] [G] G-ext ok)
goodCases (Idᵣ ⊩A) (Idᵣ ⊩B) _ = Idᵥ ⊩A ⊩B
goodCases {Γ} {B} ⊩A (emb p _) A≡B = embᵥ₂ p (lemma p)
  where
  lemma :
    (p : l <ᵘ l′) {⊩<B : Γ ⊩<⟨ p ⟩ B} →
    ShapeView _ _ _ _ _ ⊩A (⊩<⇔⊩ p .proj₁ ⊩<B)
  lemma ≤ᵘ-refl     = goodCases _ _ A≡B
  lemma (≤ᵘ-step p) = lemma p
goodCases {Γ} {A} {B} (emb p _) ⊩B A≡B = embᵥ₁ p (lemma p A≡B)
  where
  lemma :
    (p : l <ᵘ l′) {⊩<A : Γ ⊩<⟨ p ⟩ A} →
    Γ ⊩⟨ l′ ⟩ A ≡ B / emb p ⊩<A →
    ShapeView _ _ _ _ _ (⊩<⇔⊩ p .proj₁ ⊩<A) ⊩B
  lemma ≤ᵘ-refl     = goodCases _ _
  lemma (≤ᵘ-step p) = lemma p

-- Refutable cases
-- U ≡ _
goodCases (Uᵣ _) (ℕᵣ D') D with whrDet* (D , Uₙ) (D' , ℕₙ)
... | ()
goodCases (Uᵣ _) (Emptyᵣ D') D with whrDet* (D , Uₙ) (D' , Emptyₙ)
... | ()
goodCases (Uᵣ _) (Unitᵣ (Unitₜ D' _)) D with whrDet* (D , Uₙ) (D' , Unitₙ)
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (ne′ _ D' neK K≡K) D =
  ⊥-elim (U≢ne neK (whrDet* ( D , Uₙ ) (D' , ne neK)))
goodCases (Uᵣ′ _ _ _) (Bᵣ′ W _ _ D' _ _ _ _ _) D =
  ⊥-elim (U≢B W (whrDet* ( D , Uₙ ) (D' , ⟦ W ⟧ₙ )))
goodCases (Uᵣ _) (Idᵣ ⊩B) D =
  case whrDet* (D , Uₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- ℕ ≡ _
goodCases (ℕᵣ _) (Uᵣ (Uᵣ _ _ D')) D with whrDet* (D , ℕₙ) (D' , Uₙ)
... | ()
goodCases (ℕᵣ _) (Emptyᵣ D') D with whrDet* (D , ℕₙ) (D' , Emptyₙ)
... | ()
goodCases (ℕᵣ x) (Unitᵣ (Unitₜ D' _)) D
  with whrDet* (D , ℕₙ) (D' , Unitₙ)
... | ()
goodCases (ℕᵣ D) (ne′ _ D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (D₁ , ne neK)))
goodCases (ℕᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _) A≡B =
  ⊥-elim (ℕ≢B W (whrDet* (A≡B , ℕₙ) (D , ⟦ W ⟧ₙ)))
goodCases (ℕᵣ _) (Idᵣ ⊩B) ⇒*ℕ =
  case whrDet* (⇒*ℕ , ℕₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- Empty ≢ _
goodCases (Emptyᵣ _) (Uᵣ (Uᵣ _ _ D')) D with whrDet* (D , Emptyₙ) (D' , Uₙ)
... | ()
goodCases (Emptyᵣ _) (Unitᵣ (Unitₜ D' _)) D
  with whrDet* (D' , Unitₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ _) (ℕᵣ D') D with whrDet* (D' , ℕₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ D) (ne′ _ D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (D₁ , ne neK)))
goodCases (Emptyᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _) A≡B =
  ⊥-elim (Empty≢B W (whrDet* (A≡B , Emptyₙ) (D , ⟦ W ⟧ₙ)))
goodCases (Emptyᵣ _) (Idᵣ ⊩B) ⇒*Empty =
  case whrDet* (⇒*Empty , Emptyₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- Unit ≡ _
goodCases (Unitᵣ _) (Uᵣ (Uᵣ _ _ D')) D with whrDet* (D , Unitₙ) (D' , Uₙ)
... | ()
goodCases (Unitᵣ _) (Emptyᵣ D') D with whrDet* (D' , Emptyₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ _) (ℕᵣ D') D with whrDet* (D' , ℕₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ D) (ne′ _ D₁ neK K≡K) A≡B =
  ⊥-elim (Unit≢ne neK (whrDet* (A≡B , Unitₙ) (D₁ , ne neK)))
goodCases (Unitᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _) A≡B =
  ⊥-elim (Unit≢B W (whrDet* (A≡B , Unitₙ) (D , ⟦ W ⟧ₙ)))
goodCases (Unitᵣ _) (Idᵣ ⊩B) ⇒*Unit =
  case whrDet* (⇒*Unit , Unitₙ) (_⊩ₗId_.⇒*Id ⊩B , Idₙ) of λ ()

-- ne ≡ _
goodCases (ne′ _ D neK K≡K) (Uᵣ (Uᵣ _ _ D')) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whrDet* (D' , Uₙ) (D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (D₁ , ℕₙ) (D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (D₁ , Emptyₙ) (D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (Unitᵣ (Unitₜ D₁ _)) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Unit≢ne neM (whrDet* (D₁ , Unitₙ) (D′ , ne neM)))
goodCases (ne′ _ _ _ _) (Bᵣ′ W _ _ D₁ _ _ _ _ _) (ne₌ _ D₂ neM _) =
  ⊥-elim (B≢ne W neM (whrDet* (D₁ , ⟦ W ⟧ₙ) (D₂ , ne neM)))
goodCases (ne _) (Idᵣ ⊩B) A≡B =
  ⊥-elim $ Id≢ne N.neM $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (N.D′ , ne N.neM)
  where
  module N = _⊩ne_≡_/_ A≡B

-- B ≡ _
goodCases (Bᵣ W x) (Uᵣ (Uᵣ _ _ D')) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢B W (whrDet* (D' , Uₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ℕᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢B W (whrDet* (D₁ , ℕₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (Emptyᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢B W (whrDet* (D₁ , Emptyₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases
  (Bᵣ W x) (Unitᵣ (Unitₜ D₁ _)) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Unit≢B W (whrDet* (D₁ , Unitₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ne′ _ D neK K≡K) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (B≢ne W neK (whrDet* (D′ , ⟦ W ⟧ₙ) (D , ne neK)))
goodCases (Bᵣ′ BΠ! _ _ _ _ _ _ _ _) (Bᵣ′ BΣ! _ _ D₁ _ _ _ _ _)
          (B₌ _ _ D₂ _ _ _) =
  ⊥-elim (Π≢Σ (whrDet* (D₂ , ΠΣₙ) (D₁ , ΠΣₙ)))
goodCases (Bᵣ′ BΣ! _ _ _ _ _ _ _ _) (Bᵣ′ BΠ! _ _ D₁ _ _ _ _ _)
          (B₌ _ _ D₂ _ _ _) =
  ⊥-elim (Π≢Σ (whrDet* (D₁ , ΠΣₙ) (D₂ , ΠΣₙ)))
goodCases (Bᵣ _ _) (Idᵣ ⊩B) A≡B =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (_⊩ₗB⟨_⟩_≡_/_.D′ A≡B , ⟦ _ ⟧ₙ)

-- Id ≡ _
goodCases (Idᵣ _) (Uᵣ (Uᵣ _ _ D')) A≡B =
  case whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (D' , Uₙ)
  of λ ()
goodCases (Idᵣ _) (ℕᵣ ⇒*ℕ) A≡B =
  case whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (⇒*ℕ , ℕₙ)
  of λ ()
goodCases (Idᵣ _) (Emptyᵣ ⇒*Empty) A≡B =
  case
    whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (⇒*Empty , Emptyₙ)
  of λ ()
goodCases (Idᵣ _) (Unitᵣ ⊩B) A≡B =
  case
    whrDet*
      (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ)
      (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B , Unitₙ)
  of λ ()
goodCases (Idᵣ _) (ne ⊩B) A≡B =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B
goodCases (Idᵣ _) (Bᵣ _ ⊩B) A≡B =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (_⊩ₗB⟨_⟩_.D ⊩B , ⟦ _ ⟧ₙ)

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
  embᵥ₁ : ∀ p {⊩A ⊩B ⊩C} →
          ShapeView₃ Γ l₁′ l₂ l₃ A B C (⊩<⇔⊩ p .proj₁ ⊩A) ⊩B ⊩C →
          ShapeView₃ Γ l₁ l₂ l₃ A B C (emb p ⊩A) ⊩B ⊩C
  embᵥ₂ : ∀ p {⊩A ⊩B ⊩C} →
          ShapeView₃ Γ l₁ l₂′ l₃ A B C ⊩A (⊩<⇔⊩ p .proj₁ ⊩B) ⊩C →
          ShapeView₃ Γ l₁ l₂ l₃ A B C ⊩A (emb p ⊩B) ⊩C
  embᵥ₃ : ∀ p {⊩A ⊩B ⊩C} →
          ShapeView₃ Γ l₁ l₂ l₃′ A B C ⊩A ⊩B (⊩<⇔⊩ p .proj₁ ⊩C) →
          ShapeView₃ Γ l₁ l₂ l₃ A B C ⊩A ⊩B (emb p ⊩C)

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
  with whrDet* (D , Unitₙ) (D′ , Unitₙ)
... | PE.refl = Unitᵥ UnitA₁ UnitB₁ UnitB
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (Bᵥ BΠ! ΠA₁ (Bᵣ F G D A≡A [F] [G] G-ext ok))
        (Bᵥ BΠ! (Bᵣ _ _ D′ _ _ _ _ _) ΠB)
        with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl =
  Bᵥ BΠ! BΠ! BΠ! ΠA₁ (Bᵣ F G D A≡A [F] [G] G-ext ok) ΠB
combine (Bᵥ BΣ! ΣA₁ (Bᵣ F G D A≡A [F] [G] G-ext ok))
        (Bᵥ BΣ! (Bᵣ _ _ D′ _ _ _ _ _) ΣB)
        with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | PE.refl =
  Bᵥ BΣ! BΣ! BΣ! ΣA₁ (Bᵣ F G D A≡A [F] [G] G-ext ok) ΣB
combine (Idᵥ ⊩A ⊩B) (Idᵥ _ ⊩C) =
  Idᵥ ⊩A ⊩B ⊩C
combine (embᵥ₁ p A≡B)          B≡C  = embᵥ₁ p (combine A≡B B≡C)
combine (embᵥ₂ p A≡B)          B≡C  = embᵥ₂ p (combine A≡B B≡C)
combine          A≡B  (embᵥ₁ p B≡C) =          combine A≡B B≡C
combine          A≡B  (embᵥ₂ p B≡C) = embᵥ₃ p (combine A≡B B≡C)

-- Refutable cases
-- U ≡ _
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (ℕᵥ ℕA ℕB) with whrDet* (⇒*U , Uₙ) (ℕA , ℕₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (Emptyᵥ EA EB) with whrDet* (⇒*U , Uₙ) (EA , Emptyₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (Unitᵥ (Unitₜ UnA _) UnB) with whrDet* (⇒*U , Uₙ) (UnA , Unitₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whrDet* (⇒*U , Uₙ) (D , ne neK)))
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (U≢B W (whrDet* (⇒*U , Uₙ) (D , ⟦ W ⟧ₙ)))
combine (Uᵥ UA (Uᵣ _ _ ⇒*U)) (Idᵥ ⊩B′ _) =
  case whrDet* (⇒*U , Uₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) of λ ()

-- ℕ ≡ _
combine (ℕᵥ ℕA ℕB) (Uᵥ (Uᵣ _ _ ⇒*U) UB) with whrDet* (ℕB , ℕₙ)  (⇒*U , Uₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (ℕB , ℕₙ) (EmptyA , Emptyₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Unitᵥ (Unitₜ UnA _) UnB)
  with whrDet* (ℕB , ℕₙ) (UnA , Unitₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (ℕB , ℕₙ) (D , ne neK)))
combine (ℕᵥ _ ℕB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (ℕ≢B W (whrDet* (ℕB , ℕₙ) (D , ⟦ W ⟧ₙ)))
combine (ℕᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case whrDet* (⊩B , ℕₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) of λ ()

-- Empty ≡ _
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ (Uᵣ _ _ ⇒*U) UB) with whrDet* (EmptyB , Emptyₙ)  (⇒*U , Uₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (EmptyB , Emptyₙ) (ℕA , ℕₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Unitᵥ (Unitₜ UnA _) UnB)
  with whrDet* (EmptyB , Emptyₙ) (UnA , Unitₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Empty≢ne neK (whrDet* (EmptyB , Emptyₙ) (D , ne neK)))
combine
  (Emptyᵥ _ EmptyB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (Empty≢B W (whrDet* (EmptyB , Emptyₙ) (D , ⟦ W ⟧ₙ)))
combine (Emptyᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case whrDet* (⊩B , Emptyₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) of λ ()

-- Unit ≡ _
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (Uᵥ (Uᵣ _ _ ⇒*U) UB) with whrDet* (UnitB , Unitₙ)  (⇒*U , Uₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (ℕᵥ ℕA ℕB)
  with whrDet* (UnitB , Unitₙ) (ℕA , ℕₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (Emptyᵥ EmptyA EmptyB)
  with whrDet* (UnitB , Unitₙ) (EmptyA , Emptyₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ UnitB _)) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Unit≢ne neK (whrDet* (UnitB , Unitₙ) (D , ne neK)))
combine (Unitᵥ _ (Unitₜ UnitB _)) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _) _) =
  ⊥-elim (Unit≢B W (whrDet* (UnitB , Unitₙ) (D , ⟦ W ⟧ₙ)))
combine (Unitᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case
    whrDet* (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B , Unitₙ) (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ)
  of λ ()

-- ne ≡ _
combine (ne neA (ne _ D neK K≡K)) (Uᵥ (Uᵣ _ _ ⇒*U) UB) =
  ⊥-elim (U≢ne neK (whrDet* (⇒*U , Uₙ) (D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (ℕA , ℕₙ) (D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (EmptyA , Emptyₙ) (D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (Unitᵥ (Unitₜ UnA _) UnB) =
  ⊥-elim (Unit≢ne neK (whrDet* (UnA , Unitₙ) (D , ne neK)))
combine (ne _ (ne _ D neK _)) (Bᵥ W (Bᵣ _ _ D′ _ _ _ _ _) _) =
  ⊥-elim (B≢ne W neK (whrDet* (D′ , ⟦ W ⟧ₙ) (D , ne neK)))
combine (ne _ ⊩B) (Idᵥ ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) (N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B

-- Π/Σ ≡ _
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (Uᵥ (Uᵣ _ _ ⇒*U) UB) =
  ⊥-elim (U≢B W (whrDet* (⇒*U , Uₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (ℕᵥ ℕA _) =
  ⊥-elim (ℕ≢B W (whrDet* (ℕA , ℕₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (Emptyᵥ EmptyA _) =
  ⊥-elim (Empty≢B W (whrDet* (EmptyA , Emptyₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _)) (Unitᵥ (Unitₜ UnitA _) _) =
  ⊥-elim (Unit≢B W (whrDet* (UnitA , Unitₙ) (D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D₁ _ _ _ _ _)) (ne (ne _ D neK _) _) =
  ⊥-elim (B≢ne W neK (whrDet* (D₁ , ⟦ W ⟧ₙ) (D , ne neK)))
combine (Bᵥ BΠ! _ (Bᵣ _ _ D _ _ _ _ _)) (Bᵥ BΣ! (Bᵣ _ _ D′ _ _ _ _ _) _)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | ()
combine (Bᵥ BΣ! _ (Bᵣ _ _ D _ _ _ _ _)) (Bᵥ BΠ! (Bᵣ _ _ D′ _ _ _ _ _) _)
  with whrDet* (D , ΠΣₙ) (D′ , ΠΣₙ)
... | ()
combine (Bᵥ _ _ ⊩B) (Idᵥ ⊩B′ _) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B′ , Idₙ) (_⊩ₗB⟨_⟩_.D ⊩B , ⟦ _ ⟧ₙ)

-- Id ≡ _
combine (Idᵥ _ ⊩B) (Uᵥ (Uᵣ _ _ ⇒*U) UB) =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (⇒*U , Uₙ) of λ ()
combine (Idᵥ _ ⊩B) (ℕᵥ ⊩B′ _) =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (⊩B′ , ℕₙ) of λ ()
combine (Idᵥ _ ⊩B) (Emptyᵥ ⊩B′ _) =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (⊩B′ , Emptyₙ) of λ ()
combine (Idᵥ _ ⊩B) (Unitᵥ ⊩B′ _) =
  case
    whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B′ , Unitₙ)
  of λ ()
combine (Idᵥ _ ⊩B) (ne ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B′
combine (Idᵥ _ ⊩B) (Bᵥ _ ⊩B′ _) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (_⊩ₗB⟨_⟩_.D ⊩B′ , ⟦ _ ⟧ₙ)
