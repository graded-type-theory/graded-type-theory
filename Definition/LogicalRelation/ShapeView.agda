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
open import Tools.Level hiding (Level)
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE

private
  variable
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

_⊩⟨_⟩Level_ : (Γ : Con Term n) (l : Universe-level) (A : Term n) → Set a
Γ ⊩⟨ l ⟩Level A = MaybeEmb l (λ l′ → Γ ⊩Level A)

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

Level-intr : ∀ {A l} → Γ ⊩⟨ l ⟩Level A → Γ ⊩⟨ l ⟩ A
Level-intr (noemb x) = Levelᵣ x
Level-intr (emb p x) = emb-<-⊩ p (Level-intr x)

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

Level-elim′ : ∀ {A l} → Γ ⊢ A ⇒* Level → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Level A
Level-elim′ D (Levelᵣ D′) = noemb D′
Level-elim′ D (Uᵣ′ _ _ _ D') with whrDet* (D , Levelₙ) (red  D' , Uₙ)
... | ()
Level-elim′ D (ℕᵣ D′) with whrDet* (D , Levelₙ) (red D′ , ℕₙ)
... | ()
Level-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (Level≢ne neK (whrDet* (D , Levelₙ) (red D′ , ne neK)))
Level-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (Level≢B W (whrDet* (D , Levelₙ) (red D′ , ⟦ W ⟧ₙ)))
Level-elim′ D (Emptyᵣ D′) with whrDet* (D , Levelₙ) (red D′ , Emptyₙ)
... | ()
Level-elim′ D (Unitᵣ (Unitₜ _ _ _ D′ _)) with whrDet* (D , Levelₙ) (red D′ , Unitₙ)
... | ()
Level-elim′ A⇒*Level (Idᵣ ⊩A) =
  case whrDet* (A⇒*Level , Levelₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
Level-elim′ A⇒Level (emb ≤ᵘ-refl x) with Level-elim′  A⇒Level x
Level-elim′ A⇒Level (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
Level-elim′ A⇒Level (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
Level-elim′ A⇒Level (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (Level-elim′ A⇒Level (emb p x))

Level-elim : ∀ {l} → Γ ⊩⟨ l ⟩ Level → Γ ⊩⟨ l ⟩Level Level
Level-elim [Level] = Level-elim′ (id (escape [Level])) [Level]

U-elim′ : Γ ⊢ A ⇒* U t → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩U A
U-elim′ A⇒U (Levelᵣ D) with whrDet* (A⇒U , Uₙ) (red D , Levelₙ)
... | ()
U-elim′ _ (Uᵣ ⊩U) = noemb ⊩U
U-elim′ A⇒U (ℕᵣ D) with whrDet* (A⇒U , Uₙ) (red D , ℕₙ)
... | ()
U-elim′ A⇒U (Emptyᵣ D) with whrDet* (A⇒U , Uₙ) (red D , Emptyₙ)
... | ()
U-elim′ A⇒U (Unitᵣ (Unitₜ _ _ _ D _)) with whrDet* (A⇒U , Uₙ) (red D , Unitₙ)
... | ()
U-elim′ A⇒U (ne′ _ D neK K≡K) =
  ⊥-elim (U≢ne neK (whrDet* (A⇒U , Uₙ) (red D , ne neK)))
U-elim′ A⇒U (Bᵣ′ W _ _ D _ _ _ _ _ _ _) =
  ⊥-elim (U≢B W (whrDet* (A⇒U , Uₙ) (red D , ⟦ W ⟧ₙ)))
U-elim′ A⇒U (Idᵣ ⊩A) =
  case whrDet* (A⇒U , Uₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
U-elim′ A⇒U (emb ≤ᵘ-refl x) with U-elim′  A⇒U x
U-elim′ A⇒U (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
U-elim′ A⇒U (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
U-elim′ A⇒U (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (U-elim′ A⇒U (emb p x))

U-elim : Γ ⊩⟨ l ⟩ U t → Γ ⊩⟨ l ⟩U U t
U-elim ⊩U = U-elim′ (id (escape ⊩U)) ⊩U

ℕ-elim′ : ∀ {A l} → Γ ⊢ A ⇒* ℕ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Levelᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Levelₙ)
... | ()
ℕ-elim′ D (Uᵣ′ _ _ _ D') with whrDet* (D , ℕₙ) (red  D' , Uₙ)
... | ()
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (ℕ≢B W (whrDet* (D , ℕₙ) (red D′ , ⟦ W ⟧ₙ)))
ℕ-elim′ D (Emptyᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Emptyₙ)
... | ()
ℕ-elim′ D (Unitᵣ (Unitₜ _ _ _ D′ _)) with whrDet* (D , ℕₙ) (red D′ , Unitₙ)
... | ()
ℕ-elim′ A⇒*Nat (Idᵣ ⊩A) =
  case whrDet* (A⇒*Nat , ℕₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
ℕ-elim′ A⇒ℕ (emb ≤ᵘ-refl x) with ℕ-elim′  A⇒ℕ x
ℕ-elim′ A⇒ℕ (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
ℕ-elim′ A⇒ℕ (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
ℕ-elim′ A⇒ℕ (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (ℕ-elim′ A⇒ℕ (emb p x))

ℕ-elim : ∀ {l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

Empty-elim′ : ∀ {A l} → Γ ⊢ A ⇒* Empty → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Levelᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , Levelₙ)
... | ()
Empty-elim′ D (Uᵣ′ _ _ _ D') with whrDet* (D , Emptyₙ) (red  D' , Uₙ)
... | ()
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (Unitᵣ (Unitₜ _ _ _ D′ _))
  with whrDet* (D , Emptyₙ) (red D′ , Unitₙ)
... | ()
Empty-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (Empty≢B W (whrDet* (D , Emptyₙ) (red D′ , ⟦ W ⟧ₙ)))
Empty-elim′ D (ℕᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , ℕₙ)
... | ()
Empty-elim′ A⇒*Empty (Idᵣ ⊩A) =
  case whrDet* (A⇒*Empty , Emptyₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
Empty-elim′ A⇒E (emb ≤ᵘ-refl x) with Empty-elim′  A⇒E x
Empty-elim′ A⇒E (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
Empty-elim′ A⇒E (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
Empty-elim′ A⇒E (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (Empty-elim′ A⇒E (emb p x))

Empty-elim : ∀ {l} → Γ ⊩⟨ l ⟩ Empty → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

Unit-elim′ : Γ ⊢ A ⇒* Unit s t → Γ ⊩⟨ l′ ⟩ A → Γ ⊩⟨ l′ ⟩Unit⟨ s ⟩ A
Unit-elim′ D (Levelᵣ D′) with whrDet* (D , Unitₙ) (red D′ , Levelₙ)
... | ()
Unit-elim′ D (Uᵣ′ _ _ _ D') with whrDet* (D , Unitₙ) (red  D' , Uₙ)
... | ()
Unit-elim′ D (Unitᵣ (Unitₜ k [k] k< D′ ok))
  with whrDet* (red D′ , Unitₙ) (D , Unitₙ)
... | PE.refl = noemb (Unitₜ k [k] k< D′ ok)
Unit-elim′ D (Emptyᵣ D′) with whrDet* (D , Unitₙ) (red D′ , Emptyₙ)
... | ()
Unit-elim′ D (ne′ _ D′ neK K≡K) =
  ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (red D′ , ne neK)))
Unit-elim′ D (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (Unit≢B W (whrDet* (D , Unitₙ) (red D′ , ⟦ W ⟧ₙ)))
Unit-elim′ D (ℕᵣ D′) with whrDet* (D , Unitₙ) (red D′ , ℕₙ)
... | ()
Unit-elim′ A⇒*Unit (Idᵣ ⊩A) =
  case whrDet* (A⇒*Unit , Unitₙ) (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) of λ ()
Unit-elim′ A⇒U (emb ≤ᵘ-refl x) with Unit-elim′  A⇒U x
Unit-elim′ A⇒U (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
Unit-elim′ A⇒U (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
Unit-elim′ A⇒U (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (Unit-elim′ A⇒U (emb p x))

Unit-elim : Γ ⊩⟨ l′ ⟩ Unit s t → Γ ⊩⟨ l′ ⟩Unit⟨ s ⟩ Unit s t
Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

ne-elim′ : ∀ {A l K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ne A
ne-elim′ D neK (Levelᵣ D′) =
  ⊥-elim (Level≢ne neK (whrDet* (red D′ , Levelₙ) (D , ne neK)))
ne-elim′ D neK (Uᵣ′ _ _ _ D') =
  ⊥-elim (U≢ne neK (whrDet* (red D' , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (Unitᵣ (Unitₜ _ _ _ D′ _)) =
  ⊥-elim (Unit≢ne neK (whrDet* (red D′ , Unitₙ) (D , ne neK)))
ne-elim′ D neK (ne′ _ D′ neK′ K≡K) = noemb (ne _ D′ neK′ K≡K)
ne-elim′ D neK (Bᵣ′ W _ _ D′ _ _ _ _ _ _ _) =
  ⊥-elim (B≢ne W neK (whrDet* (red D′ , ⟦ W ⟧ₙ) (D , ne neK)))
ne-elim′ A⇒*ne n (Idᵣ ⊩A) =
  ⊥-elim (Id≢ne n (whrDet* (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) (A⇒*ne , ne n)))
ne-elim′ A⇒n neK (emb ≤ᵘ-refl x) with ne-elim′ A⇒n neK x
ne-elim′ A⇒n neK (emb ≤ᵘ-refl x) | noemb x₁ =  emb ≤ᵘ-refl (noemb x₁)
ne-elim′ A⇒n neK (emb ≤ᵘ-refl x) | emb x1 k = emb ≤ᵘ-refl (emb x1 k)
ne-elim′ A⇒n neK (emb (≤ᵘ-step p) x) = emb ≤ᵘ-refl (ne-elim′ A⇒n neK (emb p x))

ne-elim : ∀ {l K} → Neutral K  → Γ ⊩⟨ l ⟩ K → Γ ⊩⟨ l ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

B-elim′ : ∀ {A F G l} W → Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩B⟨ W ⟩ A
B-elim′ W D (Levelᵣ D') = ⊥-elim (Level≢B W (whrDet* (red D' , Levelₙ) (D ,  ⟦ W ⟧ₙ)))
B-elim′ W D (Uᵣ′ _ _ _ D') = ⊥-elim (U≢B W (whrDet* (red D' , Uₙ) (D ,  ⟦ W ⟧ₙ)))
B-elim′ W D (ℕᵣ D′) =
  ⊥-elim (ℕ≢B W (whrDet* (red D′ , ℕₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Emptyᵣ D′) =
  ⊥-elim (Empty≢B W (whrDet* (red D′ , Emptyₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Unitᵣ (Unitₜ _ _ _ D′ _)) =
  ⊥-elim (Unit≢B W (whrDet* (red D′ , Unitₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ne′ _ D′ neK K≡K) =
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
Id-elim′ ⇒*Id (Levelᵣ D') with whrDet* (⇒*Id , Idₙ) (red D' , Levelₙ)
... | ()
Id-elim′ ⇒*Id (Uᵣ′ _ _ _ D') with whrDet* (⇒*Id , Idₙ) (red  D' , Uₙ)
... | ()
Id-elim′ ⇒*Id (ℕᵣ ⇒*ℕ) =
  case whrDet* (red ⇒*ℕ , ℕₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Emptyᵣ ⇒*Empty) =
  case whrDet* (red ⇒*Empty , Emptyₙ) (⇒*Id , Idₙ) of λ ()
Id-elim′ ⇒*Id (Unitᵣ ⊩Unit) =
  case whrDet* (red (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩Unit) , Unitₙ) (⇒*Id , Idₙ)
  of λ ()
Id-elim′ ⇒*Id (ne′ _ ⇒*ne n _) =
  ⊥-elim (Id≢ne n (whrDet* (⇒*Id , Idₙ) (red ⇒*ne , ne n)))
Id-elim′ ⇒*Id (Bᵣ′ _ _ _ ⇒*B _ _ _ _ _ _ _) =
  ⊥-elim (Id≢⟦⟧▷ _ (whrDet* (⇒*Id , Idₙ) (red ⇒*B , ⟦ _ ⟧ₙ)))
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
    ∀ {ℓ} {P : Universe-level → Set ℓ} →
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
  Levelᵥ : ∀ {A B l l′} LevelA LevelB → ShapeView Γ l l′ A B (Levelᵣ LevelA) (Levelᵣ LevelB)
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
goodCases (Levelᵣ LevelA) (Levelᵣ LevelB) A≡B = Levelᵥ LevelA LevelB
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Unitᵣ UnitA) (Unitᵣ  UnitB@(Unitₜ _ _ _ D _)) D′
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
-- Level ≡ _
goodCases (Levelᵣ _) (Uᵣ′ _ _ _ D') D with whrDet* (D , Levelₙ) (red D' , Uₙ)
... | ()
goodCases (Levelᵣ _) (ℕᵣ D') D with whrDet* (D , Levelₙ) (red D' , ℕₙ)
... | ()
goodCases (Levelᵣ _) (Emptyᵣ D') D with whrDet* (D , Levelₙ) (red D' , Emptyₙ)
... | ()
goodCases (Levelᵣ _) (Unitᵣ (Unitₜ _ _ _ D' _)) D with whrDet* (D , Levelₙ) (red D' , Unitₙ)
... | ()
goodCases (Levelᵣ _) (ne′ _ D' neK K≡K) D =
  ⊥-elim (Level≢ne neK (whrDet* ( D , Levelₙ ) ( red D' , ne neK)))
goodCases (Levelᵣ _) (Bᵣ′ W _ _ D' _ _ _ _ _ _ _) D =
  ⊥-elim (Level≢B W (whrDet* ( D , Levelₙ ) ( red D' , ⟦ W ⟧ₙ )))
goodCases (Levelᵣ _) (Idᵣ ⊩B) D =
  case whrDet* (D , Levelₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- U ≡ _
goodCases (Uᵣ _) (Levelᵣ D') (U₌ _ [ _ , _ , D ] _) with whrDet* (D , Uₙ) (red D' , Levelₙ)
... | ()
goodCases (Uᵣ _) (ℕᵣ D') (U₌ _ [ _ , _ , D ] _) with whrDet* (D , Uₙ) (red D' , ℕₙ)
... | ()
goodCases (Uᵣ _) (Emptyᵣ D') (U₌ _ [ _ , _ , D ] _) with whrDet* (D , Uₙ) (red D' , Emptyₙ)
... | ()
goodCases (Uᵣ _) (Unitᵣ (Unitₜ _ _ _ D' _)) (U₌ _ [ _ , _ , D ] _) with whrDet* (D , Uₙ) (red D' , Unitₙ)
... | ()
goodCases (Uᵣ′ _ _ _ ⊢Γ) (ne′ _ D' neK K≡K) (U₌ _ [ _ , _ , D ] _) =
  ⊥-elim (U≢ne neK (whrDet* ( D , Uₙ ) ( red D' , ne neK)))
goodCases (Uᵣ′ _ _ _ _) (Bᵣ′ W _ _ D' _ _ _ _ _ _ _) (U₌ _ [ _ , _ , D ] _) =
  ⊥-elim (U≢B W (whrDet* ( D , Uₙ ) ( red D' , ⟦ W ⟧ₙ )))
goodCases (Uᵣ _) (Idᵣ ⊩B) (U₌ _ [ _ , _ , D ] _) =
  case whrDet* (D , Uₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- ℕ ≡ _
goodCases (ℕᵣ _) (Levelᵣ D') D with whrDet* (D , ℕₙ) (red  D' , Levelₙ)
... | ()
goodCases (ℕᵣ _) (Uᵣ′ _ _ _ D') D with whrDet* (D , ℕₙ) (red  D' , Uₙ)
... | ()
goodCases (ℕᵣ _) (Emptyᵣ D') D with whrDet* (D , ℕₙ) (red D' , Emptyₙ)
... | ()
goodCases (ℕᵣ x) (Unitᵣ (Unitₜ _ _ _ D' _)) D
  with whrDet* (D , ℕₙ) (red D' , Unitₙ)
... | ()
goodCases (ℕᵣ D) (ne′ _ D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _ _ _) A≡B =
  ⊥-elim (ℕ≢B W (whrDet* (A≡B , ℕₙ) (red D , ⟦ W ⟧ₙ)))
goodCases (ℕᵣ _) (Idᵣ ⊩B) ⇒*ℕ =
  case whrDet* (⇒*ℕ , ℕₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- Empty ≢ _
goodCases (Emptyᵣ _) (Levelᵣ D') D with whrDet* (D , Emptyₙ) (red D' , Levelₙ)
... | ()
goodCases (Emptyᵣ _) (Uᵣ′ _ _ _ D') D with whrDet* (D , Emptyₙ) (red  D' , Uₙ)
... | ()
goodCases (Emptyᵣ _) (Unitᵣ (Unitₜ _ _ _ D' _)) D
  with whrDet* (red D' , Unitₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ D) (ne′ _ D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _ _ _) A≡B =
  ⊥-elim (Empty≢B W (whrDet* (A≡B , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
goodCases (Emptyᵣ _) (Idᵣ ⊩B) ⇒*Empty =
  case whrDet* (⇒*Empty , Emptyₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- Unit ≡ _
goodCases (Unitᵣ _) (Levelᵣ D') D with whrDet* (D , Unitₙ) (red D' , Levelₙ)
... | ()
goodCases (Unitᵣ _) (Uᵣ′ _ _ _ D') D with whrDet* (D , Unitₙ) (red  D' , Uₙ)
... | ()
goodCases (Unitᵣ _) (Emptyᵣ D') D with whrDet* (red D' , Emptyₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ D) (ne′ _ D₁ neK K≡K) A≡B =
  ⊥-elim (Unit≢ne neK (whrDet* (A≡B , Unitₙ) (red D₁ , ne neK)))
goodCases (Unitᵣ _) (Bᵣ′ W _ _ D _ _ _ _ _ _ _) A≡B =
  ⊥-elim (Unit≢B W (whrDet* (A≡B , Unitₙ) (red D , ⟦ W ⟧ₙ)))
goodCases (Unitᵣ _) (Idᵣ ⊩B) ⇒*Unit =
  case whrDet* (⇒*Unit , Unitₙ) (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) of λ ()

-- ne ≡ _
goodCases (ne′ _ D neK K≡K) (Levelᵣ D') (ne₌ M D′ neM K≡M) =
  ⊥-elim (Level≢ne neM (whrDet* (red D' , Levelₙ) (red D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (Uᵣ′ _ _ _ D') (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whrDet* (red D' , Uₙ) (red D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne′ _ D neK K≡K) (Unitᵣ (Unitₜ _ _ _ D₁ _)) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Unit≢ne neM (whrDet* (red D₁ , Unitₙ) (red D′ , ne neM)))
goodCases (ne′ _ _ _ _) (Bᵣ′ W _ _ D₁ _ _ _ _ _ _ _) (ne₌ _ D₂ neM _) =
  ⊥-elim (B≢ne W neM (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D₂ , ne neM)))
goodCases (ne _) (Idᵣ ⊩B) A≡B =
  ⊥-elim $ Id≢ne N.neM $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red N.D′ , ne N.neM)
  where
  module N = _⊩ne_≡_/_ A≡B

-- B ≡ _
goodCases (Bᵣ W x) (Levelᵣ D') (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Level≢B W (whrDet* (red D' , Levelₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (Uᵣ′ _ _ _ D') (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢B W (whrDet* (red D' , Uₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ℕᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢B W (whrDet* (red D₁ , ℕₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (Emptyᵣ D₁) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢B W (whrDet* (red D₁ , Emptyₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases
  (Bᵣ W x) (Unitᵣ (Unitₜ _ _ _ D₁ _)) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Unit≢B W (whrDet* (red D₁ , Unitₙ) (red D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ W x) (ne′ _ D neK K≡K) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
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
goodCases (Idᵣ _) (Levelᵣ D') A≡B =
  case whrDet* (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ) (red D' , Levelₙ)
  of λ ()
goodCases (Idᵣ _) (Uᵣ′ _ _ _ D') A≡B =
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
      (red (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B) , Unitₙ)
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
  Levelᵥ : ∀ {A B C l l′ l″} LevelA LevelB LevelC → ShapeView₃ Γ l l′ l″ A B C (Levelᵣ LevelA) (Levelᵣ LevelB) (Levelᵣ LevelC)
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
combine (Levelᵥ LevelA₁ LevelB₁) (Levelᵥ LevelA LevelB) = Levelᵥ LevelA₁ LevelB₁ LevelB
combine (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine (Unitᵥ UnitA₁ UnitB₁@(Unitₜ _ _ _ D _)) (Unitᵥ (Unitₜ _ _ _ D′ _) UnitB)
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
combine (embᵥ₁ p A≡B)          B≡C  = embᵥ₁ p (combine A≡B B≡C)
combine (embᵥ₂ p A≡B)          B≡C  = embᵥ₂ p (combine A≡B B≡C)
combine          A≡B  (embᵥ₁ p B≡C) =          combine A≡B B≡C
combine          A≡B  (embᵥ₂ p B≡C) = embᵥ₃ p (combine A≡B B≡C)

-- Refutable cases
-- Level ≡ _
combine (Levelᵥ LevelA LevelB) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) with whrDet* (red LevelB , Levelₙ) (red ⇒*U , Uₙ)
... | ()
combine (Levelᵥ LevelA LevelB) (ℕᵥ ℕA ℕB) with whrDet* (red LevelB , Levelₙ) (red ℕA , ℕₙ)
... | ()
combine (Levelᵥ LevelA LevelB) (Emptyᵥ EA EB) with whrDet* (red LevelB , Levelₙ) (red EA , Emptyₙ)
... | ()
combine (Levelᵥ LevelA LevelB) (Unitᵥ (Unitₜ _ _ _ UnA _) UnB) with whrDet* (red LevelB , Levelₙ) (red UnA , Unitₙ)
... | ()
combine (Levelᵥ LevelA LevelB) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Level≢ne neK (whrDet* (red LevelB , Levelₙ) (red D , ne neK)))
combine (Levelᵥ LevelA LevelB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (Level≢B W (whrDet* (red LevelB , Levelₙ) (red D , ⟦ W ⟧ₙ)))
combine (Levelᵥ LevelA LevelB) (Idᵥ ⊩B′ _) =
  case whrDet* (red LevelB , Levelₙ) (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) of λ ()

-- U ≡ _
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Levelᵥ LevelA LevelB) with whrDet* (red ⇒*U , Uₙ) (red LevelA , Levelₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (ℕᵥ ℕA ℕB) with whrDet* (red ⇒*U , Uₙ) (red ℕA , ℕₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Emptyᵥ EA EB) with whrDet* (red ⇒*U , Uₙ) (red EA , Emptyₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Unitᵥ (Unitₜ _ _ _ UnA _) UnB) with whrDet* (red ⇒*U , Uₙ) (red UnA , Unitₙ)
... | ()
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whrDet* (red ⇒*U , Uₙ) (red D , ne neK)))
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (U≢B W (whrDet* (red ⇒*U , Uₙ) (red D , ⟦ W ⟧ₙ)))
combine (Uᵥ UA (Uᵣ _ _ _ ⇒*U)) (Idᵥ ⊩B′ _) =
  case whrDet* (red ⇒*U , Uₙ) (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) of λ ()

-- ℕ ≡ _
combine (ℕᵥ ℕA ℕB) (Levelᵥ LevelA LevelB) with whrDet* (red ℕB , ℕₙ)  (red LevelA , Levelₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) with whrDet* (red ℕB , ℕₙ)  (red ⇒*U , Uₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Unitᵥ (Unitₜ _ _ _ UnA _) UnB)
  with whrDet* (red ℕB , ℕₙ) (red UnA , Unitₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine (ℕᵥ _ ℕB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕB , ℕₙ) (red D , ⟦ W ⟧ₙ)))
combine (ℕᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case whrDet* (red ⊩B , ℕₙ) (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) of λ ()

-- Empty ≡ _
combine (Emptyᵥ EmptyA EmptyB) (Levelᵥ LevelA LevelB) with whrDet* (red EmptyB , Emptyₙ)  (red LevelA , Levelₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) with whrDet* (red EmptyB , Emptyₙ)  (red ⇒*U , Uₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Unitᵥ (Unitₜ _ _ _ UnA _) UnB)
  with whrDet* (red EmptyB , Emptyₙ) (red UnA , Unitₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine
  (Emptyᵥ _ EmptyB) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyB , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
combine (Emptyᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case whrDet* (red ⊩B , Emptyₙ) (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) of λ ()

-- Unit ≡ _
combine (Unitᵥ UnitA (Unitₜ _ _ _ UnitB _)) (Levelᵥ LevelA LevelB) with whrDet* (red UnitB , Unitₙ)  (red LevelA , Levelₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ _ _ _ UnitB _)) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) with whrDet* (red UnitB , Unitₙ)  (red ⇒*U , Uₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ _ _ _ UnitB _)) (ℕᵥ ℕA ℕB)
  with whrDet* (red UnitB , Unitₙ) (red ℕA , ℕₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ _ _ _ UnitB _)) (Emptyᵥ EmptyA EmptyB)
  with whrDet* (red UnitB , Unitₙ) (red EmptyA , Emptyₙ)
... | ()
combine (Unitᵥ UnitA (Unitₜ _ _ _ UnitB _)) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnitB , Unitₙ) (red D , ne neK)))
combine (Unitᵥ _ (Unitₜ _ _ _ UnitB _)) (Bᵥ W (Bᵣ _ _ D _ _ _ _ _ _ _) _) =
  ⊥-elim (Unit≢B W (whrDet* (red UnitB , Unitₙ) (red D , ⟦ W ⟧ₙ)))
combine (Unitᵥ _ ⊩B) (Idᵥ ⊩B′ _) =
  case
    whrDet*
      (red (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B) , Unitₙ)
      (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ)
  of λ ()

-- ne ≡ _
combine (ne neA (ne _ D neK K≡K)) (Levelᵥ LevelA LevelB) =
  ⊥-elim (Level≢ne neK (whrDet* (red LevelA , Levelₙ) (red D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) =
  ⊥-elim (U≢ne neK (whrDet* (red ⇒*U , Uₙ) (red D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine (ne neA (ne _ D neK K≡K)) (Unitᵥ (Unitₜ _ _ _ UnA _) UnB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnA , Unitₙ) (red D , ne neK)))
combine (ne _ (ne _ D neK _)) (Bᵥ W (Bᵣ _ _ D′ _ _ _ _ _ _ _) _) =
  ⊥-elim (B≢ne W neK (whrDet* (red D′ , ⟦ W ⟧ₙ) (red D , ne neK)))
combine (ne _ ⊩B) (Idᵥ ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B′) , Idₙ) (red N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B

-- Π/Σ ≡ _
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (Levelᵥ LevelA LevelB) =
  ⊥-elim (Level≢B W (whrDet* (red LevelA , Levelₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) =
  ⊥-elim (U≢B W (whrDet* (red ⇒*U , Uₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (ℕᵥ ℕA _) =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕA , ℕₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (Emptyᵥ EmptyA _) =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyA , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W _ (Bᵣ _ _ D _ _ _ _ _ _ _)) (Unitᵥ (Unitₜ _ _ _ UnitA _) _) =
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
combine (Idᵥ _ ⊩B) (Levelᵥ LevelA LevelB) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red LevelA , Levelₙ) of λ ()
combine (Idᵥ _ ⊩B) (Uᵥ (Uᵣ _ _ _ ⇒*U) UB) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⇒*U , Uₙ) of λ ()
combine (Idᵥ _ ⊩B) (ℕᵥ ⊩B′ _) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⊩B′ , ℕₙ) of λ ()
combine (Idᵥ _ ⊩B) (Emptyᵥ ⊩B′ _) =
  case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⊩B′ , Emptyₙ) of λ ()
combine (Idᵥ _ ⊩B) (Unitᵥ ⊩B′ _) =
  case
    whrDet*
      (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ)
      (red (_⊩Unit⟨_,_⟩_.⇒*-Unit ⊩B′) , Unitₙ)
  of λ ()
combine (Idᵥ _ ⊩B) (ne ⊩B′ _) =
  ⊥-elim $ Id≢ne N.neK $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red N.D , ne N.neK)
  where
  module N = _⊩ne_ ⊩B′
combine (Idᵥ _ ⊩B) (Bᵥ _ ⊩B′ _) =
  ⊥-elim $ Id≢⟦⟧▷ _ $
  whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red (_⊩ₗB⟨_⟩_.D ⊩B′) , ⟦ _ ⟧ₙ)
