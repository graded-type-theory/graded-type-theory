------------------------------------------------------------------------
-- Function combinators
------------------------------------------------------------------------

module Tools.Function where

open import Function.Base
  using (case_of_; flip; _$_; _∋_)
  renaming (id to idᶠ; _∘_ to _∘→_)
  public
open import Relation.Nullary.Decidable public
  using (_→-dec_)

open import Tools.Empty
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

private variable
  a b p   : Level
  A B C D : Set _
  P Q     : A → Set _
  y       : A
  f g     : (x : A) → P x

-- Function composition (simply typed variant)
_∘ᶠ_ : ∀ {ℓ} → {A B C : Set ℓ} → (B → C) → (A → B) → A → C
_∘ᶠ_ f g a = f (g a)

-- "Equational" reasoning combinators.

infix  -1 _□
infixr -2 step-→ step-≡→
infix  -3 $⟨_⟩_

step-→ : (A : Set a) → (B → C) → (A → B) → A → C
step-→ _ f g = f ∘→ g

syntax step-→ A B→C A→B = A →⟨ A→B ⟩ B→C

step-≡→ : (A : Set a) → (B → C) → A ≡ B → A → C
step-≡→ _ f refl = f

syntax step-≡→ A B→C A≡B = A ≡⟨ A≡B ⟩→ B→C

_□ : (A : Set a) → A → A
_ □ = idᶠ

$⟨_⟩_ : A → (A → B) → B
$⟨ x ⟩ f = f x

-- Logical equivalence.

infix 3 _⇔_

_⇔_ : Set a → Set b → Set (a ⊔ b)
A ⇔ B = (A → B) × (B → A)

-- The identity logical equivalence.

id⇔ : A ⇔ A
id⇔ = idᶠ , idᶠ

-- The relation _⇔_ is symmetric.

sym⇔ : A ⇔ B → B ⇔ A
sym⇔ (f , g) = g , f

-- Composition of logical equivalences.

infixr 9 _∘⇔_

_∘⇔_ : B ⇔ C → A ⇔ B → A ⇔ C
(f₁ , f₂) ∘⇔ (g₁ , g₂) = f₁ ∘→ g₁ , g₂ ∘→ f₂

-- "Equational" reasoning combinators related to logical equivalence.

infix  -1 _□⇔
infixr -2 step-⇔ step-⇔˘ step-⇔→ step-⇔˘→ step-≡⇔ step-≡˘⇔

step-⇔ : (A : Set a) → (B ⇔ C) → (A ⇔ B) → A ⇔ C
step-⇔ _ f g = f ∘⇔ g

syntax step-⇔ A B⇔C A⇔B = A ⇔⟨ A⇔B ⟩ B⇔C

step-⇔˘ : (A : Set a) → (B ⇔ C) → (B ⇔ A) → A ⇔ C
step-⇔˘ _ f g = f ∘⇔ sym⇔ g

syntax step-⇔˘ A B⇔C A⇔B = A ⇔˘⟨ A⇔B ⟩ B⇔C

step-⇔→ : (A : Set a) → (B → C) → A ⇔ B → A → C
step-⇔→ _ f g = f ∘→ g .proj₁

syntax step-⇔→ A B→C A⇔B = A ⇔⟨ A⇔B ⟩→ B→C

step-⇔˘→ : (A : Set a) → (B → C) → B ⇔ A → A → C
step-⇔˘→ _ f g = f ∘→ g .proj₂

syntax step-⇔˘→ A B→C B⇔A = A ⇔˘⟨ B⇔A ⟩→ B→C

step-≡⇔ : (A : Set a) → (B ⇔ C) → A ≡ B → A ⇔ C
step-≡⇔ _ f refl = f

syntax step-≡⇔ A B⇔C A≡B = A ≡⟨ A≡B ⟩⇔ B⇔C

step-≡˘⇔ : (A : Set a) → (B ⇔ C) → B ≡ A → A ⇔ C
step-≡˘⇔ _ f refl = f

syntax step-≡˘⇔ A B⇔C A≡B = A ≡˘⟨ A≡B ⟩⇔ B⇔C

_□⇔ : (A : Set a) → A ⇔ A
_ □⇔ = id⇔

-- The operator _⇔_ preserves logical equivalences.

infix 3 _⇔-cong-⇔_

_⇔-cong-⇔_ : A ⇔ B → C ⇔ D → (A ⇔ C) ⇔ (B ⇔ D)
_⇔-cong-⇔_ {A = A} {B = B} {C = C} {D = D} A⇔B C⇔D =
    (λ A⇔C →
       B  ⇔˘⟨ A⇔B ⟩
       A  ⇔⟨ A⇔C ⟩
       C  ⇔⟨ C⇔D ⟩
       D  □⇔)
  , (λ B⇔D →
       A  ⇔⟨ A⇔B ⟩
       B  ⇔⟨ B⇔D ⟩
       D  ⇔˘⟨ C⇔D ⟩
       C  □⇔)

-- The non-dependent function space preserves logical equivalences.

infixr 3 _→-cong-⇔_

_→-cong-⇔_ : A ⇔ B → C ⇔ D → (A → C) ⇔ (B → D)
_→-cong-⇔_ {A = A} {B = B} {C = C} {D = D} A⇔B C⇔D =
    (λ A→C →
       B  →⟨ A⇔B .proj₂ ⟩
       A  →⟨ A→C ⟩
       C  →⟨ C⇔D .proj₁ ⟩
       D  □)
  , (λ B→D →
       A  →⟨ A⇔B .proj₁ ⟩
       B  →⟨ B→D ⟩
       D  →⟨ C⇔D .proj₂ ⟩
       C  □)

-- Π A preserves logical equivalences.

Π-cong-⇔ : (∀ x → P x ⇔ Q x) → ((x : A) → P x) ⇔ ((x : A) → Q x)
Π-cong-⇔ eq =
    (λ f x → eq x .proj₁ (f x))
  , (λ f x → eq x .proj₂ (f x))

-- The implicit variant of Π A preserves logical equivalences.

implicit-Π-cong-⇔ :
  (∀ x → P x ⇔ Q x) → ({x : A} → P x) ⇔ ({x : A} → Q x)
implicit-Π-cong-⇔ eq =
    (λ f → eq _ .proj₁ f)
  , (λ f → eq _ .proj₂ f)

-- Σ A preserves logical equivalences.

Σ-cong-⇔ : (∀ x → P x ⇔ Q x) → Σ A P ⇔ Σ A Q
Σ-cong-⇔ eq =
    (λ (x , y) → x , eq x .proj₁ y)
  , (λ (x , y) → x , eq x .proj₂ y)

-- The operator _×_ preserves logical equivalences.

infixr 2 _×-cong-⇔_

_×-cong-⇔_ : A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
(f₁ , g₁) ×-cong-⇔ (f₂ , g₂) =
    (λ (x , y) → f₁ x , f₂ y)
  , (λ (x , y) → g₁ x , g₂ y)

-- The operator _⊎_ preserves logical equivalences.

infixr 1 _⊎-cong-⇔_

_⊎-cong-⇔_ : A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
A⇔B ⊎-cong-⇔ C⇔D =
    (λ where
       (inj₁ x) → inj₁ (A⇔B .proj₁ x)
       (inj₂ x) → inj₂ (C⇔D .proj₁ x))
  , (λ where
       (inj₁ x) → inj₁ (A⇔B .proj₂ x)
       (inj₂ x) → inj₂ (C⇔D .proj₂ x))

-- The operator _⊎_ is commutative up to _⇔_.

⊎-comm-⇔ : (A ⊎ B) ⇔ (B ⊎ A)
⊎-comm-⇔ = ⊎.sym , ⊎.sym

-- The operator _⊎_ is associative up to _⇔_.

⊎-assoc-⇔ : ((A ⊎ B) ⊎ C) ⇔ (A ⊎ (B ⊎ C))
⊎-assoc-⇔ =
    (λ where
       (inj₁ (inj₁ x)) → inj₁ x
       (inj₁ (inj₂ x)) → inj₂ (inj₁ x)
       (inj₂ x)        → inj₂ (inj₂ x))
  , (λ where
       (inj₁ x)        → inj₁ (inj₁ x)
       (inj₂ (inj₁ x)) → inj₁ (inj₂ x)
       (inj₂ (inj₂ x)) → inj₂ x)

-- The operator _⊎_ is idempotent up to _⇔_.

⊎-idem-⇔ : (A ⊎ A) ⇔ A
⊎-idem-⇔ = (λ { (inj₁ x) → x; (inj₂ x) → x }) , inj₁

-- The type ∀ x → P x ⇔ x ≡ y is logically equivalent to
-- P y × ∀ x → P x → x ≡ y.

Π⇔≡⇔ : (∀ x → P x ⇔ x ≡ y) ⇔ (P y × ∀ x → P x → x ≡ y)
Π⇔≡⇔ =
    (λ f → f _ .proj₂ refl , λ _ → f _ .proj₁)
  , (λ (p , f) _ → f _ , λ { refl → p })

-- If two functions are equal, then they are pointwise equal.

ext⁻¹ : f ≡ g → (∀ x → f x ≡ g x)
ext⁻¹ refl _ = refl

-- A statement of function extensionality.
--
-- The statement is based on the one in the HoTT book.

Function-extensionality : (a p : Level) → Set (lsuc (a ⊔ p))
Function-extensionality a p =
  {A : Set a} {P : A → Set p} {f g : (x : A) → P x} →
  Is-equivalence (ext⁻¹ {f = f} {g = g})
  where
  Is-equivalence :
    ∀ {a b} {A : Set a} {B : Set b} →
    (A → B) → Set (a ⊔ b)
  Is-equivalence {A = A} {B = B} f =
    ∃ λ (f⁻¹ : B → A) →
    ∃ λ (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
    ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
    ∀ x → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x)

-- If function extensionality holds, then pointwise equal functions
-- are equal.

ext :
  {A : Set a} {P : A → Set p} {f g : (x : A) → P x} →
  Function-extensionality a p →
  (∀ x → f x ≡ g x) → f ≡ g
ext fe = fe .proj₁

-- Is-proposition is closed under Π A (assuming function
-- extensionality).

Is-proposition-Π :
  {A : Set a} {P : A → Set p} →
  Function-extensionality a p →
  (∀ x → Is-proposition (P x)) →
  Is-proposition (∀ x → P x)
Is-proposition-Π fe prop = ext fe λ _ → prop _

-- If A is a proposition, then Dec A is a proposition, assuming
-- function extensionality.

Is-proposition-Dec :
  {A : Set a} →
  Function-extensionality a lzero →
  Is-proposition A → Is-proposition (Dec A)
Is-proposition-Dec = λ where
  _  prop {x = yes x} {y = yes y} → cong yes prop
  _  _    {x = yes x} {y = no y}  → ⊥-elim (y x)
  _  _    {x = no x}  {y = yes y} → ⊥-elim (x y)
  fe _    {x = no x}  {y = no y}  →
    cong no (Is-proposition-Π fe λ _ → ⊥-propositional)
