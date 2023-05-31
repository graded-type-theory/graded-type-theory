------------------------------------------------------------------------
-- Function combinators
------------------------------------------------------------------------

module Tools.Function where

open import Function.Base
  using (case_of_; flip; _$_)
  renaming (id to idᶠ; _∘_ to _∘→_)
  public

open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality

private variable
  a b     : Level
  A B C D : Set _

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

-- Composition of logical equivalences.

infixr 9 _∘⇔_

_∘⇔_ : B ⇔ C → A ⇔ B → A ⇔ C
(f₁ , f₂) ∘⇔ (g₁ , g₂) = f₁ ∘→ g₁ , g₂ ∘→ f₂

-- "Equational" reasoning combinators for logical equivalence.

infix  -1 _□⇔
infixr -2 step-⇔ step-≡⇔

step-⇔ : (A : Set a) → (B ⇔ C) → (A ⇔ B) → A ⇔ C
step-⇔ _ f g = f ∘⇔ g

syntax step-⇔ A B⇔C A⇔B = A ⇔⟨ A⇔B ⟩ B⇔C

step-≡⇔ : (A : Set a) → (B ⇔ C) → A ≡ B → A ⇔ C
step-≡⇔ _ f refl = f

syntax step-≡⇔ A B⇔C A≡B = A ≡⟨ A≡B ⟩⇔ B⇔C

_□⇔ : (A : Set a) → A ⇔ A
_ □⇔ = id⇔

-- The operator _×_ preserves logical equivalences.

infixr 2 _×-cong-⇔_

_×-cong-⇔_ : A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
(f₁ , g₁) ×-cong-⇔ (f₂ , g₂) =
    (λ (x , y) → f₁ x , f₂ y)
  , (λ (x , y) → g₁ x , g₂ y)
