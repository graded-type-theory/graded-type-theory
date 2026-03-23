------------------------------------------------------------------------
-- Universe-level⁻
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Decidable.Internal.Universe-level
  {a} {M : Set a} {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Untyped.Sup TR

open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties.Admissible.Level TR
open import Definition.Typed.Properties.Well-formed TR
open import Definition.Typed.Reasoning.Level TR
open import Definition.Typed.Well-formed TR

open import Tools.Function
open import Tools.Nat as N
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  n : Nat
  Γ : Cons _ _

------------------------------------------------------------------------
-- The type

-- Universe-level without the top-most element.

data Universe-level⁻ : Set where
  0ᵘ+ ωᵘ+ : (m : Nat) → Universe-level⁻

private variable
  ℓ ℓ₁ ℓ₂ : Universe-level⁻

opaque

  -- The semantics of Universe-level⁻.

  ⌜_⌝⁻ : Universe-level⁻ → Lvl n
  ⌜ 0ᵘ+ m ⌝⁻ = level (↓ᵘ m)
  ⌜ ωᵘ+ m ⌝⁻ = ωᵘ+ m

------------------------------------------------------------------------
-- _≟_

-- Equality is decidable for Universe-level⁻.

_≟⁻_ : (ℓ₁ ℓ₂ : Universe-level⁻) → Dec (ℓ₁ PE.≡ ℓ₂)
0ᵘ+ m₁ ≟⁻ 0ᵘ+ m₂ =
  Dec-map (PE.cong 0ᵘ+ , (λ { PE.refl → PE.refl })) (m₁ N.≟ m₂)
0ᵘ+ _  ≟⁻ ωᵘ+ _  = no (λ ())
ωᵘ+ _  ≟⁻ 0ᵘ+ _  = no (λ ())
ωᵘ+ m₁ ≟⁻ ωᵘ+ m₂ =
  Dec-map (PE.cong ωᵘ+ , (λ { PE.refl → PE.refl })) (m₁ N.≟ m₂)

------------------------------------------------------------------------
-- 1+⁻

-- A successor operation for Universe-level⁻.

1+⁻ : Universe-level⁻ → Universe-level⁻
1+⁻ (0ᵘ+ m) = 0ᵘ+ (1+ m)
1+⁻ (ωᵘ+ m) = ωᵘ+ (1+ m)

opaque
  unfolding ⌜_⌝⁻ ↓ᵘ_

  -- ⌜_⌝⁻ commutes with 1+⁻/1ᵘ+ (for well-formed levels).

  ⊢⌜1+⁻⌝⁻≡ :
    Γ ⊢ ⌜ ℓ ⌝⁻ ∷Level →
    Γ ⊢ ⌜ 1+⁻ ℓ ⌝⁻ ≡ 1ᵘ+ ⌜ ℓ ⌝⁻ ∷Level
  ⊢⌜1+⁻⌝⁻≡ {ℓ = 0ᵘ+ _} ⊢ℓ = refl-⊢≡∷L (⊢1ᵘ+ ⊢ℓ)
  ⊢⌜1+⁻⌝⁻≡ {ℓ = ωᵘ+ _} ⊢ℓ = refl-⊢≡∷L (⊢1ᵘ+ ⊢ℓ)

------------------------------------------------------------------------
-- _⊔⁻_

-- Max for Universe-level⁻.

infixl 6 _⊔⁻_

_⊔⁻_ : (_ _ : Universe-level⁻) → Universe-level⁻
0ᵘ+ m ⊔⁻ 0ᵘ+ n = 0ᵘ+ (m ⊔ n)
0ᵘ+ _ ⊔⁻ ωᵘ+ n = ωᵘ+ n
ωᵘ+ m ⊔⁻ 0ᵘ+ _ = ωᵘ+ m
ωᵘ+ m ⊔⁻ ωᵘ+ n = ωᵘ+ (m ⊔ n)

opaque
  unfolding ⌜_⌝⁻ _supᵘₗ_

  -- ⌜_⌝⁻ commutes with _⊔⁻_/_supᵘₗ_ (for well-formed levels).

  ⊢⌜⊔⁻⌝⁻≡ :
    Γ ⊢ ⌜ ℓ₁ ⌝⁻ ∷Level →
    Γ ⊢ ⌜ ℓ₂ ⌝⁻ ∷Level →
    Γ ⊢ ⌜ ℓ₁ ⊔⁻ ℓ₂ ⌝⁻ ≡ ⌜ ℓ₁ ⌝⁻ supᵘₗ ⌜ ℓ₂ ⌝⁻ ∷Level
  ⊢⌜⊔⁻⌝⁻≡ {ℓ₁ = 0ᵘ+ m₁} {ℓ₂ = 0ᵘ+ m₂} ⊢ℓ₁ _ =
    level (↓ᵘ (m₁ N.⊔ m₂))             ≡˘⟨ supᵘₗ-↓ᵘ (wf ⊢ℓ₁) ⟩⊢∎
    level (↓ᵘ m₁) supᵘₗ level (↓ᵘ m₂)  ∎
  ⊢⌜⊔⁻⌝⁻≡ {ℓ₁ = 0ᵘ+ _} {ℓ₂ = ωᵘ+ m₂} _ ⊢ℓ₂ =
    ωᵘ+ m₂  ∎⟨ uncurry ⊢ωᵘ+ (inversion-ωᵘ+ ⊢ℓ₂) ⟩⊢
  ⊢⌜⊔⁻⌝⁻≡ {ℓ₁ = ωᵘ+ m₁} {ℓ₂ = 0ᵘ+ _} ⊢ℓ₁ _ =
    ωᵘ+ m₁  ∎⟨ uncurry ⊢ωᵘ+ (inversion-ωᵘ+ ⊢ℓ₁) ⟩⊢
  ⊢⌜⊔⁻⌝⁻≡ {ℓ₁ = ωᵘ+ m₁} {ℓ₂ = ωᵘ+ m₂} ⊢ℓ₁ _ =
    ωᵘ+ (m₁ N.⊔ m₂)  ∎⟨ uncurry ⊢ωᵘ+ (inversion-ωᵘ+ ⊢ℓ₁) ⟩⊢

opaque
  unfolding ⌜_⌝⁻

  -- ⌜ ℓ₁ ⊔⁻ ℓ₂ ⌝⁻ is well-formed if ⌜ ℓ₁ ⌝⁻ and ⌜ ℓ₂ ⌝⁻ are (for the
  -- same context).

  ⊢⌜⌝⁻ :
    Γ ⊢ ⌜ ℓ₁ ⌝⁻ ∷Level →
    Γ ⊢ ⌜ ℓ₂ ⌝⁻ ∷Level →
    Γ ⊢ ⌜ ℓ₁ ⊔⁻ ℓ₂ ⌝⁻ ∷Level
  ⊢⌜⌝⁻ ⊢ℓ₁ ⊢ℓ₂ = wf-⊢ (⊢⌜⊔⁻⌝⁻≡ ⊢ℓ₁ ⊢ℓ₂) .proj₁

------------------------------------------------------------------------
-- _≤⁻_

opaque

  -- An ordering relation for Universe-level⁻.

  infix 4 _≤⁻_

  _≤⁻_ : Universe-level⁻ → Universe-level⁻ → Set
  ℓ₁ ≤⁻ ℓ₂ = ℓ₁ ⊔⁻ ℓ₂ PE.≡ ℓ₂

opaque
  unfolding _≤⁻_

  -- Reflexivity.

  ≤⁻-refl : ℓ ≤⁻ ℓ
  ≤⁻-refl {ℓ = 0ᵘ+ _} = PE.cong 0ᵘ+ (N.⊔-idem _)
  ≤⁻-refl {ℓ = ωᵘ+ _} = PE.cong ωᵘ+ (N.⊔-idem _)
