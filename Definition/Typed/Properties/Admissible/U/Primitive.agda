------------------------------------------------------------------------
-- Admissible rules related to U
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.U.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open import Definition.Typed TR
open import Definition.Typed.Properties.Admissible.Level.Primitive TR

open import Definition.Untyped M hiding (wk)

private variable
  Γ       : Cons _ _
  l l₁ l₂ : Term _

opaque

  -- A variant of Uⱼ.

  ⊢U₀∷ : ⊢ Γ → Γ ⊢ U zeroᵘ ∷ U (sucᵘ zeroᵘ)
  ⊢U₀∷ ⊢Γ = Uⱼ (⊢zeroᵘ ⊢Γ)

opaque

  -- A variant of Uⱼ.

  ⊢U : Γ ⊢ l ∷Level → Γ ⊢ U l
  ⊢U ⊢l = univ (Uⱼ ⊢l)

opaque

  -- A variant of ⊢U.

  ⊢U₀ : ⊢ Γ → Γ ⊢ U zeroᵘ
  ⊢U₀ ⊢Γ = ⊢U (⊢zeroᵘ ⊢Γ)

opaque

  -- A variant of _⊢_≡_.U-cong.

  U-cong-⊢≡ : Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ U l₁ ≡ U l₂
  U-cong-⊢≡ (term _ l₁≡l₂)            = U-cong l₁≡l₂
  U-cong-⊢≡ (literal not-ok ⊢Γ l-lit) =
    refl (⊢U (literal not-ok ⊢Γ l-lit))

opaque

  -- A variant of _⊢_≡_∷_.U-cong.

  U-cong-⊢≡∷ : Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ U l₁ ≡ U l₂ ∷ U (sucᵘ l₁)
  U-cong-⊢≡∷ (term _ l₁≡l₂)            = U-cong l₁≡l₂
  U-cong-⊢≡∷ (literal not-ok ⊢Γ l-lit) =
    refl (Uⱼ (literal not-ok ⊢Γ l-lit))
