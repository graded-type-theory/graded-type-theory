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
  Γ       : Con Term _
  l l₁ l₂ : Term _

opaque

  -- A variant of Uⱼ.

  ⊢U₀∷ : ⊢ Γ → Γ ⊢ U zeroᵘ ∷ U (sucᵘ zeroᵘ)
  ⊢U₀∷ ⊢Γ = Uⱼ ⊢Γ (⊢zeroᵘ ⊢Γ)

opaque

  -- A variant of Uⱼ.

  ⊢U : ⊢ Γ → Γ ⊢ l ∷Level → Γ ⊢ U l
  ⊢U ⊢Γ ⊢l = univ (Uⱼ ⊢Γ ⊢l)

opaque

  -- A variant of ⊢U.

  ⊢U₀ : ⊢ Γ → Γ ⊢ U zeroᵘ
  ⊢U₀ ⊢Γ = ⊢U ⊢Γ (⊢zeroᵘ ⊢Γ)

opaque

  -- A variant of _⊢_≡_.U-cong.

  U-cong-⊢≡ : ⊢ Γ → Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ U l₁ ≡ U l₂
  U-cong-⊢≡ _  (term _ l₁≡l₂)         = U-cong l₁≡l₂
  U-cong-⊢≡ ⊢Γ (literal not-ok l-lit) =
    refl (⊢U ⊢Γ (literal not-ok l-lit))

opaque

  -- A variant of _⊢_≡_∷_.U-cong.

  U-cong-⊢≡∷ : ⊢ Γ → Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ U l₁ ≡ U l₂ ∷ U (sucᵘ l₁)
  U-cong-⊢≡∷ _  (term _ l₁≡l₂)         = U-cong l₁≡l₂
  U-cong-⊢≡∷ ⊢Γ (literal not-ok l-lit) =
    refl (Uⱼ ⊢Γ (literal not-ok l-lit))
