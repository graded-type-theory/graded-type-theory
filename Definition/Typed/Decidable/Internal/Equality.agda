------------------------------------------------------------------------
-- Term equality tests used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Decidable.Internal.Equality
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed.Decidable.Internal.Term 𝐌 R

import Definition.Untyped M as U

open import Tools.Fin as Fin
open import Tools.Maybe
open import Tools.Nat as N using (Nat)
open import Tools.PropositionalEquality
import Tools.Vec as Vec

private variable
  m n : Nat
  c   : Constants

-- Are the two grade terms syntactically equal?

infix 4 _≟ᵍ_

_≟ᵍ_ : (t₁ t₂ : Termᵍ n) → Maybe (t₁ ≡ t₂)
var x ≟ᵍ var y =
  cong var <$> dec⇒maybe (x ≟ⱽ y)
𝟘 ≟ᵍ 𝟘 =
  just refl
𝟙 ≟ᵍ 𝟙 =
  just refl
ω ≟ᵍ ω =
  just refl
t₁₁ + t₁₂ ≟ᵍ t₂₁ + t₂₂ =
  cong₂ _+_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
t₁₁ · t₁₂ ≟ᵍ t₂₁ · t₂₂ =
  cong₂ _·_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
t₁₁ ∧ t₁₂ ≟ᵍ t₂₁ ∧ t₂₂ =
  cong₂ _∧_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
⌜⌞ t₁ ⌟⌝ ≟ᵍ ⌜⌞ t₂ ⌟⌝ =
  cong ⌜⌞_⌟⌝ <$> t₁ ≟ᵍ t₂
_ ≟ᵍ _ =
  nothing

-- Are the two strength terms syntactically equal?

infix 4 _≟ˢ_

_≟ˢ_ : (t₁ t₂ : Termˢ n) → Maybe (t₁ ≡ t₂)
var x ≟ˢ var y =
  cong var <$> dec⇒maybe (x ≟ⱽ y)
𝕤 ≟ˢ 𝕤 =
  just refl
𝕨 ≟ˢ 𝕨 =
  just refl
_ ≟ˢ _ =
  nothing

-- Are the two binder mode terms syntactically equal?

infix 4 _≟ᵇᵐ_

_≟ᵇᵐ_ : (t₁ t₂ : Termᵇᵐ m n) → Maybe (t₁ ≡ t₂)
var x ≟ᵇᵐ var y =
  cong var <$> dec⇒maybe (x ≟ⱽ y)
BMΠ ≟ᵇᵐ BMΠ =
  just refl
BMΣ s₁ ≟ᵇᵐ BMΣ s₂ =
  cong BMΣ <$> s₁ ≟ˢ s₂
_ ≟ᵇᵐ _ =
  nothing
