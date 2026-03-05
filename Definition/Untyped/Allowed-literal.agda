------------------------------------------------------------------------
-- Lemmas related to Allowed-literal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Untyped.Allowed-literal
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  m m₁ m₂ n : Nat
  X         : Set _
  ξ         : DExt _ _ _
  t         : Term _
  l         : Lvl _

opaque
  unfolding Allowed-literal

  -- If l is an allowed literal, then l is a literal.

  Allowed-literal→Level-literal : Allowed-literal l → Level-literal l
  Allowed-literal→Level-literal {l = ωᵘ+ _}   _           = ωᵘ+
  Allowed-literal→Level-literal {l = level _} (t-lit , _) = level t-lit

opaque
  unfolding Allowed-literal→Level-literal Level-literal→Universe-level

  -- A function that converts from Allowed-literal to Universe-level.

  Allowed-literal→Universe-level : Allowed-literal l → Universe-level
  Allowed-literal→Universe-level {l} =
    Level-literal→Universe-level {l = l} ∘→
    Allowed-literal→Level-literal

opaque
  unfolding Allowed-literal→Level-literal

  -- Irrelevance for Allowed-literal→Level-literal.

  Allowed-literal→Level-literal-irrelevance :
    {l₁ l₂ : Allowed-literal l} →
    Allowed-literal→Level-literal l₁ ≡
    Allowed-literal→Level-literal l₂
  Allowed-literal→Level-literal-irrelevance {l = ωᵘ+ _}   = refl
  Allowed-literal→Level-literal-irrelevance {l = level _} =
    cong level Level-literal-propositional

opaque
  unfolding Allowed-literal→Universe-level

  -- Irrelevance for Allowed-literal→Universe-level.

  Allowed-literal→Universe-level-irrelevance :
    {l₁ l₂ : Allowed-literal l} →
    Allowed-literal→Universe-level l₁ ≡
    Allowed-literal→Universe-level l₂
  Allowed-literal→Universe-level-irrelevance =
    cong Level-literal→Universe-level
      Allowed-literal→Level-literal-irrelevance

opaque
  unfolding Allowed-literal

  -- The literal ωᵘ+ m is allowed if and only if Omega-plus-allowed
  -- holds.

  Allowed-literal-ωᵘ+-⇔ :
    Allowed-literal {n = n} (ωᵘ+ m) ⇔ Omega-plus-allowed
  Allowed-literal-ωᵘ+-⇔ = id⇔

opaque

  -- The literal ωᵘ+ m₂ is allowed if ωᵘ+ m₁ is.

  Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ :
    Allowed-literal {n = n} (ωᵘ+ m₁) → Allowed-literal {n = n} (ωᵘ+ m₂)
  Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ {m₁} {m₂} =
    Allowed-literal (ωᵘ+ m₁)  ⇔⟨ Allowed-literal-ωᵘ+-⇔ ⟩→
    Omega-plus-allowed        ⇔˘⟨ Allowed-literal-ωᵘ+-⇔ ⟩→
    Allowed-literal (ωᵘ+ m₂)  □

opaque
  unfolding Allowed-literal

  -- The level level t is allowed as a literal if and only if it is a
  -- literal and Level is not allowed.

  Allowed-literal-level-⇔ :
    Allowed-literal (level t) ⇔ (Level-literal t × ¬ Level-allowed)
  Allowed-literal-level-⇔ = id⇔

opaque
  unfolding Allowed-literal Level-literal-1ᵘ+-⇔

  -- The level 1ᵘ+ l is an allowed literal if and only if l is.

  Allowed-literal-1ᵘ+-⇔ :
    Allowed-literal (1ᵘ+ l) ⇔ Allowed-literal l
  Allowed-literal-1ᵘ+-⇔ {l = ωᵘ+ _}   = id⇔
  Allowed-literal-1ᵘ+-⇔ {l = level _} =
    Level-literal-1ᵘ+-⇔ ×-cong-⇔ id⇔

opaque
  unfolding Allowed-literal inline

  -- The level inline ξ l is an allowed literal if l is.

  Allowed-literal-inline :
    Allowed-literal l → Allowed-literal (inline ξ l)
  Allowed-literal-inline {l = ωᵘ+ _}   = idᶠ
  Allowed-literal-inline {l = level _} =
    Σ.map Level-literal-inline idᶠ

opaque

  -- If Level is allowed and l is allowed as a literal, then l is
  -- infinite.

  Allowed-literal→Infinite :
    Level-allowed → Allowed-literal l → Infinite l
  Allowed-literal→Infinite {l = ωᵘ+ _}   _   _   = ωᵘ+
  Allowed-literal→Infinite {l = level _} ok₁ ok₂ =
    ⊥-elim (Allowed-literal-level-⇔ .proj₁ ok₂ .proj₂ ok₁)

opaque

  -- If Level is allowed and Allowed-literal (level t) holds, then
  -- anything can be derived.

  Level-allowed→Allowed-literal→ :
    Level-allowed → Allowed-literal (level t) → X
  Level-allowed→Allowed-literal→ okᴸ ok =
    case Allowed-literal→Infinite okᴸ ok of λ ()

opaque

  -- If l is an allowed literal, then either Level is not allowed or l
  -- is infinite.

  Allowed-literal→¬Level-allowed⊎Infinite :
    Allowed-literal l → ¬ Level-allowed ⊎ Infinite l
  Allowed-literal→¬Level-allowed⊎Infinite {l = ωᵘ+ m}   _  = inj₂ ωᵘ+
  Allowed-literal→¬Level-allowed⊎Infinite {l = level t} ok =
    inj₁ (Allowed-literal-level-⇔ .proj₁ ok .proj₂)
