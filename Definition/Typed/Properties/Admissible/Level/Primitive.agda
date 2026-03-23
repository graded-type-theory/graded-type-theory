------------------------------------------------------------------------
-- Admissible rules for Level as well as some lemmas related to
-- _⊢_≡_∷Level
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Level.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎

private variable
  m                          : Nat
  Γ                          : Cons _ _
  A B t t₁ t₂                : Term _
  l l₁ l₁₁ l₁₂ l₂ l₂₁ l₂₂ l₃ : Lvl _

------------------------------------------------------------------------
-- A lemma related to Level

opaque
  unfolding Level-allowed Level-is-small Level-is-not-small

  -- A variant of _⊢_.Levelⱼ.

  Levelⱼ′ : Level-allowed → ⊢ Γ → Γ ⊢ Level
  Levelⱼ′ ok ⊢Γ with level-support in eq
  … | only-literals        = ⊥-elim (ok PE.refl)
  … | level-type small     = univ (Levelⱼ ⊢Γ eq)
  … | level-type not-small = Levelⱼ eq ⊢Γ

------------------------------------------------------------------------
-- Lemmas related to zeroᵘ, sucᵘ and ωᵘ+

opaque
  unfolding Level-allowed

  -- A variant of zeroᵘⱼ.

  ⊢zeroᵘ : ⊢ Γ → Γ ⊢ zeroᵘₗ ∷Level
  ⊢zeroᵘ ⊢Γ with level-support in eq
  … | only-literals =
    literal (Allowed-literal-level-⇔ .proj₂ (zeroᵘ , (_$ eq))) ⊢Γ
  … | level-type _ =
    let ok = λ eq′ → case PE.trans (PE.sym eq) eq′ of λ () in
    term ok (zeroᵘⱼ ok ⊢Γ)

opaque

  -- A variant of sucᵘⱼ.

  ⊢1ᵘ+ : Γ ⊢ l ∷Level → Γ ⊢ 1ᵘ+ l ∷Level
  ⊢1ᵘ+ (term ok ⊢l)    = term ok (sucᵘⱼ ⊢l)
  ⊢1ᵘ+ (literal ok ⊢Γ) = literal (Allowed-literal-1ᵘ+-⇔ .proj₂ ok) ⊢Γ

opaque

  -- An admissible typing rule for ωᵘ+.

  ⊢ωᵘ+ :
    Omega-plus-allowed →
    ⊢ Γ →
    Γ ⊢ ωᵘ+ m ∷Level
  ⊢ωᵘ+ ok ⊢Γ =
    literal (Allowed-literal-ωᵘ+-⇔ .proj₂ ok) ⊢Γ

------------------------------------------------------------------------
-- A lemma related to Level-literal

opaque

  -- If l is a level literal and, if l is infinite, then infinite
  -- levels are allowed, then l is a well-formed level in well-formed
  -- contexts.

  Level-literal→⊢∷L :
    ⊢ Γ → Level-literal l →
    (Infinite l → Omega-plus-allowed) →
    Γ ⊢ l ∷Level
  Level-literal→⊢∷L ⊢Γ ωᵘ+ ok =
    ⊢ωᵘ+ (ok ωᵘ+) ⊢Γ
  Level-literal→⊢∷L ⊢Γ (level zeroᵘ) _ =
    ⊢zeroᵘ ⊢Γ
  Level-literal→⊢∷L ⊢Γ (level (sucᵘ lit)) _ =
    ⊢1ᵘ+ (Level-literal→⊢∷L ⊢Γ (level lit) (λ ()))

------------------------------------------------------------------------
-- Some lemmas related to _⊢_∷Level or _⊢_≡_∷Level

opaque

  -- Reflexivity for _⊢_≡_∷Level.

  refl-⊢≡∷L : Γ ⊢ l ∷Level → Γ ⊢ l ≡ l ∷Level
  refl-⊢≡∷L (term ok ⊢l)    = term ok (refl ⊢l)
  refl-⊢≡∷L (literal ok ⊢Γ) = literal ok ⊢Γ

opaque

  -- Symmetry for _⊢_≡_∷Level.

  sym-⊢≡∷L : Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₂ ≡ l₁ ∷Level
  sym-⊢≡∷L (term ok l₁≡l₂) =
    term ok (sym (Levelⱼ′ ok (wf l₁≡l₂)) l₁≡l₂)
  sym-⊢≡∷L (literal ok ⊢Γ) =
    literal ok ⊢Γ

opaque

  -- Transitivity for _⊢_≡_∷Level.

  trans-⊢≡∷L :
    Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₂ ≡ l₃ ∷Level → Γ ⊢ l₁ ≡ l₃ ∷Level
  trans-⊢≡∷L (term ok l₁≡l₂) (term _ l₂≡l₃) =
    term ok (trans l₁≡l₂ l₂≡l₃)
  trans-⊢≡∷L (term ok₁ _) (literal ok₂ _) =
    ⊥-elim (Allowed-literal-level-⇔ .proj₁ ok₂ .proj₂ ok₁)
  trans-⊢≡∷L (literal ok₁ _) (term ok₂ _) =
    ⊥-elim (Allowed-literal-level-⇔ .proj₁ ok₁ .proj₂ ok₂)
  trans-⊢≡∷L (literal ok ⊢Γ) (literal _ _) =
    literal ok ⊢Γ

------------------------------------------------------------------------
-- A lemma related to _supᵘ_

opaque

  -- The level zeroᵘ is a right unit for _supᵘ_ (if Level is allowed).

  supᵘ-zeroʳⱼ :
    Level-allowed →
    Γ ⊢ t ∷ Level →
    Γ ⊢ t supᵘ zeroᵘ ≡ t ∷ Level
  supᵘ-zeroʳⱼ ok ⊢l =
    trans (supᵘ-comm ⊢l (zeroᵘⱼ ok (wf ⊢l))) (supᵘ-zeroˡ ⊢l)

------------------------------------------------------------------------
-- Some lemmas related to _supᵘₗ_

opaque
  unfolding _supᵘₗ_

  -- A variant of supᵘⱼ.

  ⊢supᵘₗ : Γ ⊢ l₁ ∷Level → Γ ⊢ l₂ ∷Level → Γ ⊢ l₁ supᵘₗ l₂ ∷Level
  ⊢supᵘₗ (term ok ⊢l₁) (term _ ⊢l₂) =
    PE.subst (_⊢_∷Level _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘⱼ ⊢l₁ ⊢l₂)
  ⊢supᵘₗ (term ok₁ _) (literal ok₂ ⊢Γ)
    with Allowed-literal→Infinite ok₁ ok₂
  … | ωᵘ+ = literal ok₂ ⊢Γ
  ⊢supᵘₗ (literal ok₁ ⊢Γ) (term ok₂ _)
    with Allowed-literal→Infinite ok₂ ok₁
  … | ωᵘ+ = literal ok₁ ⊢Γ
  ⊢supᵘₗ (literal ok₁ ⊢Γ) (literal ok₂ _) =
    literal (Allowed-literal-supᵘₗ ok₁ ok₂) ⊢Γ

opaque
  unfolding _supᵘₗ_

  -- The operator _supᵘₗ_ preserves equality.

  supᵘₗ-cong :
    Γ ⊢ l₁₁ ≡ l₂₁ ∷Level →
    Γ ⊢ l₁₂ ≡ l₂₂ ∷Level →
    Γ ⊢ l₁₁ supᵘₗ l₁₂ ≡ l₂₁ supᵘₗ l₂₂ ∷Level
  supᵘₗ-cong (term ok l₁₁≡l₂₁) (term _ l₁₂≡l₂₂) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡supᵘ ok) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-cong l₁₁≡l₂₁ l₁₂≡l₂₂)
  supᵘₗ-cong (term ok₁ _) (literal ok₂ ⊢Γ)
    with Allowed-literal→Infinite ok₁ ok₂
  … | ωᵘ+ = literal ok₂ ⊢Γ
  supᵘₗ-cong (literal ok₁ ⊢Γ) (term ok₂ _)
    with Allowed-literal→Infinite ok₂ ok₁
  … | ωᵘ+ = literal ok₁ ⊢Γ
  supᵘₗ-cong (literal ok₁ ⊢Γ) (literal ok₂ _) =
    literal (Allowed-literal-supᵘₗ ok₁ ok₂) ⊢Γ

opaque
  unfolding _supᵘₗ_

  -- The operator _supᵘₗ_ is commutative.

  supᵘₗ-comm :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ l₁ supᵘₗ l₂ ≡ l₂ supᵘₗ l₁ ∷Level
  supᵘₗ-comm (term ok ⊢l₁) (term _ ⊢l₂) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡supᵘ ok) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-comm ⊢l₁ ⊢l₂)
  supᵘₗ-comm (term ok₁ _) (literal ok₂ ⊢Γ)
    with Allowed-literal→Infinite ok₁ ok₂
  … | ωᵘ+ = literal ok₂ ⊢Γ
  supᵘₗ-comm (literal ok₁ ⊢Γ) (term ok₂ _)
    with Allowed-literal→Infinite ok₂ ok₁
  … | ωᵘ+ = literal ok₁ ⊢Γ
  supᵘₗ-comm ⊢l₁@(literal ok₁ _) ⊢l₂@(literal ok₂ _) =
    PE.subst (_⊢_≡_∷Level _ _)
      (Level-literal→supᵘₗ-comm
         (⊎.map idᶠ inj₁ (Allowed-literal→¬Level-allowed⊎Infinite ok₁))
         (Allowed-literal→Level-literal ok₁)
         (Allowed-literal→Level-literal ok₂)) $
    refl-⊢≡∷L (⊢supᵘₗ ⊢l₁ ⊢l₂)

opaque
  unfolding _supᵘₗ_ size-of-Level

  -- The level zeroᵘₗ is a left identity for _supᵘₗ_.

  supᵘₗ-identityˡ :
    Γ ⊢ l ∷Level →
    Γ ⊢ zeroᵘₗ supᵘₗ l ≡ l ∷Level
  supᵘₗ-identityˡ (term ok ⊢l) =
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-zeroˡ ⊢l)
  supᵘₗ-identityˡ ⊢l@(literal ok ⊢Γ) =
    PE.subst (_⊢_≡_∷Level _ _)
      (Level-literal→zeroᵘₗ-supᵘₗ
         (Allowed-literal→¬Level-allowed⊎Infinite ok)
         (Allowed-literal→Level-literal ok)) $
    refl-⊢≡∷L (⊢supᵘₗ (⊢zeroᵘ ⊢Γ) ⊢l)

------------------------------------------------------------------------
-- Some lemmas related to _⊢_∷Level, _⊢_≡_∷Level or _⊢_≤ₗ_∷Level

opaque

  -- If Γ ⊢ level t ∷Level holds and Level is allowed, then
  -- Γ ⊢ t ∷ Level holds.

  ⊢∷Level→⊢∷Level :
    Level-allowed →
    Γ ⊢ level t ∷Level →
    Γ ⊢ t ∷ Level
  ⊢∷Level→⊢∷Level _   (term _ ⊢t)     = ⊢t
  ⊢∷Level→⊢∷Level ok₁ (literal ok₂ _) =
    Level-allowed→Allowed-literal→ ok₁ ok₂

opaque

  -- If Γ ⊢ level t₁ ≡ level t₂ ∷Level holds and Level is allowed, then
  -- Γ ⊢ t₁ ≡ t₂ ∷ Level holds.

  ⊢≡∷Level→⊢≡∷Level :
    Level-allowed →
    Γ ⊢ level t₁ ≡ level t₂ ∷Level →
    Γ ⊢ t₁ ≡ t₂ ∷ Level
  ⊢≡∷Level→⊢≡∷Level _   (term _ t₁≡t₂)  = t₁≡t₂
  ⊢≡∷Level→⊢≡∷Level ok₁ (literal ok₂ _) =
    Level-allowed→Allowed-literal→ ok₁ ok₂

opaque
  unfolding _⊢_≤ₗ_∷Level _supᵘₗ_

  -- If Γ ⊢ level t₁ ≤ₗ level t₂ ∷Level holds and Level is allowed,
  -- then Γ ⊢ t₁ ≤ t₂ ∷Level holds.

  ⊢≤ₗ∷Level→⊢≤∷Level :
    Level-allowed →
    Γ ⊢ level t₁ ≤ₗ level t₂ ∷Level →
    Γ ⊢ t₁ ≤ t₂ ∷Level
  ⊢≤ₗ∷Level→⊢≤∷Level ok (_ , t₁≤t₂) = ⊢≤ₗ∷Level→⊢≤∷Level′ t₁≤t₂ PE.refl
    where
    ⊢≤ₗ∷Level→⊢≤∷Level′ :
      Γ ⊢ l ≡ level t₂ ∷Level →
      l PE.≡ level t₁ supᵘₗ level t₂ →
      Γ ⊢ t₁ ≤ t₂ ∷Level
    ⊢≤ₗ∷Level→⊢≤∷Level′ {t₂} {t₁} (term {t₁ = t₁′} _ t₁≤t₂) eq =
      PE.subst₃ (_⊢_≡_∷_ _)
        (level-PE-injectivity
           (level t₁′                ≡⟨ eq ⟩
            level t₁ supᵘₗ level t₂  ≡⟨ supᵘₗ≡supᵘ ok ⟩
            level (t₁ supᵘ t₂)       ∎))
        PE.refl PE.refl t₁≤t₂
    ⊢≤ₗ∷Level→⊢≤∷Level′ (literal ok′ _) _ =
      Level-allowed→Allowed-literal→ ok ok′
