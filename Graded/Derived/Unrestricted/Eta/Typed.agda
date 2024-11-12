------------------------------------------------------------------------
-- Some properties related to typing and Unrestricted
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions

module Graded.Derived.Unrestricted.Eta.Typed
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Strong unit types are assumed to be allowed.
  (Unit-ok : Unitˢ-allowed)
  -- It is assumed that strong Σ-types are allowed for the quantities
  -- ω and ω.
  (Σˢ-ok : Σˢ-allowed ω ω)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M hiding (_[_])
open import Graded.Derived.Unrestricted.Eta.Untyped 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private variable
  Γ       : Con Term _
  A B t u : Term _
  l       : Universe-level

------------------------------------------------------------------------
-- Typing rules

-- A formation rule for Unrestricted.

Unrestrictedⱼ : Γ ⊢ A → Γ ⊢ Unrestricted A
Unrestrictedⱼ ⊢A = ΠΣⱼ (Unitⱼ (∙ ⊢A) Unit-ok) Σˢ-ok

-- A corresponding congruence rule.

Unrestricted-cong :
  Γ ⊢ A ≡ B →
  Γ ⊢ Unrestricted A ≡ Unrestricted B
Unrestricted-cong A≡B =
  ΠΣ-cong A≡B (refl (Unitⱼ (∙ ⊢A) Unit-ok)) Σˢ-ok
  where
  ⊢A = syntacticEq A≡B .proj₁

-- An introduction rule for U.

Unrestrictedⱼ-U : Γ ⊢ A ∷ U l → Γ ⊢ Unrestricted A ∷ U l
Unrestrictedⱼ-U ⊢A∷U = ΠΣⱼ ⊢A∷U (Unitⱼ (∙ ⊢A) Unit-ok) Σˢ-ok
  where
  ⊢A = univ ⊢A∷U

-- A corresponding congruence rule.

Unrestricted-cong-U :
  Γ ⊢ A ≡ B ∷ U l →
  Γ ⊢ Unrestricted A ≡ Unrestricted B ∷ U l
Unrestricted-cong-U A≡B =
  ΠΣ-cong A≡B (refl (Unitⱼ (∙ ⊢A) Unit-ok)) Σˢ-ok
  where
  ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

-- An introduction rule for Unrestricted.

[]ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Unrestricted A
[]ⱼ ⊢t = prodⱼ (Unitⱼ (∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) Σˢ-ok
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- A corresponding congruence rule.

[]-cong′ :
  Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Unrestricted A
[]-cong′ t≡u =
  prod-cong (Unitⱼ (∙ ⊢A) Unit-ok) t≡u (refl (starⱼ (wf ⊢A) Unit-ok))
    Σˢ-ok
  where
  ⊢A = syntacticEqTerm t≡u .proj₁

-- An elimination rule for Unrestricted.

unboxⱼ : Γ ⊢ t ∷ Unrestricted A → Γ ⊢ unbox t ∷ A
unboxⱼ ⊢t = fstⱼ (Unitⱼ (∙ ⊢A) Unit-ok) ⊢t
  where
  ⊢A = inversion-ΠΣ (syntacticTerm ⊢t) .proj₁

-- A corresponding congruence rule.

unbox-cong : Γ ⊢ t ≡ u ∷ Unrestricted A → Γ ⊢ unbox t ≡ unbox u ∷ A
unbox-cong t≡u = fst-cong (Unitⱼ (∙ ⊢A) Unit-ok) t≡u
  where
  ⊢A = inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) .proj₁

-- A β-rule for Unrestricted.

Unrestricted-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ unbox [ t ] ≡ t ∷ A
Unrestricted-β ⊢t =
  Σ-β₁ (Unitⱼ (∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) PE.refl Σˢ-ok
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- An η-rule for Unrestricted.

Unrestricted-η :
  Γ ⊢ t ∷ Unrestricted A →
  Γ ⊢ u ∷ Unrestricted A →
  Γ ⊢ unbox t ≡ unbox u ∷ A →
  Γ ⊢ t ≡ u ∷ Unrestricted A
Unrestricted-η ⊢t ⊢u t≡u =
  case Unitⱼ (∙ syntacticEqTerm t≡u .proj₁) Unit-ok of λ
    Γ∙A⊢Unit → Σ-η′
      ⊢t ⊢u t≡u
      (η-unit (sndⱼ Γ∙A⊢Unit ⊢t) (sndⱼ Γ∙A⊢Unit ⊢u) (inj₁ PE.refl))

-- An instance of the η-rule.

[unbox] :
  Γ ⊢ t ∷ Unrestricted A →
  Γ ⊢ [ unbox t ] ≡ t ∷ Unrestricted A
[unbox] ⊢t =
  Unrestricted-η ([]ⱼ (unboxⱼ ⊢t)) ⊢t $
  Unrestricted-β (unboxⱼ ⊢t)

------------------------------------------------------------------------
-- Inversion lemmas for typing

-- An inversion lemma for Unrestricted.

inversion-Unrestricted-∷ :
  Γ ⊢ Unrestricted A ∷ B →
  ∃ λ l → Γ ⊢ A ∷ U l × Γ ⊢ B ≡ U l
inversion-Unrestricted-∷ ⊢Unrestricted =
  case inversion-ΠΣ-U ⊢Unrestricted of λ
    (_ , _ , ⊢A , ⊢Unit , B≡ , _) →
  case U-injectivity (inversion-Unit-U ⊢Unit .proj₁) of λ {
    PE.refl →
  _ , ⊢A , B≡ }

-- Another inversion lemma for Unrestricted.

inversion-Unrestricted : Γ ⊢ Unrestricted A → Γ ⊢ A
inversion-Unrestricted (ΠΣⱼ ⊢Unit _)        = ⊢∙→⊢ (wf ⊢Unit)
inversion-Unrestricted (univ ⊢Unrestricted) =
  univ (inversion-Unrestricted-∷ ⊢Unrestricted .proj₂ .proj₁)

-- An inversion lemma for [_].
--
-- TODO: Make it possible to replace the conclusion with
--
--   ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Unrestricted B?

inversion-[] :
  Γ ⊢ [ t ] ∷ A →
  ∃₃ λ B q C →
     Γ ⊢ t ∷ B ×
     Γ ⊢ A ≡ Σˢ ω , q ▷ B ▹ C ×
     Γ ⊢ C [ t ]₀ ≡ Unitˢ 0
inversion-[] ⊢[] =
  case inversion-prod ⊢[] of
    λ (B , C , q , ⊢B , _ , ⊢t , ⊢star , A≡ , _) →
  case inversion-star ⊢star of λ (≡Unit , _) →
    B , q , C , ⊢t , A≡ , ≡Unit

-- Another inversion lemma for [_].

inversion-[]′ : Γ ⊢ [ t ] ∷ Unrestricted A → Γ ⊢ t ∷ A
inversion-[]′ ⊢[] =
  case inversion-[] ⊢[] of
    λ (_ , _ , _ , ⊢t , Unrestricted-A≡ , _) →
  case Σ-injectivity Unrestricted-A≡ of
    λ (A≡ , _) →
  conv ⊢t (_⊢_≡_.sym A≡)

-- A certain form of inversion for [_] does not hold.

¬-inversion-[]′ :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ [ t ] ∷ A →
     ∃₃ λ B q l → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Σˢ ω , q ▷ B ▹ Unitˢ l)
¬-inversion-[]′ inversion-[] = bad
  where
  Γ′ = ε
  t′ = zero
  A′ = Σˢ ω , ω ▷ ℕ ▹ natrec 𝟙 𝟙 𝟙 (U 0) (Unitˢ 0) ℕ (var x0)

  ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
  ⊢Γ′∙ℕ = ∙ ℕⱼ ε

  ⊢Γ′∙ℕ∙ℕ : ⊢ Γ′ ∙ ℕ ∙ ℕ
  ⊢Γ′∙ℕ∙ℕ = ∙ ℕⱼ ⊢Γ′∙ℕ

  ⊢Γ′∙ℕ∙U : ⊢ Γ′ ∙ ℕ ∙ U 0
  ⊢Γ′∙ℕ∙U = ∙ Uⱼ ⊢Γ′∙ℕ

  ⊢[t′] : Γ′ ⊢ [ t′ ] ∷ A′
  ⊢[t′] = prodⱼ
    (univ (natrecⱼ
             (Unitⱼ ⊢Γ′∙ℕ Unit-ok)
             (ℕⱼ (∙ Uⱼ ⊢Γ′∙ℕ∙ℕ))
             (var ⊢Γ′∙ℕ here)))
    (zeroⱼ ε)
    (conv (starⱼ ε Unit-ok)
       (_⊢_≡_.sym $
        univ (natrec-zero (Unitⱼ ε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U))))
    Σˢ-ok

  ℕ≡Unit : ∃ λ l → Γ′ ⊢ ℕ ≡ Unitˢ l
  ℕ≡Unit =
    case inversion-[] ⊢[t′] of
      λ (_ , _ , _ , _ , A′≡) →
    case Σ-injectivity A′≡ of
      λ (_ , ≡Unit , _ , _ , _) →
      _
    , _⊢_≡_.trans
        (_⊢_≡_.sym $ _⊢_≡_.univ $
         natrec-suc (Unitⱼ ε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U) (zeroⱼ ε))
        (substTypeEq ≡Unit (refl (sucⱼ (zeroⱼ ε))))

  bad : ⊥
  bad = ℕ≢Unitⱼ (ℕ≡Unit .proj₂)

-- Another form of inversion for [] also does not hold.

¬-inversion-[] :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ [ t ] ∷ A →
     ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Unrestricted B)
¬-inversion-[] inversion-[] =
  ¬-inversion-[]′ λ ⊢[] →
  case inversion-[] ⊢[] of λ (B , ⊢t , A≡) →
  B , ω , 0 , ⊢t , A≡

-- An inversion lemma for unbox.
--
-- TODO: Make it possible to replace the conclusion with
--
--   Γ ⊢ t ∷ Unrestricted A?

inversion-unbox :
  Γ ⊢ unbox t ∷ A →
  ∃₂ λ q B → Γ ⊢ t ∷ Σˢ ω , q ▷ A ▹ B
inversion-unbox ⊢unbox =
  case inversion-fst ⊢unbox of λ (_ , C , q , _ , ⊢C , ⊢t , ≡B) →
    q
  , C
  , conv ⊢t (ΠΣ-cong (_⊢_≡_.sym ≡B) (refl ⊢C) (⊢∷ΠΣ→ΠΣ-allowed ⊢t))

-- A certain form of inversion for unbox does not hold.

¬-inversion-unbox′ :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ unbox t ∷ A →
     ∃₂ λ q l → Γ ⊢ t ∷ Σˢ ω , q ▷ A ▹ Unitˢ l)
¬-inversion-unbox′ inversion-unbox = bad
  where
  Γ′ = ε
  t′ = prodˢ ω zero zero
  A′ = ℕ

  ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
  ⊢Γ′∙ℕ = ∙ ℕⱼ ε

  ⊢t′₁ : Γ′ ⊢ t′ ∷ Σ ω , ω ▷ ℕ ▹ ℕ
  ⊢t′₁ = prodⱼ (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σˢ-ok

  ⊢unbox-t′ : Γ′ ⊢ unbox t′ ∷ A′
  ⊢unbox-t′ = fstⱼ (ℕⱼ ⊢Γ′∙ℕ) ⊢t′₁

  unbox-t′≡zero : Γ′ ⊢ unbox t′ ≡ zero ∷ A′
  unbox-t′≡zero =
    Σ-β₁ (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) PE.refl Σˢ-ok

  ⊢t′₂ : ∃₂ λ q l → Γ′ ⊢ t′ ∷ Σˢ ω , q ▷ A′ ▹ Unitˢ l
  ⊢t′₂ = inversion-unbox ⊢unbox-t′

  ⊢snd-t′ : ∃ λ l → Γ′ ⊢ snd ω t′ ∷ Unitˢ l
  ⊢snd-t′ = _ , sndⱼ (Unitⱼ ⊢Γ′∙ℕ Unit-ok) (⊢t′₂ .proj₂ .proj₂)

  ℕ≡Unit : ∃ λ l → Γ′ ⊢ ℕ ≡ Unitˢ l
  ℕ≡Unit =
    case ⊢snd-t′ of λ
      (l , ⊢snd-t′) →
    case inversion-snd ⊢snd-t′ of
      λ (_ , _ , _ , _ , _ , ⊢t′ , Unit≡) →
    case inversion-prod ⊢t′ of
      λ (_ , _ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ , _) →
    case Σ-injectivity Σ≡Σ of
      λ (F≡F′ , G≡G′ , _ , _ , _) →
    case inversion-zero ⊢zero of
      λ ≡ℕ →
    case inversion-zero ⊢zero′ of
      λ ≡ℕ′ →
      l
    , (_⊢_≡_.sym $
       trans Unit≡ $
       trans
         (substTypeEq G≡G′ $
          conv unbox-t′≡zero (_⊢_≡_.sym (trans F≡F′ ≡ℕ)))
       ≡ℕ′)

  bad : ⊥
  bad = ℕ≢Unitⱼ (ℕ≡Unit .proj₂)

-- Another form of inversion for unbox also does not hold.

¬-inversion-unbox :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ unbox t ∷ A →
     Γ ⊢ t ∷ Unrestricted A)
¬-inversion-unbox inversion-unbox =
  ¬-inversion-unbox′ λ ⊢unbox →
  _ , _ , inversion-unbox ⊢unbox
