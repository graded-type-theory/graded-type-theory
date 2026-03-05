------------------------------------------------------------------------
-- Definitions related to type and usage restrictions
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode

module Graded.Restrictions
  {a a′} {M : Set a} {Mode : Set a′}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Graded.Mode Mode 𝕄)
  (𝐌 : IsMode)
  where

open Modality 𝕄
open IsMode 𝐌

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation as Dec
open import Tools.Sum
open import Tools.Unit

open import Graded.Modality.Properties 𝕄
import Graded.Usage.Decidable.Assumptions as UD
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions 𝕄 𝐌
open import Graded.Usage.Restrictions.Natrec 𝕄

import Definition.Typechecking.Decidable.Assumptions as TD
open import Definition.Typed.Restrictions 𝕄
open import Definition.Typed.Variant
open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

private variable
  TR : Type-restrictions
  UR : Usage-restrictions
  b  : Bool
  ok : T _
  s  : Strength
  nm : Natrec-mode

------------------------------------------------------------------------
-- Functions that construct Type-restrictions

-- No type restrictions except that
-- * if the modality is trivial, then []-cong is not allowed,
-- * the K rule is allowed if and only if the first boolean is true,
-- * η-equality is not allowed for weak unit types,
-- * opacity is allowed if and only if the second boolean is false,
--   and
-- * equality reflection is allowed if and only if the second boolean
--   is true.
-- Furthermore transitive unfolding is used.

no-type-restrictions : Bool → Bool → Type-restrictions
no-type-restrictions k equality-reflection = λ where
    .level-support                 → level-type small
    .Omega-plus-allowed            → Lift _ ⊤
    .Unit-allowed                  → λ _ → Lift _ ⊤
    .ΠΣ-allowed                    → λ _ _ _ → Lift _ ⊤
    .Opacity-allowed               → Lift _ (¬ T equality-reflection)
    .Opacity-allowed?              → Lift? (¬? (T? equality-reflection))
    .K-allowed                     → Lift _ (T k)
    .[]-cong-allowed               → λ _ → ¬ Trivial
    .[]-cong→Erased                → _
    .[]-cong→¬Trivial              → idᶠ
    .Equality-reflection           → Lift _ (T equality-reflection)
    .Equality-reflection?          → Lift? (T? equality-reflection)
    .no-opaque-equality-reflection → (_∘→ Lift.lower) ∘→ Lift.lower
    .type-variant                  → λ where
      .Type-variant.unfolding-mode → transitive
      .Type-variant.η-for-Unitʷ    → false
  where
  open Type-restrictions

-- The function adds the restriction that the two quantities on a Π-
-- or Σ-type have to be equal.

equal-binder-quantities : Type-restrictions → Type-restrictions
equal-binder-quantities R = record R
  { ΠΣ-allowed     = λ b p q → ΠΣ-allowed b p q × p ≡ q
  ; []-cong→Erased = λ ok →
      []-cong→Erased ok .proj₁ , []-cong→Erased ok .proj₂ , refl
  }
  where
  open Type-restrictions R

-- The function adds the restriction that the second quantities
-- associated with Π- and Σ-types are equal to 𝟘.

second-ΠΣ-quantities-𝟘 :
  Type-restrictions → Type-restrictions
second-ΠΣ-quantities-𝟘 R = record R
  { ΠΣ-allowed     = λ b p q → ΠΣ-allowed b p q × q ≡ 𝟘
  ; []-cong→Erased = λ ok →
      []-cong→Erased ok .proj₁ , []-cong→Erased ok .proj₂ , refl
  }
  where
  open Type-restrictions R

-- The function second-ΠΣ-quantities-𝟘-or-ω 𝕄 adds the restriction
-- that if the first quantity associated with a Π- or Σ-type is the ω
-- grade of 𝕄, then the second quantity is also ω, and if the first
-- quantity is not ω, then the second quantity is the 𝟘 of 𝕄.

second-ΠΣ-quantities-𝟘-or-ω :
  Type-restrictions → Type-restrictions
second-ΠΣ-quantities-𝟘-or-ω R = record R
  { ΠΣ-allowed = λ b p q →
      ΠΣ-allowed b p q ×
      (p ≡ ω → q ≡ ω) ×
      (p ≢ ω → q ≡ 𝟘)
  ; []-cong→Erased = λ ok →
        []-cong→Erased ok .proj₁
      , []-cong→Erased ok .proj₂
      , idᶠ
      , λ _ → refl
  }
  where
  open Type-restrictions R

-- A lemma used to define strong-types-restricted and no-strong-types.

strong-types-restricted′ :
  (P : BinderMode → M → Set a) →
  (∀ {s} → s ≢ 𝕤 → P (BMΣ s) 𝟘) →
  Type-restrictions → Type-restrictions
strong-types-restricted′ P hyp R = record R
  { Unit-allowed = λ s →
      Unit-allowed s × s ≢ 𝕤
  ; ΠΣ-allowed = λ b p q →
      ΠΣ-allowed b p q × P b p
  ; []-cong-allowed = λ s →
      []-cong-allowed s × s ≢ 𝕤
  ; []-cong→Erased = λ (ok , s≢𝕤) →
        ([]-cong→Erased ok .proj₁ , s≢𝕤)
      , []-cong→Erased ok .proj₂
      , hyp s≢𝕤
  ; []-cong→¬Trivial =
      []-cong→¬Trivial ∘→ proj₁
  }
  where
  open Type-restrictions R

-- The function strong-types-restricted adds the following
-- restrictions:
--
-- * Strong unit types are not allowed.
-- * If strong Σ-types are allowed for p and q, then p is 𝟙.
-- * []-cong is not allowed for 𝕤.

strong-types-restricted :
  Type-restrictions → Type-restrictions
strong-types-restricted =
  strong-types-restricted′ (λ b p → b ≡ BMΣ 𝕤 → p ≡ 𝟙)
    (λ { hyp refl → ⊥-elim $ hyp refl })

-- The function no-strong-types adds the following restrictions:
--
-- * Strong unit types are not allowed.
-- * Strong Σ-types are not allowed.
-- * []-cong is not allowed for 𝕤.

no-strong-types :
  Type-restrictions → Type-restrictions
no-strong-types =
  strong-types-restricted′ (λ b _ → Lift _ (b ≢ BMΣ 𝕤))
    (λ hyp → lift (λ { refl → ⊥-elim $ hyp refl }))

-- The function adds the restriction that erased matches are not
-- allowed for the given strength.

no-erased-matches-TR : Strength → Type-restrictions → Type-restrictions
no-erased-matches-TR s TR = record TR
  { []-cong-allowed  = λ s′ → []-cong-allowed s′ × s′ ≢ s
  ; []-cong→Erased   = []-cong→Erased ∘→ proj₁
  ; []-cong→¬Trivial = []-cong→¬Trivial ∘→ proj₁
  }
  where
  open Type-restrictions TR

-- The function _with-η-for-Unitʷ enables η-equality for weak unit
-- types.

_with-η-for-Unitʷ : Type-restrictions → Type-restrictions
TR with-η-for-Unitʷ = record TR
  { type-variant = record type-variant
    { η-for-Unitʷ = true
    }
  }
  where
  open Type-restrictions TR

-- The function []-cong-TR enables unrestricted support for []-cong if
-- the modality is non-trivial.

[]-cong-TR : Type-restrictions → Type-restrictions
[]-cong-TR TR = record TR
  { Unit-allowed     = λ s → Unit-allowed s ⊎ ¬ Trivial
  ; ΠΣ-allowed       = λ where
                         (BMΣ s) p q → ΠΣ-allowed (BMΣ s) p q ⊎
                                       ¬ Trivial × p ≡ 𝟘 × q ≡ 𝟘
                         BMΠ     p q → ΠΣ-allowed BMΠ p q
  ; []-cong-allowed  = λ _ → ¬ Trivial
  ; []-cong→Erased   = λ non-trivial →
                         inj₂ non-trivial ,
                         inj₂ (non-trivial , refl , refl)
  ; []-cong→¬Trivial = idᶠ
  }
  where
  open Type-restrictions TR

-- The function no-[]-cong-TR disables support for []-cong.

no-[]-cong-TR : Type-restrictions → Type-restrictions
no-[]-cong-TR TR = record TR
  { []-cong-allowed  = λ _ → Lift _ ⊥
  ; []-cong→Erased   = λ ()
  ; []-cong→¬Trivial = λ ()
  }

-- The function with-equality-reflection enables support for equality
-- reflection, and disables support for opaque definitions.

with-equality-reflection : Type-restrictions → Type-restrictions
with-equality-reflection TR = record TR
  { Opacity-allowed               = Lift _ ⊥
  ; Opacity-allowed?              = no (λ ())
  ; Equality-reflection           = Lift _ ⊤
  ; Equality-reflection?          = yes _
  ; no-opaque-equality-reflection = λ ()
  }

------------------------------------------------------------------------
-- Functions that construct Usage-restrictions

-- No restrictions for prodrec, unitrec or emptyrec, all erased
-- matches are allowed for J and K, the natrec mode can be anything,
-- Id-erased is inhabited if the first boolean is true, and starˢ
-- is treated as a sink if the second boolean is true.

no-usage-restrictions :
  (nm : Natrec-mode) →
  (⦃ has-nr : Natrec-mode-has-nr nm ⦄ →
     Mode-supports-nr ⦃ Natrec-mode-Has-nr has-nr ⦄ 𝐌) →
  Bool → Bool → Usage-restrictions
no-usage-restrictions nm nr-ok erased sink = λ where
    .natrec-mode                             → nm
    .Prodrec-allowed                         → λ _ _ _ _ → Lift _ ⊤
    .Prodrec-allowed-upwards-closed          → λ _ _ → _
    .Unitrec-allowed                         → λ _ _ _ → Lift _ ⊤
    .Unitrec-allowed-upwards-closed          → λ _ _ → _
    .Emptyrec-allowed                        → λ _ _ → Lift _ ⊤
    .Emptyrec-allowed-upwards-closed         → λ _ _ → _
    .[]-cong-allowed-mode                    → λ _ _ → Lift _ ⊤
    .[]-cong-allowed-mode-upwards-closed     → λ _ _ → _
    .starˢ-sink                              → sink
    .Id-erased                               → Lift _ (T erased)
    .Id-erased?                              → Dec.map lift Lift.lower $
                                                T? erased
    .erased-matches-for-J                    → λ _ → all
    .erased-matches-for-J-≤ᵉᵐ                → _
    .erased-matches-for-K                    → λ _ → all
    .erased-matches-for-K-≤ᵉᵐ                → _
    .mode-supports-nr                        → nr-ok
  where
  open Usage-restrictions

-- The function updates the usage restrictions to use the usage rule
-- natrecₘ for natrec using a given nr function.

nr-available-UR :
  (has-nr : Has-nr 𝕄) →
  Mode-supports-nr ⦃ has-nr ⦄ 𝐌 →
  Usage-restrictions → Usage-restrictions
nr-available-UR has-nr nr-ok UR = record UR
  { natrec-mode      = Nr ⦃ has-nr ⦄
  ; mode-supports-nr = λ { ⦃ (Nr) ⦄ → nr-ok}
  }

-- The function updates the usage restrictions to use the usage rule
-- natrec-no-nr-glbₘ for natrec, assuming that the rule is supported.

nr-not-available-glb-UR :
  Has-well-behaved-GLBs 𝕄 →
  Usage-restrictions → Usage-restrictions
nr-not-available-glb-UR ok UR =
  record UR
    { natrec-mode = No-nr-glb ⦃ ok ⦄
    ; mode-supports-nr = λ { ⦃ () ⦄}
    }

-- The function enables support for []-cong (if the modality is
-- non-trivial), but disables support for erased matches for J.

[]-cong-UR : Usage-restrictions → Usage-restrictions
[]-cong-UR UR = record UR
  { []-cong-allowed-mode     = λ m s → []-cong-allowed-mode m s ⊎
                                     ¬ Trivial
  ; []-cong-allowed-mode-upwards-closed = λ where
      (inj₁ ok) m≤m′ → inj₁ ([]-cong-allowed-mode-upwards-closed ok m≤m′)
      (inj₂ 𝟙≢𝟘) _   → inj₂ 𝟙≢𝟘
  ; erased-matches-for-J     = λ _ → none
  ; erased-matches-for-J-≤ᵉᵐ = _
  }
  where
  open Usage-restrictions UR

------------------------------------------------------------------------
-- No-secret-matches

-- The property of not allowing (certain) secret matches (matches on
-- data that is "more secret" than a given grade).

-- record No-secret-matches
--   (p₀ : M) (TV : Type-variant) (UR : Usage-restrictions) : Set (a ⊔ a′) where

--   no-eta-equality

--   open Usage-restrictions UR
--   open Type-variant TV

--   field
--     no-secret-prodrec :
--       ∀ {m p q r} → m ≤ᵐ ⌞ p₀ ⌟ → Prodrec-allowed m r p q → r ≤ p₀
--     no-secret-unitrec :
--       ∀ {m p q} → m ≤ᵐ ⌞ p₀ ⌟ → ¬ Unitʷ-η → Unitrec-allowed ⌞ m ⌟ p q → p ≤ p₀
--     no-secret-J :
--       erased-matches-for-J ⌞ p₀ ⌟ ≡ none
--     no-secret-K :
--       m ≤ᵐ ⌞ p₀ ⌟ → erased-matches-for-K m ≡ none
--     no-secret-[]-cong :
--       ∀ {s m} → m ≤ p₀ → []-cong-allowed-mode s ⌞ m ⌟ → 𝟘 ≤ p₀

------------------------------------------------------------------------
-- No-erased-matches

-- The property of not allowing (certain) erased matches:
-- * Erased matches are allowed for emptyrec.
-- * "Erased" matches are allowed for unitrec if η-equality is allowed
--   for weak unit types.
-- * "Erased" matches are allowed for trivial modalities.
-- * Erased matches are allowed when the mode is not 𝟙ᵐ, except for
--   []-cong. (Note that a variant of []-cong that works when the mode
--   is not 𝟙ᵐ can be defined without the use of []-cong, see
--   Graded.Box-cong.▸[]-cong-J-𝟘ᵐ.)

No-erased-matches : Type-restrictions → Usage-restrictions → Set (a ⊔ a′)
No-erased-matches TR UR =
  ¬ Trivial →
  (∀ {m r p q} → Prodrec-allowed m r p q → r ≡ 𝟘 → ⌜ m ⌝ ≡ 𝟘) ×
  (∀ {m p q}   → Unitrec-allowed m p q   → p ≡ 𝟘 → ⌜ m ⌝ ≢ 𝟘 → Unitʷ-η) ×
  (∀ {s} → ¬ ([]-cong-allowed s)) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- An alternative to No-erased-matches that refers to
-- Type-variant instead of Type-restrictions

No-erased-matches′ : Type-variant → Usage-restrictions → Set (a ⊔ a′)
No-erased-matches′ TV UR =
  ¬ Trivial →
  (∀ {m r p q} → Prodrec-allowed m r p q → r ≡ 𝟘 → ⌜ m ⌝ ≡ 𝟘) ×
  (∀ {m p q}   → Unitrec-allowed m p q   → p ≡ 𝟘 → ⌜ m ⌝ ≢ 𝟘 → Unitʷ-η) ×
  (∀ {m s} → []-cong-allowed-mode s m → ⌜ m ⌝ ≡ 𝟘) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-variant TV
  open Usage-restrictions UR

------------------------------------------------------------------------
-- Some lemmas related to TD.Assumptions

opaque

  -- If grade equality is decidable, then TD.Assumptions holds for
  -- no-type-restrictions b false.

  Assumptions-no-type-restrictions :
    Decidable (_≡_ {A = M}) →
    TD.Assumptions (no-type-restrictions b false)
  Assumptions-no-type-restrictions {b} dec = λ where
      ._≟_                 → dec
      .Omega-plus-allowed? → yes _
      .Unit-allowed? _     → yes _
      .ΠΣ-allowed? _ _ _   → yes _
      .K-allowed?          → case singleton b of λ where
        (true  , refl) → yes _
        (false , refl) → no (λ ())
      .[]-cong-allowed? _ → case trivial? of λ where
        (yes trivial)    → no (_$ trivial)
        (no non-trivial) → yes non-trivial
      .no-equality-reflection (lift ())
    where
    open TD.Assumptions

opaque

  -- The function equal-binder-quantities preserves TD.Assumptions.

  Assumptions-equal-binder-quantities :
    TD.Assumptions TR → TD.Assumptions (equal-binder-quantities TR)
  Assumptions-equal-binder-quantities as = λ where
      ._≟_                    → A._≟_
      .Omega-plus-allowed?    → A.Omega-plus-allowed?
      .Unit-allowed?          → A.Unit-allowed?
      .ΠΣ-allowed? b p q      → A.ΠΣ-allowed? b p q ×-dec p A.≟ q
      .K-allowed?             → A.K-allowed?
      .[]-cong-allowed?       → A.[]-cong-allowed?
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions

opaque

  -- The function second-ΠΣ-quantities-𝟘 preserves TD.Assumptions.

  Assumptions-second-ΠΣ-quantities-𝟘 :
    TD.Assumptions TR → TD.Assumptions (second-ΠΣ-quantities-𝟘 TR)
  Assumptions-second-ΠΣ-quantities-𝟘 as = λ where
      ._≟_                    → A._≟_
      .Omega-plus-allowed?    → A.Omega-plus-allowed?
      .Unit-allowed?          → A.Unit-allowed?
      .ΠΣ-allowed? b p q      → A.ΠΣ-allowed? b p q ×-dec q A.≟ 𝟘
      .K-allowed?             → A.K-allowed?
      .[]-cong-allowed?       → A.[]-cong-allowed?
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions

opaque

  -- The function second-ΠΣ-quantities-𝟘-or-ω preserves
  -- TD.Assumptions.

  Assumptions-second-ΠΣ-quantities-𝟘-or-ω :
    TD.Assumptions TR → TD.Assumptions (second-ΠΣ-quantities-𝟘-or-ω TR)
  Assumptions-second-ΠΣ-quantities-𝟘-or-ω as = λ where
      ._≟_                    → A._≟_
      .Omega-plus-allowed?    → A.Omega-plus-allowed?
      .Unit-allowed?          → A.Unit-allowed?
      .ΠΣ-allowed? b p q      → A.ΠΣ-allowed? b p q
                                  ×-dec
                                (p A.≟ ω →-dec q A.≟ ω)
                                  ×-dec
                                (¬? (p A.≟ ω) →-dec q A.≟ 𝟘)
      .K-allowed?             → A.K-allowed?
      .[]-cong-allowed?       → A.[]-cong-allowed?
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions

opaque

  -- The function strong-types-restricted′ P ok preserves
  -- TD.Assumptions if P is pointwise decidable.

  Assumptions-strong-types-restricted′ :
    {P : BinderMode → M → Set a}
    {ok : ∀ {s} → s ≢ 𝕤 → P (BMΣ s) 𝟘} →
    (∀ b p → Dec (P b p)) →
    TD.Assumptions TR →
    TD.Assumptions (strong-types-restricted′ P ok TR)
  Assumptions-strong-types-restricted′ P-dec as = λ where
      ._≟_                    → A._≟_
      .Omega-plus-allowed?    → A.Omega-plus-allowed?
      .Unit-allowed? s        → A.Unit-allowed? s
                                  ×-dec
                                ¬? (decStrength s 𝕤)
      .ΠΣ-allowed? b p q      → A.ΠΣ-allowed? b p q
                                  ×-dec
                                P-dec b p
      .K-allowed?             → A.K-allowed?
      .[]-cong-allowed? s     → A.[]-cong-allowed? s
                                  ×-dec
                                ¬? (decStrength s 𝕤)
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions

opaque

  -- The function strong-types-restricted preserves TD.Assumptions.

  Assumptions-strong-types-restricted :
    TD.Assumptions TR → TD.Assumptions (strong-types-restricted TR)
  Assumptions-strong-types-restricted as =
    Assumptions-strong-types-restricted′
      (λ b p → decBinderMode b (BMΣ 𝕤) →-dec p ≟ 𝟙)
      as
    where
    open TD.Assumptions as

opaque

  -- The function no-strong-types preserves TD.Assumptions.

  Assumptions-no-strong-types :
    TD.Assumptions TR → TD.Assumptions (no-strong-types TR)
  Assumptions-no-strong-types as =
    Assumptions-strong-types-restricted′
      (λ b _ → Dec.map lift Lift.lower (¬? (decBinderMode b (BMΣ 𝕤))))
      as
    where
    open TD.Assumptions as

opaque

  -- The function no-erased-matches-TR s preserves TD.Assumptions.

  Assumptions-no-erased-matches-TR :
    TD.Assumptions TR → TD.Assumptions (no-erased-matches-TR s TR)
  Assumptions-no-erased-matches-TR {s} as = λ where
      ._≟_                    → A._≟_
      .Omega-plus-allowed?    → A.Omega-plus-allowed?
      .Unit-allowed?          → A.Unit-allowed?
      .ΠΣ-allowed?            → A.ΠΣ-allowed?
      .K-allowed?             → A.K-allowed?
      .[]-cong-allowed? s′    → A.[]-cong-allowed? s′
                                  ×-dec
                                ¬? (decStrength s′ s)
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions
