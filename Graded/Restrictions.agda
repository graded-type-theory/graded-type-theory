------------------------------------------------------------------------
-- Definitions related to type and usage restrictions
------------------------------------------------------------------------

import Graded.Modality

module Graded.Restrictions
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

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
open import Graded.Mode 𝕄 as Mode hiding (_≟_)
import Graded.Usage.Decidable.Assumptions as UD
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions 𝕄
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

no-usage-restrictions : Natrec-mode → Bool → Bool → Usage-restrictions
no-usage-restrictions nm erased sink = λ where
    .natrec-mode              → nm
    .Prodrec-allowed-𝟙ᵐ       → λ _ _ _ → Lift _ ⊤
    .Unitrec-allowed-𝟙ᵐ       → λ _ _ → Lift _ ⊤
    .Emptyrec-allowed-𝟙ᵐ      → λ _ → Lift _ ⊤
    .[]-cong-allowed-mode-𝟙ᵐ  → λ _ → Lift _ ⊤
    .starˢ-sink               → sink
    .Id-erased                → Lift _ (T erased)
    .Id-erased?               → Dec.map lift Lift.lower $
                                T? erased
    .erased-matches-for-J     → λ _ → all
    .erased-matches-for-J-≤ᵉᵐ → _
    .erased-matches-for-K     → λ _ → all
    .erased-matches-for-K-≤ᵉᵐ → _
  where
  open Usage-restrictions

-- A function used to define not-all-erased-matches-JK.

not-all-for-𝟙ᵐ : (Mode → Erased-matches) → Mode → Erased-matches
not-all-for-𝟙ᵐ f 𝟘ᵐ = f 𝟘ᵐ
not-all-for-𝟙ᵐ f 𝟙ᵐ with f 𝟙ᵐ
… | all = some
… | em  = em

-- The function adds the restriction that, for the mode 𝟙ᵐ, "all"
-- erased matches are not allowed for J and K.

not-all-erased-matches-JK : Usage-restrictions → Usage-restrictions
not-all-erased-matches-JK UR = record UR
  { erased-matches-for-J =
      not-all-for-𝟙ᵐ erased-matches-for-J
  ; erased-matches-for-J-≤ᵉᵐ =
      not-all-for-𝟙ᵐ-≤ᵉᵐ erased-matches-for-J erased-matches-for-J-≤ᵉᵐ
  ; erased-matches-for-K =
      not-all-for-𝟙ᵐ erased-matches-for-K
  ; erased-matches-for-K-≤ᵉᵐ =
      not-all-for-𝟙ᵐ-≤ᵉᵐ erased-matches-for-K erased-matches-for-K-≤ᵉᵐ
  }
  where
  open Usage-restrictions UR

  opaque

    not-all-for-𝟙ᵐ-≤ᵉᵐ :
      (f : Mode → Erased-matches) →
      f 𝟙ᵐ ≤ᵉᵐ f 𝟘ᵐ[ ok ] →
      not-all-for-𝟙ᵐ f 𝟙ᵐ ≤ᵉᵐ not-all-for-𝟙ᵐ f 𝟘ᵐ[ ok ]
    not-all-for-𝟙ᵐ-≤ᵉᵐ f f-≤ᵉᵐ with f 𝟙ᵐ
    … | all  = ≤ᵉᵐ-transitive _ f-≤ᵉᵐ
    … | some = f-≤ᵉᵐ
    … | none = f-≤ᵉᵐ

-- The function adds the restriction that certain erased matches are
-- not allowed for the mode 𝟙ᵐ. No restriction is added for emptyrec
-- or unitrec. For prodrec the added restriction only applies to
-- non-trivial modalities.

only-some-erased-matches : Usage-restrictions → Usage-restrictions
only-some-erased-matches UR = record UR
  { Prodrec-allowed-𝟙ᵐ = λ r p q →
      Prodrec-allowed-𝟙ᵐ r p q ×
      (¬ Trivial → r ≢ 𝟘)
  ; erased-matches-for-J = λ where
      𝟙ᵐ → none
      𝟘ᵐ → erased-matches-for-J 𝟘ᵐ
  ; erased-matches-for-J-≤ᵉᵐ =
      _
  ; erased-matches-for-K = λ where
      𝟙ᵐ → none
      𝟘ᵐ → erased-matches-for-K 𝟘ᵐ
  ; erased-matches-for-K-≤ᵉᵐ =
      _
  }
  where
  open Usage-restrictions UR

-- The function adds the restriction that certain erased matches are
-- not allowed for the mode 𝟙ᵐ. No restriction is added for emptyrec.
-- For prodrec and unitrec the added restriction only applies to
-- non-trivial modalities, and for unitrec the added restriction only
-- applies if η-equality is not allowed for weak unit types.

no-erased-matches-UR :
  Type-restrictions → Usage-restrictions → Usage-restrictions
no-erased-matches-UR TR UR = record (only-some-erased-matches UR)
  { Unitrec-allowed-𝟙ᵐ = λ p q →
      Unitrec-allowed-𝟙ᵐ p q ×
      (¬ Trivial → p ≡ 𝟘 → Unitʷ-η)
  }
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- The function updates the usage restrictions to use the usage rule
-- natrecₘ for natrec using a given nr function.

nr-available-UR :
  Has-nr semiring-with-meet → Usage-restrictions → Usage-restrictions
nr-available-UR has-nr UR =
  record UR { natrec-mode = Nr ⦃ has-nr ⦄ }

-- The function updates the usage restrictions to use the usage rule
-- natrec-no-nr-glbₘ for natrec, assuming that the rule is supported.

nr-not-available-glb-UR :
  Has-well-behaved-GLBs semiring-with-meet →
  Usage-restrictions → Usage-restrictions
nr-not-available-glb-UR ok UR =
  record UR { natrec-mode = No-nr-glb ⦃ ok ⦄ }

-- The function enables support for []-cong (if the modality is
-- non-trivial), but disables support for erased matches for J.

[]-cong-UR : Usage-restrictions → Usage-restrictions
[]-cong-UR UR = record UR
  { []-cong-allowed-mode-𝟙ᵐ  = λ s → []-cong-allowed-mode-𝟙ᵐ s ⊎
                                     ¬ Trivial
  ; erased-matches-for-J     = λ _ → none
  ; erased-matches-for-J-≤ᵉᵐ = _
  }
  where
  open Usage-restrictions UR

-- A function used to define no-[]-cong-UR.

at-least-some : (Mode → Erased-matches) → Mode → Erased-matches
at-least-some f m = case f m of λ where
  none → some
  em   → em

-- The function no-[]-cong-UR disables support for []-cong but enables
-- "some" erased matches for J.

no-[]-cong-UR : Usage-restrictions → Usage-restrictions
no-[]-cong-UR UR = record UR
  { []-cong-allowed-mode-𝟙ᵐ  = λ _ → Lift _ ⊥
  ; erased-matches-for-J     = at-least-some erased-matches-for-J
  ; erased-matches-for-J-≤ᵉᵐ = at-least-some-≤ᵉᵐ

  }
  where
  open Usage-restrictions UR

  at-least-some-≤ᵉᵐ :
    at-least-some erased-matches-for-J 𝟙ᵐ ≤ᵉᵐ
    at-least-some erased-matches-for-J 𝟘ᵐ[ ok ]
  at-least-some-≤ᵉᵐ {ok}
    with erased-matches-for-J 𝟙ᵐ
       | erased-matches-for-J 𝟘ᵐ[ ok ]
       | erased-matches-for-J-≤ᵉᵐ ⦃ ok = ok ⦄
  … | none       | none       | _  = _
  … | none       | some       | _  = _
  … | none       | all        | _  = _
  … | all        | none       | ()
  … | some       | none       | ()
  … | not-none _ | not-none _ | r  = r

------------------------------------------------------------------------
-- Only-some-erased-matches

-- The property of not allowing certain erased matches:
-- * Erased matches are allowed for emptyrec and unitrec.
-- * "Erased" matches are allowed for trivial modalities.
-- * Erased matches are allowed when the mode is not 𝟙ᵐ, except for
--   []-cong.

Only-some-erased-matches :
  Type-restrictions → Usage-restrictions → Set a
Only-some-erased-matches TR UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed-𝟙ᵐ r p q → r ≢ 𝟘) ×
  (∀ {s} → ¬ ([]-cong-allowed s)) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-restrictions TR
  open Usage-restrictions UR

opaque

  -- Certain restrictions obtained from no-erased-matches-TR and
  -- only-some-erased-matches satisfy Only-some-erased-matches.

  Only-some-erased-matches-only-some-erased-matches :
    ∀ TR UR →
    Only-some-erased-matches
      (no-erased-matches-TR 𝕤 (no-erased-matches-TR 𝕨 TR))
      (only-some-erased-matches UR)
  Only-some-erased-matches-only-some-erased-matches _ _ 𝟙≢𝟘 =
      (_$ 𝟙≢𝟘) ∘→ proj₂
    , (λ where
         {s = 𝕤} → (_$ refl) ∘→ proj₂
         {s = 𝕨} → (_$ refl) ∘→ proj₂ ∘→ proj₁)
    , refl
    , refl

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

No-erased-matches : Type-restrictions → Usage-restrictions → Set a
No-erased-matches TR UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed-𝟙ᵐ r p q → r ≢ 𝟘) ×
  (∀ {p q}   → Unitrec-allowed-𝟙ᵐ p q   → p ≡ 𝟘 → Unitʷ-η) ×
  (∀ {s} → ¬ ([]-cong-allowed s)) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- Certain restrictions obtained from no-erased-matches-TR and
-- no-erased-matches-UR satisfy No-erased-matches.

No-erased-matches-no-erased-matches :
  ∀ TR UR →
  let TR′ = no-erased-matches-TR 𝕤 (no-erased-matches-TR 𝕨 TR) in
  No-erased-matches TR′ (no-erased-matches-UR TR′ UR)
No-erased-matches-no-erased-matches TR UR 𝟙≢𝟘 =
  case Only-some-erased-matches-only-some-erased-matches TR UR 𝟙≢𝟘 of λ
    (pr , rest) →
    (λ {_ _ _} → pr)
  , (λ {_ _} → (_$ 𝟙≢𝟘) ∘→ proj₂)
  , rest

opaque

  -- If Unitʷ-η holds for TR, then Only-some-erased-matches TR UR
  -- implies No-erased-matches TR UR.

  Only-some-erased-matches→No-erased-matches :
    ∀ TR UR →
    Type-restrictions.Unitʷ-η TR →
    Only-some-erased-matches TR UR → No-erased-matches TR UR
  Only-some-erased-matches→No-erased-matches _ _ η =
    Σ.map idᶠ ((λ {_ _} _ _ → η) ,_) ∘→_

-- An alternative to No-erased-matches that refers to
-- Type-variant instead of Type-restrictions

No-erased-matches′ : Type-variant → Usage-restrictions → Set a
No-erased-matches′ TV UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed 𝟙ᵐ r p q → r ≢ 𝟘) ×
  (∀ {p q}   → Unitrec-allowed 𝟙ᵐ p q   → p ≡ 𝟘 → Unitʷ-η) ×
  (∀ {s} → ¬ ([]-cong-allowed-mode s 𝟙ᵐ)) ×
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
      ._≟_                → dec
      .Unit-allowed? _    → yes _
      .ΠΣ-allowed? _ _ _  → yes _
      .K-allowed?         → case singleton b of λ where
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

------------------------------------------------------------------------
-- Some lemmas related to UD.Assumptions

opaque

  -- If grade equality is decidable and the modality supports usage
  -- inference for a given natrec-mode nm, UD.Assumptions holds for
  -- no-usage-restrictions nm b false.

  Assumptions-no-usage-restrictions :
    ⦃ ok : Natrec-mode-supports-usage-inference nm ⦄ →
    Decidable (_≡_ {A = M}) →
    UD.Assumptions (no-usage-restrictions nm b false)
  Assumptions-no-usage-restrictions dec = λ where
      ._≟_                        → dec
      .Prodrec-allowed-𝟙ᵐ? _ _ _  → yes _
      .Unitrec-allowed-𝟙ᵐ? _ _    → yes _
      .Emptyrec-allowed-𝟙ᵐ? _     → yes _
      .[]-cong-allowed-mode-𝟙ᵐ? _ → yes _
      .no-sink-or-≤𝟘              → inj₁ idᶠ
    where
    open UD.Assumptions

opaque

  -- The function not-all-erased-matches-JK preserves UD.Assumptions.

  Assumptions-not-all-erased-matches-JK :
    UD.Assumptions UR → UD.Assumptions (not-all-erased-matches-JK UR)
  Assumptions-not-all-erased-matches-JK as = λ where
      ._≟_                      → A._≟_
      .Prodrec-allowed-𝟙ᵐ?      → A.Prodrec-allowed-𝟙ᵐ?
      .Unitrec-allowed-𝟙ᵐ?      → A.Unitrec-allowed-𝟙ᵐ?
      .Emptyrec-allowed-𝟙ᵐ?     → A.Emptyrec-allowed-𝟙ᵐ?
      .[]-cong-allowed-mode-𝟙ᵐ? → A.[]-cong-allowed-mode-𝟙ᵐ?
      .no-sink-or-≤𝟘            → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions

opaque

  -- The function only-some-erased-matches preserves UD.Assumptions.

  Assumptions-only-some-erased-matches :
    UD.Assumptions UR → UD.Assumptions (only-some-erased-matches UR)
  Assumptions-only-some-erased-matches as = λ where
      ._≟_                       → A._≟_
      .Prodrec-allowed-𝟙ᵐ? r p q → A.Prodrec-allowed-𝟙ᵐ? r p q
                                     ×-dec
                                   (¬? trivial?
                                      →-dec
                                    ¬? (r A.≟ 𝟘))
      .Unitrec-allowed-𝟙ᵐ?       → A.Unitrec-allowed-𝟙ᵐ?
      .Emptyrec-allowed-𝟙ᵐ?      → A.Emptyrec-allowed-𝟙ᵐ?
      .[]-cong-allowed-mode-𝟙ᵐ?  → A.[]-cong-allowed-mode-𝟙ᵐ?
      .no-sink-or-≤𝟘             → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions

opaque

  -- The function no-erased-matches-UR TR preserves UD.Assumptions.

  Assumptions-no-erased-matches-UR :
    ∀ TR → UD.Assumptions UR →
    UD.Assumptions (no-erased-matches-UR TR UR)
  Assumptions-no-erased-matches-UR TR as = λ where
      ._≟_                      → A._≟_
      .Prodrec-allowed-𝟙ᵐ?      → A.Prodrec-allowed-𝟙ᵐ?
      .Unitrec-allowed-𝟙ᵐ? p q  → A.Unitrec-allowed-𝟙ᵐ? p q
                                    ×-dec
                                  (¬? trivial?
                                    →-dec
                                   p A.≟ 𝟘
                                    →-dec
                                   Unitʷ-η?)
      .Emptyrec-allowed-𝟙ᵐ?     → A.Emptyrec-allowed-𝟙ᵐ?
      .[]-cong-allowed-mode-𝟙ᵐ? → A.[]-cong-allowed-mode-𝟙ᵐ?
      .no-sink-or-≤𝟘            → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions (Assumptions-only-some-erased-matches as)
    open UD.Assumptions
    open Type-restrictions TR
