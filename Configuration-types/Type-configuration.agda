------------------------------------------------------------------------
-- Functions that construct type configurations
------------------------------------------------------------------------

import Graded.Modality

module Configuration-types.Type-configuration
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

open import Configuration-types
open import Configuration-types.Omega 𝕄

open import Graded.Modality.Omega-instances
open import Graded.Modality.Properties 𝕄

import Definition.Typechecking.Decidable.Assumptions as TD
open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

private variable
  TC : Type-configuration _
  b  : Bool
  s  : Strength

------------------------------------------------------------------------
-- Functions that construct type configurations

-- No type restrictions except that
-- * there is a dedicated grade omega if and only if such a grade is
--   supplied, and if no such grade is supplied, then quotient types
--   are not allowed,
-- * if the modality is trivial, then []-cong and quotient types are
--   not allowed,
-- * the K rule is allowed if and only if the first boolean is true,
-- * η-equality is not allowed for weak unit types,
-- * opacity is allowed if and only if the second boolean is false,
--   and
-- * equality reflection is allowed if and only if the second boolean
--   is true.
-- Furthermore transitive unfolding is used.

no-type-restrictions :
  With-or-without-omega → Bool → Bool → Type-configuration 𝕄
no-type-restrictions omega k equality-reflection = λ where
    .TC⁻ → λ where
      .level-support                 → level-type small
      .Omega-plus-allowed            → Lift _ ⊤
      .Unit-allowed                  → λ _ → Lift _ ⊤
      .η-for-Unitʷ                   → false
      .K-allowed                     → Lift _ (T k)
      .Equality-reflection           → Lift _ (T equality-reflection)
      .Equality-reflection?          → Lift? (T? equality-reflection)
      .Quot-allowed                  → ¬ Trivial × With-omega omega
      .Opacity-allowed               → Lift _ (¬ T equality-reflection)
      .Opacity-allowed?              → Lift?
                                         (¬? (T? equality-reflection))
      .no-opaque-equality-reflection → (_∘→ Lift.lower) ∘→ Lift.lower
      .unfolding-mode                → transitive
    .with-or-without-omega      → omega
    .Quot-allowed→Omega-allowed → proj₂
    .ΠΣ-allowed                 → λ _ _ _ → Lift _ ⊤
    .[]-cong-allowed            → λ _ → ¬ Trivial
    .[]-cong→Erased             → _
    .[]-cong→¬Trivial           → idᶠ
  where
  open Type-configuration
  open Type-configuration⁻

-- The function adds the restriction that the two quantities on a Π-
-- or Σ-type have to be equal.

equal-binder-quantities : Type-configuration 𝕄 → Type-configuration 𝕄
equal-binder-quantities TC = record TC
  { ΠΣ-allowed     = λ b p q → ΠΣ-allowed b p q × p ≡ q
  ; []-cong→Erased = λ ok →
      []-cong→Erased ok .proj₁ , []-cong→Erased ok .proj₂ , refl
  }
  where
  open Type-configuration TC

-- The function adds the restriction that the second quantities
-- associated with Π- and Σ-types are equal to 𝟘.

second-ΠΣ-quantities-𝟘 :
  Type-configuration 𝕄 → Type-configuration 𝕄
second-ΠΣ-quantities-𝟘 TC = record TC
  { ΠΣ-allowed     = λ b p q → ΠΣ-allowed b p q × q ≡ 𝟘
  ; []-cong→Erased = λ ok →
      []-cong→Erased ok .proj₁ , []-cong→Erased ok .proj₂ , refl
  }
  where
  open Type-configuration TC

-- The function second-ΠΣ-quantities-𝟘-or-ω 𝕄 adds the restriction
-- that if the first quantity associated with a Π- or Σ-type is the ω
-- grade of 𝕄, then the second quantity is also ω, and if the first
-- quantity is not ω, then the second quantity is the 𝟘 of 𝕄.

second-ΠΣ-quantities-𝟘-or-ω :
  ⦃ ok : Has-omega 𝕄 ⦄ →
  Type-configuration 𝕄 → Type-configuration 𝕄
second-ΠΣ-quantities-𝟘-or-ω TC = record TC
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
  open Type-configuration TC

-- A lemma used to define strong-types-restricted and no-strong-types.

strong-types-restricted′ :
  (P : BinderMode → M → Set a) →
  (∀ {s} → s ≢ 𝕤 → P (BMΣ s) 𝟘) →
  Type-configuration 𝕄 → Type-configuration 𝕄
strong-types-restricted′ P hyp TC = record TC
  { TC⁻ = record TC⁻
    { Unit-allowed = λ s →
        Unit-allowed s × s ≢ 𝕤
    }
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
  open Type-configuration TC

-- The function strong-types-restricted adds the following
-- restrictions:
--
-- * Strong unit types are not allowed.
-- * If strong Σ-types are allowed for p and q, then p is 𝟙.
-- * []-cong is not allowed for 𝕤.

strong-types-restricted :
  Type-configuration 𝕄 → Type-configuration 𝕄
strong-types-restricted =
  strong-types-restricted′ (λ b p → b ≡ BMΣ 𝕤 → p ≡ 𝟙)
    (λ { hyp refl → ⊥-elim $ hyp refl })

-- The function no-strong-types adds the following restrictions:
--
-- * Strong unit types are not allowed.
-- * Strong Σ-types are not allowed.
-- * []-cong is not allowed for 𝕤.

no-strong-types :
  Type-configuration 𝕄 → Type-configuration 𝕄
no-strong-types =
  strong-types-restricted′ (λ b _ → Lift _ (b ≢ BMΣ 𝕤))
    (λ hyp → lift (λ { refl → ⊥-elim $ hyp refl }))

-- The function _with-η-for-Unitʷ enables η-equality for weak unit
-- types.

_with-η-for-Unitʷ : Type-configuration 𝕄 → Type-configuration 𝕄
TC with-η-for-Unitʷ = record TC
  { TC⁻ = record TC⁻
    { η-for-Unitʷ = true
    }
  }
  where
  open Type-configuration TC

-- The function with-[]-cong enables unrestricted support for []-cong
-- if the modality is non-trivial.

with-[]-cong : Type-configuration 𝕄 → Type-configuration 𝕄
with-[]-cong TC = record TC
  { TC⁻ = record TC⁻
    { Unit-allowed = λ s → Unit-allowed s ⊎ ¬ Trivial
    }
  ; ΠΣ-allowed       = λ where
                         (BMΣ s) p q → ΠΣ-allowed (BMΣ s) p q ⊎
                                       ¬ Trivial × p ≡ 𝟘 × q ≡ 𝟘
                         BMΠ     p q → ΠΣ-allowed BMΠ p q
  ; []-cong-allowed  = λ s → []-cong-allowed s ⊎ ¬ Trivial
  ; []-cong→Erased   = [ Σ.map inj₁ inj₁ ∘→ []-cong→Erased
                       , (λ non-trivial →
                            inj₂ non-trivial ,
                            inj₂ (non-trivial , refl , refl))
                       ]
  ; []-cong→¬Trivial = [ []-cong→¬Trivial , idᶠ ]
  }
  where
  open Type-configuration TC

-- The function no-[]-cong disables support for []-cong.

no-[]-cong : Type-configuration 𝕄 → Type-configuration 𝕄
no-[]-cong TR = record TR
  { []-cong-allowed  = λ _ → Lift _ ⊥
  ; []-cong→Erased   = λ ()
  ; []-cong→¬Trivial = λ ()
  }

-- The function with-equality-reflection enables support for equality
-- reflection, and disables support for opaque definitions.

with-equality-reflection : Type-configuration 𝕄 → Type-configuration 𝕄
with-equality-reflection TC = record TC
  { TC⁻ = record (TC .Type-configuration.TC⁻)
    { Equality-reflection           = Lift _ ⊤
    ; Equality-reflection?          = yes _
    ; Opacity-allowed               = Lift _ ⊥
    ; Opacity-allowed?              = no (λ ())
    ; no-opaque-equality-reflection = λ ()
    }
  }

-- The function no-quotients adds the restriction that quotient types
-- are not allowed.

no-quotients : Type-configuration 𝕄 → Type-configuration 𝕄
no-quotients TC = record TC
  { TC⁻ =
    record (TC .Type-configuration.TC⁻)
      { Quot-allowed = Lift _ ⊥
      }
  ; Quot-allowed→Omega-allowed = λ ()
  }

------------------------------------------------------------------------
-- Some lemmas related to TD.Assumptions

opaque

  -- If grade equality is decidable, then TD.Assumptions holds for
  -- no-type-restrictions omega b false.

  Assumptions-no-type-restrictions :
    {omega : With-or-without-omega} →
    Decidable (_≡_ {A = M}) →
    TD.Assumptions (no-type-restrictions omega b false)
  Assumptions-no-type-restrictions {b} dec = λ where
      ._≟_                 → dec
      .Omega-plus-allowed? → yes _
      .Unit-allowed? _     → yes _
      .ΠΣ-allowed? _ _ _   → yes _
      .K-allowed?          → case singleton b of λ where
        (true  , refl) → yes _
        (false , refl) → no (λ ())
      .[]-cong-allowed? _ →
        ¬? trivial?
      .Quot-allowed? →
        ¬? trivial? ×-dec With-omega?
      .no-equality-reflection (lift ())
    where
    open TD.Assumptions

opaque

  -- The function equal-binder-quantities preserves TD.Assumptions.

  Assumptions-equal-binder-quantities :
    TD.Assumptions TC → TD.Assumptions (equal-binder-quantities TC)
  Assumptions-equal-binder-quantities as = λ where
      ._≟_                    → A._≟_
      .Omega-plus-allowed?    → A.Omega-plus-allowed?
      .Unit-allowed?          → A.Unit-allowed?
      .ΠΣ-allowed? b p q      → A.ΠΣ-allowed? b p q ×-dec p A.≟ q
      .K-allowed?             → A.K-allowed?
      .[]-cong-allowed?       → A.[]-cong-allowed?
      .Quot-allowed?          → A.Quot-allowed?
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions

opaque

  -- The function second-ΠΣ-quantities-𝟘 preserves TD.Assumptions.

  Assumptions-second-ΠΣ-quantities-𝟘 :
    TD.Assumptions TC → TD.Assumptions (second-ΠΣ-quantities-𝟘 TC)
  Assumptions-second-ΠΣ-quantities-𝟘 as = λ where
      ._≟_                    → A._≟_
      .Omega-plus-allowed?    → A.Omega-plus-allowed?
      .Unit-allowed?          → A.Unit-allowed?
      .ΠΣ-allowed? b p q      → A.ΠΣ-allowed? b p q ×-dec q A.≟ 𝟘
      .K-allowed?             → A.K-allowed?
      .[]-cong-allowed?       → A.[]-cong-allowed?
      .Quot-allowed?          → A.Quot-allowed?
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions

opaque

  -- The function second-ΠΣ-quantities-𝟘-or-ω preserves
  -- TD.Assumptions.

  Assumptions-second-ΠΣ-quantities-𝟘-or-ω :
    ⦃ ok : Has-omega 𝕄 ⦄ →
    TD.Assumptions TC → TD.Assumptions (second-ΠΣ-quantities-𝟘-or-ω TC)
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
      .Quot-allowed?          → A.Quot-allowed?
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
    TD.Assumptions TC →
    TD.Assumptions (strong-types-restricted′ P ok TC)
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
      .Quot-allowed?          → A.Quot-allowed?
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions

opaque

  -- The function strong-types-restricted preserves TD.Assumptions.

  Assumptions-strong-types-restricted :
    TD.Assumptions TC → TD.Assumptions (strong-types-restricted TC)
  Assumptions-strong-types-restricted as =
    Assumptions-strong-types-restricted′
      (λ b p → decBinderMode b (BMΣ 𝕤) →-dec p ≟ 𝟙)
      as
    where
    open TD.Assumptions as

opaque

  -- The function no-strong-types preserves TD.Assumptions.

  Assumptions-no-strong-types :
    TD.Assumptions TC → TD.Assumptions (no-strong-types TC)
  Assumptions-no-strong-types as =
    Assumptions-strong-types-restricted′
      (λ b _ → Dec.map lift Lift.lower (¬? (decBinderMode b (BMΣ 𝕤))))
      as
    where
    open TD.Assumptions as

opaque

  -- The function no-quotients preserves TD.Assumptions.

  Assumptions-no-quotients :
    TD.Assumptions TC → TD.Assumptions (no-quotients TC)
  Assumptions-no-quotients as = λ where
      ._≟_                    → A._≟_
      .Omega-plus-allowed?    → A.Omega-plus-allowed?
      .Unit-allowed?          → A.Unit-allowed?
      .ΠΣ-allowed?            → A.ΠΣ-allowed?
      .K-allowed?             → A.K-allowed?
      .[]-cong-allowed? s′    → A.[]-cong-allowed? s′
      .Quot-allowed?          → no (λ ())
      .no-equality-reflection → A.no-equality-reflection
    where
    module A = TD.Assumptions as
    open TD.Assumptions
