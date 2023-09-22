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
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

open import Graded.Modality.Properties 𝕄
open import Graded.Usage.Restrictions M

open import Definition.Typed.Restrictions 𝕄

private variable
  TR : Type-restrictions
  UR : Usage-restrictions

-- No type restrictions except that if the modality is trivial, then
-- []-cong is not allowed.

no-type-restrictions : Type-restrictions
no-type-restrictions = λ where
    .Unit-allowed     → Lift _ ⊤
    .ΠΣ-allowed       → λ _ _ _ → Lift _ ⊤
    .K-allowed        → Lift _ ⊤
    .[]-cong-allowed  → ¬ Trivial
    .[]-cong→Erased   → _
    .[]-cong→¬Trivial → idᶠ
  where
  open Type-restrictions

-- No usage restrictions, and Id-erased, Erased-matches-for-J and
-- Erased-matches-for-K are all inhabited.

no-usage-restrictions : Usage-restrictions
no-usage-restrictions = λ where
  .Usage-restrictions.Prodrec-allowed       → λ _ _ _ → Lift _ ⊤
  .Usage-restrictions.Id-erased             → Lift _ ⊤
  .Usage-restrictions.Id-erased?            → yes _
  .Usage-restrictions.Erased-matches-for-J  → Lift _ ⊤
  .Usage-restrictions.Erased-matches-for-J? → yes _
  .Usage-restrictions.Erased-matches-for-K  → Lift _ ⊤
  .Usage-restrictions.Erased-matches-for-K? → yes _

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

-- The property of not allowing erased matches.
--
-- "Erased" matches are allowed for trivial modalities.

No-erased-matches : Type-restrictions → Usage-restrictions → Set a
No-erased-matches TR UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed r p q → r ≢ 𝟘) ×
  ¬ []-cong-allowed ×
  ¬ Erased-matches-for-J ×
  ¬ Erased-matches-for-K
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- The function adds the restriction that erased matches are not
-- allowed.

no-erased-matches-TR : Type-restrictions → Type-restrictions
no-erased-matches-TR TR = record TR
  { []-cong-allowed  = Lift _ ⊥
  ; []-cong→Erased   = λ ()
  ; []-cong→¬Trivial = λ ()
  }
  where
  open Type-restrictions TR

-- The function adds the restriction that erased matches are not
-- allowed (for prodrec the restriction only applies to non-trivial
-- modalities).

no-erased-matches-UR : Usage-restrictions → Usage-restrictions
no-erased-matches-UR UR = record UR
  { Prodrec-allowed       = λ r p q →
                              Prodrec-allowed r p q ×
                              (¬ Trivial → r ≢ 𝟘)
  ; Erased-matches-for-J  = Lift _ ⊥
  ; Erased-matches-for-J? = no (λ ())
  ; Erased-matches-for-K  = Lift _ ⊥
  ; Erased-matches-for-K? = no (λ ())
  }
  where
  open Usage-restrictions UR

-- The restrictions obtained from no-erased-matches-TR and
-- no-erased-matches-UR satisfy No-erased-matches.

No-erased-matches-no-erased-matches :
  ∀ TR UR →
  No-erased-matches (no-erased-matches-TR TR) (no-erased-matches-UR UR)
No-erased-matches-no-erased-matches _ _ 𝟙≢𝟘 =
  (_$ 𝟙≢𝟘) ∘→ proj₂ , (λ ()) , (λ ()) , (λ ())
