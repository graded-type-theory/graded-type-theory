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
open import Tools.Relation
open import Tools.Unit

open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions 𝕄

open import Definition.Typed.Restrictions 𝕄

private variable
  TR : Type-restrictions
  UR : Usage-restrictions

-- No type restrictions except that if the modality is trivial, then
-- []-cong is not allowed.

no-type-restrictions : Type-restrictions
no-type-restrictions = λ where
    .Unit-allowed     → λ _ → Lift _ ⊤
    .ΠΣ-allowed       → λ _ _ _ → Lift _ ⊤
    .K-allowed        → Lift _ ⊤
    .[]-cong-allowed  → λ _ → ¬ Trivial
    .[]-cong→Erased   → _
    .[]-cong→¬Trivial → idᶠ
  where
  open Type-restrictions

-- No restrictions for prodrec or unitrec, all erased matches are
-- allowed for J and K, Id-erased is inhabited, and starˢ is treated
-- as a sink.

no-usage-restrictions : Usage-restrictions
no-usage-restrictions = λ where
    .Prodrec-allowed                  → λ _ _ _ _ → Lift _ ⊤
    .Prodrec-allowed-downwards-closed → _
    .Unitrec-allowed                  → λ _ _ _ → Lift _ ⊤
    .Unitrec-allowed-downwards-closed → _
    .starˢ-sink                       → true
    .Id-erased                        → Lift _ ⊤
    .Id-erased?                       → yes _
    .erased-matches-for-J             → λ _ → all
    .erased-matches-for-J-≤ᵉᵐ         → _
    .erased-matches-for-K             → λ _ → all
    .erased-matches-for-K-≤ᵉᵐ         → _
  where
  open Usage-restrictions

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
-- "Erased" matches are allowed for trivial modalities. Erased matches
-- are also allowed when the mode is not 𝟙ᵐ, except for []-cong. (Note
-- that a variant of []-cong that works when the mode is not 𝟙ᵐ can be
-- defined without the use of []-cong, see
-- Graded.Box-cong.▸[]-cong-J-𝟘ᵐ.)

No-erased-matches : Type-restrictions → Usage-restrictions → Set a
No-erased-matches TR UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed 𝟙ᵐ r p q → r ≢ 𝟘) ×
  (∀ {p q}   → Unitrec-allowed 𝟙ᵐ p q   → p ≢ 𝟘) ×
  (∀ {s} → ¬ ([]-cong-allowed s)) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- The function adds the restriction that erased matches are not
-- allowed.

no-erased-matches-TR : Type-restrictions → Type-restrictions
no-erased-matches-TR TR = record TR
  { []-cong-allowed  = λ _ → Lift _ ⊥
  ; []-cong→Erased   = λ ()
  ; []-cong→¬Trivial = λ ()
  }
  where
  open Type-restrictions TR

-- The function adds the restriction that erased matches are not
-- allowed for the mode 𝟙ᵐ (for prodrec and unitrec the restriction
-- only applies to non-trivial modalities).

no-erased-matches-UR : Usage-restrictions → Usage-restrictions
no-erased-matches-UR UR = record UR
  { Prodrec-allowed = λ m r p q →
      Prodrec-allowed m r p q ×
      (¬ Trivial → m ≡ 𝟙ᵐ → r ≢ 𝟘)
  ; Prodrec-allowed-downwards-closed =
      Σ.map Prodrec-allowed-downwards-closed (λ _ _ ())
  ; Unitrec-allowed = λ m p q →
      Unitrec-allowed m p q ×
      (¬ Trivial → m ≡ 𝟙ᵐ → p ≢ 𝟘)
  ; Unitrec-allowed-downwards-closed =
      Σ.map Unitrec-allowed-downwards-closed (λ _ _ ())
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

-- The restrictions obtained from no-erased-matches-TR and
-- no-erased-matches-UR satisfy No-erased-matches.

No-erased-matches-no-erased-matches :
  ∀ TR UR →
  No-erased-matches (no-erased-matches-TR TR) (no-erased-matches-UR UR)
No-erased-matches-no-erased-matches _ _ 𝟙≢𝟘 =
    (_$ refl) ∘→ (_$ 𝟙≢𝟘) ∘→ proj₂
  , (_$ refl) ∘→ (_$ 𝟙≢𝟘) ∘→ proj₂
  , (λ ())
  , refl
  , refl
