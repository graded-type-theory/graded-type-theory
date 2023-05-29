------------------------------------------------------------------------
-- Definitions related to type and usage restrictions
------------------------------------------------------------------------

module Definition.Modality.Restrictions {a} {M : Set a} where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit

open import Definition.Modality M
open import Definition.Modality.Usage.Restrictions M

open import Definition.Typed.Restrictions M

-- No type restrictions.

no-type-restrictions : Type-restrictions
no-type-restrictions = λ where
    .Unit-restriction    → Lift _ ⊤
    .ΠΣ-restriction      → λ _ _ _ → Lift _ ⊤
  where
  open Type-restrictions

-- No usage restrictions.

no-usage-restrictions : Usage-restrictions
no-usage-restrictions = λ where
    .Prodrec-restriction → λ _ _ _ → Lift _ ⊤
  where
  open Usage-restrictions

-- The function adds the restriction that the two quantities on a Π-
-- or Σ-type have to be equal.

equal-binder-quantities : Type-restrictions → Type-restrictions
equal-binder-quantities R = record R
  { ΠΣ-restriction = λ b p q → ΠΣ-restriction b p q × p ≡ q
  }
  where
  open Type-restrictions R

-- The function adds the restriction that the second quantities
-- associated with Π- and Σ-types are equal to 𝟘.

second-ΠΣ-quantities-𝟘 :
  Modality → Type-restrictions → Type-restrictions
second-ΠΣ-quantities-𝟘 𝕄 R = record R
  { ΠΣ-restriction = λ b p q → ΠΣ-restriction b p q × q ≡ 𝟘
  }
  where
  open Modality 𝕄
  open Type-restrictions R

-- The function adds the restriction that if the first quantity
-- associated with a Π- or Σ-type is 𝟘, then the second quantity is
-- also 𝟘, and if the first quantity is not 𝟘, then the second
-- quantity has the given value.

second-ΠΣ-quantities-𝟘-or-ω :
  M → Modality → Type-restrictions → Type-restrictions
second-ΠΣ-quantities-𝟘-or-ω ω 𝕄 R = record R
  { ΠΣ-restriction = λ b p q →
      ΠΣ-restriction b p q ×
      (p ≡ 𝟘 → q ≡ 𝟘) ×
      (p ≢ 𝟘 → q ≡ ω)
  }
  where
  open Modality 𝕄
  open Type-restrictions R

-- The property of not allowing erased matches.
--
-- "Erased" matches are allowed for trivial modalities.

No-erased-matches : Modality → Usage-restrictions → Set a
No-erased-matches 𝕄 R =
  𝟙 ≢ 𝟘 → ∀ {r p q} → Prodrec-restriction r p q → r ≢ 𝟘
  where
  open Modality 𝕄
  open Usage-restrictions R

-- The function adds the restriction that erased matches are not
-- allowed (for non-trivial modalities).

no-erased-matches : Modality → Usage-restrictions → Usage-restrictions
no-erased-matches 𝕄 R = record R
  { Prodrec-restriction = λ r p q →
      Prodrec-restriction r p q × (𝟙 ≢ 𝟘 → r ≢ 𝟘)
  }
  where
  open Modality 𝕄
  open Usage-restrictions R

-- The modalities obtained from no-erased-matches satisfy
-- No-erased-matches.

No-erased-matches-no-erased-matches :
  ∀ 𝕄 R → No-erased-matches 𝕄 (no-erased-matches 𝕄 R)
No-erased-matches-no-erased-matches
  𝕄 R 𝟙≢𝟘 {r = r} {p = p} {q = q} =
  Prodrec-restriction r p q × (𝟙 ≢ 𝟘 → r ≢ 𝟘)  →⟨ proj₂ ⟩
  (𝟙 ≢ 𝟘 → r ≢ 𝟘)                              →⟨ _$ 𝟙≢𝟘 ⟩
  r ≢ 𝟘                                        □
  where
  open Modality 𝕄
  open Usage-restrictions R
