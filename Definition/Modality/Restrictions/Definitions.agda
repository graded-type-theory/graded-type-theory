------------------------------------------------------------------------
-- Definitions related to restrictions
------------------------------------------------------------------------

module Definition.Modality.Restrictions.Definitions {a} {M : Set a} where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit

open import Definition.Modality M
open import Definition.Modality.Restrictions M

private variable
  𝕄 : Modality

-- A function that modifies the Term-restrictions.

modify-term-restrictions :
  (Term-restrictions → Term-restrictions) →
  Restrictions → Restrictions
modify-term-restrictions f r = record r
  { term-restrictions = f term-restrictions
  }
  where
  open Restrictions r

-- A function that modifies the Term-restrictions.

modify-term-restrictions-Modality :
  (Modality → Term-restrictions) →
  Modality → Modality
modify-term-restrictions-Modality f 𝕄 = record 𝕄
  { modalityWithout⊛ = record modalityWithout⊛
    { restrictions = record restrictions
      { term-restrictions = f 𝕄
      }
    }
  }
  where
  open Modality 𝕄

-- No type/term restrictions.

no-term-restrictions : Term-restrictions
no-term-restrictions = record
  { Prodrec    = λ _ _ _ → Lift _ ⊤
  ; Binder     = λ _ _ _ → Lift _ ⊤
  }

-- No restrictions, except that 𝟘ᵐ is only allowed if the given
-- boolean is true.

𝟘ᵐ-allowed-if : Bool → Restrictions
𝟘ᵐ-allowed-if b = record
  { 𝟘ᵐ-allowed        = b
  ; term-restrictions = no-term-restrictions
  }

-- No restrictions.

no-restrictions : Restrictions
no-restrictions = 𝟘ᵐ-allowed-if true

-- The function adds the restriction that the two quantities on a Π-
-- or Σ-type have to be equal.

equal-binder-quantities : Term-restrictions → Term-restrictions
equal-binder-quantities r = record r
  { Binder = λ b p q → Binder b p q × p ≡ q
  }
  where
  open Term-restrictions r

-- The function adds the restriction that the second quantities
-- associated with Π- and Σ-types are equal to 𝟘.

second-ΠΣ-quantities-𝟘 : Modality → Term-restrictions
second-ΠΣ-quantities-𝟘 𝕄 = record term-restrictions
  { Binder = λ b p q → Binder b p q × q ≡ 𝟘
  }
  where
  open Modality 𝕄

-- The function adds the restriction that if the first quantity
-- associated with a Π- or Σ-type is 𝟘, then the second quantity is
-- also 𝟘, and if the first quantity is not 𝟘, then the second
-- quantity has the given value.

second-ΠΣ-quantities-𝟘-or-ω : M → Modality → Term-restrictions
second-ΠΣ-quantities-𝟘-or-ω ω 𝕄 = record term-restrictions
  { Binder = λ b p q →
      Binder b p q ×
      (p ≡ 𝟘 → q ≡ 𝟘) ×
      (p ≢ 𝟘 → q ≡ ω)
  }
  where
  open Modality 𝕄

-- The property of not allowing erased matches.
--
-- "Erased" matches are allowed for trivial modalities.

No-erased-matches : Modality → Set a
No-erased-matches 𝕄 =
  𝟙 ≢ 𝟘 → ∀ {r p q} → Prodrec r p q → r ≢ 𝟘
  where
  open Modality 𝕄

-- The function adds the restriction that erased matches are not
-- allowed (for non-trivial modalities).

no-erased-matches : Modality → Term-restrictions
no-erased-matches 𝕄 = record term-restrictions
  { Prodrec = λ r p q → Prodrec r p q × (𝟙 ≢ 𝟘 → r ≢ 𝟘)
  }
  where
  open Modality 𝕄

-- The modalities obtained from
-- modify-term-restrictions-Modality no-erased-matches satisfy
-- No-erased-matches.

No-erased-matches-no-erased-matches :
  No-erased-matches
    (modify-term-restrictions-Modality no-erased-matches 𝕄)
No-erased-matches-no-erased-matches
  {𝕄 = 𝕄} 𝟙≢𝟘 {r = r} {p = p} {q = q} =
  Prodrec r p q × (𝟙 ≢ 𝟘 → r ≢ 𝟘)  →⟨ proj₂ ⟩
  (𝟙 ≢ 𝟘 → r ≢ 𝟘)                  →⟨ _$ 𝟙≢𝟘 ⟩
  r ≢ 𝟘                            □
  where
  open Modality 𝕄
