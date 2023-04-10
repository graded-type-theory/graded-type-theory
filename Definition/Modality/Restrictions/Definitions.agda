------------------------------------------------------------------------
-- Definitions related to restrictions
------------------------------------------------------------------------

module Definition.Modality.Restrictions.Definitions {a} {M : Set a} where

open import Tools.Bool
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit

open import Definition.Modality M
open import Definition.Modality.Restrictions M

-- A function that modifies the Term-restrictions.

modify-term-restrictions :
  (Term-restrictions → Term-restrictions) →
  Restrictions → Restrictions
modify-term-restrictions f r = record r
  { term-restrictions = f term-restrictions
  }
  where
  open Restrictions r

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
