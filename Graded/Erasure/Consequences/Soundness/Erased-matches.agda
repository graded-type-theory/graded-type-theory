------------------------------------------------------------------------
-- Soundness of the extraction function in the presence of certain
-- kinds of erased matches
------------------------------------------------------------------------

import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Erasure.Target as T using (Strictness)
open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
import Graded.Restrictions.Zero-one
import Graded.Usage
open import Graded.Usage.Restrictions
open import Tools.Nat

module Graded.Erasure.Consequences.Soundness.Erased-matches
  {a} {M : Set a}
  (open Definition.Untyped M)
  {𝕄 : Modality M}
  {variant : Mode-variant 𝕄}
  (open Modality 𝕄)
  (open Graded.Mode.Instances.Zero-one variant)
  (open Graded.Restrictions.Zero-one 𝕄 variant)
  (TR : Type-restrictions 𝕄)
  (open Type-restrictions TR)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  (open Graded.Usage UR)
  (open Usage-restrictions UR)
  {kᵈ k : Nat}
  -- A definition context.
  (∇ : DCon (Term 0) kᵈ)
  -- A context.
  (Δ : Con Term k)
  -- Every definition in glassify ∇ is well-resourced.
  (well-resourced : ▸[ 𝟙ᵐ ] (glassify ∇))
  -- If erased matches are allowed for emptyrec when the mode is 𝟙ᵐ,
  -- then glassify ∇ and Δ are consistent with respect to a variant of
  -- the type system for which η-equality is allowed for weak unit
  -- types.
  (consistent :
     let open Definition.Typed (TR with-η-for-Unitʷ) in
     Emptyrec-allowed 𝟙ᵐ 𝟘 →
     Consistent (glassify ∇ » Δ))
  -- Certain erased matches are not allowed.
  (only-some-erased-matches : Only-some-erased-matches TR UR)
  -- Equality reflection is not allowed or Δ is empty.
  ⦃ ok : No-equality-reflection or-empty Δ ⦄
  -- The variant of extraction that is used.
  (str : Strictness)
  -- The modality's zero is well-behaved.
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

import Definition.Typed.QuantityTranslation as QT
open import Definition.Untyped.QuantityTranslation.Identity M

open import Graded.Context 𝕄
open import Graded.Modality.Morphism

import Graded.Erasure.Consequences.Soundness
open import Graded.Erasure.Extraction 𝕄
import Graded.Erasure.SucRed

open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Sum

private variable
  Γ   : Cons _ _
  A t : Term _
  s   : Strength
  l   : Universe-level

-- A variant of the type restrictions for which η-equality is allowed
-- for weak unit types.

TR-η : Type-restrictions 𝕄
TR-η = TR with-η-for-Unitʷ

-- TR is used by default.

open Definition.Typed TR
open Graded.Erasure.SucRed TR

-- The modules T-η and SR-η use TR-η.

private
  module T-η         = Definition.Typed TR-η
  module SR-η        = Graded.Erasure.SucRed TR-η
  module Soundness-η =
    Graded.Erasure.Consequences.Soundness.Soundness TR-η UR
      (record
         { well-resourced              = well-resourced
         ; consistent                  = consistent
         ; closed-or-no-erased-matches =
             inj₁ $
             Only-some-erased-matches→No-erased-matches
               TR-η UR _ only-some-erased-matches
         ; no-equality-reflection-or-empty =
             Type-restrictions.No-equality-reflection-or-empty⇔ TR-η
               .proj₂ $
             No-equality-reflection-or-empty⇔ .proj₁ $
             ok
         })
      str

opaque

  -- The relation _⊢_∷_ is contained in T-η._⊢_∷_.

  ⊢∷→⊢∷-η : Γ ⊢ t ∷ A → Γ T-η.⊢ t ∷ A
  ⊢∷→⊢∷-η ⊢t =
    case Is-order-embedding.tr-morphism Is-order-embedding-id of λ
      (m : Is-morphism 𝕄 𝕄 idᶠ) →
    subst₃ T-η._⊢_∷_ tr-Cons-id tr-Term-id tr-Term-id $
    QT.tr-⊢∷ TR TR-η idᶠ idᶠ m (Is-morphism→Is-Σ-morphism m)
      (record
         { unfolding-mode-preserved = refl
         ; Unit-preserved           = idᶠ
         ; ΠΣ-preserved             =
             λ {b = b} →
               subst (flip (ΠΣ-allowed _) _) $
               PE.sym $ tr-BinderMode-id b
         ; Opacity-preserved             = idᶠ
         ; K-preserved                   = idᶠ
         ; []-cong-preserved             = idᶠ
         ; Equality-reflection-preserved = idᶠ
         })
      ⊢t

opaque

  -- Soundness of erasure for natural numbers.
  --
  -- Note that SR-η._⊢_⇒ˢ*_∷ℕ is used in the statement of this
  -- theorem. This reduction relation uses the rule unitrec-β-η rather
  -- than unitrec-subst and unitrec-β.

  soundness-ℕ :
    ∇ » Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    ∃ λ n →
    glassify ∇ » Δ SR-η.⊢ t ⇒ˢ* sucᵏ n ∷ℕ ×
    eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
  soundness-ℕ = Soundness-η.soundness-ℕ ∘→ ⊢∷→⊢∷-η

opaque

  -- Soundness of erasure for unit types.
  --
  -- Note that T-η._⊢_⇒*_∷_ is used in the statement of this theorem.
  -- This reduction relation uses the rule unitrec-β-η rather than
  -- unitrec-subst and unitrec-β.

  soundness-Unit :
    ∇ » Δ ⊢ t ∷ Unit s l → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
    glassify ∇ » Δ T-η.⊢ t ⇒* star s l ∷ Unit s l ×
    eraseDCon str ∇ T.⊢ erase str t ⇒* T.star
  soundness-Unit = Soundness-η.soundness-Unit ∘→ ⊢∷→⊢∷-η
