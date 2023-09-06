------------------------------------------------------------------------
-- Proof that consistent erased axioms do not jeopardize canonicity
-- if erased matches are not allowed.
------------------------------------------------------------------------

open import Tools.Empty
open import Tools.Level

open import Graded.Modality.Instances.Erasure.Modality
open import Graded.Modality.Instances.Erasure

open import Graded.Restrictions
open import Graded.Usage.Restrictions Erasure
open import Graded.Modality.Variant lzero
import Definition.Typed
open import Definition.Typed.Restrictions Erasure
open import Definition.Untyped Erasure hiding (_∷_)

module Application.NegativeOrErasedAxioms.Canonicity.Erased
  (variant : Modality-variant)
  (TR : Type-restrictions)
  (open Definition.Typed TR)
  (UR : Usage-restrictions)
  -- Erased matches are not allowed.
  (no-erased-matches : No-erased-matches (ErasureModality variant) UR)
  {m} {Γ : Con Term m} (consistent : ∀{t} → Γ ⊢ t ∷ Empty → ⊥)
  where

open import Graded.Context (ErasureModality variant)
open import Graded.Usage (ErasureModality variant) UR
open import Graded.Mode (ErasureModality variant)
import Application.NegativeOrErasedAxioms.Canonicity
  variant TR UR no-erased-matches
  as NE
open import Application.NegativeOrErasedAxioms.NegativeOrErasedContext
  (ErasureModality variant) (λ ()) TR
open import Graded.Erasure.SucRed TR

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    t u : Term n

-- Canonicity theorem: Any well-typed term Γ ⊢ t ∷ ℕ, γ ▸ t
-- reduces to a numeral under the ⇒ˢ* reduction.

canonicityRed : Γ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t
              → ∃ λ u → Numeral u × Γ ⊢ t ⇒ˢ* u ∷ℕ
canonicityRed ⊢t 𝟘▸t = NE.canonicityRed erasedContext consistent ⊢t 𝟘▸t

-- Canonicity theorem: Any well-typed term Γ ⊢ t : ℕ is convertible to a numeral.

canonicityEq : Γ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t
             → ∃ λ u → Numeral u × Γ ⊢ t ≡ u ∷ ℕ
canonicityEq ⊢t 𝟘▸t =
  let u , numU , d = canonicityRed ⊢t 𝟘▸t
  in  u , numU , subset*Termˢ d