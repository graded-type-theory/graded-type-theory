------------------------------------------------------------------------
-- Proof that consistent erased axioms do not jeopardize canonicity
-- if erased matches are not allowed.
------------------------------------------------------------------------

import Definition.Modality.Instances.Erasure.Modality
open import Definition.Modality.Instances.Erasure

open import Definition.Modality.Type-restrictions
open import Definition.Mode.Restrictions
import Definition.Typed
open import Definition.Typed.Restrictions Erasure
open import Definition.Untyped Erasure hiding (_∷_)

open import Tools.Empty

module Application.NegativeAxioms.Canonicity.Erased
  (mrs : Mode-restrictions)
  (open Definition.Modality.Instances.Erasure.Modality mrs)
  (R : Type-restrictions)
  (open Definition.Typed R)
  -- Erased matches are not allowed.
  (no-erased-matches : No-erased-matches ErasureModality R)
  {m} {Γ : Con Term m} (consistent : ∀{t} → Γ ⊢ t ∷ Empty → ⊥)
  where

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Mode ErasureModality
import Application.NegativeAxioms.Canonicity.NegativeErased
  mrs R no-erased-matches
  as NE
open import Application.NegativeAxioms.NegativeErasedContext
  ErasureModality (λ ()) R
open import Erasure.SucRed R

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
