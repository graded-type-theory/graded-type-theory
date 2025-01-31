------------------------------------------------------------------------
-- Graded.Erasure validity of the empty type.
------------------------------------------------------------------------

import Definition.Typed
open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Erasure.LogicalRelation.Fundamental.Empty
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Graded.Mode 𝕄)
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (open Definition.Typed R)
  (UR : Usage-restrictions 𝕄)
  (open Usage-restrictions UR)
  (as : Assumptions R)
  (open Assumptions as)
  (consistent : Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden as
import Graded.Erasure.Target as T
open import Graded.Erasure.Extraction 𝕄

open import Definition.LogicalRelation.Substitution R
open import Definition.Typed.Substitution R
open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private
  variable
    n : Nat
    l : Universe-level
    γ : Conₘ n
    p : M
    Γ : Con Term n
    t A : Term n
    v : T.Term n
    m : Mode

opaque

  -- Validity of Empty.

  Emptyʳ : γ ▸ Γ ⊩ʳ Empty ∷[ m ] U 0
  Emptyʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷U⇔ .proj₂ (_ , ≤ᵘ-refl , Uᵣ (λ { refl → T.refl })))

opaque

  -- Validity of emptyrec

  emptyrecʳ :
    Emptyrec-allowed m p →
    Γ ⊢ t ∷ Empty →
    γ ▸ Γ ⊩ʳ t ∷[ m ᵐ· p ] Empty →
    p ·ᶜ γ ▸ Γ ⊩ʳ emptyrec p A t ∷[ m ] A
  emptyrecʳ {m = 𝟘ᵐ} _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  emptyrecʳ {m = 𝟙ᵐ} {p} {Γ} {t} {γ} ok ⊢t ⊩ʳt =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊩σ σ®σ′ →
    case is-𝟘? p of λ where
      (yes refl) →
        ⊥-elim (consistent ok _ (subst-⊢∷ ⊢t (escape-⊩ˢ∷ ⊩σ .proj₂)))
      (no p≢𝟘) →
        case PE.sym (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) of λ
          𝟙ᵐ≡⌞p⌟ →
        case                                                  $⟨ σ®σ′ ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ p ·ᶜ γ                           →⟨ (subsumption-®∷[]◂ λ x →

              (p ·ᶜ γ) ⟨ x ⟩ ≡ 𝟘                                    →⟨ ·ᶜ-zero-product-⟨⟩ γ ⟩
              p ≡ 𝟘 ⊎ γ ⟨ x ⟩ ≡ 𝟘                                   →⟨ (λ { (inj₁ p≡𝟘)    → ⊥-elim (p≢𝟘 p≡𝟘)
                                                                          ; (inj₂ γ⟨x⟩≡𝟘) → γ⟨x⟩≡𝟘
                                                                          }) ⟩
              γ ⟨ x ⟩ ≡ 𝟘                                           □) ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                ≡⟨ cong₃ (_®_∷[_]_◂_ _ _) 𝟙ᵐ≡⌞p⌟ refl refl ⟩→

          σ ® σ′ ∷[ ⌞ p ⌟ ] Γ ◂ γ                             →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊩σ ⟩

          t [ σ ] ® erase str t T.[ σ′ ] ∷ Empty ◂ ⌜ ⌞ p ⌟ ⌝  →⟨ ®∷→®∷◂ω (non-trivial ∘→ PE.trans (PE.cong ⌜_⌝ 𝟙ᵐ≡⌞p⌟)) ⟩

          t [ σ ] ® erase str t T.[ σ′ ] ∷ Empty              →⟨ ®∷Empty⇔ .proj₁ ⟩

          t [ σ ] ® erase str t T.[ σ′ ] ∷Empty               □

        of λ ()
