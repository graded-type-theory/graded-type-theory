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
import Graded.Erasure.LogicalRelation.Irrelevance as as I
open import Graded.Erasure.LogicalRelation.Subsumption as
import Graded.Erasure.Target as T

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Irrelevance R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Empty R
open import Definition.Untyped M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private
  variable
    n : Nat
    l : TypeLevel
    γ : Conₘ n
    p : M
    Γ : Con Term n
    t A : Term n
    v : T.Term n
    m : Mode
    ⊩Γ : ⊩ᵛ _

Emptyʳ : ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Empty ∷[ m ] U / [Γ] / [U]
Emptyʳ {m = m} ⊢Γ =
  [Γ] , [U] , λ _ _ → Uᵣ (λ { refl → T.refl }) ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

emptyrecʳ′ :
  ∀ t →
  Emptyrec-allowed m p →
  (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
  Γ ⊩ᵛ⟨ l ⟩ t ∷ Empty / ⊩Γ / Emptyᵛ ⊩Γ →
  γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· p ] Empty / ⊩Γ / Emptyᵛ ⊩Γ →
  p ·ᶜ γ ▸ Γ ⊩ʳ⟨ l ⟩ emptyrec p A t ∷[ m ] A / ⊩Γ / ⊩A
emptyrecʳ′ {m = 𝟘ᵐ} _ _ _ _ _ _ _ with is-𝟘? 𝟘
... | yes _  = _
... | no 𝟘≢𝟘 = ⊥-elim $ 𝟘≢𝟘 refl
emptyrecʳ′ {m = 𝟙ᵐ} {p} {γ} t ok _ ⊩t ⊩ʳt ⊩σ σ®σ′ with is-𝟘? 𝟙 | is-𝟘? p
... | yes _ | _       = _
... | no _  | yes refl =
  case ⊩t ⊢Δ ⊩σ .proj₁ of λ where
    (Emptyₜ _ _ _ (ne (neNfₜ _ ⊢k _))) →
      ⊥-elim $ consistent ok _ ⊢k
... | no _  | no p≢𝟘 =
  case
    subst (λ m → _ ▸ _ ⊩ʳ⟨ _ ⟩ t ∷[ m ] Empty / _ / Emptyᵛ _)
      (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ⊩ʳt ⊩σ
      (subsumptionSubst σ®σ′ λ _ ≡𝟘 →
       case ·ᶜ-zero-product-⟨⟩ γ ≡𝟘 of λ where
         (inj₁ p≡𝟘) → ⊥-elim $ p≢𝟘 p≡𝟘
         (inj₂ ≡𝟘)  → ≡𝟘)
    ◀≢𝟘 non-trivial
  of λ ()

emptyrecʳ :
  ∀ t →
  Emptyrec-allowed m p →
  (⊩Empty : Γ ⊩ᵛ⟨ l ⟩ Empty / ⊩Γ)
  (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
  Γ ⊩ᵛ⟨ l ⟩ t ∷ Empty / ⊩Γ / ⊩Empty →
  γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ᵐ· p ] Empty / ⊩Γ / ⊩Empty →
  p ·ᶜ γ ▸ Γ ⊩ʳ⟨ l ⟩ emptyrec p A t ∷[ m ] A / ⊩Γ / ⊩A
emptyrecʳ {l} t ok ⊩Empty₁ ⊩A ⊩t₁ ⊩ʳt =
  let ⊩Empty₂ = Emptyᵛ {l = l} _
      ⊩t₂     = irrelevanceTerm {t = t} _ _ ⊩Empty₁ ⊩Empty₂ ⊩t₁
  in  emptyrecʳ′ t ok ⊩A ⊩t₂ $
      I.irrelevance {t = t} _ _ ⊩Empty₁ ⊩Empty₂ ⊩ʳt
