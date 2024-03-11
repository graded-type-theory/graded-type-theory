------------------------------------------------------------------------
-- Graded.Erasure validity of the natural numbers.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Tools.PropositionalEquality
open import Tools.Relation

module Graded.Erasure.LogicalRelation.Fundamental.Nat
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as

open import Graded.Erasure.Extraction 𝕄 is-𝟘?
open import Graded.Erasure.LogicalRelation is-𝟘? as
open import Graded.Erasure.LogicalRelation.Irrelevance is-𝟘? as
open import Graded.Erasure.LogicalRelation.Reduction is-𝟘? as
open import Graded.Erasure.LogicalRelation.Subsumption is-𝟘? as
open import Graded.Erasure.LogicalRelation.Value is-𝟘? as
import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP
open import Graded.Erasure.Target.Reasoning

open import Definition.Typed R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Properties R

open import Definition.Untyped M as U hiding (_∷_)

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Nat R

open import Graded.Context 𝕄
open import Graded.Mode 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    γ : Conₘ n
    Γ : Con Term n
    t t′ : Term n
    v v′ : T.Term n
    p : M
    m : Mode

ℕʳ : ⊢ Γ
   → ∃ λ ([Γ] : ⊩ᵛ Γ)
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ ℕ ∷[ m ] U / [Γ] / [U]
ℕʳ {m = m} ⊢Γ = [Γ] , [U] , λ _ _ → Uᵣ T.refl ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

zeroʳ : ∀ {l} → ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ zero ∷[ m ] ℕ / [Γ] / [ℕ]
zeroʳ {m = m} ⊢Γ =
    [Γ] , [ℕ]
    , λ _ _ → zeroᵣ (id (zeroⱼ ⊢Δ)) T.refl ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [ℕ] = ℕᵛ [Γ]

-- successor case of the logical relation for any quantity

sucʳ : ∀ {l}
     → ([Γ] : ⊩ᵛ Γ)
       ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
       (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] ℕ / [Γ] / [ℕ])
     → Γ ⊢ t ∷ ℕ
     → γ ▸ Γ ⊩ʳ⟨ l ⟩ suc t ∷[ m ] ℕ / [Γ] / [ℕ]
sucʳ {Γ = Γ} {γ = γ} {t = t} {m = m} {l = l}
     [Γ] [ℕ] ⊩ʳt Γ⊢t:ℕ {σ = σ} {σ′ = σ′} [σ] σ®σ′
  with is-𝟘? ⌜ m ⌝
… | yes _ = _
… | no _  =
  let [ℕ]′ = ℕᵛ {l = l} [Γ]
      ⊢suc-t =
        sucⱼ $ substitutionTerm Γ⊢t:ℕ (wellformedSubst [Γ] ⊢Δ [σ]) ⊢Δ
      t®v = ⊩ʳt [σ] σ®σ′
      [σℕ] = proj₁ (unwrap [ℕ] ⊢Δ [σ])
      [σℕ]′ = proj₁ (unwrap [ℕ]′ ⊢Δ [σ])
      t®v∷ℕ = irrelevanceTerm [σℕ] [σℕ]′ t®v
  in
  irrelevanceTerm [σℕ]′ [σℕ] $
  case singleton str of λ where
    (T.non-strict , refl) →
      sucᵣ (id ⊢suc-t) T.refl _ t®v∷ℕ
    (T.strict , refl) →
      case reduces-to-numeral refl [σℕ] t®v of λ
        (v′ , v′-num , erase-t[σ′]⇒*v′) →
      sucᵣ (id ⊢suc-t)
        (T.lam (T.suc (T.var x0)) T.∘⟨ T.strict ⟩
         erase T.strict t T.[ σ′ ]                    ⇒*⟨ TP.app-subst*-arg T.lam erase-t[σ′]⇒*v′ ⟩

         T.lam (T.suc (T.var x0)) T.∘⟨ T.strict ⟩ v′  ⇒⟨ T.β-red (TP.Numeral→Value v′-num) ⟩

         T.suc v′                                     ∎⇒)
        v′-num
        (targetRedSubstTerm*′ [σℕ]′ t®v∷ℕ erase-t[σ′]⇒*v′)
