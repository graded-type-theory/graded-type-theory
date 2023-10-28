------------------------------------------------------------------------
-- The fundamental lemma does not hold in general without the
-- assumption that erased matches are disallowed or the context is
-- empty
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Tools.PropositionalEquality as PE

module Graded.Erasure.LogicalRelation.Fundamental.Counterexample
  {a} {M : Set a}
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (TR : Type-restrictions M)
  (UR : Usage-restrictions M)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet TR}}
  where

open EqRelSet {{...}}
open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Substitution TR
open import Definition.LogicalRelation.Substitution.Properties TR
import Definition.LogicalRelation.Substitution.Irrelevance TR as IS

import Graded.Erasure.Target as T
import Graded.Erasure.LogicalRelation 𝕄 TR is-𝟘? as LR
import Graded.Erasure.LogicalRelation.Irrelevance 𝕄 TR is-𝟘? as LRI
import Graded.Erasure.LogicalRelation.Subsumption 𝕄 TR is-𝟘? as LRS

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.Relation

private variable
  p : M

-- If Prodrec-allowed 𝟘 p 𝟘 holds for some p (which means that certain
-- kinds of erased matches are allowed), and if additionally
-- Σᵣ-allowed p 𝟘 holds, then one cannot prove a variant of the
-- fundamental lemma without the assumption "erased matches are not
-- allowed or the context is empty" (assuming that Agda is
-- consistent).

negation-of-fundamental-lemma-with-erased-matches :
  Prodrec-allowed 𝟘 p 𝟘 →
  Σᵣ-allowed p 𝟘 →
  ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
     let open LR ⊢Δ in
     Consistent Δ →
     ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
     Γ ⊢ t ∷ A → γ ▸[ m ] t →
     ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
       γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
negation-of-fundamental-lemma-with-erased-matches
  {p = p} P-ok Σᵣ-ok hyp =
  case cEx of λ {
    (_ , _ , _ , _ , _ , ⊢t , ▸t , not-ok) →
  not-ok (hyp ⊢Δ consistent ⊢t ▸t) }
  where
  Δ : Con Term 1
  Δ = ε ∙ (Σᵣ p , 𝟘 ▷ ℕ ▹ ℕ)

  ⊢Δ : ⊢ Δ
  ⊢Δ = ε ∙ ΠΣⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) Σᵣ-ok

  consistent : Consistent Δ
  consistent =
    inhabited-consistent $ singleSubst $
    prodⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) (zeroⱼ ε) (zeroⱼ ε) Σᵣ-ok

  open LR ⊢Δ
  open LRI ⊢Δ
  open LRS ⊢Δ

  cEx″ : ∀ {v} → prodrec 𝟘 p 𝟘 ℕ (var x0) zero ® v ∷ℕ → ⊥
  cEx″ (zeroᵣ x x₁) with whnfRed*Term x (ne (prodrecₙ (var x0)))
  ... | ()
  cEx″ (sucᵣ x x₁ t®v) with whnfRed*Term x (ne (prodrecₙ (var x0)))
  ... | ()

  cEx′ :
    ([Δ] : ⊩ᵛ Δ)
    ([A] : Δ ⊩ᵛ⟨ ¹ ⟩ ℕ / [Δ]) →
    ε ∙ 𝟘 ▸ Δ ⊩ʳ⟨ ¹ ⟩ prodrec 𝟘 p 𝟘 ℕ (var x0) zero
      ∷[ 𝟙ᵐ ] ℕ / [Δ] / [A] →
    ⊥
  cEx′ [Δ] [A] ⊩ʳpr =
    let [σ]′ = idSubstS [Δ]
        ⊢Δ′ = soundContext [Δ]
        [σ] = IS.irrelevanceSubst [Δ] [Δ] ⊢Δ′ ⊢Δ [σ]′
        σ®σ′ = erasedSubst {l = ¹} {σ′ = T.idSubst} [Δ] [σ]
        pr®pr = ⊩ʳpr [σ] σ®σ′
        [σA] = proj₁ (unwrap [A] ⊢Δ [σ])
        [ℕ] = ℕᵣ {l = ¹} (idRed:*: (ℕⱼ ⊢Δ))
        pr®pr′ = irrelevanceTerm [σA] [ℕ] (pr®pr ◀≢𝟘 𝟙≢𝟘)
    in  cEx″ pr®pr′

  cEx : ∃ λ n
      → ∃₄ λ (t A : Term n) (Γ : Con Term n) (γ : Conₘ n)
      → Γ ⊢ t ∷ A
      × γ ▸[ 𝟙ᵐ ] t
      × ((∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
          γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ 𝟙ᵐ ] A / [Γ] / [A]) →
         ⊥)
  cEx = _
    , prodrec 𝟘 p 𝟘 ℕ (var x0) zero , ℕ , ε ∙ (Σᵣ p , 𝟘 ▷ ℕ ▹ ℕ)
    , ε ∙ 𝟘
    , prodrecⱼ Δ⊢ℕ Δℕ⊢ℕ ΔΣ⊢ℕ (var ⊢Δ here) (zeroⱼ ⊢Δℕℕ) Σᵣ-ok
    , sub ▸pr
        (≤ᶜ-reflexive
           (≈ᶜ-refl ∙ PE.sym (PE.trans (+-identityʳ _) (·-zeroˡ _))))
    , λ {([Γ] , [A] , ⊩ʳpr) → cEx′ [Γ] [A] ⊩ʳpr}
    where
    Δ⊢ℕ = ℕⱼ ⊢Δ
    ⊢Δℕ = ⊢Δ ∙ Δ⊢ℕ
    Δℕ⊢ℕ = ℕⱼ ⊢Δℕ
    Δ⊢Σ = ΠΣⱼ Δ⊢ℕ Δℕ⊢ℕ Σᵣ-ok
    ⊢ΔΣ = ⊢Δ ∙ Δ⊢Σ
    ΔΣ⊢ℕ = ℕⱼ ⊢ΔΣ
    ⊢Δℕℕ = ⊢Δ ∙ Δ⊢ℕ ∙ Δℕ⊢ℕ
    ▸zero =
      sub zeroₘ
        (≤ᶜ-reflexive
           (≈ᶜ-refl ∙
            PE.trans (·-congˡ (·-zeroˡ p)) (·-zeroʳ 𝟙) ∙ ·-zeroʳ _))
    ▸ℕ = sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (·-zeroʳ _))
    ▸pr = prodrecₘ {η = 𝟘ᶜ} var ▸zero ▸ℕ P-ok
