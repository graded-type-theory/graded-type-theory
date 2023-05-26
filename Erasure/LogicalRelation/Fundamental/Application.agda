------------------------------------------------------------------------
-- Erasure validity of application.
------------------------------------------------------------------------

open import Definition.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped
open import Tools.Nullary
open import Tools.Sum hiding (id)
import Tools.PropositionalEquality as PE

module Erasure.LogicalRelation.Fundamental.Application
  {a k} {M : Set a}
  (open Definition.Untyped M)
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (R : Type-restrictions M)
  (open Definition.Typed R)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped.Properties M
open import Definition.Typed.Weakening R
open import Definition.Typed.Consequences.Syntactic R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R

import Definition.LogicalRelation.Weakening R as W
import Definition.LogicalRelation.Irrelevance R as I
import Definition.LogicalRelation.Substitution.Irrelevance R as IS

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet-and-star 𝟘-well-behaved
open import Definition.Mode 𝕄

open import Erasure.LogicalRelation 𝕄 R ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Subsumption 𝕄 R ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Irrelevance 𝕄 R ⊢Δ is-𝟘?
import Erasure.Target as T

open import Tools.Function
open import Tools.Nat hiding (_+_)
open import Tools.Product
import Tools.Reasoning.PropositionalEquality

private
  variable
    n : Nat
    γ δ : Conₘ n
    Γ : Con Term n
    t u F : Term n
    G : Term (1+ n)
    p q : M
    m : Mode

appʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ) ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ]) ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([G[u]] : Γ ⊩ᵛ⟨ l ⟩ G [ u ] / [Γ])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F / [Γ] / [F])
       (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Π p , q ▷ F ▹ G / [Γ] /
              Πᵛ {F = F} {G = G} [Γ] [F] [G])
       (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷[ m ᵐ· p ] F / [Γ] / [F])
     → γ +ᶜ p ·ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∘⟨ p ⟩ u ∷[ m ] G [ u ] / [Γ] / [G[u]]
appʳ′ {m = 𝟘ᵐ} with is-𝟘? 𝟘
... | yes m≡𝟘 = _
... | no m≢𝟘 = PE.⊥-elim (m≢𝟘 PE.refl)
appʳ′
  {F = F} {G = G} {u = u} {γ = γ} {t = t} {m = 𝟙ᵐ} {p = p} {q = q}
  {δ = δ} {l = l} [Γ] [F] [G] [G[u]] [u] ⊩ʳt ⊩ʳu {σ = σ} [σ] σ®σ′
  with is-𝟘? 𝟙
... | yes 𝟙≡𝟘 = _
... | no 𝟙≢𝟘
  with is-𝟘? p
... | yes p≡𝟘 =
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [ρσF] = W.wk id ⊢Δ [σF]
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σu]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [ρσF] [σu]
      [σu]″ = I.irrelevanceTerm′ (wk-subst F) [ρσF]
                                 (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [σu]′
      tu®v↯ = ⊩ʳt [σ] (subsumptionSubst {l = l} σ®σ′ λ x γ+pδ≡𝟘 →
                        +-positiveˡ (PE.trans (PE.sym (lookup-distrib-+ᶜ γ _ x)) γ+pδ≡𝟘))
                  [σu]′
      [σG[u]] = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ u) σ G))
                               (proj₁ (unwrap [G] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [σu]″)))
  in  irrelevanceTerm′ (PE.trans (PE.cong (_[ subst σ u ]) (wk-lift-id (subst (liftSubst σ) G)))
                                 (PE.sym (singleSubstLift G u)))
                       [σG[u]] (proj₁ (unwrap [G[u]] ⊢Δ [σ])) tu®v↯
... | no p≢𝟘 =
  let [Π] = Πᵛ {F = F} {G = G} {p = p} {q = q} [Γ] [F] [G]
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [ρσF] = W.wk id ⊢Δ [σF]
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σu]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [ρσF] [σu]
      [σu]″ = I.irrelevanceTerm′ (wk-subst F) [ρσF]
                                 (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [σu]′
      σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ λ x γ+pδ≡𝟘 →
               lem (PE.trans (+-congˡ (PE.sym (lookup-distrib-·ᶜ δ p x)))
                   (PE.trans (PE.sym (lookup-distrib-+ᶜ γ _ x)) γ+pδ≡𝟘))
      u®w′ = ⊩ʳu [σ] (subsumptionSubstMode l σ®σ′ᵤ)
      u®w = irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [ρσF]
                             (u®w′ ◀≢𝟘 (λ ⌜⌞p⌟⌝≡𝟘 →
                                   𝟙≉𝟘 (PE.trans (PE.cong ⌜_⌝ (PE.sym (≉𝟘→⌞⌟≡𝟙ᵐ p≢𝟘))) ⌜⌞p⌟⌝≡𝟘)))
      σ®σ′ₜ = subsumptionSubst {l = l} σ®σ′ λ x γ+pδ≡𝟘 →
                +-positiveˡ (PE.trans (PE.sym (lookup-distrib-+ᶜ γ _ x)) γ+pδ≡𝟘)
      t∘u®v∘w = ⊩ʳt [σ] (subsumptionSubstMode l σ®σ′ₜ)
                    [σu]′ u®w
      [σG[u]] = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ u) σ G))
                               (proj₁ (unwrap [G] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [σu]″)))
  in  irrelevanceTerm′ (PE.trans (PE.cong (_[ subst σ u ])
                                          (wk-lift-id (subst (liftSubst σ) G)))
                                 (PE.sym (singleSubstLift G u)))
                       [σG[u]] (proj₁ (unwrap [G[u]] ⊢Δ [σ])) t∘u®v∘w
  where
  lem : ∀ {a b} → a + p · b PE.≡ 𝟘 → b PE.≡ 𝟘
  lem eq = case (zero-product (+-positiveʳ eq)) of λ where
    (inj₁ p≡𝟘) → PE.⊥-elim (p≢𝟘 p≡𝟘)
    (inj₂ b≡𝟘) → b≡𝟘

appʳ : ∀ {Γ : Con Term n}
     → ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
       ([Π] : Γ ⊩ᵛ⟨ ¹ ⟩ Π p , q ▷ F ▹ G / [Γ])
       ([u] : Γ ⊩ᵛ⟨ ¹ ⟩ u ∷ F / [Γ] / [F])
       (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] Π p , q ▷ F ▹ G / [Γ] / [Π])
       (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ ¹ ⟩ u ∷[ m ᵐ· p ] F / [Γ] / [F])
     → ∃ λ ([G[u]] : Γ ⊩ᵛ⟨ ¹ ⟩ G [ u ] / [Γ])
     → γ +ᶜ p ·ᶜ δ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∘⟨ p ⟩ u ∷[ m ] G [ u ] / [Γ] / [G[u]]
appʳ {F = F} {p} {q} {G} {u} {γ} {t} {δ}
     [Γ] [F] [Π] [u] ⊩ʳt ⊩ʳu =
  let ⊢Γ = soundContext [Γ]
      Γ⊢Π = escapeᵛ [Γ] [Π]
      Γ⊢F , Γ⊢G = syntacticΠ {F = F} {G = G} Γ⊢Π
      [Γ]′ , [G]′ = fundamental Γ⊢G
      [G] = IS.irrelevance {A = G} [Γ]′ ([Γ] ∙ [F]) [G]′
      [G[u]] = substSΠ {F = F} {G = G} {t = u} (BΠ p q) [Γ] [F] [Π] [u]
      [Π]′ = Πᵛ {F = F} {G = G} {p = p} {q = q} [Γ] [F] [G]
      ⊩ʳt′ = irrelevance {A = Π p , q ▷ F ▹ G} {t = t} [Γ] [Γ] [Π] [Π]′ ⊩ʳt
      ⊩ʳt∘u = appʳ′ {F = F} {G = G} {u = u} {t = t} {p = p} [Γ] [F] [G] [G[u]] [u] ⊩ʳt′ ⊩ʳu
  in  [G[u]] , ⊩ʳt∘u
