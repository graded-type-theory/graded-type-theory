{-# OPTIONS --without-K --safe #-}
open import Definition.Modality.Instances.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Application {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Subsumption
open import Erasure.LogicalRelation.Irrelevance
import Erasure.Target as T

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure′
open import Definition.Typed.Weakening Erasure′
open import Definition.Typed.Consequences.Syntactic Erasure′

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Fundamental Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.Escape Erasure′
open import Definition.LogicalRelation.Substitution.Properties Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure′

import Definition.LogicalRelation.Weakening Erasure′ as W
import Definition.LogicalRelation.Irrelevance Erasure′ as I
import Definition.LogicalRelation.Substitution.Irrelevance Erasure′ as IS

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Instances.Erasure.Properties

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    γ δ : Conₘ n
    Γ : Con Term n
    t u F : Term n
    G : Term (1+ n)
    p q : Erasure


appʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ) ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ]) ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([G[u]] : Γ ⊩ᵛ⟨ l ⟩ G [ u ] / [Γ])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F / [Γ] / [F])
       (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Π p , q ▷ F ▹ G / [Γ] / Πᵛ {F = F} {G = G} [Γ] [F] [G])
       (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷ F / [Γ] / [F])
     → γ +ᶜ p ·ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∘ p ▷ u ∷ G [ u ] / [Γ] / [G[u]]
appʳ′ {F = F} {G} {u} {γ} {t} {p = 𝟘} {q} {δ}
      [Γ] [F] [G] [G[u]] [u] ⊩ʳt ⊩ʳu {σ = σ} [σ] σ®σ′ =
  let [Π] = Πᵛ {F = F} {G = G} {p = 𝟘} {q = q} [Γ] [F] [G]
      [σF] = proj₁ ([F] ε [σ])
      [ρσF] = W.wk id ε [σF]
      [σu] = proj₁ ([u] ε [σ])
      [σu]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [ρσF] [σu]
      [σu]″ = I.irrelevanceTerm′ (wk-subst F) [ρσF]
                                 (proj₁ ([F] ε (wkSubstS [Γ] ε ε id [σ]))) [σu]′
      ⊩ʳt′ = subsumption {t = t} {A = Π 𝟘 , q ▷ F ▹ G} [Γ] [Π] ⊩ʳt (+ᶜ-decreasingˡ γ (𝟘 ·ᶜ δ))
      t∘u®v∘w = ⊩ʳt′ [σ] σ®σ′ [σu]′
      [σG[u]] = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ u) σ G))
                               (proj₁ ([G] ε (wkSubstS [Γ] ε ε id [σ] , [σu]″)))
  in  irrelevanceTerm′ (PE.trans (PE.cong (_[ subst σ u ]) (wk-lift-id (subst (liftSubst σ) G)))
                                 (PE.sym (singleSubstLift G u)))
                       [σG[u]] (proj₁ ([G[u]] ε [σ])) t∘u®v∘w

appʳ′ {F = F} {G} {u} {γ = γ} {t = t} {p = ω} {q = q} {δ = δ}
      [Γ] [F] [G] [G[u]] [u] ⊩ʳt ⊩ʳu {σ = σ} {σ′ = σ′} [σ] σ®σ′ =
  let [Π] = Πᵛ {F = F} {G = G} {p = ω} {q = q} [Γ] [F] [G]
      [σF] = proj₁ ([F] ε [σ])
      [ρσF] = W.wk id ε [σF]
      [σu] = proj₁ ([u] ε [σ])
      [σu]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [ρσF] [σu]
      [σu]″ = I.irrelevanceTerm′ (wk-subst F) [ρσF]
                                 (proj₁ ([F] ε (wkSubstS [Γ] ε ε id [σ]))) [σu]′
      ⊩ʳt′ = subsumption {t = t} {A = Π ω , q ▷ F ▹ G} [Γ] [Π] ⊩ʳt (+ᶜ-decreasingˡ γ (ω ·ᶜ δ))
      ⊩ʳu′ = subsumption {t = u} {A = F} [Γ] [F] ⊩ʳu
                         (≤ᶜ-trans (+ᶜ-decreasingʳ γ (ω ·ᶜ δ))
                                   (≤ᶜ-reflexive (·ᶜ-identityˡ δ)))
      u®w′ = ⊩ʳu′ [σ] σ®σ′
      u®w = irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [ρσF] u®w′
      t∘u®v∘w = ⊩ʳt′ [σ] σ®σ′ [σu]′ u®w
      [σG[u]] = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ u) σ G))
                               (proj₁ ([G] ε (wkSubstS [Γ] ε ε id [σ] , [σu]″)))
  in  irrelevanceTerm′ (PE.trans (PE.cong (_[ subst σ u ])
                                          (wk-lift-id (subst (liftSubst σ) G)))
                                 (PE.sym (singleSubstLift G u)))
                       [σG[u]] (proj₁ ([G[u]] ε [σ])) t∘u®v∘w


appʳ : ∀ {Γ : Con Term n}
     → ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
       ([Π] : Γ ⊩ᵛ⟨ ¹ ⟩ Π p , q ▷ F ▹ G / [Γ])
       ([u] : Γ ⊩ᵛ⟨ ¹ ⟩ u ∷ F / [Γ] / [F])
       (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷ Π p , q ▷ F ▹ G / [Γ] / [Π])
       (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ ¹ ⟩ u ∷ F / [Γ] / [F])
     → ∃ λ ([G[u]] : Γ ⊩ᵛ⟨ ¹ ⟩ G [ u ] / [Γ])
     → γ +ᶜ p ·ᶜ δ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∘ p ▷ u ∷ G [ u ] / [Γ] / [G[u]]
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
