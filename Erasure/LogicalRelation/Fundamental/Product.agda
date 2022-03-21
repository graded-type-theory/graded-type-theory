{-# OPTIONS --without-K --safe #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation


module Erasure.LogicalRelation.Fundamental.Product {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure′
open import Definition.Typed.Properties Erasure′
open import Definition.Typed.Weakening Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Fundamental Erasure′
open import Definition.LogicalRelation.Fundamental.Reducibility Erasure′
open import Definition.LogicalRelation.Properties.Escape Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.Properties Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Fst Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure′

import Definition.LogicalRelation.Irrelevance Erasure′ as I
import Definition.LogicalRelation.Weakening Erasure′ as W
import Definition.LogicalRelation.Substitution.Irrelevance Erasure′ as IS

open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Erasure.Properties

open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Conversion
open import Erasure.LogicalRelation.Reduction
open import Erasure.LogicalRelation.Subsumption
open import Erasure.LogicalRelation.Irrelevance

open import Erasure.Extraction
import Erasure.Target as T
import Erasure.Target.Properties as TP

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A F t u : Term n
    t₁ t₂ : Term 0
    v₁ v₂ : T.Term 0
    G : Term (1+ n)
    p q : Erasure
    γ δ : Conₘ n
    σ : Subst 0 n
    σ′ : T.Subst 0 n

Σʳ : ([Γ] : ⊩ᵛ Γ) → Γ ⊢ Σ q ▷ F ▹ G ∷ U
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Σ q ▷ F ▹ G ∷ U / [Γ] / [U]
Σʳ [Γ] ⊢Σ = Uᵛ [Γ] , λ [σ] σ®σ′ →
  let ⊢σΣ = substitutionTerm ⊢Σ (wellformedSubst [Γ] ε [σ]) ε
  in  Uᵣ ⊢σΣ

prodʳ : ∀ {l}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([G[t]] : Γ ⊩ᵛ⟨ l ⟩ G [ t ] / [Γ])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
        ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / [G[t]])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ F / [Γ] / [F])
        (⊩ʳu : δ ▸ Γ ⊩ʳ⟨ l ⟩ u ∷ G [ t ] / [Γ] / [G[t]])
      → ∃ λ ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ q ▷ F ▹ G / [Γ])
      → γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prod t u ∷ Σ q ▷ F ▹ G / [Γ] / [Σ]
prodʳ {F = F} {G = G} {t = t} {u = u} {γ = γ} {δ = δ} {q = q} {l = l}
      [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu =
  let [Σ] = Σᵛ {F = F} {G = G} [Γ] [F] [G]
  in  [Σ] , λ {σ = σ} {σ′ = σ′} [σ] σ®σ′ [t₁] →
      let σ®σ′ₜ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingˡ γ δ)
          σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ γ δ)
          [σF] = proj₁ ([F] ε [σ])
          ⊢F = escape [σF]
          [σG] = proj₁ ([G] (ε ∙ ⊢F) (liftSubstS {F = F} [Γ] ε [F] [σ]))
          [σF]′ = W.wk id ε [σF]
          [σG[t]] = proj₁ ([G[t]] ε [σ])
          ⊢G = escape [σG]
          ⊢t = escapeTerm [σF] (proj₁ ([t] ε [σ]))
          ⊢u = escapeTerm [σG[t]] (proj₁ ([u] ε [σ]))
          ⊢u′ = PE.subst (λ A → ε ⊢ subst σ u ∷ A) (singleSubstLift G t) ⊢u
          ⊢p = prodⱼ {q = q} ⊢F ⊢G ⊢t ⊢u′
          t®t′ = ⊩ʳt [σ] σ®σ′ₜ
          p₁⇒t = Σ-β₁ ⊢F ⊢G ⊢t ⊢u′ ⊢p
          p₁′⇒t′ = T.Σ-β₁ {t = T.subst σ′ (erase t)} {u = T.subst σ′ (erase u)}
          p₁®p₁′ = redSubstTerm [σF] t®t′ p₁⇒t p₁′⇒t′
          p₁®p₁″ = irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′ p₁®p₁′
          [t₁]′ = I.irrelevanceTerm′ (wk-subst F) [σF]′ (proj₁ ([F] ε (wkSubstS [Γ] ε ε id [σ]))) [t₁]
          G[p₁]≡G[t] = substTypeEq (refl ⊢G) (subsetTerm p₁⇒t)
          G[p₁]≡G[t]′ = PE.subst (λ x → ε ⊢ (subst (liftSubst σ) G) [ _ ] ≡ x)
                                 (PE.sym (singleSubstLift G t)) G[p₁]≡G[t]
          [σG[p₁]]′ = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ (fst (prod t u))) σ G))
                                    (proj₁ ([G] ε (wkSubstS [Γ] ε ε id [σ] , [t₁]′)))
          [σG[p₁]] = reducible (substType ⊢G (fstⱼ ⊢F ⊢G ⊢p))
          u®u′ = ⊩ʳu [σ] σ®σ′ᵤ
          u®u″ = convTermʳ [σG[t]] [σG[p₁]] (sym G[p₁]≡G[t]′) u®u′
          p₂®p₂′ = redSubstTerm [σG[p₁]] u®u″ (Σ-β₂ ⊢F ⊢G ⊢t ⊢u′ ⊢p)
                                (T.Σ-β₂ {t = T.subst σ′ (erase t)} {u = T.subst σ′ (erase u)})
          p₂®p₂″ = irrelevanceTerm′ (PE.cong (λ x → x [ _ ]) (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                    [σG[p₁]] [σG[p₁]]′ p₂®p₂′
      in  p₁®p₁″ , p₂®p₂″

fstʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} [Γ] [F] [G])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} [Γ] [F] [G])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ fst t ∷ F / [Γ] / [F]
fstʳ′ {F = F} {G} {t = t} {q = q} [Γ] [F] [G] [t] ⊩ʳt {σ = σ} [σ] σ®σ′ =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      [σF] = proj₁ ([F] ε [σ])
      [σF]′ = W.wk id ε [σF]
      [t₁] = fstᵛ {F = F} {G = G} {t = t} [Γ] [F] [G] [t]
      [σt₁] = proj₁ ([t₁] ε [σ])
      [σt₁]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′ [σt₁]
      t®v = ⊩ʳt [σ] σ®σ′
      t₁®v₁ , _ = t®v [σt₁]′
  in  irrelevanceTerm′ (wk-id (subst σ F)) [σF]′ [σF] t₁®v₁

fstʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σ q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σ q ▷ F ▹ G / [Γ])
     → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / [Σ])
     → ∃ λ ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
     → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ fst t ∷ F / [Γ] / [F]
fstʳ {Γ = Γ} {F = F} {G = G} {t = t} {q = q} Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt =
  let [Γ]₁ , [F]′ = fundamental Γ⊢F
      [Γ]₂ , [G]′ = fundamental Γ⊢G
      [F] = IS.irrelevance {A = F} [Γ]₁ [Γ] [F]′
      [G] = IS.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]′
      [Σ]′ = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      [Γ]₃ , [Σ]″ , [t]′ = fundamentalTerm Γ⊢t:Σ
      [t] = IS.irrelevanceTerm {A = Σ q ▷ F ▹ G} {t = t} [Γ]₃ [Γ] [Σ]″ [Σ]′ [t]′
      ⊩ʳt′ = irrelevance {A = Σ q ▷ F ▹ G} {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
  in  [F] , fstʳ′ {F = F} {G = G} {t = t} [Γ] [F] [G] [t] ⊩ʳt′

sndʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G])
      → ∃ λ ([G] : Γ ⊩ᵛ⟨ l ⟩ G [ fst t ] / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ snd t ∷ G [ fst t ] / [Γ] / [G]
sndʳ′ {F = F} {G} {t} {q = q} [Γ] [F] [G] [t] ⊩ʳt =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      [t₁] = fstᵛ {F = F} {G = G} {t = t} [Γ] [F] [G] [t]
      [G[t₁]] = substSΠ {F = F} {G = G} {t = fst t} (BΣ q) [Γ] [F] [Σ] [t₁]
  in  [G[t₁]] , λ {σ = σ} [σ] σ®σ′ →
      let [σF] = proj₁ ([F] ε [σ])
          [σF]′ = W.wk id ε [σF]
          [σF]″ = proj₁ ([F] ε (wkSubstS [Γ] ε ε id [σ]))
          [σt₁] = proj₁ ([t₁] ε [σ])
          [σt₁]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′ [σt₁]
          [σt₁]″ = I.irrelevanceTerm′ (wk-subst F) [σF]′ [σF]″ [σt₁]′
          t®v = ⊩ʳt [σ] σ®σ′
          _ , t₂®v₂ = t®v [σt₁]′
          [σG[t₁]]′ = proj₁ ([G] ε ((wkSubstS [Γ] ε ε id [σ]) , [σt₁]″))
          [σG[t₁]]″ = I.irrelevance′ (PE.sym (singleSubstWkComp (fst (subst σ t)) σ G)) [σG[t₁]]′
          [σG[t₁]] = proj₁ ([G[t₁]] ε [σ])
      in  irrelevanceTerm′ (PE.trans (PE.cong (λ x → x [ _ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                     (PE.sym (singleSubstLift G (fst t))))
                           [σG[t₁]]″ [σG[t₁]] t₂®v₂


sndʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σ q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σ q ▷ F ▹ G / [Γ])
     → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / [Σ])
     → ∃ λ ([G] : Γ ⊩ᵛ⟨ ¹ ⟩ G [ fst t ] / [Γ])
     → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ snd t ∷ G [ fst t ] / [Γ] / [G]
sndʳ {Γ = Γ} {F = F} {G = G} {t = t} {q = q} Γ⊢F Γ⊢G Γ⊢t:Σ [Γ] [Σ] ⊩ʳt =
  let [Γ]₁ , [F]′ = fundamental Γ⊢F
      [Γ]₂ , [G]′ = fundamental Γ⊢G
      [F] = IS.irrelevance {A = F} [Γ]₁ [Γ] [F]′
      [G] = IS.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]′
      [Σ]′ = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      ⊩ʳt′ = irrelevance {A = Σ q ▷ F ▹ G} {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
      [Γ]₃ , [Σ]″ , [t]′ = fundamentalTerm Γ⊢t:Σ
      [t] = IS.irrelevanceTerm {A = Σ q ▷ F ▹ G} {t = t} [Γ]₃ [Γ] [Σ]″ [Σ]′ [t]′
  in  sndʳ′ {F = F} {G = G} {t = t} {q = q} [Γ] [F] [G] [t] ⊩ʳt′
