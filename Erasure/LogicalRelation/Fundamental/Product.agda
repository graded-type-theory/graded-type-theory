{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Fundamental.Product
  (restrictions : Restrictions Erasure′)
  {{eqrel : EqRelSet Erasure′}}
  where

open EqRelSet {{...}}

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure′
open import Definition.Typed.Properties Erasure′
open import Definition.Typed.RedSteps Erasure′
open import Definition.Typed.Weakening Erasure′
open import Definition.Typed.Consequences.Inversion Erasure′
open import Definition.Typed.Consequences.Injectivity Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′
open import Definition.Typed.Consequences.Syntactic Erasure′
open import Definition.Typed.Consequences.RedSteps Erasure′
open import Definition.Typed.Consequences.Reduction Erasure′

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Fundamental Erasure′
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

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Instances.Erasure.Properties
  restrictions

open import Erasure.LogicalRelation restrictions
open import Erasure.LogicalRelation.Conversion restrictions
open import Erasure.LogicalRelation.Reduction restrictions
open import Erasure.LogicalRelation.Subsumption restrictions
open import Erasure.LogicalRelation.Irrelevance restrictions

open import Erasure.Extraction
import Erasure.Target as T
import Erasure.Target.Properties as TP

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Unit
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
    m : SigmaMode

Σʳ : ([Γ] : ⊩ᵛ Γ) → Γ ⊢ Σ q ▷ F ▹ G ∷ U
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Σ⟨ m ⟩ q ▷ F ▹ G ∷ U / [Γ] / [U]
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
      → ∃ λ ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ q ▷ F ▹ G / [Γ])
      → γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prod m t u ∷ Σ q ▷ F ▹ G / [Γ] / [Σ]
prodʳ {Γ = Γ} {F} {G} {t} {u} {γ} {δ} {m} {q} {l}
      [Γ] [F] [G] [G[t]] [t] [u] ⊩ʳt ⊩ʳu =
  let [Σ] = Σᵛ {F = F} {G = G} [Γ] [F] [G]
  in  [Σ] , λ {σ} {σ′} [σ] σ®σ′ →
    let σ®σ′ₜ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingˡ γ δ)
        σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ γ δ)
        t®t′ = ⊩ʳt [σ] σ®σ′ₜ
        u®u′ = ⊩ʳu [σ] σ®σ′ᵤ
        [σF] = proj₁ (unwrap [F] ε [σ])
        [σF]′ = W.wk id ε [σF]
        [σG[t]] = proj₁ (unwrap [G[t]] ε [σ])
        [σt] = proj₁ ([t] ε [σ])
        [σt]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′ [σt]
        [σt]″ = I.irrelevanceTerm′ (wk-subst F) [σF]′ (proj₁ (unwrap [F] ε (wkSubstS [Γ] ε ε id [σ]))) [σt]′
        [σG[t]]′ = proj₁ (unwrap [G] ε (wkSubstS [Γ] ε ε id [σ] , [σt]″))
        [σG[t]]″ = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ t) σ G)) [σG[t]]′
        ⊢σF = escape [σF]
        ⊢σG = escape (proj₁ (unwrap [G] (ε ∙ ⊢σF) (liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ])))
        ⊢σt = escapeTerm [σF] [σt]
        ⊢σu = escapeTerm [σG[t]] (proj₁ ([u] ε [σ]))
        ⊢prod = prodⱼ ⊢σF ⊢σG ⊢σt (PE.subst (λ x → ε ⊢ subst σ u ∷ x) (singleSubstLift G t) ⊢σu)
        t®t″ = irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′ t®t′
        u®u″ = irrelevanceTerm′ (PE.trans (singleSubstLift G t)
                                          (PE.cong (_[ _ ]) (PE.sym (wk-lift-id (subst (liftSubst σ) G)))))
                                [σG[t]] [σG[t]]″ u®u′
    in  subst σ t , subst σ u , T.subst σ′ (erase t) , T.subst σ′ (erase u)
      , id ⊢prod , T.refl , [σt]′ , t®t″ , u®u″

fstʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σₚ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} [Γ] [F] [G])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σₚ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} [Γ] [F] [G])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ fst t ∷ F / [Γ] / [F]
fstʳ′ {F = F} {G} {t = t} {q = q} [Γ] [F] [G] [t] ⊩ʳt {σ = σ} [σ] σ®σ′ =
  let [σF] = proj₁ (unwrap [F] ε [σ])
      [σF]′ = W.wk id ε [σF]
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒v′ , [t₁] , t₁®v₁ , t₂®v₂ = ⊩ʳt [σ] σ®σ′
      _ , _ , ⊢t′ = syntacticRedTerm t⇒t′
      _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , Σ≡Σ′ = inversion-prod ⊢t′
      F≡F′ , G≡G′ , _ = Σ-injectivity Σ≡Σ′
      ⊢t₁′ = conv ⊢t₁ (sym F≡F′)
      ⊢t₂′ = conv ⊢t₂ (substTypeEq (sym G≡G′) (refl ⊢t₁′))
      fstt⇒t₁ = fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷* redMany (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′)
      fstt⇒t₁′ = PE.subst (λ x → ε ⊢ _ ⇒* _ ∷ x) (PE.sym (wk-id (subst σ F))) fstt⇒t₁
      fstv⇒v₁ = TP.red*concat (TP.fst-subst* v⇒v′) (T.trans T.Σ-β₁ T.refl)
      fstt®fstv = redSubstTerm* [σF]′ t₁®v₁ fstt⇒t₁′ fstv⇒v₁
  in  irrelevanceTerm′ (wk-id (subst σ F)) [σF]′ [σF] fstt®fstv

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
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σₚ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G])
        (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σₚ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G])
      → ∃ λ ([G] : Γ ⊩ᵛ⟨ l ⟩ G [ fst t ] / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ snd t ∷ G [ fst t ] / [Γ] / [G]
sndʳ′ {F = F} {G} {t} {q = q} [Γ] [F] [G] [t] ⊩ʳt =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} [Γ] [F] [G]
      [t₁] = fstᵛ {F = F} {G = G} {t = t} [Γ] [F] [G] [t]
      [G[t₁]] = substSΠ {F = F} {G = G} {t = fst t} (BΣ Σₚ q) [Γ] [F] [Σ] [t₁]
  in  [G[t₁]] , λ {σ = σ} [σ] σ®σ′ →
      let t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒v′ , [t₁] , t₁®v₁ , t₂®v₂ = ⊩ʳt [σ] σ®σ′
          [σF] = proj₁ (unwrap [F] ε [σ])
          ⊢σF = escape [σF]
          [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]
          [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF) [⇑σ])
          ⊢σG = escape [σG]
          _ , _ , ⊢t′ = syntacticRedTerm t⇒t′
          _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , eq = inversion-prod ⊢t′
          eq₁ , eq₂ , _ = Σ-injectivity eq
          ⊢t₁′ = conv ⊢t₁ (sym eq₁)
          eq₂′ = substitutionEq eq₂ (substRefl (singleSubst ⊢t₁′)) ε
          ⊢t₂′ = conv ⊢t₂ (sym eq₂′)
          t≡t₁ = subset*Term (redMany (Σ-β₁ {q = q} ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′))
          t′≡t₁ = subset*Term (fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷*
                               redMany (Σ-β₁ {q = q} ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′))
          G[t]≡G[t₁] = substTypeEq (refl ⊢σG) t≡t₁
          G[t]≡G[t₁]′ = PE.subst (ε ⊢ subst (liftSubst σ) G [ _ ] ≡_)
                                 (PE.cong (_[ t₁ ])
                                          (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                 G[t]≡G[t₁]
          G[t′]≡G[t₁] = substTypeEq (refl ⊢σG) t′≡t₁
          G[t′]≡G[t₁]′ = PE.subst₂ (ε ⊢_≡_)
                                   (PE.cong (_[ t₁ ])
                                            (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                   (PE.sym (singleSubstLift G (fst t)))
                                   (sym G[t′]≡G[t₁])
          t⇒u = conv* (snd-subst* t⇒t′ ⊢σF ⊢σG)
                      (substTypeEq (refl ⊢σG) (fst-cong ⊢σF ⊢σG (subset*Term t⇒t′)))
          t⇒u′ = t⇒u ⇨∷* redMany (Σ-β₂ {q = q} ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′)
          t⇒u″ = conv* t⇒u′ G[t]≡G[t₁]′
          v⇒w = TP.red*concat (TP.snd-subst* v⇒v′) (T.trans T.Σ-β₂ T.refl)
          wk[σ] = wkSubstS {σ = σ} [Γ] ε ε id [σ]
          wk[σF] = W.wk id ε [σF]
          wk[t₁] = I.irrelevanceTerm′ (wk-subst F) wk[σF] (proj₁ (unwrap [F] ε wk[σ])) [t₁]
          wk[Gt₁] = I.irrelevance′ (PE.sym (singleSubstWkComp t₁ σ G)) (proj₁ (unwrap [G] ε (wk[σ] , wk[t₁])))
          t₂®v₂′ = redSubstTerm* wk[Gt₁] t₂®v₂ t⇒u″ v⇒w
      in  convTermʳ wk[Gt₁] (proj₁ (unwrap [G[t₁]] ε [σ])) G[t′]≡G[t₁]′ t₂®v₂′


sndʳ : Γ ⊢ F → Γ ∙ F ⊢ G → Γ ⊢ t ∷ Σₚ q ▷ F ▹ G
     → ([Γ] : ⊩ᵛ Γ) ([Σ] : Γ ⊩ᵛ⟨ ¹ ⟩ Σₚ q ▷ F ▹ G / [Γ])
     → (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷ Σₚ q ▷ F ▹ G / [Γ] / [Σ])
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

prodrecʳ′ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
          → let [Σ] = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G] in
           ([A] : Γ ∙ (Σᵣ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
           ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
           (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σᵣ q ▷ F ▹ G / [Γ] / [Σ])
           (⊩ʳu : δ ∙ p ∙ p ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
           ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ])
           ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
           ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
           (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷ Γ ◂ p ·ᶜ γ +ᶜ δ / [Γ] / [σ])
           ([σt] : ε ⊩⟨ l ⟩ subst σ t ∷ subst σ (Σᵣ q ▷ F ▹ G) / proj₁ (unwrap [Σ] ε [σ]))
         → subst σ (prodrec p A t u) ®⟨ l ⟩ T.subst σ′ (erase (prodrec p A t u)) ∷ subst σ (A [ t ]) / proj₁ (unwrap [At] ε [σ])
prodrecʳ′ {n} {F} {G} {q} {A} {γ} {t} {δ} {r} {u} {σ} {σ′} {l} {Γ}
          [Γ] [F] [G] [A] [A₊] ⊩ʳt ⊩ʳu [At] [u] [σ] σ®σ′ (Σₜ p d p≡p (ne x) prop) = PE.⊥-elim (noClosedNe x)
prodrecʳ′ {n} {F} {G} {q} {A} {γ} {t} {δ} {𝟘} {u} {σ} {σ′} {l} {Γ}
          [Γ] [F] [G] [A] [A₊] ⊩ʳt ⊩ʳu [At] [u] [σ] σ®σ′ (Σₜ p d p≡p (prodₙ {t = p₁} {u = p₂}) (wk[p₁] , wk[p₂] , PE.refl)) =
  let σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ (𝟘 ·ᶜ γ) δ)
      [σF] = proj₁ (unwrap [F] ε [σ])
      ⊢σF = escape [σF]
      ⊢ε = wf ⊢σF
      wk[σF] = W.wk id ⊢ε [σF]
      [p₁] = I.irrelevanceTerm′ (wk-id (subst σ F)) wk[σF] [σF] wk[p₁]
      [σGp₁] = proj₁ (unwrap [G] {σ = consSubst σ _} ε ([σ] , [p₁]))
      wk[σ] = wkSubstS [Γ] ε ⊢ε id [σ]
      wk[σGp₁] = I.irrelevance′ (PE.sym (singleSubstWkComp p₁ σ G))
                                (proj₁ (unwrap [G] ⊢ε (wk[σ] , I.irrelevanceTerm′ (wk-subst F)
                                                                           wk[σF]
                                                                           (proj₁ (unwrap [F] ⊢ε wk[σ]))
                                                                           wk[p₁])))
      [p₂] = I.irrelevanceTerm′ (PE.trans (PE.cong (_[ p₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                          (singleSubstComp p₁ σ G))
                                wk[σGp₁] [σGp₁] wk[p₂]
      [σ₊] = ([σ] , [p₁]) , [p₂]
      u®u′ = ⊩ʳu {σ = consSubst (consSubst σ p₁) p₂}
                 {σ′ = T.consSubst (T.consSubst σ′ T.undefined) T.undefined}
                 [σ₊] ((σ®σ′ᵤ , tt) , tt)
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [Σ] = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G]
      [σΣ] = proj₁ (unwrap [Σ] ε [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (ε ∙ ⊢σΣ) (liftSubstS {σ = σ} {F = Σ q ▷ F ▹ G} [Γ] ε [Σ] [σ]))
      ⊢σA = escape [σA]
      [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (ε ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (ε ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (ε ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x) (subst-β-prodrec A σ) ⊢σu
      red₁ = prodrec-subst* {p = 𝟘} (redₜ d) ⊢σF ⊢σG ⊢σA ⊢σu′
      ⊢p₁ = escapeTerm [σF] [p₁]
      ⊢p₂ = escapeTerm [σGp₁] [p₂]
      ⊢p₂′ = PE.subst (λ x → ε ⊢ p₂ ∷ x) (PE.sym (singleSubstComp p₁ σ G)) ⊢p₂
      At≡Ap = substTypeEq (refl ⊢σA) (subset*Term (redₜ d))
      red₂ = prodrec-β ⊢σF ⊢σG ⊢σA ⊢p₁ ⊢p₂′ ⊢σu′
      red = conv* red₁ At≡Ap ⇨∷* redMany red₂
      red′ = PE.subst₂ (λ x y → ε ⊢ _ ⇒* x ∷ y) (doubleSubstComp u p₁ p₂ σ)
                       (substCompProdrec A p₁ p₂ σ) red
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = consSubst (consSubst σ p₁) p₂} ε [σ₊])
      pr®u′ = sourceRedSubstTerm* [σ₊A₊] u®u′ red′
      [σAt] = proj₁ (unwrap [At] ε [σ])
  in  convTermʳ [σ₊A₊] [σAt]
                (PE.subst₂ (λ x y → ε ⊢ x ≡ y) (substCompProdrec A p₁ p₂ σ)
                           (PE.sym (singleSubstLift A t)) (sym At≡Ap))
                (PE.subst (λ x → subst σ (prodrec 𝟘 A t u) ®⟨ l ⟩ x
                               ∷ subst (consSubst (consSubst σ p₁) p₂) (A [ prodᵣ (var (x0 +1)) (var x0) ]↑²)
                               / [σ₊A₊])
                          (PE.sym (PE.trans (TP.doubleSubstLift σ′ (erase u) T.undefined T.undefined)
                                            (TP.doubleSubstComp (erase u) T.undefined T.undefined σ′)))
                          pr®u′)
prodrecʳ′ {n} {F} {G} {q} {A} {γ} {t} {δ} {ω} {u} {σ} {σ′} {l} {Γ}
          [Γ] [F] [G] [A] [A₊] ⊩ʳt ⊩ʳu [At] [u] [σ] σ®σ′ (Σₜ p d p≡p prodₙ (wk[p₁]′ , wk[p₂] , PE.refl))
          with ⊩ʳt [σ] (subsumptionSubst {l = l} σ®σ′ (≤ᶜ-trans (+ᶜ-decreasingˡ (ω ·ᶜ γ) δ) (≤ᶜ-reflexive (·ᶜ-identityˡ γ))))
... | p₁ , p₂ , q₁ , q₂ , t⇒p , v⇒q , wk[p₁] , p₁®q₁ , p₂®q₂
    with whrDet*Term (redₜ d , prodₙ) (t⇒p , prodₙ) | wf (escape (proj₁ (unwrap [F] ε [σ])))
... | PE.refl | ε =
  let σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ (ω ·ᶜ γ) δ)
      [σF] = proj₁ (unwrap [F] ε [σ])
      ⊢σF = escape [σF]
      wk[σF] = W.wk id ε [σF]
      p₁®q₁′ = irrelevanceTerm′ (wk-id (subst σ F)) wk[σF] [σF] p₁®q₁
      [p₁] = I.irrelevanceTerm′ (wk-id (subst σ F)) wk[σF] [σF] wk[p₁]
      [σGp₁] = proj₁ (unwrap [G] {σ = consSubst σ p₁} ε ([σ] , [p₁]))
      wk[σ] = wkSubstS [Γ] ε ε id [σ]
      wk[σGp₁] = λ x → I.irrelevance′ (PE.sym (singleSubstWkComp p₁ σ G))
                                (proj₁ (unwrap [G] ε (wk[σ] , I.irrelevanceTerm′ (wk-subst F)
                                                                           wk[σF]
                                                                           (proj₁ (unwrap [F] ε wk[σ]))
                                                                           x)))
      [p₂] = I.irrelevanceTerm′ (PE.trans (PE.cong (_[ p₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                          (singleSubstComp p₁ σ G))
                                (wk[σGp₁] wk[p₁]′) [σGp₁] wk[p₂]
      p₂®q₂′ = irrelevanceTerm′ (PE.trans (PE.cong (_[ p₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                          (singleSubstComp p₁ σ G))
                                (wk[σGp₁] wk[p₁]) [σGp₁] p₂®q₂
      σ₊®σ′₊ = (σ®σ′ᵤ , p₁®q₁′) , p₂®q₂′
      [σ₊] = ([σ] , [p₁]) , [p₂]
      u®u′ = ⊩ʳu {σ = consSubst (consSubst σ p₁) p₂}
                 {σ′ = T.consSubst (T.consSubst σ′ q₁) q₂}
                 [σ₊] σ₊®σ′₊
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [Σ] = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G]
      [σΣ] = proj₁ (unwrap [Σ] ε [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (ε ∙ ⊢σΣ) (liftSubstS {σ = σ} {F = Σ q ▷ F ▹ G} [Γ] ε [Σ] [σ]))
      ⊢σA = escape [σA]
      [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (ε ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (ε ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (ε ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x) (subst-β-prodrec A σ) ⊢σu
      red₁ = prodrec-subst* {p = ω} (redₜ d) ⊢σF ⊢σG ⊢σA ⊢σu′
      ⊢p₁ = escapeTerm [σF] [p₁]
      ⊢p₂ = escapeTerm [σGp₁] [p₂]
      ⊢p₂′ = PE.subst (λ x → ε ⊢ p₂ ∷ x) (PE.sym (singleSubstComp p₁ σ G)) ⊢p₂
      At≡Ap = substTypeEq (refl ⊢σA) (subset*Term (redₜ d))
      red₂ = prodrec-β ⊢σF ⊢σG ⊢σA ⊢p₁ ⊢p₂′ ⊢σu′
      red = PE.subst₂ (λ x y → ε ⊢ _ ⇒* x ∷ y) (doubleSubstComp u p₁ p₂ σ)
                      (substCompProdrec A p₁ p₂ σ)
                      (conv* red₁ At≡Ap ⇨∷* redMany red₂)
      red₁′ = TP.prodrec-subst* {u = T.subst (T.liftSubstn σ′ 2) (erase u)} v⇒q
      red₂′ = PE.subst (λ x → T.prodrec (T.prod q₁ q₂) (T.subst (T.liftSubstn σ′ 2) (erase u)) T.⇒ x)
                       (TP.doubleSubstComp (erase u) q₁ q₂ σ′)
                       (T.prodrec-β {t = q₁} {q₂} {T.subst (T.liftSubstn σ′ 2) (erase u)})
      red′ = TP.red*concat red₁′ (T.trans red₂′ T.refl)
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = consSubst (consSubst σ p₁) p₂} ε [σ₊])
      pr®pr′ = redSubstTerm* [σ₊A₊] u®u′ red red′
      [σAt] = proj₁ (unwrap [At] ε [σ])
  in  convTermʳ [σ₊A₊] [σAt]
                (PE.subst₂ (λ x y → ε ⊢ x ≡ y)
                           (substCompProdrec A p₁ p₂ σ)
                           (PE.sym (singleSubstLift A t)) (sym At≡Ap))
                pr®pr′



prodrecʳ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
           ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σᵣ q ▷ F ▹ G / [Γ])
           ([A] : Γ ∙ (Σᵣ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
           ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
           ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σᵣ q ▷ F ▹ G / [Γ] / [Σ])
           ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
           (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σᵣ q ▷ F ▹ G / [Γ] / [Σ])
           (⊩ʳu : δ ∙ p ∙ p ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
         → ∃ λ ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ])
         → p ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec p A t u ∷ A [ t ] / [Γ] / [At]
prodrecʳ {n} {F} {G} {q} {A} {t} {u} {γ} {δ} {p} {l} {Γ}
         [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu =
  let [At] = substS {F = Σ q ▷ F ▹ G} {A} {t} [Γ] [Σ] [A] [t]
  in  [At] , λ {σ} [σ] σ®σ′ →
    let [Σ]′ = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G]
        [A]′ = IS.irrelevance {A = A} (_∙_ {A = Σ q ▷ F ▹ G} [Γ] [Σ])
                              (_∙_ {A = Σ q ▷ F ▹ G} [Γ] [Σ]′) [A]
        ⊩ʳt′ = irrelevance {A = Σ q ▷ F ▹ G} {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
        [t]′ = IS.irrelevanceTerm {A = Σ q ▷ F ▹ G} {t = t} [Γ] [Γ] [Σ] [Σ]′ [t]
        [σt] = proj₁ ([t]′ ε [σ])
    in  prodrecʳ′ {F = F} {G} {q} {A} {γ} {t} {δ} {p} {u}
                  [Γ] [F] [G] [A]′ [A₊] ⊩ʳt′ ⊩ʳu [At] [u] [σ] σ®σ′ [σt]
