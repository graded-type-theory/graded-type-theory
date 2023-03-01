{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Typed Erasure′

module Erasure.LogicalRelation.Fundamental.Product {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
                                                   (Prodrec : Erasure → Set)
                                                   {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.Untyped.Properties Erasure
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

open import Definition.Modality.Instances.Erasure.Modality Prodrec
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Instances.Erasure.Properties Prodrec

open import Erasure.LogicalRelation ⊢Δ Prodrec
open import Erasure.LogicalRelation.Conversion ⊢Δ Prodrec
open import Erasure.LogicalRelation.Reduction ⊢Δ Prodrec
open import Erasure.LogicalRelation.Subsumption ⊢Δ Prodrec
open import Erasure.LogicalRelation.Irrelevance ⊢Δ Prodrec

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
    t₁ t₂ : Term n
    v₁ v₂ : T.Term n
    G : Term (1+ n)
    p q q′ : Erasure
    γ δ : Conₘ n
    σ : Subst k n
    σ′ : T.Subst k n
    m : SigmaMode

Σʳ : ([Γ] : ⊩ᵛ Γ) → Γ ⊢ Σ q ▷ F ▹ G ∷ U
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Σ⟨ m ⟩ q ▷ F ▹ G ∷ U / [Γ] / [U]
Σʳ [Γ] ⊢Σ = Uᵛ [Γ] , λ [σ] σ®σ′ →
  let ⊢σΣ = substitutionTerm ⊢Σ (wellformedSubst [Γ] ⊢Δ [σ]) ⊢Δ
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
        [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
        [σF]′ = W.wk id ⊢Δ [σF]
        [σG[t]] = proj₁ (unwrap [G[t]] ⊢Δ [σ])
        [σt] = proj₁ ([t] ⊢Δ [σ])
        [σt]′ = I.irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) [σF] [σF]′ [σt]
        [σt]″ = I.irrelevanceTerm′ (wk-subst F) [σF]′ (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [σt]′
        [σG[t]]′ = proj₁ (unwrap [G] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [σt]″))
        [σG[t]]″ = I.irrelevance′ (PE.sym (singleSubstWkComp (subst σ t) σ G)) [σG[t]]′
        ⊢σF = escape [σF]
        ⊢σG = escape (proj₁ (unwrap [G] (⊢Δ ∙ ⊢σF) (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ])))
        ⊢σt = escapeTerm [σF] [σt]
        ⊢σu = escapeTerm [σG[t]] (proj₁ ([u] ⊢Δ [σ]))
        ⊢prod = prodⱼ ⊢σF ⊢σG ⊢σt (PE.subst (λ x → Δ ⊢ subst σ u ∷ x) (singleSubstLift G t) ⊢σu)
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
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [σF]′ = W.wk id ⊢Δ [σF]
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      t₁ , t₂ , v₁ , v₂ , t⇒t′ , v⇒v′ , [t₁] , t₁®v₁ , t₂®v₂ = ⊩ʳt [σ] σ®σ′
      _ , _ , ⊢t′ = syntacticRedTerm t⇒t′
      _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , Σ≡Σ′ = inversion-prod ⊢t′
      F≡F′ , G≡G′ , _ = Σ-injectivity Σ≡Σ′
      ⊢t₁′ = conv ⊢t₁ (sym F≡F′)
      ⊢t₂′ = conv ⊢t₂ (substTypeEq (sym G≡G′) (refl ⊢t₁′))
      fstt⇒t₁ = fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷* redMany (Σ-β₁ ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′)
      fstt⇒t₁′ = PE.subst (λ x → Δ ⊢ _ ⇒* _ ∷ x) (PE.sym (wk-id (subst σ F))) fstt⇒t₁
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
          [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
          ⊢σF = escape [σF]
          [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
          [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
          ⊢σG = escape [σG]
          _ , _ , ⊢t′ = syntacticRedTerm t⇒t′
          _ , _ , _ , _ , _ , ⊢t₁ , ⊢t₂ , eq = inversion-prod ⊢t′
          eq₁ , eq₂ , _ = Σ-injectivity eq
          ⊢t₁′ = conv ⊢t₁ (sym eq₁)
          eq₂′ = substitutionEq eq₂ (substRefl (singleSubst ⊢t₁′)) ⊢Δ
          ⊢t₂′ = conv ⊢t₂ (sym eq₂′)
          t≡t₁ = subset*Term (redMany (Σ-β₁ {q = q} ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′))
          t′≡t₁ = subset*Term (fst-subst* t⇒t′ ⊢σF ⊢σG ⇨∷*
                               redMany (Σ-β₁ {q = q} ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′))
          G[t]≡G[t₁] = substTypeEq (refl ⊢σG) t≡t₁
          G[t]≡G[t₁]′ = PE.subst (Δ ⊢ subst (liftSubst σ) G [ _ ] ≡_)
                                 (PE.cong (_[ t₁ ])
                                          (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                 G[t]≡G[t₁]
          G[t′]≡G[t₁] = substTypeEq (refl ⊢σG) t′≡t₁
          G[t′]≡G[t₁]′ = PE.subst₂ (Δ ⊢_≡_)
                                   (PE.cong (_[ t₁ ])
                                            (PE.sym (wk-lift-id (subst (liftSubst σ) G))))
                                   (PE.sym (singleSubstLift G (fst t)))
                                   (sym G[t′]≡G[t₁])
          t⇒u = conv* (snd-subst* t⇒t′ ⊢σF ⊢σG)
                      (substTypeEq (refl ⊢σG) (fst-cong ⊢σF ⊢σG (subset*Term t⇒t′)))
          t⇒u′ = t⇒u ⇨∷* redMany (Σ-β₂ {q = q} ⊢σF ⊢σG ⊢t₁′ ⊢t₂′ ⊢t′)
          t⇒u″ = conv* t⇒u′ G[t]≡G[t₁]′
          v⇒w = TP.red*concat (TP.snd-subst* v⇒v′) (T.trans T.Σ-β₂ T.refl)
          wk[σ] = wkSubstS {σ = σ} [Γ] ⊢Δ ⊢Δ id [σ]
          wk[σF] = W.wk id ⊢Δ [σF]
          wk[t₁] = I.irrelevanceTerm′ (wk-subst F) wk[σF] (proj₁ (unwrap [F] ⊢Δ wk[σ])) [t₁]
          wk[Gt₁] = I.irrelevance′ (PE.sym (singleSubstWkComp t₁ σ G)) (proj₁ (unwrap [G] ⊢Δ (wk[σ] , wk[t₁])))
          t₂®v₂′ = redSubstTerm* wk[Gt₁] t₂®v₂ t⇒u″ v⇒w
      in  convTermʳ wk[Gt₁] (proj₁ (unwrap [G[t₁]] ⊢Δ [σ])) G[t′]≡G[t₁]′ t₂®v₂′

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
