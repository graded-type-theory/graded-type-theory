{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Typed Erasure′

module Erasure.LogicalRelation.Fundamental.Prodrec {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
                                                   (Prodrec : Erasure → Set)
                                                   {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.Untyped.Properties Erasure
open import Definition.Typed.Properties Erasure′
open import Definition.Typed.RedSteps Erasure′
open import Definition.Typed.Weakening Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′
open import Definition.Typed.Consequences.RedSteps Erasure′
open import Definition.Typed.Consequences.Reduction Erasure′

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Properties.Escape Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.Properties Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure′

import Definition.LogicalRelation.Irrelevance Erasure′ as I
import Definition.LogicalRelation.Weakening Erasure′ as W
import Definition.LogicalRelation.Substitution.Irrelevance Erasure′ as IS

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

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

prodrecωʳ″ : ∀ {l t₁ t₂ v₁ v₂} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
          → let [Σ] = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G] in
           ([A] : Γ ∙ (Σᵣ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
           ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
           (⊩ʳu : δ ∙ ω ∙ ω ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
           ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ])
           ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
           ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ +ᶜ δ / [Γ] / [σ])
         → ([t₁] : Δ ⊩⟨ l ⟩ t₁ ∷ subst σ F / proj₁ (unwrap [F] ⊢Δ [σ]))
         → ([t₂] : Δ ⊩⟨ l ⟩ t₂ ∷ subst (consSubst σ t₁) G / proj₁ (unwrap [G] ⊢Δ ([σ] , [t₁])))
         → Δ ⊢ subst σ t ⇒* prodᵣ t₁ t₂ ∷ subst σ (Σᵣ q ▷ F ▹ G)
         → T.subst σ′ (erase t) T.⇒* T.prod v₁ v₂
         → t₁ ®⟨ l ⟩ v₁ ∷ subst σ F / proj₁ (unwrap [F] ⊢Δ [σ])
         → t₂ ®⟨ l ⟩ v₂ ∷ subst (consSubst σ t₁) G / proj₁ (unwrap [G] ⊢Δ ([σ] , [t₁]))
         → subst σ (prodrec ω q′ A t u) ®⟨ l ⟩ T.subst σ′ (erase (prodrec ω q′ A t u)) ∷ subst σ (A [ t ]) / proj₁ (unwrap [At] ⊢Δ [σ])
prodrecωʳ″ {n} {F} {G} {q} {A} {δ} {u} {t} {σ} {σ′} {γ} {q′} {l} {t₁} {t₂} {v₁} {v₂} {Γ}
          [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [t₁] [t₂] d d′ t₁®v₁ t₂®v₂ =
  let σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ γ δ)
      σ₊ = consSubst (consSubst σ t₁) t₂
      σ₊®σ′₊ = (σ®σ′ᵤ , t₁®v₁) , t₂®v₂
      [σ₊] = ([σ] , [t₁]) , [t₂]
      u®u′ = ⊩ʳu {σ = σ₊}
                 {σ′ = T.consSubst (T.consSubst σ′ v₁) v₂}
                 [σ₊] σ₊®σ′₊
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = σ₊} ⊢Δ [σ₊])

      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [σGt₁] = proj₁ (unwrap [G] ⊢Δ ([σ] , [t₁]))
      [Σ] = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G]
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) (liftSubstS {σ = σ} {F = Σ q ▷ F ▹ G} [Γ] ⊢Δ [Σ] [σ]))
      ⊢σA = escape [σA]
      [σAt] = proj₁ (unwrap [At] ⊢Δ [σ])
      [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x) (subst-β-prodrec A σ) ⊢σu
      ⊢t₁ = escapeTerm [σF] [t₁]
      ⊢t₂ = escapeTerm [σGt₁] [t₂]
      ⊢t₂′ = PE.subst (λ x → Δ ⊢ t₂ ∷ x) (PE.sym (singleSubstComp t₁ σ G)) ⊢t₂

      red₁ = prodrec-subst* {p = ω} {q′ = q′} d ⊢σF ⊢σG ⊢σA ⊢σu′
      red₂ = prodrec-β ⊢σF ⊢σG ⊢σA ⊢t₁ ⊢t₂′ ⊢σu′
      At≡Ap = substTypeEq (refl ⊢σA) (subset*Term d)
      red = PE.subst₂ (λ x y → Δ ⊢ _ ⇒* x ∷ y)
                      (doubleSubstComp u t₁ t₂ σ)
                      (substCompProdrec A t₁ t₂ σ)
                      (conv* red₁ At≡Ap ⇨∷* redMany red₂)

      red′₁ = TP.prodrec-subst* {u = T.subst (T.liftSubstn σ′ 2) (erase u)} d′
      red′₂ = PE.subst (λ x → T.prodrec (T.prod v₁ v₂) (T.subst (T.liftSubstn σ′ 2) (erase u)) T.⇒ x)
                       (TP.doubleSubstComp (erase u) v₁ v₂ σ′)
                       (T.prodrec-β {t = v₁} {v₂} {T.subst (T.liftSubstn σ′ 2) (erase u)})
      red′ = TP.red*concat red′₁ (T.trans red′₂ T.refl)

      pr®pr′ = redSubstTerm* [σ₊A₊] u®u′ red red′
      At≡Ap′ = PE.subst₂ (λ x y → Δ ⊢ x ≡ y)
                         (PE.sym (singleSubstLift A t))
                         (substCompProdrec A t₁ t₂ σ)
                         At≡Ap
  in  convTermʳ [σ₊A₊] [σAt] (sym At≡Ap′) pr®pr′

prodrecωʳ′ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
          → let [Σ] = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G] in
           ([A] : Γ ∙ (Σᵣ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
           ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
           (⊩ʳu : δ ∙ ω ∙ ω ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
           ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ])
           ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
           ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷ Γ ◂ γ +ᶜ δ / [Γ] / [σ])
           ([σt] : Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ (Σᵣ q ▷ F ▹ G) / proj₁ (unwrap [Σ] ⊢Δ [σ]))
           (t®t′ : subst σ t ®⟨ l ⟩ T.subst σ′ (erase t) ∷ subst σ (Σᵣ q ▷ F ▹ G) / proj₁ (unwrap [Σ] ⊢Δ [σ]))
         → subst σ (prodrec ω q′ A t u) ®⟨ l ⟩ T.subst σ′ (erase (prodrec ω q′ A t u)) ∷ subst σ (A [ t ]) / proj₁ (unwrap [At] ⊢Δ [σ])
prodrecωʳ′ {n} {F} {G} {q} {A} {δ} {u} {t} {σ} {σ′} {γ} {q′} {l} {Γ}
          [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
          (Σₜ p t⇒p p≅p prodₙ ([t₁] , [t₂] , PE.refl))
          (t₁ , t₂ , v₁ , v₂ , d , d′ , [t₁]₁ , t₁®v₁ , t₂®v₂)
          with whrDet*Term (redₜ t⇒p , prodₙ) (d , prodₙ)
... | PE.refl =
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σF]′ = W.wk id ⊢Δ [σF]
      [σF]″ = W.wk id (wf ⊢σF) [σF]
      [t₁]′ = I.irrelevanceTerm′ (wk-id (subst σ F)) [σF]″ [σF] [t₁]
      [Gt₁] = proj₁ (unwrap [G] {σ = consSubst σ t₁} ⊢Δ
                                ([σ] , [t₁]′))
      [idσ] = wkSubstS [Γ] ⊢Δ (wf ⊢σF) id [σ]
      [σF]‴ = proj₁ (unwrap [F] (wf ⊢σF) [idσ])
      [t₁]″ = I.irrelevanceTerm′ (wk-subst F) [σF]″ [σF]‴ [t₁]
      [Gt₁]′ = proj₁ (unwrap [G] {σ = consSubst (id •ₛ σ) t₁} (wf ⊢σF) ([idσ] , [t₁]″))
      [Gt₁]″ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (_[ t₁ ]) (wk-subst-lift G))
                                                (singleSubstComp t₁ (id •ₛ σ) G)))
                              [Gt₁]′
      [t₂]′ = I.irrelevanceTerm′ (PE.trans (PE.cong (_[ t₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                           (singleSubstComp t₁ σ G))
                                 [Gt₁]″ [Gt₁] [t₂]
      t₁®v₁′ = irrelevanceTerm′ (wk-id (subst σ F)) [σF]′ [σF] t₁®v₁
      [idσ]′ = wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]
      [σF]₁ = proj₁ (unwrap [F] ⊢Δ [idσ]′)
      [t₁]₁′ = I.irrelevanceTerm′ (wk-subst F) [σF]′ [σF]₁ [t₁]₁
      [Gt₁]₁ = proj₁ (unwrap [G] {σ = consSubst (id •ₛ σ) t₁} ⊢Δ ([idσ]′ , [t₁]₁′))
      [Gt₁]₁′ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (_[ t₁ ]) (wk-subst-lift G))
                                                 (singleSubstComp t₁ (id •ₛ σ) G)))
                               [Gt₁]₁
      t₂®v₂′ = irrelevanceTerm′ (PE.trans (PE.cong (_[ t₁ ]) (wk-lift-id (subst (liftSubst σ) G)))
                                          (singleSubstComp t₁ σ G))
                                [Gt₁]₁′ [Gt₁] t₂®v₂
  in  prodrecωʳ″ {u = u} [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [t₁]′ [t₂]′ d d′ t₁®v₁′ t₂®v₂′
prodrecωʳ′ {n} {F} {G} {q} {A} {δ} {u} {t} {σ} {σ′} {γ} {q′} {l} {Γ}
          [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
          (Σₜ p t⇒p p≅p (ne x) prop)
          (t₁ , t₂ , v₁ , v₂ , d , d′ , [t₁] , t₁®v₁ , t₂®v₂)
          with whrDet*Term (redₜ t⇒p , ne x) (d , prodₙ) | x
... | PE.refl | ()

prodrecωʳ : ∀ {l} {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
           ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σᵣ q ▷ F ▹ G / [Γ])
           ([A] : Γ ∙ (Σᵣ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
           ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
           ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σᵣ q ▷ F ▹ G / [Γ] / [Σ])
           ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
           (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷ Σᵣ q ▷ F ▹ G / [Γ] / [Σ])
           (⊩ʳu : δ ∙ ω ∙ ω ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
         → ∃ λ ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ])
         → ω ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec ω q′ A t u ∷ A [ t ] / [Γ] / [At]
prodrecωʳ {n} {F} {G} {q} {A} {t} {u} {γ} {δ} {q′} {l} {Γ} [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu =
  let [At] = substS {F = Σ q ▷ F ▹ G} {A} {t} [Γ] [Σ] [A] [t]
  in  [At] , λ {σ} [σ] σ®σ′ →
    let [Σ]′ = Σᵛ {F = F} {G} {q = q} {m = Σᵣ} [Γ] [F] [G]
        [A]′ = IS.irrelevance {A = A} (_∙_ {A = Σ q ▷ F ▹ G} [Γ] [Σ])
                              (_∙_ {A = Σ q ▷ F ▹ G} [Γ] [Σ]′) [A]
        ⊩ʳt′ = irrelevance {A = Σ q ▷ F ▹ G} {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
        t®t′ = ⊩ʳt′ [σ] (subsumptionSubst {l = l} σ®σ′
                    (≤ᶜ-trans (+ᶜ-decreasingˡ (ω ·ᶜ γ) δ)
                              (≤ᶜ-reflexive (·ᶜ-identityˡ γ))))
        [t]′ = IS.irrelevanceTerm {A = Σ q ▷ F ▹ G} {t = t} [Γ] [Γ] [Σ] [Σ]′ [t]
        [σt] = proj₁ ([t]′ ⊢Δ [σ])
    in  prodrecωʳ′ {A = A} {u = u} {t = t} [Γ] [F] [G] [A]′ [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [σt] t®t′
