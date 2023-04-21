open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Typed Erasure

module Erasure.LogicalRelation.Fundamental.Prodrec
  {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.Untyped.Properties Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure
open import Definition.Typed.Weakening Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Consequences.RedSteps Erasure
open import Definition.Typed.Consequences.Reduction Erasure

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.Substitution Erasure
open import Definition.LogicalRelation.Substitution.Properties Erasure
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst Erasure

import Definition.LogicalRelation.Irrelevance Erasure as I
import Definition.LogicalRelation.Weakening Erasure as W
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as IS

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Instances.Erasure.Properties
  restrictions
open import Definition.Mode ErasureModality

open import Erasure.LogicalRelation ⊢Δ restrictions
open import Erasure.LogicalRelation.Conversion ⊢Δ restrictions
open import Erasure.LogicalRelation.Reduction ⊢Δ restrictions
open import Erasure.LogicalRelation.Subsumption ⊢Δ restrictions
open import Erasure.LogicalRelation.Irrelevance ⊢Δ restrictions

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
    p q q′ r : Erasure
    γ δ : Conₘ n
    σ : Subst k n
    σ′ : T.Subst k n
    m : Mode
    l : TypeLevel

prodrecωʳ′-𝟘 :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]) →
  Γ ∙ (Σᵣ 𝟘 , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ Σᵛ [Γ] [F] [G] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ 𝟘 (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ 𝟘 ∙ ω ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodᵣ 𝟘 (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ 𝟘 (var (x0 +1)) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ +ᶜ δ / [Γ] / [σ] →
  ([t₁] : Δ ⊩⟨ l ⟩ t₁ ∷ subst σ F / [F] .unwrap ⊢Δ [σ] .proj₁) →
  Δ ⊩⟨ l ⟩ t₂ ∷ subst (consSubst σ t₁) G /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  Δ ⊢ subst σ t ⇒* prodᵣ 𝟘 t₁ t₂ ∷ subst σ (Σᵣ 𝟘 , q ▷ F ▹ G) →
  T.subst σ′ (erase t) T.⇒* v₂ →
  t₂ ®⟨ l ⟩ v₂ ∷ subst (consSubst σ t₁) G /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  subst σ (prodrec ω 𝟘 q′ A t u) ®⟨ l ⟩
    T.subst σ′ (erase (prodrec ω 𝟘 q′ A t u)) ∷ subst σ (A [ t ]) /
    [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′-𝟘
  {l = l} {G = G} {A = A} {δ = δ} {u = u} {t = t} {σ = σ} {σ′ = σ′}
  {γ = γ} {t₁ = t₁} {t₂ = t₂}
  [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [t₁] [t₂] d d′ t₂®v₂ =
  convTermʳ _ [σ₊A₊] [σAt] (sym At≡Ap′) pr®pr′
  where
  open Tools.Reasoning.PropositionalEquality

  σ₊     = consSubst (consSubst σ t₁) t₂
  [σ₊]   = ([σ] , [t₁]) , [t₂]
  [σ₊A₊] = [A₊] .unwrap {σ = σ₊} ⊢Δ [σ₊] .proj₁
  [σF]   = [F] .unwrap ⊢Δ [σ] .proj₁
  ⊢σF    = escape [σF]
  [⇑σ]   = liftSubstS [Γ] ⊢Δ [F] [σ]
  [σG]   = [G] .unwrap {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ] .proj₁
  ⊢σG    = escape [σG]
  [σGt₁] = [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁
  [Σ]    = Σᵛ [Γ] [F] [G]
  [σΣ]   = [Σ] .unwrap ⊢Δ [σ] .proj₁
  ⊢σΣ    = escape [σΣ]
  [σA]   = [A] .unwrap {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ)
             (liftSubstS [Γ] ⊢Δ [Σ] [σ]) .proj₁
  ⊢σA    = escape [σA]
  [σAt]  = [At] .unwrap ⊢Δ [σ] .proj₁
  [⇑²σ]  = liftSubstS {σ = liftSubst σ} ([Γ] ∙ [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
  [σA₊]  = [A₊] .unwrap {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ]
             .proj₁
  [σu]   = [u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ] .proj₁
  ⊢σu    = escapeTerm [σA₊] [σu]
  ⊢σu′   = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x)
             (subst-β-prodrec A σ) ⊢σu
  ⊢t₁    = escapeTerm [σF] [t₁]
  ⊢t₂    = escapeTerm [σGt₁] [t₂]
  ⊢t₂′   = PE.subst (λ x → Δ ⊢ t₂ ∷ x) (PE.sym (singleSubstComp t₁ σ G))
             ⊢t₂
  At≡Ap  = substTypeEq (refl ⊢σA) (subset*Term d)
  At≡Ap′ = PE.subst₂ (λ x y → Δ ⊢ x ≡ y)
             (PE.sym (singleSubstLift A t))
             (substCompProdrec A t₁ t₂ σ)
             At≡Ap
  red₁   = prodrec-subst* {r = ω} d ⊢σF ⊢σG ⊢σA ⊢σu′
  red₂   = prodrec-β ⊢σF ⊢σG ⊢σA ⊢t₁ ⊢t₂′ ⊢σu′ PE.refl
  red′   = PE.subst₂ (λ x y → Δ ⊢ _ ⇒* x ∷ y)
             (doubleSubstComp u t₁ t₂ σ)
             (substCompProdrec A t₁ t₂ σ)
             (conv* red₁ At≡Ap ⇨∷* redMany red₂)
  lemma′ = λ x →
             T.subst
               (T.consSubst (T.sgSubst T.↯) (T.subst σ′ (erase t)))
               (T.wk1 (T.wk1 (σ′ x)))                                ≡⟨ TP.wk1-tail (T.wk1 (σ′ x)) ⟩

             T.subst (T.sgSubst T.↯) (T.wk1 (σ′ x))                  ≡⟨ TP.wk1-tail (σ′ x) ⟩

             T.subst T.idSubst (σ′ x)                                ≡⟨ TP.subst-id (σ′ x) ⟩

             σ′ x                                                    ∎
  lemma  = T.subst (T.consSubst (T.sgSubst T.↯) (T.subst σ′ (erase t)))
             (T.subst (T.liftSubst (T.liftSubst σ′)) (erase u))          ≡⟨ TP.substCompEq (erase u) ⟩

           T.subst
             (T.consSubst (T.sgSubst T.↯) (T.subst σ′ (erase t)) T.ₛ•ₛ
              T.liftSubst (T.liftSubst σ′))
             (erase u)                                                   ≡⟨ TP.substVar-to-subst
                                                                              (λ where
                                                                                 x0        → PE.refl
                                                                                 (x0 +1)   → PE.refl
                                                                                 (x +1 +1) → lemma′ x)
                                                                              (erase u) ⟩
           T.subst
             (T.consSubst (T.consSubst σ′ T.↯) (T.subst σ′ (erase t)))
             (erase u)                                                   ∎
  red″   = T.trans T.prodrec-β
             (PE.subst
                (T._⇒* T.subst (T.consSubst (T.consSubst σ′ T.↯)
                                  (T.subst σ′ (erase t)))
                         (erase u))
                (PE.sym lemma)
                T.refl)
  σ®σ′ᵤ  = subsumptionSubst {l = l} σ®σ′ (+ᶜ-decreasingʳ γ δ)
  σ₊®σ′₊ = (σ®σ′ᵤ , _) , targetRedSubstTerm* [σGt₁] t₂®v₂ d′
  u®u′   = ⊩ʳu [σ₊] σ₊®σ′₊
  pr®pr′ = redSubstTerm* [σ₊A₊] u®u′ red′ red″

prodrecωʳ′-ω :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]) →
  Γ ∙ (Σᵣ ω , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ Σᵛ [Γ] [F] [G] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ ω (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ ω ∙ ω ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodᵣ ω (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ ω (var (x0 +1)) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ +ᶜ δ / [Γ] / [σ] →
  ([t₁] : Δ ⊩⟨ l ⟩ t₁ ∷ subst σ F / [F] .unwrap ⊢Δ [σ] .proj₁) →
  Δ ⊩⟨ l ⟩ t₂ ∷ subst (consSubst σ t₁) G /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  Δ ⊢ subst σ t ⇒* prodᵣ ω t₁ t₂ ∷ subst σ (Σᵣ ω , q ▷ F ▹ G) →
  T.subst σ′ (erase t) T.⇒* T.prod v₁ v₂ →
  t₁ ®⟨ l ⟩ v₁ ∷ subst σ F / [F] .unwrap ⊢Δ [σ] .proj₁ →
  t₂ ®⟨ l ⟩ v₂ ∷ subst (consSubst σ t₁) G /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  subst σ (prodrec ω ω q′ A t u) ®⟨ l ⟩
    T.subst σ′ (erase (prodrec ω ω q′ A t u)) ∷ subst σ (A [ t ]) /
    [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′-ω
  {l = l} {F = F} {G = G} {q = q} {A = A} {δ = δ} {u = u} {t = t}
  {σ = σ} {σ′ = σ′} {γ = γ} {t₁ = t₁} {t₂ = t₂} {v₁ = v₁} {v₂ = v₂}
  {Γ = Γ} [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [t₁] [t₂] d d′
  t₁®v₁ t₂®v₂ =
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
      [σA] = [A] .unwrap {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ)
               (liftSubstS [Γ] ⊢Δ [Σ] [σ]) .proj₁
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

      red₁ = prodrec-subst* {r = ω} d ⊢σF ⊢σG ⊢σA ⊢σu′
      red₂ = prodrec-β ⊢σF ⊢σG ⊢σA ⊢t₁ ⊢t₂′ ⊢σu′ PE.refl
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
  in  convTermʳ _ [σ₊A₊] [σAt] (sym At≡Ap′) pr®pr′

prodrecωʳ′ :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]) →
  let [Σ] = Σᵛ [Γ] [F] [G] in
  Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ p ∙ ω ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ +ᶜ δ / [Γ] / [σ] →
  Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ (Σᵣ p , q ▷ F ▹ G) /
    [Σ] .unwrap ⊢Δ [σ] .proj₁ →
  subst σ t ®⟨ l ⟩ T.subst σ′ (erase t) ∷ subst σ (Σᵣ p , q ▷ F ▹ G) /
    [Σ] .unwrap ⊢Δ [σ] .proj₁ →
  subst σ (prodrec ω p q′ A t u) ®⟨ l ⟩
    T.subst σ′ (erase (prodrec ω p q′ A t u)) ∷
    subst σ (A [ t ]) / [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′
  {n = n} {l = l} {F = F} {G = G} {q = q} {A = A} {δ = δ} {u = u}
  {t = t} {σ = σ} {σ′ = σ′} {γ = γ} {Γ = Γ}
  [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
  (Σₜ p t⇒p p≅p prodₙ (foo , [t₁] , [t₂] , PE.refl))
  (t₁ , t₂ , d , [t₁]₁ , v₂ , t₂®v₂ , extra)
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
  in
  case Σ-®-view extra of λ where
    (𝟘 d′) → prodrecωʳ′-𝟘 {u = u} [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
        [t₁]′ [t₂]′ d d′ t₂®v₂′
    (ω v₁ d′ t₁®v₁) →
      let t₁®v₁′ = irrelevanceTerm′ (wk-id (subst σ F)) [σF]′ [σF] t₁®v₁
      in
      prodrecωʳ′-ω {u = u} [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
        [t₁]′ [t₂]′ d d′ t₁®v₁′ t₂®v₂′
prodrecωʳ′ _ _ _ _ _ _ _ _ _ _ (Σₜ _ t⇒p _ (ne x) _) (_ , _ , d , _)
  with whrDet*Term (redₜ t⇒p , ne x) (d , prodₙ) | x
... | PE.refl | ()

prodrecωʳ :
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σᵣ p , q ▷ F ▹ G / [Γ]) →
  Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  Γ ⊩ᵛ⟨ l ⟩ t ∷ Σᵣ p , q ▷ F ▹ G / [Γ] / [Σ] →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ 𝟙ᵐ ] Σᵣ p , q ▷ F ▹ G / [Γ] / [Σ] →
  δ ∙ p ∙ ω ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ∃ λ ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
    ω ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec ω p q′ A t u ∷[ 𝟙ᵐ ] A [ t ] / [Γ] /
      [At]
prodrecωʳ
  {l = l} {t = t} {γ = γ} {δ = δ}
  [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu =
  let [At] = substS [Γ] [Σ] [A] [t]
  in  [At] , λ {σ} [σ] σ®σ′ →
    let [Σ]′ = Σᵛ [Γ] [F] [G]
        [A]′ = IS.irrelevance ([Γ] ∙ [Σ]) ([Γ] ∙ [Σ]′) [A]
        ⊩ʳt′ = irrelevance {t = t} [Γ] [Γ] [Σ] [Σ]′ ⊩ʳt
        t®t′ = ⊩ʳt′ [σ] (subsumptionSubst {l = l} σ®σ′
                    (≤ᶜ-trans (+ᶜ-decreasingˡ (ω ·ᶜ γ) δ)
                              (≤ᶜ-reflexive (·ᶜ-identityˡ γ))))
        [t]′ = IS.irrelevanceTerm {t = t} [Γ] [Γ] [Σ] [Σ]′ [t]
        [σt] = proj₁ ([t]′ ⊢Δ [σ])
    in  prodrecωʳ′ [Γ] [F] [G] [A]′ [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [σt] t®t′
