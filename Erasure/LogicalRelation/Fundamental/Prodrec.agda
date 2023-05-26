------------------------------------------------------------------------
-- Erasure validity of prodrec.
------------------------------------------------------------------------

open import Definition.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed as T′
import Definition.Untyped as U hiding (_∷_)
open import Tools.Nullary
open import Tools.Sum hiding (id; sym)
import Tools.PropositionalEquality as PE

module Erasure.LogicalRelation.Fundamental.Prodrec
  {a k} {M : Set a} (𝕄 : Modality M)
  (open U M) (open T′ M) (open Modality 𝕄)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet)
  {{eqrel : EqRelSet M}}
  where

open EqRelSet {{...}}

open import Definition.Untyped.Properties M
open import Definition.Typed.Properties M
open import Definition.Typed.RedSteps M
open import Definition.Typed.Weakening M
open import Definition.Typed.Consequences.Substitution M
open import Definition.Typed.Consequences.RedSteps M
open import Definition.Typed.Consequences.Reduction M

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Properties.Escape M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Properties M
open import Definition.LogicalRelation.Substitution.Introductions.Pi M
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst M

import Definition.LogicalRelation.Irrelevance M as I
import Definition.LogicalRelation.Weakening M as W
import Definition.LogicalRelation.Substitution.Irrelevance M as IS

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.Reasoning.PropositionalEquality

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet-and-star 𝟘-well-behaved
open import Definition.Mode 𝕄

open import Erasure.LogicalRelation 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Conversion 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Reduction 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Subsumption 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Irrelevance 𝕄 ⊢Δ is-𝟘?

open import Erasure.Extraction 𝕄 is-𝟘?
open import Erasure.Extraction.Properties 𝕄 𝟘-well-behaved
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
    p q q′ r : M
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
  Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ Σᵛ [Γ] [F] [G] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ (r · p) ∙ r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ / [Γ] / [σ] →
  ([t₁] : Δ ⊩⟨ l ⟩ t₁ ∷ subst σ F / [F] .unwrap ⊢Δ [σ] .proj₁) →
  Δ ⊩⟨ l ⟩ t₂ ∷ subst (consSubst σ t₁) G /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  Δ ⊢ subst σ t ⇒* prodᵣ p t₁ t₂ ∷ subst σ (Σᵣ p , q ▷ F ▹ G) →
  T.subst σ′ (erase t) T.⇒* v₂ →
  t₂ ®⟨ l ⟩ v₂ ∷ subst (consSubst σ t₁) G /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  p PE.≡ 𝟘 → r PE.≢ 𝟘 →
  subst σ (prodrec r p q′ A t u) ®⟨ l ⟩
    T.subst σ′ (erase (prodrec r p q′ A t u)) ∷ subst σ (A [ t ]) /
    [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′-𝟘
  {l = l} {G = G} {p = p} {A = A} {δ = δ} {r = r} {u = u} {t = t} {σ = σ} {σ′ = σ′}
  {γ = γ} {t₁ = t₁} {t₂ = t₂}
  [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [t₁] [t₂] d d′ t₂®v₂ p≡𝟘 r≢𝟘
  with is-𝟘? r
... | yes r≡𝟘 = PE.⊥-elim (r≢𝟘 r≡𝟘)
... | no _ with is-𝟘? p
... | no p≢𝟘 = PE.⊥-elim (p≢𝟘 p≡𝟘)
... | yes PE.refl =
  convTermʳ [σ₊A₊] [σAt] (sym At≡Ap′) pr®pr′
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
  red₁   = prodrec-subst* {r = r} d ⊢σF ⊢σG ⊢σA ⊢σu′
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
  σ®σ′ᵤ  = subsumptionSubst {l = l} σ®σ′ λ x rγ+δ≡𝟘 →
             +-positiveʳ (PE.trans (PE.sym (lookup-distrib-+ᶜ (r ·ᶜ γ) δ x)) rγ+δ≡𝟘)
  t₁®v₁ = subsumptionTerm {p = p} t®v◂𝟘 λ _ → PE.trans (·-identityˡ (r · 𝟘)) (·-zeroʳ r)
  t₂®v₂′ = targetRedSubstTerm* [σGt₁] t₂®v₂ d′ ◀ _
  σ₊®σ′₊ = (σ®σ′ᵤ , t₁®v₁) , t₂®v₂′
  u®u′   = ⊩ʳu [σ₊] σ₊®σ′₊
  pr®pr′ = redSubstTerm* [σ₊A₊] (u®u′ ◀≢𝟘 𝟙≉𝟘) red′ red″

prodrecωʳ′-ω :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]) →
  Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ Σᵛ [Γ] [F] [G] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ (r · p) ∙ r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ / [Γ] / [σ] →
  ([t₁] : Δ ⊩⟨ l ⟩ t₁ ∷ subst σ F / [F] .unwrap ⊢Δ [σ] .proj₁) →
  Δ ⊩⟨ l ⟩ t₂ ∷ subst (consSubst σ t₁) G /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  Δ ⊢ subst σ t ⇒* prodᵣ p t₁ t₂ ∷ subst σ (Σᵣ p , q ▷ F ▹ G) →
  T.subst σ′ (erase t) T.⇒* T.prod v₁ v₂ →
  t₁ ®⟨ l ⟩ v₁ ∷ subst σ F / [F] .unwrap ⊢Δ [σ] .proj₁ →
  t₂ ®⟨ l ⟩ v₂ ∷ subst (consSubst σ t₁) G /
    [G] .unwrap ⊢Δ ([σ] , [t₁]) .proj₁ →
  p PE.≢ 𝟘 → r PE.≢ 𝟘 →
  subst σ (prodrec r p q′ A t u) ®⟨ l ⟩
    T.subst σ′ (erase (prodrec r p q′ A t u)) ∷ subst σ (A [ t ]) /
    [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′-ω
  {l = l} {F = F} {G = G} {p = p} {q = q} {A = A} {δ = δ} {r = r} {u = u} {t = t}
  {σ = σ} {σ′ = σ′} {γ = γ} {t₁ = t₁} {t₂ = t₂} {v₁ = v₁} {v₂ = v₂}
  {Γ = Γ} [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′ [t₁] [t₂] d d′
  t₁®v₁ t₂®v₂ p≢𝟘 r≢𝟘 with is-𝟘? r
... | yes r≡𝟘 = PE.⊥-elim (r≢𝟘 r≡𝟘)
... | no _ with is-𝟘? p
... | yes p≡𝟘 = PE.⊥-elim (p≢𝟘 p≡𝟘)
... | no _ =
  let σ®σ′ᵤ = subsumptionSubst {l = l} σ®σ′ λ x rγ+δ≡𝟘 →
                +-positiveʳ (PE.trans (PE.sym (lookup-distrib-+ᶜ (r ·ᶜ γ) δ x)) rγ+δ≡𝟘)
      σ₊ = consSubst (consSubst σ t₁) t₂
      t₁®v₁′ = t₁®v₁ ◀ _
      t₂®v₂′ = t₂®v₂ ◀ _
      σ₊®σ′₊ = (σ®σ′ᵤ , t₁®v₁′) , t₂®v₂′
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

      red₁ = prodrec-subst* {r = r} d ⊢σF ⊢σG ⊢σA ⊢σu′
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

      pr®pr′ = redSubstTerm* [σ₊A₊] (u®u′ ◀≢𝟘 𝟙≉𝟘) red red′
      At≡Ap′ = PE.subst₂ (λ x y → Δ ⊢ x ≡ y)
                         (PE.sym (singleSubstLift A t))
                         (substCompProdrec A t₁ t₂ σ)
                         At≡Ap
  in  convTermʳ [σ₊A₊] [σAt] (sym At≡Ap′) pr®pr′

prodrecωʳ′ :
  {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]) →
  let [Σ] = Σᵛ [Γ] [F] [G] in
  Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ (r · p) ∙ r ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  r PE.≢ 𝟘 →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ r ·ᶜ γ +ᶜ δ / [Γ] / [σ] →
  Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ (Σᵣ p , q ▷ F ▹ G) /
    [Σ] .unwrap ⊢Δ [σ] .proj₁ →
  subst σ t ®⟨ l ⟩ T.subst σ′ (erase t) ∷ subst σ (Σᵣ p , q ▷ F ▹ G) /
    [Σ] .unwrap ⊢Δ [σ] .proj₁ →
  subst σ (prodrec r p q′ A t u) ®⟨ l ⟩
    T.subst σ′ (erase (prodrec r p q′ A t u)) ∷
    subst σ (A [ t ]) / [At] .unwrap ⊢Δ [σ] .proj₁
prodrecωʳ′
  {n = n} {l = l} {F = F} {G = G} {p = p′} {q = q} {A = A} {δ = δ} {r = r} {u = u}
  {t = t} {σ = σ} {σ′ = σ′} {γ = γ} {q′ = q′} {Γ = Γ}
  [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] r≢𝟘 [σ] σ®σ′
  (Σₜ p t⇒p p≅p prodₙ (foo , [t₁] , [t₂] , PE.refl))
  (t₁ , t₂ , d , [t₁]₁ , v₂ , t₂®v₂ , extra)
  with is-𝟘? r
... | yes r≡𝟘 = PE.⊥-elim (r≢𝟘 r≡𝟘)
... | no _
  with whrDet*Term (redₜ t⇒p , prodₙ) (d , prodₙ)
... | PE.refl = PE.subst (λ x → subst σ (prodrec r p′ q′ A t u) ®⟨ l ⟩ x ∷ subst σ (A [ t ]) / [At] .unwrap ⊢Δ [σ] .proj₁)
                         (PE.cong (T.subst σ′) (prodrec-ω {q = q′} {A = A} p′ r≢𝟘))
                         pr®pr′
  where
  [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
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
  pr = prodrec r p′ q′ A t u
  [σAt] = proj₁ (unwrap [At] ⊢Δ [σ])
  pr®pr′ = Σ-®-elim (λ _ → subst σ pr ®⟨ l ⟩ T.subst σ′ (erase pr) ∷ subst σ (A [ t ]) / [σAt]) extra
                    (λ d′ p≡𝟘 →
                      let pr®pr′ = prodrecωʳ′-𝟘 {δ = δ} {u = u} {γ = γ} {q′ = q′}
                                                [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
                                                [t₁]′ [t₂]′ d d′ t₂®v₂′ p≡𝟘 r≢𝟘
                      in  pr®pr′)
                    λ v₁ d′ t₁®v₁ p≢𝟘 →
                      let t₁®v₁′ = irrelevanceTerm′ (wk-id (subst σ F)) [σF]′ [σF] t₁®v₁
                          pr®pr′ = prodrecωʳ′-ω {δ = δ} {u = u} {γ = γ} {q′ = q′}
                                                [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] [σ] σ®σ′
                                                [t₁]′ [t₂]′ d d′ t₁®v₁′ t₂®v₂′ p≢𝟘 r≢𝟘
                      in  pr®pr′

prodrecωʳ′ _ _ _ _ _ _ _ _ _ _ _ (Σₜ _ t⇒p _ (ne x) _) (_ , _ , d , _)
  with whrDet*Term (redₜ t⇒p , ne x) (d , prodₙ) | x
... | PE.refl | ()

prodrec𝟘ʳ : ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]) →
  let [Σ] = Σᵛ [Γ] [F] [G] in
  Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ] →
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  δ ∙ 𝟘 ∙ 𝟘 ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ]
    A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G] / [A₊] →
  r PE.≡ 𝟘 →
  k PE.≡ 0 →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ / [Γ] / [σ] →
  Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ (Σᵣ p , q ▷ F ▹ G) /
    [Σ] .unwrap ⊢Δ [σ] .proj₁ →
  subst σ (prodrec r p q′ A t u) ®⟨ l ⟩
    T.subst σ′ (erase (prodrec r p q′ A t u)) ∷
    subst σ (A [ t ]) / [At] .unwrap ⊢Δ [σ] .proj₁
prodrec𝟘ʳ  {n} {Γ} {l} {F} {G} {p} {q} {A} {δ} {u} {t} {r} {σ} {σ′} {q′}
          [Γ] [F] [G] [A] [A₊] ⊩ʳu [At] [u] r≡𝟘 PE.refl [σ] σ®σ′
          (Σₜ t′ t⇒t′ p≅p (prodₙ {t = t₁} {u = t₂}) (PE.refl , [t₁]′ , [t₂]′ , PE.refl)) with is-𝟘? r
... | yes _ =
  let [Σ] = Σᵛ [Γ] [F] [G]
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [⇑σ]′ = liftSubstS [Γ] ⊢Δ [Σ] [σ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) [⇑σ]′)
      ⊢σA = escape [σA]
      [⇑²σ] = liftSubstS ([Γ] ∙ [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x)
                      (subst-β-prodrec A σ) ⊢σu

      ⊢Δ′ = wf ⊢σF
      [σF]′ = W.wk id ⊢Δ′ [σF]
      [t₁] = I.irrelevanceTerm′ (wk-id (subst σ F)) [σF]′ [σF] [t₁]′
      ⊢t₁ = escapeTerm [σF] [t₁]
      [Gt₁] = proj₁ (unwrap [G] ⊢Δ ([σ] , [t₁]))
      [σ]′ = wkSubstS [Γ] ⊢Δ ⊢Δ′ id [σ]
      [σF]″ = proj₁ (unwrap [F] ⊢Δ′ [σ]′)
      [t₁]″ = I.irrelevanceTerm′ (wk-subst F) [σF]′ [σF]″ [t₁]′
      [Gt₁]″ = proj₁ (unwrap [G] ⊢Δ′ ([σ]′ , [t₁]″))
      [Gt₁]′ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (subst (sgSubst t₁)) (wk-subst-lift G))
                                                (singleSubstComp _ _ G)))
                              [Gt₁]″
      [t₂] = I.irrelevanceTerm′ (PE.trans (PE.cong (subst (sgSubst t₁)) (wk-lift-id (subst (liftSubst σ) G)))
                                          (PE.trans (substCompEq G) (substSingletonComp G)))
                                [Gt₁]′ [Gt₁] [t₂]′
      ⊢t₂ = escapeTerm [Gt₁] [t₂]
      ⊢t₂′ = PE.subst (λ x → _ ⊢ t₂ ∷ x)
                      (PE.sym (singleSubstComp t₁ σ G)) ⊢t₂

      σ₊ = consSubst (consSubst σ t₁) t₂
      σ′₊ = T.consSubst (T.consSubst σ′ T.↯) T.↯
      [σ₊] = ([σ] , [t₁]) , [t₂]
      σ₊®σ′₊ = (σ®σ′ , PE.subst (λ p → t₁ ®⟨ l ⟩ T.↯ ∷ subst σ F ◂ p / [σF])
                                (PE.sym (·-zeroʳ 𝟙)) t®v◂𝟘)
                    , PE.subst (λ p → t₂ ®⟨ _ ⟩ T.↯ ∷ subst (consSubst σ t₁) G ◂ p / [Gt₁])
                               (PE.sym (·-zeroʳ 𝟙)) t®v◂𝟘
      σ₊u®σ′₊u′ = ⊩ʳu {σ = σ₊} {σ′ = σ′₊} [σ₊] σ₊®σ′₊
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = σ₊} ⊢Δ [σ₊])

      At≡At′ = substTypeEq (refl ⊢σA) (subset*Term (redₜ t⇒t′))
      At≡At″ = PE.subst (λ x → Δ ⊢ _ ≡ x) (substCompProdrec A t₁ t₂ σ) At≡At′

      red₁ = prodrec-subst* (redₜ t⇒t′) ⊢σF ⊢σG ⊢σA ⊢σu′
      red₁′ = conv* red₁ At≡At″
      red₂ = redMany (prodrec-β {r = r} {q′ = q′} ⊢σF ⊢σG ⊢σA ⊢t₁ ⊢t₂′ ⊢σu′ PE.refl)
      red₂′ = PE.subst (λ x → _ ⊢ prodrec r p q′ _ _ _ ⇒* _ ∷ x) (substCompProdrec A t₁ t₂ σ) red₂
      red = PE.subst (λ x → _ ⊢ subst σ (prodrec r p q′ A t u) ⇒* x ∷ _)
                     (doubleSubstComp u t₁ t₂ σ)
                     (red₁′ ⇨∷* red₂′)
      red′ = PE.subst (λ x → T.subst σ′ (T.prodrec (T.prod T.↯ T.↯) (erase u)) T.⇒ x)
                      (TP.doubleSubstComp (erase u) T.↯ T.↯ σ′)
                      (T.prodrec-β {t = T.↯} {T.↯} {T.subst (T.liftSubstn σ′ 2) (erase u)})


      pr®pr′ = redSubstTerm* [σ₊A₊] (σ₊u®σ′₊u′ ◀≢𝟘 𝟙≉𝟘)
                             red (T.trans red′ T.refl)
      [σAt] = proj₁ (unwrap [At] ⊢Δ [σ])
      At≡At‴ = PE.subst (λ x → Δ ⊢ x ≡ _) (PE.sym (singleSubstLift A t)) At≡At″

  in  convTermʳ [σ₊A₊] [σAt] (sym At≡At‴) pr®pr′

... | no r≢𝟘 = PE.⊥-elim (r≢𝟘 r≡𝟘)
prodrec𝟘ʳ {n} {Γ} {l} {F} {G} {p} {q} {A} {δ} {u} {t} {r} {σ} {σ′} {q′}
          [Γ] [F] [G] x [A₊] x₁ [At] x₂ r≡𝟘 PE.refl [σ] x₄
          (Σₜ t′ t⇒t′ p≅p (ne y) prop) = PE.⊥-elim (noClosedNe y)

prodrecʳ :
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
  (r PE.≢ 𝟘 → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] Σᵣ p , q ▷ F ▹ G / [Γ] / [Σ]) →
  δ ∙ (⌜ m ⌝ · r · p) ∙ (⌜ m ⌝ · r) ▸ Γ ∙ F ∙ G ⊩ʳ⟨ l ⟩ u ∷[ m ]
    A [ prodᵣ p (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊] →
  (r PE.≡ 𝟘 → k PE.≡ 0) →
  ∃ λ ([At] : Γ ⊩ᵛ⟨ l ⟩ A [ t ] / [Γ]) →
    r ·ᶜ γ +ᶜ δ ▸ Γ ⊩ʳ⟨ l ⟩ prodrec r p q′ A t u ∷[ m ] A [ t ] / [Γ] /
      [At]
prodrecʳ {m = 𝟘ᵐ} [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu r≢𝟘
  with is-𝟘? 𝟘
... | yes _  = substS [Γ] [Σ] [A] [t] , _
... | no 𝟘≢𝟘 = PE.⊥-elim (𝟘≢𝟘 PE.refl)
prodrecʳ
  {Γ = Γ} {l = l} {p = p} {t = t} {u = u} {r = r} {γ = γ} {m = 𝟙ᵐ} {δ = δ}
  [Γ] [F] [G] [Σ] [A] [A₊] [t] [u] ⊩ʳt ⊩ʳu r≡𝟘→k≡0 with is-𝟘? 𝟙
... | yes 𝟙≡𝟘 = PE.⊥-elim (𝟙≉𝟘 𝟙≡𝟘)
... | no 1≢𝟘 =
  let [At] = substS [Γ] [Σ] [A] [t]
  in  [At] , λ {σ} [σ] σ®σ′ →
    let [Σ]′ = Σᵛ [Γ] [F] [G]
        [A]′ = IS.irrelevance ([Γ] ∙ [Σ]) ([Γ] ∙ [Σ]′) [A]
        [t]′ = IS.irrelevanceTerm {t = t} [Γ] [Γ] [Σ] [Σ]′ [t]
        [σt] = proj₁ ([t]′ ⊢Δ [σ])
        ⊩ʳu′ = subsumption {t = u} ([Γ] ∙ [F] ∙ [G]) [A₊]
                           (subsumption′ {t = u} ([Γ] ∙ [F] ∙ [G]) [A₊] ⊩ʳu)
                           lemma′
    in case is-𝟘? r of λ where
      (yes r≡𝟘) →
        let ⊩ʳu″ = PE.subst (λ x → x ▸ _ ∙ _ ∙ _ ⊩ʳ⟨ l ⟩ u ∷[ 𝟙ᵐ ] _ / [Γ] ∙ [F] ∙ [G] / [A₊])
                            (PE.cong₃ (λ x y z → (x ∙ y) ∙ z)
                                      (PE.sym (PE.trans (PE.cong (λ x → x ·ᶜ γ +ᶜ δ) r≡𝟘)
                                              (≈ᶜ→≡ (≈ᶜ-trans (+ᶜ-congʳ (·ᶜ-zeroˡ γ))
                                                              (+ᶜ-identityˡ δ)))))
                                      (PE.trans (·-congʳ r≡𝟘) (·-zeroˡ p))
                                      r≡𝟘)
                            ⊩ʳu′
        in  prodrec𝟘ʳ [Γ] [F] [G] [A]′ [A₊] ⊩ʳu″ [At] [u] r≡𝟘 (r≡𝟘→k≡0 r≡𝟘) [σ] σ®σ′ [σt]
      (no r≢𝟘) →
        let ⊩ʳt′ = irrelevance {t = t} [Γ] [Γ] [Σ] [Σ]′ (subsumption′ {t = t} [Γ] [Σ] (⊩ʳt r≢𝟘))
            t®t′ = ⊩ʳt′ [σ] (subsumptionSubst {l = l} σ®σ′ (lemma r≢𝟘))
        in  prodrecωʳ′ [Γ] [F] [G] [A]′ [A₊] ⊩ʳu′ [At] [u] r≢𝟘 [σ] σ®σ′ [σt] (t®t′ ◀≢𝟘 𝟙≉𝟘)
    where
    lemma : (r PE.≢ 𝟘) → (x : Fin _) → (r ·ᶜ γ +ᶜ δ) ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘
    lemma r≢𝟘 x rγ+δ≡𝟘 =
      case zero-product (PE.trans (PE.sym (lookup-distrib-·ᶜ γ r x))
                        (+-positiveˡ (PE.trans (PE.sym (lookup-distrib-+ᶜ (r ·ᶜ γ) δ x))
                                             rγ+δ≡𝟘))) of λ where
        (inj₁ r≡𝟘) → PE.⊥-elim (r≢𝟘 r≡𝟘)
        (inj₂ γx≡𝟘) → γx≡𝟘
    lemma′ : ∀ x → (δ ∙ (r · p) ∙ r) ⟨ x ⟩ PE.≡ 𝟘 → (δ ∙ (𝟙 · r · p) ∙ (𝟙 · r)) ⟨ x ⟩ PE.≡ 𝟘
    lemma′ x0 r≡𝟘 = PE.trans (·-identityˡ r) r≡𝟘
    lemma′ (x0 +1) rp≡𝟘 = PE.trans (·-identityˡ (r · p)) rp≡𝟘
    lemma′ (x +1 +1) δx≡𝟘 = δx≡𝟘
