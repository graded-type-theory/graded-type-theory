open import Definition.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed as T′
import Definition.Untyped as U hiding (_∷_)
open import Tools.Nullary
import Tools.PropositionalEquality as PE

module Erasure.LogicalRelation.Fundamental.Lambda
  {a k} {M : Set a} (𝕄 : Modality M)
  (open U M) (open T′ M) (open Modality 𝕄)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (is-𝟘? : (p : M) → Dec (p PE.≡ 𝟘))
  (𝟙≉𝟘 : 𝟙 PE.≢ 𝟘)
  {{eqrel : EqRelSet M}}
  where

open EqRelSet {{...}}

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Properties.Escape M
open import Definition.LogicalRelation.Fundamental M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Properties M
open import Definition.LogicalRelation.Substitution.Introductions.Pi M

import Definition.LogicalRelation.Irrelevance M as I
import Definition.LogicalRelation.Weakening M as W
import Definition.LogicalRelation.Substitution.Irrelevance M as IS

open import Definition.Modality.Context 𝕄
open import Definition.Mode 𝕄

open import Definition.Untyped.Properties M as UP
open import Definition.Typed.Weakening M hiding (wk)
open import Definition.Typed.Consequences.Reduction M

open import Erasure.Extraction 𝕄 is-𝟘?
open import Erasure.LogicalRelation 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Irrelevance 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Reduction 𝕄 ⊢Δ is-𝟘?
open import Erasure.LogicalRelation.Subsumption 𝕄 ⊢Δ is-𝟘?
open import Erasure.Target.Properties as TP
import Erasure.Target as T

open import Tools.Nat
open import Tools.Product
open import Tools.Unit
open import Tools.Reasoning.PropositionalEquality

private
  variable
     n o : Nat
     Γ : Con Term n
     F u : Term n
     G t : Term (1+ n)
     w : T.Term n
     γ : Conₘ n
     p q : M
     σ : Subst n o
     σ′ : T.Subst n o
     m : Mode


lamʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        (⊩ʳt : γ ∙ p ▸ Γ ∙ F ⊩ʳ⟨ l ⟩ t ∷[ 𝟙ᵐ ]
               G / [Γ] ∙ [F] / [G])
        ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
        (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ])
        ([t] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ G / [Γ] ∙ [F] / [G])
        ([u] : Δ ⊩⟨ l ⟩ u ∷ subst σ F / proj₁ (unwrap [F] ⊢Δ [σ]))
        (u®w : u ®⟨ l ⟩ w ∷ subst σ F ◂ p / proj₁ (unwrap [F] ⊢Δ [σ]))
      → ((subst σ (lam p t)) ∘⟨ p ⟩ u) ®⟨ l ⟩ (T.subst σ′ (T.lam (erase t))) T.∘ w
        ∷ subst (consSubst σ u) G / proj₁ (unwrap [G] ⊢Δ ([σ] , [u]))
lamʳ′ {F = F} {G = G} {γ = γ} {p = p} {t = t} {σ = σ} {σ′ = σ′}
      {u = u} {w = w} {l = l} {Γ} [Γ] [F] [G] ⊩ʳt [σ] σ®σ′ [t] [u] u®w =
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF)
                           (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σG = escape [σG]
      [σGu] = proj₁ (unwrap [G] {σ = consSubst σ u} ⊢Δ ([σ] , [u]))
      [σt] = proj₁ ([t] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σt = escapeTerm [σG] [σt]
      ⊢u = escapeTerm [σF] [u]

      t⇒t′ : Δ ⊢ lam p (subst (liftSubst σ) t) ∘⟨ p ⟩ u ⇒*
               subst (liftSubst σ) t [ u ] ∷ (subst (liftSubst σ) G [ u ])
      t⇒t′ = redMany (β-red ⊢σF ⊢σG ⊢σt ⊢u PE.refl)
      t⇒t″ = PE.subst (λ G → Δ ⊢ _ ⇒* _ ∷ G) (UP.singleSubstComp u σ G) t⇒t′
      v⇒v′ = T.trans (T.β-red {t = T.subst (T.liftSubst σ′) (erase t)} {u = w}) T.refl

      u®w′ = PE.subst (λ p → u ®⟨ l ⟩ w ∷ subst σ F ◂ p / [σF])
                      (PE.sym (·-identityˡ p)) u®w
      σut®σwv = ⊩ʳt {σ = consSubst σ u} {σ′ = T.consSubst σ′ w} ([σ] , [u]) (σ®σ′ , u®w′)
      σut®σwv′ = PE.subst₂ (λ t v → t ®⟨ l ⟩ v ∷ subst (consSubst σ u) G ◂ 𝟙 / [σGu])
                           (PE.sym (UP.singleSubstComp u σ t))
                           (PE.sym (TP.singleSubstComp w σ′ (erase t)))
                           σut®σwv
  in  redSubstTerm* [σGu] (σut®σwv′ ◀≢𝟘 𝟙≉𝟘) t⇒t″ v⇒v′

lamʳ : ∀ {l} {Γ : Con Term n} → ([Γ] : ⊩ᵛ Γ) ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ G / [Γ] ∙ [F] / [G])
       (⊩ʳt : γ ∙ ⌜ m ⌝ · p ▸ Γ ∙ F ⊩ʳ⟨ l ⟩ t ∷[ m ]
              G / [Γ] ∙ [F] / [G])
     → γ ▸ Γ ⊩ʳ⟨ l ⟩ lam p t ∷[ m ] Π p , q ▷ F ▹ G / [Γ] /
       Πᵛ {F = F} {G = G} [Γ] [F] [G]

lamʳ {F = F} {G = G} {t = t} {m = 𝟘ᵐ} {p = p} {q = q}
     [Γ] [F] [G] [t] ⊩ʳt {σ = σ} {σ′ = σ′} [σ] σ®σ′
     with is-𝟘? 𝟘
... | yes _ = _
... | no 𝟘≢𝟘 = PE.⊥-elim (𝟘≢𝟘 PE.refl)
lamʳ {F = F} {G = G} {t = t} {m = 𝟙ᵐ} {p = p} {q = q}
     [Γ] [F] [G] [t] ⊩ʳt {σ = σ} {σ′ = σ′} [σ] σ®σ′
     with is-𝟘? ⌜ 𝟙ᵐ ⌝
... | yes 𝟙≡𝟘 = _
... | no 𝟙≢𝟘 with is-𝟘? p
... | yes PE.refl = λ [a] →
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [ρσF] = W.wk id ⊢Δ [σF]
      [a]′ = I.irrelevanceTerm′ (UP.wk-id (subst σ F)) [ρσF] [σF] [a]
      [Ga] = proj₁ (unwrap [G] {σ = consSubst σ _} ⊢Δ ([σ] , [a]′))
      [a]″ = I.irrelevanceTerm′ (UP.wk-subst F) [ρσF]
                               (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [a]
      [Ga]′ = proj₁ (unwrap [G] {σ = consSubst _ _} ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [a]″))
      [Ga]″ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (subst (sgSubst _)) (UP.wk-subst-lift G))
                                               (UP.singleSubstComp _ _ G)))
                             [Ga]′
      ⊩ʳt′ = PE.subst (λ x → _ ∙ x ▸ _ ∙ F ⊩ʳ⟨ _ ⟩ t ∷[ 𝟙ᵐ ] G / [Γ] ∙ [F] / [G])
                      (·-identityˡ 𝟘) (subsumption′ {t = t} ([Γ] ∙ [F]) [G] ⊩ʳt)
      λta®λv↯ = lamʳ′ {t = t} {w = T.↯} [Γ] [F] [G] ⊩ʳt′
                      [σ] σ®σ′ [t] [a]′ t®v◂𝟘
  in  irrelevanceTerm′ (PE.sym (PE.trans (PE.cong (subst (sgSubst _))
                                                  (UP.wk-lift-id (subst (liftSubst σ) G)))
                                         (UP.singleSubstComp _ σ G)))
                       [Ga] [Ga]″ λta®λv↯
... | no p≢𝟘 = λ [a] {w} a®w →
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [ρσF] = W.wk id ⊢Δ [σF]
      [a]′ = I.irrelevanceTerm′ (UP.wk-id (subst σ F)) [ρσF] [σF] [a]
      a®w′ = irrelevanceTerm′ (UP.wk-id (subst σ F)) [ρσF] [σF] a®w
      [Ga] = proj₁ (unwrap [G] {σ = consSubst σ _} ⊢Δ ([σ] , [a]′))
      [a]″ = I.irrelevanceTerm′ (UP.wk-subst F) [ρσF]
                               (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [a]
      [Ga]′ = proj₁ (unwrap [G] {σ = consSubst _ _} ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [a]″))
      [Ga]″ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (subst (sgSubst _)) (UP.wk-subst-lift G))
                                               (UP.singleSubstComp _ _ G)))
                             [Ga]′
      ⊩ʳt′ = PE.subst (λ x → _ ∙ x ▸ _ ∙ F ⊩ʳ⟨ _ ⟩ t ∷[ 𝟙ᵐ ] G / [Γ] ∙ [F] / [G])
                      (·-identityˡ p) (subsumption′ {t = t} ([Γ] ∙ [F]) [G] ⊩ʳt)
      λta®λvw = lamʳ′ {t = t} {w = w} [Γ] [F] [G] ⊩ʳt′
                      [σ] σ®σ′ [t] [a]′ (a®w′ ◀ p)
  in  irrelevanceTerm′ (PE.sym (PE.trans (PE.cong (subst (sgSubst _))
                                                  (UP.wk-lift-id (subst (liftSubst σ) G)))
                                         (UP.singleSubstComp _ σ G)))
                       [Ga] [Ga]″ λta®λvw
