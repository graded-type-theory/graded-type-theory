{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Fundamental.Lambda
  (restrictions : Restrictions Erasure′)
  {{eqrel : EqRelSet Erasure′}}
  where

open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Properties.Escape Erasure′
open import Definition.LogicalRelation.Fundamental Erasure′
open import Definition.LogicalRelation.Substitution Erasure′
open import Definition.LogicalRelation.Substitution.Properties Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Pi Erasure′
open import Definition.LogicalRelation.Substitution.Introductions.Universe Erasure′

import Definition.LogicalRelation.Irrelevance Erasure′ as I
import Definition.LogicalRelation.Weakening Erasure′ as W
import Definition.LogicalRelation.Substitution.Irrelevance Erasure′ as IS

open import Definition.Modality.Instances.Erasure.Modality restrictions
open import Definition.Modality.Context ErasureModality
open import Definition.Mode ErasureModality

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure as UP
open import Definition.Typed Erasure′
open import Definition.Typed.Weakening Erasure′
open import Definition.Typed.Consequences.Reduction Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′

open import Erasure.Extraction
open import Erasure.LogicalRelation restrictions
open import Erasure.LogicalRelation.Irrelevance restrictions
open import Erasure.LogicalRelation.Reduction restrictions
open import Erasure.LogicalRelation.Subsumption restrictions
open import Erasure.Target.Properties as TP
import Erasure.Target as T

open import Tools.Nat
open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE

private
  variable
     n : Nat
     Γ : Con Term n
     F u : Term n
     G t : Term (1+ n)
     w : T.Term n
     γ : Conₘ n
     p q : Erasure
     σ : Subst 0 n
     σ′ : T.Subst 0 n
     m : Mode

Πʳ : ([Γ] : ⊩ᵛ Γ) → Γ ⊢ Π p , q ▷ F ▹ G ∷ U
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Π p , q ▷ F ▹ G ∷[ m ] U / [Γ] / [U]
Πʳ {F = F} {G = G} [Γ] ⊢Π =
    [U]
  , subsumptionMode (Π _ , _ ▷ F ▹ G) [U]
      (λ [σ] _ → Uᵣ (substitutionTerm ⊢Π (wellformedSubst [Γ] ε [σ]) ε))
  where
  [U] = Uᵛ [Γ]

lamʳ′ : ∀ {l} {Γ : Con Term n}
      → ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        (⊩ʳt : γ ∙ ⌜ m ⌝ · p ▸ Γ ∙ F ⊩ʳ⟨ l ⟩ t ∷[ m ]
               G / [Γ] ∙ [F] / [G])
        ([σ] : ε ⊩ˢ σ ∷ Γ / [Γ] / ε)
        (σ®σ′ : σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ])
        ([t] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ G / [Γ] ∙ [F] / [G])
        ([u] : ε ⊩⟨ l ⟩ u ∷ subst σ F / proj₁ (unwrap [F] ε [σ]))
        (u®w : u ®⟨ l ⟩ w ∷ subst σ F ◂ ⌜ m ⌝ · p /
               proj₁ (unwrap [F] ε [σ]))
      → ((subst σ (lam p t)) ∘⟨ p ⟩ u) ®⟨ l ⟩ (T.subst σ′ (T.lam (erase t))) T.∘ w
        ∷ subst (consSubst σ u) G ◂ ⌜ m ⌝
        / proj₁ (unwrap [G] ε ([σ] , [u]))
lamʳ′ {m = 𝟘ᵐ} = _

lamʳ′ {F = F} {G = G} {γ = γ} {m = 𝟙ᵐ} {p = p} {t = t} {σ = σ} {σ′ = σ′}
      {u = u} {w = w} {l = l} {Γ} [Γ] [F] [G] ⊩ʳt [σ] σ®σ′ [t] [u] u®w =
  let [σ∙u] = [σ] , [u]
      [G]′ = proj₁ (unwrap [G] ε [σ∙u])
      [σF] = proj₁ (unwrap [F] ε [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ (unwrap [G] (ε ∙ ⊢σF) (liftSubstS {F = F} [Γ] ε [F] [σ]))
      ⊢σG = escape [σG]
      [σt] = proj₁ ([t] (ε ∙ ⊢σF) (liftSubstS {F = F} [Γ] ε [F] [σ]))
      ⊢σt = escapeTerm [σG] [σt]
      ⊢u = escapeTerm [σF] [u]
      σ∙u®σ′∙w : consSubst σ u ®⟨ l ⟩ T.consSubst σ′ w ∷[ 𝟙ᵐ ] Γ ∙ F ◂
                 γ ∙ p / [Γ] ∙ [F] / [σ∙u]
      σ∙u®σ′∙w = σ®σ′ , u®w
      σut®σwv = ⊩ʳt {σ = consSubst σ u} {σ′ = T.consSubst σ′ w} [σ∙u] σ∙u®σ′∙w
      σut®σwv′ = PE.subst₂ (λ t v → t ®⟨ l ⟩ v ∷ subst (consSubst σ u) G / [G]′)
                           (PE.sym (UP.singleSubstComp u σ t))
                           (PE.sym (TP.singleSubstComp w σ′ (erase t)))
                           σut®σwv
      t⇒t′ : ε ⊢ lam p (subst (liftSubst σ) t) ∘⟨ p ⟩ u ⇒*
               subst (liftSubst σ) t [ u ] ∷ (subst (liftSubst σ) G [ u ])
      t⇒t′ = redMany (β-red ⊢σF ⊢σG ⊢σt ⊢u PE.refl)
      t⇒t″ = PE.subst (λ G → ε ⊢ _ ⇒* _ ∷ G) (UP.singleSubstComp u σ G) t⇒t′
      v⇒v′ = T.trans (T.β-red {t = T.subst (T.liftSubst σ′) (erase t)} {u = w}) T.refl
      in  redSubstTerm* [G]′ σut®σwv′ t⇒t″ v⇒v′

lamʳ : ∀ {Γ : Con Term n} → ([Γ] : ⊩ᵛ Γ) ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ t ∷ G / [Γ] ∙ [F] / [G])
       (⊩ʳt : γ ∙ ⌜ m ⌝ · p ▸ Γ ∙ F ⊩ʳ⟨ ¹ ⟩ t ∷[ m ]
              G / [Γ] ∙ [F] / [G])
     → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ lam p t ∷[ m ] Π p , q ▷ F ▹ G / [Γ] /
       Πᵛ {F = F} {G = G} [Γ] [F] [G]
lamʳ {m = 𝟘ᵐ} = _

lamʳ {F = F} {G = G} {t = t} {m = 𝟙ᵐ} {p = ω} {q = q}
     [Γ] [F] [G] [t] ⊩ʳt {σ = σ} {σ′ = σ′} [σ] σ®σ′ {a = a} {w = w} [a] a®w =
     let [Π] = Πᵛ {F = F} {G = G} {p = ω} {q = q} [Γ] [F] [G]
         [σF] = proj₁ (unwrap [F] ε [σ])
         [ρσF] = W.wk id ε [σF]
         ⊢σF = escape [σF]
         [ε] , [σF]′ = fundamental ⊢σF
         [σF]″ = IS.irrelevance {A = subst σ F} [ε] ε [σF]′
         ⊢ρσF = escape [ρσF]
         [ε]′ , [ρσF]′ = fundamental ⊢ρσF
         [ρσF]″ = IS.irrelevance {A = U.wk id (subst σ F)} [ε]′ ε [ρσF]′
         [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (ε ∙ ⊢σF)
                           (liftSubstS {σ = σ} {F = F} [Γ] ε [F] [σ]))
         [ρσG] = W.wk (lift id) (ε ∙ ⊢ρσF) [σG]
         ⊢ρσG = escape [ρσG]
         [ε∙F] , [ρσG]′ = fundamental ⊢ρσG
         [ρσG]″ = IS.irrelevance {A = U.wk (lift id) (subst (liftSubst σ) G)}
                                 [ε∙F] (ε ∙ [ρσF]″) [ρσG]′
         a®w′ = irrelevanceTerm′   (UP.wk-id (subst σ F)) [ρσF] [σF] a®w
         [a]′ = I.irrelevanceTerm′ (UP.wk-id (subst σ F)) [ρσF] [σF] [a]
         [a]″ = I.irrelevanceTerm′ (UP.wk-subst F) [ρσF]
                                   (proj₁ (unwrap [F] ε (wkSubstS [Γ] ε ε id [σ]))) [a]
         λtu®λvw = lamʳ′ {F = F} {G = G} {t = t} {u = a} {w = w}
                         [Γ] [F] [G] ⊩ʳt [σ] σ®σ′ [t] [a]′ a®w′
         eq : U.wk (lift id) (subst (liftSubst σ) G) [ a ] PE.≡ subst (consSubst σ a) G
         eq = PE.trans (PE.cong (_[ a ]) (UP.wk-lift-id ((subst (liftSubst σ) G))))
                       (UP.singleSubstComp a σ G)
         [σaG] : ε ⊩⟨ ¹ ⟩ subst (consSubst σ a) G
         [σaG] = proj₁ (unwrap [G] ε ([σ] , [a]′))
         [ρσG[a]] : ε ⊩⟨ ¹ ⟩ U.wk (lift id) (subst (liftSubst σ) G) [ a ]
         [ρσG[a]] = I.irrelevance′ (PE.sym (UP.singleSubstWkComp a σ G))
                                   (proj₁ (unwrap [G] ε ((wkSubstS [Γ] ε ε id [σ]) , [a]″)))
     in  irrelevanceTerm′ (PE.sym eq) [σaG] [ρσG[a]] λtu®λvw

lamʳ {F = F} {G = G} {t = t} {m = 𝟙ᵐ} {p = 𝟘} {q = q}
     [Γ] [F] [G] [t] ⊩ʳt {σ = σ} {σ′ = σ′} [σ] σ®σ′ {a = a} [a] =
     let [Π] = Πᵛ {F = F} {G = G} {p = 𝟘} {q = q} [Γ] [F] [G]
         [σF] = proj₁ (unwrap [F] ε [σ])
         [ρσF] = W.wk id ε [σF]
         [a]′ = I.irrelevanceTerm′ (UP.wk-id (subst σ F)) [ρσF] [σF] [a]
         [a]″ = I.irrelevanceTerm′ (UP.wk-subst F) [ρσF]
                                   (proj₁ (unwrap [F] ε (wkSubstS [Γ] ε ε id [σ]))) [a]
         [σaG] = proj₁ (unwrap [G] ε ([σ] , [a]′))
         [ρσG[a]] = I.irrelevance′ (PE.sym (UP.singleSubstWkComp a σ G))
                                   (proj₁ (unwrap [G] ε ((wkSubstS [Γ] ε ε id [σ]) , [a]″)))
         eq = PE.trans (PE.cong (_[ a ]) (UP.wk-lift-id ((subst (liftSubst σ) G))))
                       (UP.singleSubstComp a σ G)
         λtu®λvw = lamʳ′ {F = F} {G = G} {p = 𝟘} {t = t} {u = a} {w = T.undefined}
                         [Γ] [F] [G] ⊩ʳt [σ] σ®σ′ [t] [a]′ tt
     in  irrelevanceTerm′ (PE.sym eq) [σaG] [ρσG[a]] λtu®λvw
