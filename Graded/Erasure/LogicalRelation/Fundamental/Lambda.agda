------------------------------------------------------------------------
-- Graded.Erasure validity of lambda abstractions.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Tools.Relation

module Graded.Erasure.LogicalRelation.Fundamental.Lambda
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (non-trivial : ¬ Trivial)
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R

import Definition.LogicalRelation.Irrelevance R as I
import Definition.LogicalRelation.Weakening R as W
import Definition.LogicalRelation.Substitution.Irrelevance R as IS

open import Graded.Context 𝕄
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M as UP
open import Definition.Typed R
open import Definition.Typed.Weakening R hiding (wk)
open import Definition.Typed.Consequences.Reduction R

open import Graded.Erasure.Extraction 𝕄
import Graded.Erasure.Extraction.Properties 𝕄 as EP
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Irrelevance as
open import Graded.Erasure.LogicalRelation.Reduction as
open import Graded.Erasure.LogicalRelation.Subsumption as
open import Graded.Erasure.LogicalRelation.Value as
open import Graded.Erasure.Target.Non-terminating
open import Graded.Erasure.Target.Properties as TP
open import Graded.Erasure.Target as T using (strict; non-strict)
open import Graded.Erasure.Target.Reasoning

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

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
        (σ®σ′ : σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ])
        ([t] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ G / [Γ] ∙ [F] / [G])
        ([u] : Δ ⊩⟨ l ⟩ u ∷ F [ σ ] / proj₁ (unwrap [F] ⊢Δ [σ]))
        (u®w : u ®⟨ l ⟩ w ∷ F [ σ ] ◂ p / proj₁ (unwrap [F] ⊢Δ [σ]))
      → (p PE.≡ 𝟘 → w PE.≡ loop? str)
      → Π-allowed p q
      → (lam p t [ σ ]) ∘⟨ p ⟩ u ®⟨ l ⟩
        (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ w
           ∷ G [ consSubst σ u ] / proj₁ (unwrap [G] ⊢Δ ([σ] , [u]))
lamʳ′ {F = F} {G = G} {γ = γ} {p = p} {t = t} {σ = σ} {σ′ = σ′}
      {u = u} {w = w} {l = l} {Γ}
      [Γ] [F] [G] ⊩ʳt [σ] σ®σ′ [t] [u] u®w ≡𝟘→≡↯ ok =
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF)
                           (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σG = escape [σG]
      [σGu] = proj₁ (unwrap [G] {σ = consSubst σ u} ⊢Δ ([σ] , [u]))
      [σt] = proj₁ ([t] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σt = escapeTerm [σG] [σt]
      ⊢u = escapeTerm [σF] [u]

      t⇒t′ : Δ ⊢ (lam p t [ σ ]) ∘⟨ p ⟩ u ⇒*
               t [ liftSubst σ ] [ u ]₀ ∷ G [ liftSubst σ ] [ u ]₀
      t⇒t′ = redMany (β-red ⊢σF ⊢σG ⊢σt ⊢u PE.refl ok)
      t⇒t″ = PE.subst (λ G → Δ ⊢ _ ⇒* _ ∷ G) (UP.singleSubstComp u σ G) t⇒t′

      v⇒* :
        ∃ λ w′ → T.Value⟨ str ⟩ w′ × w T.⇒* w′ ×
        T.lam (erase str t T.[ T.liftSubst σ′ ]) T.∘⟨ str ⟩ w T.⇒*
        erase str t T.[ T.liftSubst σ′ ] T.[ w′ ]₀
      v⇒* = case PE.singleton str of λ where
        (T.non-strict , PE.refl) →
          _ , _ , T.refl ,
          (T.lam (erase T.non-strict t T.[ T.liftSubst σ′ ])
             T.∘⟨ T.non-strict ⟩ w                             ⇒⟨ T.β-red _ ⟩

           erase T.non-strict t T.[ T.liftSubst σ′ ] T.[ w ]₀  ∎⇒)
        (T.strict , PE.refl) → case is-𝟘? p of λ where
          (yes p≡𝟘) →
            case PE.subst T.Value (PE.sym $ ≡𝟘→≡↯ p≡𝟘) T.↯ of λ
              val →
            _ , val , T.refl ,
            (T.lam (erase T.strict t T.[ T.liftSubst σ′ ])
               T.∘⟨ T.strict ⟩ w                             ⇒⟨ T.β-red val ⟩
             erase T.strict t T.[ T.liftSubst σ′ ] T.[ w ]₀  ∎⇒)
          (no p≢𝟘) →
            case reduces-to-value PE.refl [σF] (u®w ◀≢𝟘 p≢𝟘) of λ
              (w′ , val , w⇒*w′) →
              _ , val , w⇒*w′
            , (T.lam (erase T.strict t T.[ T.liftSubst σ′ ])
                 T.∘⟨ T.strict ⟩ w                              ⇒*⟨ app-subst*-arg T.lam w⇒*w′ ⟩

               T.lam (erase T.strict t T.[ T.liftSubst σ′ ])
                 T.∘⟨ T.strict ⟩ w′                             ⇒⟨ T.β-red val ⟩

               erase T.strict t T.[ T.liftSubst σ′ ] T.[ w′ ]₀  ∎⇒)
  in
  case v⇒* of λ
    (_ , w′-value , w⇒*w′ , v⇒*) →
  redSubstTerm* [σGu]
    (PE.subst₂ (λ t v → t ®⟨ _ ⟩ v ∷ _ / [σGu])
       (PE.sym (UP.singleSubstComp _ _ t))
       (PE.sym (TP.singleSubstComp _ _ (erase _ t))) $
      ⊩ʳt ([σ] , [u])
        ( σ®σ′
        , PE.subst (λ p → _ ®⟨ _ ⟩ _ ∷ _ ◂ p / _)
            (PE.sym $ ·-identityˡ p)
            (redSubstTerm*′-◂ u®w (id ⊢u) w⇒*w′)
        )
       ◀≢𝟘 non-trivial)
    t⇒t″ v⇒*

lamʳ : ∀ {l} {Γ : Con Term n} → ([Γ] : ⊩ᵛ Γ) ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ G / [Γ] ∙ [F] / [G])
       (⊩ʳt : γ ∙ ⌜ m ⌝ · p ▸ Γ ∙ F ⊩ʳ⟨ l ⟩ t ∷[ m ]
              G / [Γ] ∙ [F] / [G])
       (ok : Π-allowed p q)
     → γ ▸ Γ ⊩ʳ⟨ l ⟩ lam p t ∷[ m ] Π p , q ▷ F ▹ G / [Γ] /
       Πᵛ [Γ] [F] [G] ok

lamʳ {F = F} {G = G} {t = t} {m = 𝟘ᵐ} {p = p} {q = q}
     [Γ] [F] [G] [t] ⊩ʳt _ {σ = σ} {σ′ = σ′} [σ] σ®σ′
     with is-𝟘? 𝟘
... | yes _ = _
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
lamʳ {F = F} {G = G} {t = t} {m = 𝟙ᵐ} {p = p} {q = q}
     [Γ] [F] [G] [t] ⊩ʳt ok {σ = σ} {σ′ = σ′} [σ] σ®σ′
     with is-𝟘? ⌜ 𝟙ᵐ ⌝
... | yes 𝟙≡𝟘 = _
... | no 𝟙≢𝟘 with is-𝟘? p
... | yes PE.refl = (λ { PE.refl → _ , T.refl }) , λ [a] →
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [ρσF] = W.wk id ⊢Δ [σF]
      [a]′ = I.irrelevanceTerm′ (UP.wk-id (F [ σ ])) [ρσF] [σF] [a]
      [Ga] = proj₁ (unwrap [G] {σ = consSubst σ _} ⊢Δ ([σ] , [a]′))
      [a]″ = I.irrelevanceTerm′ (UP.wk-subst F) [ρσF]
                               (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [a]
      [Ga]′ = proj₁ (unwrap [G] {σ = consSubst _ _} ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [a]″))
      [Ga]″ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (_[ _ ]₀) (UP.wk-subst-lift G))
                                               (UP.singleSubstComp _ _ G)))
                             [Ga]′
      ⊩ʳt′ = PE.subst (λ x → _ ∙ x ▸ _ ∙ F ⊩ʳ⟨ _ ⟩ t ∷[ 𝟙ᵐ ] G / [Γ] ∙ [F] / [G])
                      (·-identityˡ 𝟘) (subsumption′ {t = t} ([Γ] ∙ [F]) [G] ⊩ʳt)
      λta®λv↯ = lamʳ′ {t = t} [Γ] [F] [G] ⊩ʳt′
                      [σ] σ®σ′ [t] [a]′ t®v◂𝟘 (λ _ → PE.refl) ok
  in  irrelevanceTerm′ (PE.sym (PE.trans (PE.cong (_[ _ ]₀)
                                                  (UP.wk-lift-id (G [ liftSubst σ ])))
                                         (UP.singleSubstComp _ σ G)))
                       [Ga] [Ga]″ $
      case PE.singleton str of λ where
        (strict , PE.refl) →
          targetRedSubstTerm* [Ga] λta®λv↯
            ((erase strict (lam 𝟘 t) T.[ σ′ ]) T.∘⟨ strict ⟩ T.↯  ≡⟨ PE.cong (λ t → (t T.[ σ′ ]) T.∘⟨ strict ⟩ T.↯) $
                                                                     EP.lam-𝟘-keep t ⟩⇒
             (T.lam (erase strict t) T.[ σ′ ]) T.∘⟨ strict ⟩ T.↯  ∎⇒)
        (non-strict , PE.refl) →
          targetRedSubstTerm*′ [Ga] λta®λv↯
            ((T.lam (erase non-strict t) T.[ σ′ ]) T.∘⟨ non-strict ⟩
             loop non-strict                                          ⇒⟨ T.β-red _ ⟩

             erase non-strict t T.[ T.liftSubst σ′ ]
               T.[ loop non-strict ]₀                                 ≡˘⟨ PE.cong (erase _ t T.[ T.liftSubst _ ] T.[_]₀) loop-[] ⟩⇒

             erase non-strict t T.[ T.liftSubst σ′ ]
               T.[ loop non-strict T.[ σ′ ] ]₀                        ≡˘⟨ TP.singleSubstLift (erase _ t) _ ⟩⇒

             erase non-strict t T.[ loop non-strict ]₀ T.[ σ′ ]       ≡˘⟨ PE.cong T._[ _ ] EP.lam-𝟘-remove ⟩⇒

             erase non-strict (lam 𝟘 t) T.[ σ′ ]                      ∎⇒)
... | no p≢𝟘 = (λ { PE.refl → _ , T.refl }) , λ [a] {w} a®w →
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [ρσF] = W.wk id ⊢Δ [σF]
      [a]′ = I.irrelevanceTerm′ (UP.wk-id (F [ σ ])) [ρσF] [σF] [a]
      a®w′ = irrelevanceTerm′ (UP.wk-id (F [ σ ])) [ρσF] [σF] a®w
      [Ga] = proj₁ (unwrap [G] {σ = consSubst σ _} ⊢Δ ([σ] , [a]′))
      [a]″ = I.irrelevanceTerm′ (UP.wk-subst F) [ρσF]
                               (proj₁ (unwrap [F] ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ]))) [a]
      [Ga]′ = proj₁ (unwrap [G] {σ = consSubst _ _} ⊢Δ (wkSubstS [Γ] ⊢Δ ⊢Δ id [σ] , [a]″))
      [Ga]″ = I.irrelevance′ (PE.sym (PE.trans (PE.cong (_[ _ ]₀) (UP.wk-subst-lift G))
                                               (UP.singleSubstComp _ _ G)))
                             [Ga]′
      ⊩ʳt′ = PE.subst (λ x → _ ∙ x ▸ _ ∙ F ⊩ʳ⟨ _ ⟩ t ∷[ 𝟙ᵐ ] G / [Γ] ∙ [F] / [G])
                      (·-identityˡ p) (subsumption′ {t = t} ([Γ] ∙ [F]) [G] ⊩ʳt)
      λta®λvw = lamʳ′ {t = t} {w = w} [Γ] [F] [G] ⊩ʳt′
                      [σ] σ®σ′ [t] [a]′ (a®w′ ◀ p) (⊥-elim ∘→ p≢𝟘) ok
  in  irrelevanceTerm′ (PE.sym (PE.trans (PE.cong (_[ _ ]₀)
                                                  (UP.wk-lift-id (G [ liftSubst σ ])))
                                         (UP.singleSubstComp _ σ G)))
                       [Ga] [Ga]″ $
      targetRedSubstTerm* [Ga] λta®λvw
        ((erase str (lam p t) T.[ σ′ ]) T.∘⟨ str ⟩ w  ≡⟨ PE.cong (λ t → (t T.[ _ ]) T.∘⟨ _ ⟩ _) $
                                                         EP.lam-≢𝟘 (str T.== _) p≢𝟘 ⟩⇒
         (T.lam (erase str t) T.[ σ′ ]) T.∘⟨ str ⟩ w  ∎⇒)
