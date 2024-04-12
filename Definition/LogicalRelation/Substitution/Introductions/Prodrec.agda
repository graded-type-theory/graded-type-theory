------------------------------------------------------------------------
-- Validity of prodrec.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Prodrec
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U hiding (wk)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Weakening R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
import Definition.LogicalRelation.Substitution.Irrelevance R as S
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Reflexivity R
import Definition.LogicalRelation.Weakening R as W

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n      : Nat
    Γ Δ      : Con Term n
    p p′ q q′ r : M

prodrec-subst* :
  ∀ {l t t′ u A F G σ} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σʷ p , q ▷ F ▹ G / [Γ])
  ([A] : Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G])
  ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊])
  (⊢Δ : ⊢ Δ)
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  ([t′] : Δ ⊩⟨ l ⟩ t′ ∷ Σʷ p , q ▷ F ▹ G [ σ ] /
            proj₁ (unwrap [Σ] ⊢Δ [σ])) →
  Δ ⊢ t ⇒* t′ ∷ Σʷ p , q ▷ F ▹ G [ σ ] →
  Δ ⊢ prodrec r p q′ (A [ liftSubst σ ]) t
        (u [ liftSubstn σ 2 ]) ⇒*
    prodrec r p q′ (A [ liftSubst σ ]) t′
      (u [ liftSubstn σ 2 ]) ∷
    A [ liftSubst σ ] [ t ]₀
prodrec-subst* {q = q} {l = l} {t} {.t} {u} {A} {F} {G} {σ}
               [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [t′] (id x) =
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [⇑σ]′ = liftSubstS {F = Σ _ , q ▷ F ▹ G} [Γ] ⊢Δ [Σ] [σ]
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ (unwrap [A] (⊢Δ ∙ ⊢σΣ) [⇑σ]′)
      ⊢σA = escape [σA]
      [⇑²σ] = liftSubstS {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (subst-β-prodrec A σ) ⊢σu
  in  id (prodrecⱼ ⊢σF ⊢σG ⊢σA x ⊢σu′ (⊩ᵛΠΣ→ΠΣ-allowed [Σ]))
prodrec-subst* {q = q} {Δ = Δ} {l = l} {t} {t′} {u} {A} {F} {G} {σ}
               [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [t′] (x ⇨ t⇒t′) =
  let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [⇑σ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [⇑σ]′ = liftSubstS {F = Σ _ , q ▷ F ▹ G} [Γ] ⊢Δ [Σ] [σ]
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) [⇑σ]′)
      ⊢σA = escape [σA]
      [⇑²σ] = liftSubstS {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu] = proj₁ ([u] (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ _ ∷ x) (subst-β-prodrec A σ) ⊢σu
      q , w = redSubst*Term t⇒t′ [σΣ] [t′]
      a , s = redSubstTerm x [σΣ] q
      A[t′]≡A[t]′ = ≅-eq (escapeEq (proj₁ (unwrap [A] {σ = consSubst σ _} ⊢Δ ([σ] , q)))
                                   (proj₂ (unwrap [A] {σ = consSubst σ _} ⊢Δ ([σ] , q))
                                          {σ′ = consSubst σ _} ([σ] , a)
                                          (reflSubst [Γ] ⊢Δ [σ] , symEqTerm [σΣ] s)))
      A[t′]≡A[t] = PE.subst₂ (Δ ⊢_≡_) (PE.sym (singleSubstComp _ σ A))
                             (PE.sym (singleSubstComp _ σ A)) A[t′]≡A[t]′
  in  prodrec-subst ⊢σF ⊢σG ⊢σA ⊢σu′ x (⊩ᵛΠΣ→ΠΣ-allowed [Σ]) ⇨
        conv* (prodrec-subst* {u = u} {A} {F} {G} {σ}
                 [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [t′] t⇒t′)
              A[t′]≡A[t]

prodrecTerm :
  ∀ {F G A t u σ l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σʷ-allowed p q) →
  let [Σ] = Σᵛ [Γ] [F] [G] ok in
  ([A] : Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G])
  ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊])
  (⊢Δ : ⊢ Δ)
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  ([σt] : Δ ⊩⟨ l ⟩ t ∷ Σʷ p , q ▷ F ▹ G [ σ ] /
            proj₁ (unwrap [Σ] ⊢Δ [σ])) →
  ∃ λ [A[t]] →
  Δ ⊩⟨ l ⟩ prodrec r p q′ (A [ liftSubst σ ]) t
             (u [ liftSubstn σ 2 ]) ∷
    A [ liftSubst σ ] [ t ]₀ / [A[t]]
prodrecTerm
  {Γ = Γ} {p = p′} {q = q} {Δ = Δ} {r = r}
  {F = F} {G} {A} {t} {u} {σ} {l}
  [Γ] [F] [G] ok [A] [A₊] [u] ⊢Δ [σ]
  [σt]@(Σₜ p t⇒p p≅p (prodₙ {p = p″} {t = p₁} {u = p₂})
          (PE.refl , [p₁] , [p₂] , PE.refl)) =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} {m = 𝕨} [Γ] [F] [G] _
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σG = escape [σG]
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G]
                          (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ)
                      (liftSubstS {σ = σ} {F = Σʷ _ , q ▷ F ▹ G}
                         [Γ] ⊢Δ [Σ] [σ]))
      ⊢σA = escape [σA]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])
      ⊢σA₊ = escape [σA₊]
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ u [ liftSubstn σ 2 ] ∷ x) (subst-β-prodrec A σ) ⊢σu
      [σF]′ = W.wk id (wf ⊢σF) [σF]
      ⊢p = ⊢u-redₜ t⇒p
      [p₁]′ = irrelevanceTerm′ (wk-id (F [ σ ])) [σF]′ [σF] [p₁]
      ⊢p₁ = escapeTerm [σF] [p₁]′
      [G[p₁]]′ = proj₁ (unwrap [G] {σ = consSubst σ _} ⊢Δ ([σ] , [p₁]′))
      [G[p₁]] = irrelevance′ (PE.sym (singleSubstComp _ σ G)) [G[p₁]]′
      [G[p₁]]″ = irrelevance′ (PE.sym (PE.trans (PE.cong (_[ p₁ ]₀)
                                                         (PE.trans (wk-subst G) (subst-lift-•ₛ G)))
                                                (PE.trans (substCompEq G) (substVar-to-subst substVarSingletonComp G))))
                              (proj₁ (unwrap [G] (wf ⊢σF) ((wkSubstS [Γ] ⊢Δ (wf ⊢σF) id [σ])
                                          , (irrelevanceTerm′ (wk-subst F) [σF]′
                                                              (proj₁ (unwrap [F] (wf ⊢σF) (wkSubstS [Γ] ⊢Δ (wf ⊢σF) id [σ]))) [p₁]))))
      [p₂]′ = irrelevanceTerm′ (PE.trans (PE.cong (_[ p₁ ]₀) (wk-lift-id (G [ liftSubst σ ])))
                                        (singleSubstComp p₁ σ G)) [G[p₁]]″ [G[p₁]]′ [p₂]
      ⊢p₂ = escapeTerm [G[p₁]]′ [p₂]′
      ⊢p₂′ = PE.subst (λ x → Δ ⊢ p₂ ∷ x) (PE.sym (singleSubstComp p₁ σ G)) ⊢p₂
      [σA₊′] = proj₁ (unwrap [A₊] {σ = consSubst (consSubst σ p₁) p₂} ⊢Δ (([σ] , [p₁]′) , [p₂]′))
      [σA₊′]′ = irrelevance′ (PE.sym (substCompProdrec A p₁ p₂ σ)) [σA₊′]
      [u₊] = proj₁ ([u] {σ = consSubst (consSubst σ p₁) p₂} ⊢Δ (([σ] , [p₁]′) , [p₂]′))
      [u₊]′ = irrelevanceTerm″ (PE.sym (substCompProdrec A p₁ p₂ σ))
                               (PE.sym (doubleSubstComp u p₁ p₂ σ)) [σA₊′] [σA₊′]′ [u₊]
      [σA[t]] = proj₁ (unwrap [A] {σ = consSubst _ _} ⊢Δ ([σ] , [σt]))
      [σA[t]]′ = irrelevance′ (PE.sym (singleSubstComp t σ A)) [σA[t]]
      ⊢u₊ = escapeTerm [σA₊′] [u₊]
      ⊢u₊′ = PE.subst₂ (Δ ⊢_∷_) (PE.sym (doubleSubstComp u p₁ p₂ σ))
                       (PE.sym (substCompProdrec A p₁ p₂ σ)) ⊢u₊
      [p] : Δ ⊩⟨ l ⟩ prodʷ _ p₁ p₂ ∷ Σʷ _ , q ▷ F ▹ G [ σ ] / [σΣ]
      [p] = Σₜ p (idRedTerm:*: ⊢p) p≅p prodₙ
              (PE.refl , [p₁] , [p₂] , PE.refl)
      [t≡p] = proj₂ (redSubst*Term (redₜ t⇒p) [σΣ] [p])
      A[t]≡A[p] = proj₂ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] , [σt]))
                             {σ′ = consSubst σ (prodʷ _ p₁ p₂)}
                             ([σ] , [p]) (reflSubst [Γ] ⊢Δ [σ] , [t≡p])
      A[t]≡A[p]′ = irrelevanceEq″
        (PE.sym (singleSubstComp t σ A))
        (PE.sym (singleSubstComp (prodʷ _ p₁ p₂) σ A))
        [σA[t]] [σA[t]]′ A[t]≡A[p]
      ⊢A[t]≡A[p] = ≅-eq (escapeEq [σA[t]] A[t]≡A[p])
      ⊢A[p]≡A[t] = PE.subst₂
        (Δ ⊢_≡_) (PE.sym (singleSubstComp (prodʷ _ p₁ p₂) σ A))
        (PE.sym (singleSubstComp t σ A)) (sym ⊢A[t]≡A[p])
      [u₊]″ = convTerm₂ [σA[t]]′ [σA₊′]′ A[t]≡A[p]′ [u₊]′
      reduction₁ = prodrec-subst* {r = r} {u = u} {A} {F} {G} {σ}
                     [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [p] (redₜ t⇒p)
      reduction₂ : _ ⊢ _ ⇒* _ ∷ _
      reduction₂ =
        prodrec-β {r = r} ⊢σF ⊢σG ⊢σA ⊢p₁ ⊢p₂′ ⊢σu′ PE.refl ok ⇨
        id ⊢u₊′
      reduction = reduction₁ ⇨∷* conv* reduction₂ ⊢A[p]≡A[t]
  in  [σA[t]]′ , proj₁ (redSubst*Term reduction [σA[t]]′ [u₊]″)
prodrecTerm
  {Γ = Γ} {q = q} {Δ = Δ} {r = r} {F = F} {G} {A} {t} {u} {σ} {l}
  [Γ] [F] [G] ok [A] [A₊] [u] ⊢Δ [σ]
  [σt]@(Σₜ p t⇒p p≅p (ne x) p~p) =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} {m = 𝕨} [Γ] [F] [G] _
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σG = escape [σG]
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G]
                         (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ])
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ)
                        (liftSubstS {σ = σ} {F = Σʷ _ , q ▷ F ▹ G}
                           [Γ] ⊢Δ [Σ] [σ]))
      ⊢σA = escape [σA]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])
      ⊢σA₊ = escape [σA₊]
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ u [ liftSubstn σ 2 ] ∷ x) (subst-β-prodrec A σ) ⊢σu
      ⊢p = ⊢u-redₜ t⇒p
      [p] : Δ ⊩⟨ l ⟩ p ∷ Σʷ _ , q ▷ F ▹ G [ σ ] / [σΣ]
      [p] = Σₜ p (idRedTerm:*: ⊢p) p≅p (ne x) p~p
      [σA[p]] = irrelevance′ (PE.sym (singleSubstComp p σ A)) (proj₁ (unwrap [A] {σ = consSubst σ p} ⊢Δ ([σ] , [p])))
      [σA[t]]′ = proj₁ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] , [σt]))
      [σA[t]] = irrelevance′ (PE.sym (singleSubstComp t σ A)) [σA[t]]′
      ⊢u≡u = escapeTermEq (proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑]))
                          (reflEqTerm (proj₁ (unwrap [A₊] (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑]))
                                      (proj₁ ([u] (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])))
      ⊢u≡u′ = PE.subst (λ x → Δ ∙ F [ σ ] ∙ G [ liftSubst σ ] ⊢ u [ liftSubstn σ 2 ]
                            ≅ u [ liftSubstn σ 2 ] ∷ x)
                       (subst-β-prodrec A σ) ⊢u≡u
      [t≡p] = proj₂ (redSubst*Term (redₜ t⇒p) [σΣ] [p])
      A[t]≡A[p] = proj₂ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] , [σt]))
                         {σ′ = consSubst σ p} ([σ] , [p]) (reflSubst [Γ] ⊢Δ [σ] , [t≡p])
      A[t]≡A[p]′ = irrelevanceEq″ (PE.sym (singleSubstComp t σ A))
                                   (PE.sym (singleSubstComp p σ A))
                                   [σA[t]]′ [σA[t]] A[t]≡A[p]
      reduction = prodrec-subst*
        {r = r} {u = u} {A} {F} {G} {σ}
        [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [p] (redₜ t⇒p)
      prodrecT′ = neuTerm
        [σA[p]] (prodrecₙ {r = r} x)
        (prodrecⱼ ⊢σF ⊢σG ⊢σA ⊢p ⊢σu′ ok)
        (~-prodrec ⊢σF ⊢σG (escapeEq [σA] (reflEq [σA])) p~p ⊢u≡u′ ok)
      prodrecT = convTerm₂ [σA[t]] [σA[p]] A[t]≡A[p]′ prodrecT′
  in  [σA[t]] , proj₁ (redSubst*Term reduction [σA[t]] prodrecT)

prodrecCong-eq : ∀ {m n} → (G : Term (1+ n)) (σ : Subst m n) (t : Term m)
               → G [ consSubst (id •ₛ σ) t ] PE.≡ U.wk (lift id) (G [ liftSubst σ ]) [ t ]₀
prodrecCong-eq G σ t = PE.sym (PE.trans (PE.cong (_[ t ]₀) (PE.trans (wk-subst {ρ = lift id} {σ = liftSubst σ} G)
                                                                    (subst-lift-•ₛ {ρ = id} {σ = σ} G)))
                                        (PE.trans (substCompEq {σ′ = liftSubst (id •ₛ σ)} {σ = sgSubst t} G )
                                                  (substVar-to-subst (substVarSingletonComp {σ = id •ₛ σ} {u = t}) G)))

prodrecCong :
  ∀ {Γ : Con Term n} {l F F′ G G′ A A′ t t′ u u′}
    {σ σ′ : Subst m n} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ])
  ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] / [F])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([G′] : Γ ∙ F′ ⊩ᵛ⟨ l ⟩ G′ / [Γ] ∙ [F′])
  ([G≡G′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] ∙ [F] / [G])
  (ok : Σʷ-allowed p q) →
  let [Σ] = Σᵛ [Γ] [F] [G] ok
      [Σ′] = Σᵛ [Γ] [F′] [G′] ok
  in
  ([A] : Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A′] : Γ ∙ (Σʷ p , q ▷ F′ ▹ G′) ⊩ᵛ⟨ l ⟩ A′ / [Γ] ∙ [Σ′])
  ([A≡A′] : Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A ≡ A′ / [Γ] ∙ [Σ] / [A])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G])
  ([A′₊] : Γ ∙ F′ ∙ G′ ⊩ᵛ⟨ l ⟩ A′ [ prodʷ p (var x1) (var x0) ]↑² /
             [Γ] ∙ [F′] ∙ [G′])
  ([A₊≡A′₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² ≡
                A′ [ prodʷ p (var x1) (var x0) ]↑² /
                [Γ] ∙ [F] ∙ [G] / [A₊])
  ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊])
  ([u′] : Γ ∙ F′ ∙ G′ ⊩ᵛ⟨ l ⟩ u′ ∷
            A′ [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F′] ∙ [G′] / [A′₊])
  ([u≡u′] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷
              A [ prodʷ p (var x1) (var x0) ]↑² /
              [Γ] ∙ [F] ∙ [G] / [A₊]) →
  Δ ⊢ Σʷ p , q ▷ F ▹ G [ σ ] ≡ Σʷ p , q ▷ F′ ▹ G′ [ σ′ ] →
  (⊢Δ : ⊢ Δ)
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
  ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
  ([σt] : Δ ⊩⟨ l ⟩ t ∷ Σʷ p , q ▷ F ▹ G [ σ ] /
            proj₁ (unwrap [Σ] ⊢Δ [σ]))
  ([σt′] : Δ ⊩⟨ l ⟩ t′ ∷ Σʷ p , q ▷ F′ ▹ G′ [ σ′ ] /
             proj₁ (unwrap [Σ′] ⊢Δ [σ′]))
  ([σt≡σt′] : Δ ⊩⟨ l ⟩ t ≡ t′ ∷ Σʷ p , q ▷ F ▹ G [ σ ] /
                proj₁ (unwrap [Σ] ⊢Δ [σ])) →
  ∃ λ [A[t]] →
  Δ ⊩⟨ l ⟩ prodrec r p q′ (A [ liftSubst σ ]) t
             (u [ liftSubstn σ 2 ]) ≡
    prodrec r p q′ (A′ [ liftSubst σ′ ]) t′
      (u′ [ liftSubstn σ′ 2 ]) ∷
    A [ liftSubst σ ] [ t ]₀ / [A[t]]
prodrecCong {n = n} {m = m} {p = p′} {q = q} {Δ = Δ} {r = r}
            {Γ = Γ} {l} {F} {F′} {G} {G′}
            {A} {A′} {t} {t′} {u} {u′} {σ} {σ′}
            [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] ok
            [A] [A′] [A≡A′] [A₊] [A′₊] [A₊≡A′₊] [u] [u′] [u≡u′]
            ⊢Σ≡Σ′ ⊢Δ [σ] [σ′] [σ≡σ′]
            [t]@(Σₜ pₜ dₜ p≅p (prodₙ {t = p₁} {u = p₂})
                   pProp@(PE.refl , wk[p₁] , wk[p₂] , PE.refl))
            [t′]@(Σₜ rₜ d′ₜ r≅r (prodₙ {t = r₁} {u = r₂})
                    rProp@(PE.refl , wk[r₁] , wk[r₂] , PE.refl))
            [t≡t′]@(Σₜ₌ _ _ d d′ prodₙ prodₙ p≅r wk[t] wk[t′]
                      (PE.refl , PE.refl ,
                       wk[p₁′] , wk[r₁′] , wk[p₂′] , wk[r₂′] ,
                       wk[p₁≡r₁] , wk[p₂≡r₂])) =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} {m = 𝕨} [Γ] [F] [G] ok
      [Σ′] = Σᵛ {F = F′} {G = G′} {q = q} {m = 𝕨} [Γ] [F′] [G′] ok
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
      [⇑σ′] = liftSubstS {σ = σ′} {F = F′} [Γ] ⊢Δ [F′] [σ′]
      [σ≡σ] = reflSubst {σ = σ} [Γ] ⊢Δ [σ]
      [σ′≡σ′] = reflSubst {σ = σ′} [Γ] ⊢Δ [σ′]
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [σ′F′] = proj₁ (unwrap [F′] ⊢Δ [σ′])
      ⊢σF = escape [σF]
      ⊢σ′F′ = escape [σ′F′]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
      [σ′G′] = proj₁ (unwrap [G′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢σ′F′) [⇑σ′])
      ⊢σG = escape [σG]
      ⊢σ′G′ = escape [σ′G′]
      [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
      [⇑²σ′] = liftSubstS {σ = liftSubst σ′} {F = G′} (_∙_ {A = F′} [Γ] [F′]) (⊢Δ ∙ ⊢σ′F′) [G′] [⇑σ′]
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      [σ′Σ′] = proj₁ (unwrap [Σ′] ⊢Δ [σ′])
      ⊢σΣ = escape [σΣ]
      ⊢σ′Σ′ = escape [σ′Σ′]
      [⇑σ]′ = liftSubstS {σ = σ} {F = Σ _ , q ▷ F ▹ G} [Γ] ⊢Δ [Σ] [σ]
      [⇑σ′]′ = liftSubstS {σ = σ′} {F = Σ _ , q ▷ F′ ▹ G′}
                 [Γ] ⊢Δ [Σ′] [σ′]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) [⇑σ]′)
      [σ′A′] = proj₁ (unwrap [A′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢σ′Σ′) [⇑σ′]′)
      ⊢σA = escape [σA]
      ⊢σ′A′ = escape [σ′A′]
      [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σ′A′₊] = proj₁ (unwrap [A′₊] {σ = liftSubstn σ′ 2} (⊢Δ ∙ ⊢σ′F′ ∙ ⊢σ′G′) [⇑²σ′])
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σ′u′] = proj₁ ([u′] {σ = liftSubstn σ′ 2} (⊢Δ ∙ ⊢σ′F′ ∙ ⊢σ′G′) [⇑²σ′])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu₁ = PE.subst (λ x → Δ ∙ F [ σ ] ∙ G [ liftSubst σ ] ⊢ u [ liftSubstn σ 2 ] ∷ x)
                      (subst-β-prodrec A σ) ⊢σu
      ⊢σ′u′ = escapeTerm [σ′A′₊] [σ′u′]
      ⊢σ′u′₁ = PE.subst (λ x → Δ ∙ F′ [ σ′ ] ∙ G′ [ liftSubst σ′ ] ⊢ u′ [ liftSubstn σ′ 2 ] ∷ x)
                        (subst-β-prodrec A′ σ′) ⊢σ′u′

      [A[t]]′ = proj₁ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] ,  [t]))
      [A[t]] = irrelevance′ (PE.sym (singleSubstComp t σ A)) [A[t]]′
      [A′[t′]]′ = proj₁ (unwrap [A′] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]))
      [A′[t′]] = irrelevance′ (PE.sym (singleSubstComp t′ σ′ A′)) [A′[t′]]′

      tu≡p = whrDet*Term (redₜ d , prodₙ) (redₜ dₜ , prodₙ)
      tu′≡r = whrDet*Term (redₜ d′ , prodₙ) (conv* (redₜ d′ₜ) (sym ⊢Σ≡Σ′) , prodₙ)
      d″ = PE.subst (λ x → Δ ⊢ t′ :⇒*: x ∷ Σʷ p′ , q ▷ F ▹ G [ σ ])
             tu′≡r d′
      d‴ = PE.subst (λ x → Δ ⊢ t :⇒*: x ∷ Σʷ p′ , q ▷ F ▹ G [ σ ])
             tu≡p d

      [p] : Δ ⊩⟨ _ ⟩ prodʷ _ p₁ p₂ ∷ Σ _ , q ▷ F ▹ G [ σ ] / [σΣ]
      [p] = Σₜ pₜ (idRedTerm:*: (⊢u-redₜ dₜ)) p≅p prodₙ pProp
      [r] :
        Δ ⊩⟨ _ ⟩ prodʷ _ r₁ r₂ ∷ Σ _ , q ▷ F′ ▹ G′ [ σ′ ] / [σ′Σ′]
      [r] = Σₜ rₜ (idRedTerm:*: (conv (⊢u-redₜ d″) ⊢Σ≡Σ′)) r≅r prodₙ rProp

      wk[σF] = W.wk id (wf ⊢σF) [σF]
      wk[σ′F′] = W.wk id (wf ⊢σ′F′) [σ′F′]
      [p₁] = irrelevanceTerm′ (wk-id (F [ σ ])) wk[σF] [σF] wk[p₁]
      [r₁] = irrelevanceTerm′ (wk-id (F′ [ σ′ ])) wk[σ′F′] [σ′F′] wk[r₁]

      wk[σ] = wkSubstS {σ = σ} [Γ] ⊢Δ (wf ⊢σF) id [σ]
      wk[σF]′ = proj₁ (unwrap [F] {σ = id •ₛ σ} (wf ⊢σF) wk[σ])
      wk[p₁]′ = irrelevanceTerm′ (wk-subst {ρ = id} {σ = σ} F) wk[σF] wk[σF]′ wk[p₁]
      wk[p₁′]′ = irrelevanceTerm′ (wk-subst {ρ = id} {σ = σ} F) wk[σF] wk[σF]′ wk[p₁′]
      wk[σGp₁]′ = proj₁ (unwrap [G] {σ = consSubst (id •ₛ σ) p₁} (wf ⊢σF) (wk[σ] , wk[p₁]′))
      wk[σGp₁′]′ = proj₁ (unwrap [G] (wf ⊢σF) (wk[σ] , wk[p₁′]′))
      wk[σGp₁] = irrelevance′ (prodrecCong-eq G σ p₁) wk[σGp₁]′
      wk[σGp₁′] = irrelevance′ (PE.sym (singleSubstWkComp _ σ G)) wk[σGp₁′]′
      [σGp₁]′ = proj₁ (unwrap [G] {σ = consSubst σ p₁} ⊢Δ ([σ] , [p₁]))
      [σGp₁] = irrelevance′ (PE.sym (singleSubstComp p₁ σ G)) [σGp₁]′
      [p₂] = irrelevanceTerm′ {t = p₂} (PE.cong (λ (x : Term (1+ m)) → x [ p₁ ]₀) (wk-lift-id (G [ liftSubst σ ]))) wk[σGp₁] [σGp₁] wk[p₂]

      wk[σ′] = wkSubstS {σ = σ′} [Γ] ⊢Δ (wf ⊢σ′F′) id [σ′]
      wk[σ′F′]′ = proj₁ (unwrap [F′] {σ = id •ₛ σ′} (wf ⊢σ′F′) wk[σ′])
      wk[r₁]′ = irrelevanceTerm′ (wk-subst {ρ = id} {σ = σ′} F′) wk[σ′F′] wk[σ′F′]′ wk[r₁]
      wk[σ′G′r₁]′ = proj₁ (unwrap [G′] {σ = consSubst (id •ₛ σ′) r₁} (wf ⊢σ′F′) (wk[σ′] , wk[r₁]′))
      wk[σ′G′r₁] = irrelevance′ (prodrecCong-eq G′ σ′ r₁) wk[σ′G′r₁]′
      [σ′G′r₁]′ = proj₁ (unwrap [G′] {σ = consSubst σ′ r₁} ⊢Δ ([σ′] , [r₁]))
      [σ′G′r₁] = irrelevance′ (PE.sym (singleSubstComp r₁ σ′ G′)) [σ′G′r₁]′
      [r₂] = irrelevanceTerm′ {t = r₂} (PE.cong (λ (x : Term (1+ m)) → x [ r₁ ]₀) (wk-lift-id (G′ [ liftSubst σ′ ]))) wk[σ′G′r₁] [σ′G′r₁] wk[r₂]

      ⊢p₁ = escapeTerm [σF] [p₁]
      ⊢r₁ = escapeTerm [σ′F′] [r₁]
      ⊢p₂ = escapeTerm [σGp₁] [p₂]
      ⊢r₂ = escapeTerm [σ′G′r₁] [r₂]

      red₁ = prodrec-subst* {r = r} {u = u} {A} {F} {G}
        [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [p] (redₜ d‴)
      [A[p]] , [prodrecₚ] = prodrecTerm
        {Γ = Γ} {q = q} {r = r} {F = F} {G} {A} {t = prodʷ _ p₁ p₂} {u}
        [Γ] [F] [G] ok [A] [A₊] [u] ⊢Δ [σ] [p]
      _ , [t≡p] = redSubst*Term (redₜ dₜ) [σΣ] [p]
      [At≡Ap] = proj₂ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] , [t]))
        {σ′ = consSubst σ (prodʷ _ p₁ p₂)} ([σ] , [p]) ([σ≡σ] , [t≡p])
      [At≡Ap]′ = irrelevanceEq″ (PE.sym (singleSubstComp t σ A))
                                (PE.sym (singleSubstComp _ σ A))
                                [A[t]]′ [A[t]] [At≡Ap]
      [prodrecₚ]′ = convTerm₂ [A[t]] [A[p]] [At≡Ap]′ [prodrecₚ]
      [prodrecₜ] , [prodrecₚ≡] = redSubst*Term red₁ [A[t]] [prodrecₚ]′

      d⁗ = conv* (redₜ d″) ⊢Σ≡Σ′
      red₂ = prodrec-subst*
        {r = r} {u = u′} {A′} {F′} {G′}
        [Γ] [F′] [G′] [Σ′] [A′] [A′₊] [u′] ⊢Δ [σ′] [r] d⁗
      [A′[r]] , [prodrecᵣ] = prodrecTerm
        {Γ = Γ} {q = q} {r = r} {F = F′} {G′} {A′} {t = prodʷ _ r₁ r₂} {u′}
        [Γ] [F′] [G′] ok [A′] [A′₊] [u′] ⊢Δ [σ′] [r]
      [t′≡r] = proj₂ (redSubst*Term d⁗ [σ′Σ′] [r])
      [A′t′≡A′r] = proj₂ (unwrap [A′] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]))
        {σ′ = consSubst σ′ (prodʷ _ r₁ r₂)} ([σ′] , [r]) ([σ′≡σ′] , [t′≡r])
      [A′t′≡A′r]′ = irrelevanceEq″ (PE.sym (singleSubstComp t′ σ′ A′))
                                   (PE.sym (singleSubstComp _ σ′ A′))
                                   [A′[t′]]′ [A′[t′]] [A′t′≡A′r]
      [prodrecᵣ]′ = convTerm₂ [A′[t′]] [A′[r]] [A′t′≡A′r]′ [prodrecᵣ]
      [prodrecₜ′] , [prodrecᵣ≡] = redSubst*Term red₂ [A′[t′]] [prodrecᵣ]′

      red₃ : _ ⊢ _ ⇒ _ ∷ _
      red₃ = prodrec-β {r = r} ⊢σF ⊢σG ⊢σA ⊢p₁ ⊢p₂ ⊢σu₁ PE.refl ok
      [p₂]′ = irrelevanceTerm′ (singleSubstComp p₁ σ G)
                               [σGp₁] [σGp₁]′ [p₂]
      σ₊ = consSubst (consSubst σ p₁) p₂
      [σ₊] = ([σ] , [p₁]) , [p₂]′
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = σ₊} ⊢Δ [σ₊])
      [σ₊A₊]′ = irrelevance′
        (PE.sym (singleSubstComp (prodʷ _ p₁ p₂) σ A))
        (proj₁ (unwrap [A] {σ = consSubst σ (prodʷ _ p₁ p₂)} ⊢Δ ([σ] , [p])))
      [σ₊u₊] = proj₁ ([u] {σ = σ₊} ⊢Δ [σ₊])
      [σ₊u₊]′ = irrelevanceTerm″ (PE.sym (substCompProdrec A p₁ p₂ σ))
                                 (PE.sym (doubleSubstComp u p₁ p₂ σ))
                                 [σ₊A₊] [σ₊A₊]′ [σ₊u₊]
      _ , [prodrecₚ≡u] = redSubstTerm red₃ [A[p]] [σ₊u₊]′

      red₄ : _ ⊢ _ ⇒ _ ∷ _
      red₄ = prodrec-β {r = r} ⊢σ′F′ ⊢σ′G′ ⊢σ′A′ ⊢r₁ ⊢r₂ ⊢σ′u′₁ PE.refl
               ok
      [r₂]′ = irrelevanceTerm′ (singleSubstComp r₁ σ′ G′)
                               [σ′G′r₁] [σ′G′r₁]′ [r₂]
      σ′₊ = consSubst (consSubst σ′ r₁) r₂
      [σ′₊] = ([σ′] , [r₁]) , [r₂]′
      [σ′₊A′₊] = proj₁ (unwrap [A′₊] {σ = σ′₊} ⊢Δ [σ′₊])
      [σ′₊A′₊]′ = irrelevance′
        (PE.sym (singleSubstComp (prodʷ _ r₁ r₂) σ′ A′))
        (proj₁ (unwrap [A′] {σ = consSubst σ′ (prodʷ _ r₁ r₂)} ⊢Δ ([σ′] , [r])))
      [σ′₊u′₊] = proj₁ ([u′] {σ = σ′₊} ⊢Δ [σ′₊])
      [σ′₊u′₊]′ = irrelevanceTerm″ (PE.sym (substCompProdrec A′ r₁ r₂ σ′))
                                 (PE.sym (doubleSubstComp u′ r₁ r₂ σ′))
                                 [σ′₊A′₊] [σ′₊A′₊]′ [σ′₊u′₊]
      _ , [prodrecᵣ≡u′] = redSubstTerm red₄ [A′[r]] [σ′₊u′₊]′

      [σ′F] = proj₁ (unwrap [F] ⊢Δ [σ′])
      [σ′F≡σ′F′] = [F≡F′] {σ = σ′} ⊢Δ [σ′]
      [r₁]′ = convTerm₂ [σ′F] [σ′F′] [σ′F≡σ′F′] [r₁]
      [σ′Gr₁] = proj₁ (unwrap [G] ⊢Δ ([σ′] , [r₁]′))
      [σ′Gr₁≡σ′G′r₁] = [G≡G′] {σ = consSubst σ′ r₁} ⊢Δ ([σ′] , [r₁]′)
      [r₂]″ = convTerm₂ [σ′Gr₁] [σ′G′r₁]′ [σ′Gr₁≡σ′G′r₁] [r₂]′

      [σ′₊]′ = ([σ′] , [r₁]′) , [r₂]″
      _ , _ , t≡p₁ , u≡p₂ = prod-PE-injectivity tu≡p
      _ , _ , t′≡r₁ , u′≡r₂ = prod-PE-injectivity tu′≡r
      [p₁≡r₁] = irrelevanceEqTerm″ t≡p₁ t′≡r₁
                                   (wk-id (F [ σ ])) wk[σF] [σF] wk[p₁≡r₁]
      [p₂≡r₂] = irrelevanceEqTerm″  u≡p₂ u′≡r₂
                                   (PE.trans (PE.cong₂ _[_]₀ (wk-lift-id (G [ liftSubst σ ])) t≡p₁)
                                             (singleSubstComp p₁ σ G))
                                    wk[σGp₁′] [σGp₁]′ wk[p₂≡r₂]
      [σ₊≡σ′₊] = ([σ≡σ′] , [p₁≡r₁]) , [p₂≡r₂]
      [uₚ≡uᵣ] = proj₂ ([u] {σ = σ₊} ⊢Δ [σ₊]) {σ′ = σ′₊} [σ′₊]′ [σ₊≡σ′₊]
      [uᵣ≡u′ᵣ] = [u≡u′] {σ = σ′₊} ⊢Δ [σ′₊]′
      [σ′₊A₊] = proj₁ (unwrap [A₊] {σ = σ′₊} ⊢Δ [σ′₊]′)
      [σ₊A₊≡σ′₊A₊] = proj₂ (unwrap [A₊] {σ = σ₊} ⊢Δ [σ₊]) {σ′ = σ′₊} [σ′₊]′ [σ₊≡σ′₊]
      [uᵣ≡u′ᵣ]′ = convEqTerm₂ [σ₊A₊] [σ′₊A₊] [σ₊A₊≡σ′₊A₊] [uᵣ≡u′ᵣ]
      [u₊≡u′₊] = transEqTerm [σ₊A₊] [uₚ≡uᵣ] [uᵣ≡u′ᵣ]′

      [σ′Σ] = proj₁ (unwrap [Σ] ⊢Δ [σ′])
      [Σ≡Σ′] = Σ-congᵛ {F = F} {G} {F′} {G′} {q = q}
                 [Γ] [F] [G] [F′] [G′] [F≡F′] [G≡G′] _
      [σ′Σ≡σ′Σ′] = [Σ≡Σ′] ⊢Δ [σ′]
      [t′]′ = convTerm₂ [σ′Σ] [σ′Σ′] [σ′Σ≡σ′Σ′] [t′]
      [σ′At′] = proj₁ (unwrap [A] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]′))
      [σ′A′t′] = proj₁ (unwrap [A′] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]))
      [A′[r]]′ = unwrap
        [A′] {σ = consSubst σ′ (prodʷ _ r₁ r₂)} ⊢Δ ([σ′] , [r])
        .proj₁

      [σAt≡σ′At′] = proj₂ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] , [t]))
                          {σ′ = consSubst σ′ t′} ([σ′] , [t′]′) ([σ≡σ′] , [t≡t′])
      [σ′At′≡σ′A′t′] = [A≡A′] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]′)
      [σAt≡σ′A′t′] = transEq [A[t]]′ [σ′At′] [σ′A′t′] [σAt≡σ′At′] [σ′At′≡σ′A′t′]
      [σAt≡σ′A′t′]′ = irrelevanceEq″ (PE.sym (singleSubstComp t σ A))
                                     (PE.sym (singleSubstComp t′ σ′ A′))
                                     [A[t]]′ [A[t]] [σAt≡σ′A′t′]
      [σAt≡σ′A′r] = transEq [A[t]]′ [A′[t′]]′ [A′[r]]′ [σAt≡σ′A′t′] [A′t′≡A′r]
      [σAt≡σ′A′r]′ = irrelevanceEq″
        (PE.sym (singleSubstComp t σ A))
        (PE.sym (singleSubstComp (prodʷ _ r₁ r₂) σ′ A′))
        [A[t]]′ [A[t]] [σAt≡σ′A′r]
      [prodrecₚ≡u]′ = convEqTerm₂ [A[t]] [A[p]] [At≡Ap]′ [prodrecₚ≡u]
      [u₊≡u′₊]′ = irrelevanceEqTerm″ (PE.sym (doubleSubstComp u p₁ p₂ σ))
                                     (PE.sym (doubleSubstComp u′ r₁ r₂ σ′))
                                     (PE.sym (substCompProdrec A p₁ p₂ σ))
                                     [σ₊A₊] [A[p]] [u₊≡u′₊]
      [u₊≡u′₊]″ = convEqTerm₂ [A[t]] [A[p]] [At≡Ap]′ [u₊≡u′₊]′
      [prodrecᵣ≡u′]′ = convEqTerm₂ [A[t]] [A′[r]] [σAt≡σ′A′r]′ [prodrecᵣ≡u′]

      [prodrecᵣ≡]′ = convEqTerm₂ [A[t]] [A′[t′]] [σAt≡σ′A′t′]′ [prodrecᵣ≡]

  in  [A[t]] , transEqTerm [A[t]] [prodrecₚ≡]
                           (transEqTerm [A[t]] [prodrecₚ≡u]′
                           (transEqTerm [A[t]] [u₊≡u′₊]″
                           (symEqTerm [A[t]] (transEqTerm [A[t]] [prodrecᵣ≡]′ [prodrecᵣ≡u′]′))))

prodrecCong {n = n} {m = m} {p = p′} {q = q} {Δ = Δ} {r = r}
            {Γ = Γ} {l} {F} {F′} {G} {G′}
            {A} {A′} {t} {t′} {u} {u′} {σ} {σ′}
            [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] ok
            [A] [A′] [A≡A′] [A₊] [A′₊] [A₊≡A′₊] [u] [u′] [u≡u′]
            ⊢Σ≡Σ′ ⊢Δ [σ] [σ′] [σ≡σ′]
            [t]@(Σₜ pₜ dₜ p≅p (ne xₜ) pProp)
            [t′]@(Σₜ rₜ d′ₜ r≅r (ne yₜ) rProp)
            [t≡t′]@(Σₜ₌ _ _ d d′ (ne x) (ne y) p≅r wk[t] wk[t′] p~r) =
  let [Σ] = Σᵛ {F = F} {G = G} {q = q} {m = 𝕨} [Γ] [F] [G] ok
      [Σ′] = Σᵛ {F = F′} {G = G′} {q = q} {m = 𝕨} [Γ] [F′] [G′] ok
      [Σ≡Σ′] = Σ-congᵛ {F = F} {G} {F′} {G′} {q = q} {m = 𝕨}
                 [Γ] [F] [G] [F′] [G′] [F≡F′] [G≡G′] ok
      σΣ = Σʷ p′ , q ▷ F ▹ G [ σ ]
      σΣ′ = Σʷ _ , q ▷ F′ ▹ G′ [ σ ]
      σ′Σ′ = Σʷ p′ , q ▷ F′ ▹ G′ [ σ′ ]
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σ′F′] = proj₁ (unwrap [F′] ⊢Δ [σ′])
      ⊢σ′F′ = escape [σ′F′]
      [σF′] = proj₁ (unwrap [F′] ⊢Δ [σ])
      ⊢σF′ = escape [σF′]
      [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
      ⊢σG = escape [σG]
      [⇑σ′] = liftSubstS {σ = σ′} {F = F′} [Γ] ⊢Δ [F′] [σ′]
      [σ′G′] = proj₁ (unwrap [G′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢σ′F′) [⇑σ′])
      ⊢σ′G′ = escape [σ′G′]
      [σG′] = proj₁ (unwrap [G′] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF′)
                    (liftSubstS {σ = σ} {F = F′} [Γ] ⊢Δ [F′] [σ]))
      ⊢σG′ = escape [σG′]
      [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [σ′Σ′] = proj₁ (unwrap [Σ′] ⊢Δ [σ′])
      ⊢σ′Σ′ = escape [σ′Σ′]
      [σΣ′] = proj₁ (unwrap [Σ′] ⊢Δ [σ])
      ⊢σΣ′ = escape [σΣ′]

      [↑σ]″ = liftSubstS {σ = σ} {F = Σ _ , q ▷ F ▹ G} [Γ] ⊢Δ [Σ] [σ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) [↑σ]″)
      [σA≡σA′] = [A≡A′] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) [↑σ]″
      ⊢σA≅σA′ = escapeEq [σA] [σA≡σA′]

      [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G] [⇑σ]
      [σu≡σu′] = [u≡u′] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ]
      [σA₊] = proj₁ (unwrap [A₊] (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      ⊢σu≅σu′ = escapeTermEq [σA₊] [σu≡σu′]
      ⊢σu≅σu″ : Δ ∙ F [ σ ] ∙ G [ liftSubst σ ] ⊢ u [ liftSubstn σ 2 ] ≅ u′ [ liftSubstn σ 2 ]
                  ∷ (A [ liftSubst σ ] [ prod! (var (x0 +1)) (var x0) ]↑²)
      ⊢σu≅σu″ = PE.subst (λ (x : Term (2 + m)) → _ ⊢ _ ≅ _ ∷ x )
                         (subst-β-prodrec A σ) ⊢σu≅σu′

      p≡p′ = whrDet*Term (redₜ d , ne x) (redₜ dₜ , ne xₜ)
      r≡r′ = whrDet*Term (redₜ d′ , ne y) (conv* (redₜ d′ₜ) (sym ⊢Σ≡Σ′) , ne yₜ)
      p~r′ = PE.subst₂
        (λ (x y : Term m) →
           Δ ⊢ x ~ y ∷ Σʷ _ , q ▷ (F [ σ ]) ▹ (G [ liftSubst σ ]))
        p≡p′ r≡r′ p~r
      σprₚ~σprᵣ = ~-prodrec
        {q = q} {r = r} {A = A [ liftSubst σ ]}
        {A′ [ liftSubst σ ]} {pₜ} {rₜ}
        {u [ liftSubstn σ 2 ]} {u′ [ liftSubstn σ 2 ]}
        ⊢σF ⊢σG ⊢σA≅σA′ p~r′ ⊢σu≅σu″ ok

      [⇑σ]′ = liftSubstS {σ = σ} {F = Σ _ , _ ▷ F′ ▹ G′} [Γ] ⊢Δ [Σ′] [σ]
      [↑σ′]′ : Δ ∙ Σ _ , q ▷ F′ ▹ G′ [ σ ] ⊩ˢ wk1Subst σ′ ∷ Γ /
                 [Γ] / (⊢Δ ∙ ⊢σΣ′)
      [↑σ′]′ = wk1SubstS [Γ] ⊢Δ ⊢σΣ′ [σ′]
      [σΣ′≡σ′Σ′] = proj₂ (unwrap [Σ′] {σ = σ} ⊢Δ [σ]) {σ′ = σ′} [σ′] [σ≡σ′]
      ⊢σΣ′≡σ′Σ′ = escapeEq [σΣ′] [σΣ′≡σ′Σ′]
      wk⊢σΣ′≡σ′Σ′ = ≅-wk (step id) (⊢Δ ∙ ⊢σΣ′) ⊢σΣ′≡σ′Σ′
      var0′ : Δ ∙ _ ⊢ var x0 ∷ _
      var0′ = var₀ ⊢σΣ′
      var0 : Δ ∙ _ ⊢ var x0 ∷ _
      var0 = conv var0′ (PE.subst (λ (x : Term (1+ m)) → Δ ∙ σΣ′ ⊢ U.wk (step id) σΣ′ ≡ x)
                                  (wk-subst (Σ _ , q ▷ F′ ▹ G′))
                                  (≅-eq wk⊢σΣ′≡σ′Σ′))
      [var0] : Δ ∙ σΣ′ ⊩⟨ _ ⟩ var x0 ∷
                 Σ _ , q ▷ F′ ▹ G′ [ wk1Subst σ′ ] /
                 proj₁ (unwrap [Σ′] (⊢Δ ∙ ⊢σΣ′) [↑σ′]′)
      [var0] = neuTerm {Γ = Δ ∙ σΣ′}
                       {A = Σ _ , q ▷ F′ ▹ G′ [ wk1Subst σ′ ]}
                       {n = var x0}
                       (proj₁ (unwrap [Σ′] (⊢Δ ∙ ⊢σΣ′) [↑σ′]′)) (var x0)
                       var0 (~-var var0)
      [⇑σ′]′ : Δ ∙ _ ⊩ˢ consSubst (wk1Subst σ′) (var x0) ∷ Γ ∙ _ / [Γ] ∙ [Σ′] / ⊢Δ ∙ ⊢σΣ′
      [⇑σ′]′ = [↑σ′]′ , [var0]
      [⇑σ≡⇑σ′] =
        liftSubstSEq {F = Σ _ , q ▷ F′ ▹ G′} [Γ] ⊢Δ [Σ′] [σ] [σ≡σ′]
      [σA′≡σ′A′] = proj₂ (unwrap [A′] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ′) [⇑σ]′)
                         {σ′ = liftSubst σ′} [⇑σ′]′ [⇑σ≡⇑σ′]
      ⊢σA′≡σ′A′ = escapeEq (proj₁ (unwrap [A′] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ′) [⇑σ]′)) [σA′≡σ′A′]

      [σΣ≡σΣ′] = [Σ≡Σ′] ⊢Δ [σ]
      ⊢σΣ≡σΣ′ = escapeEq [σΣ] [σΣ≡σΣ′]
      r~r = ~-conv (~-trans (~-sym p~r) p~r) (≅-eq ⊢σΣ≡σΣ′)

      [⇑²σ]′ = liftSubstS {σ = liftSubst σ} {F = G′} (_∙_ {A = F′} [Γ] [F′]) (⊢Δ ∙ ⊢σF′) [G′]
                          (liftSubstS {σ = σ} {F = F′} [Γ] ⊢Δ [F′] [σ])
      σF′ = F′ [ σ ]
      σG′ = G′ [ liftSubst σ ]
      [↑²σ′] : Δ ∙ σF′ ∙ σG′ ⊩ˢ wk1Subst (wk1Subst σ′) ∷ Γ / [Γ] / ⊢Δ ∙ ⊢σF′ ∙ ⊢σG′
      [↑²σ′] = wk1SubstS {σ = wk1Subst σ′} [Γ] (⊢Δ ∙ ⊢σF′) ⊢σG′
                         (wk1SubstS {σ = σ′} [Γ] ⊢Δ ⊢σF′ [σ′])
      [σF′≡σ′F′] = proj₂ (unwrap [F′] {σ = σ} ⊢Δ [σ])
                         {σ′ = σ′} [σ′] [σ≡σ′]
      ⊢σF′≅σ′F′ = escapeEq [σF′] [σF′≡σ′F′]
      wk⊢σF′≅σ′F′ = ≅-wk (step id) (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′)
                           (≅-wk (step id) (⊢Δ ∙ ⊢σF′) ⊢σF′≅σ′F′)
      var1 = var₁ ⊢σG′
      var1′ = conv var1 (PE.subst (λ x → Δ ∙ σF′ ∙ σG′ ⊢ wk1 (wk1 σF′) ≡ x)
                                  (PE.trans (PE.cong wk1 (wk-subst {ρ = step id} {σ = σ′} F′))
                                            (wk-subst F′))
                                  (≅-eq wk⊢σF′≅σ′F′))
      [var1] : Δ ∙ σF′ ∙ σG′ ⊩⟨ _ ⟩ var (x0 +1) ∷ F′ [ wk1Subst (wk1Subst σ′) ]
                                       / proj₁ (unwrap [F′] (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) [↑²σ′])
      [var1] = neuTerm (proj₁ (unwrap [F′] (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) [↑²σ′]))
                       (var (x0 +1)) var1′ (~-var var1′)
      [↑⇑σ′] :  Δ ∙ F′ [ σ ] ∙ G′ [ liftSubst σ ] ⊩ˢ consSubst (wk1Subst (wk1Subst σ′)) (var (x0 +1))
                  ∷ Γ ∙ F′ / [Γ] ∙ [F′] / ⊢Δ ∙ ⊢σF′ ∙ ⊢σG′
      [↑⇑σ′] = [↑²σ′] , [var1]
      var0₁′ = var₀ ⊢σF′
      wk1⊢σF′≅σ′F′ = ≅-wk (step id) (⊢Δ ∙ ⊢σF′) ⊢σF′≅σ′F′
      var0₁ = conv var0₁′ (PE.subst (λ x → Δ ∙ σF′ ⊢ wk1 σF′ ≡ x)
                                  (wk-subst F′) (≅-eq wk1⊢σF′≅σ′F′))
      [↑σ′] = wk1SubstS [Γ] ⊢Δ ⊢σF′ [σ′]
      [var0₁] : Δ ∙ σF′ ⊩⟨ _ ⟩ var x0
               ∷ F′ [ wk1Subst σ′ ] / proj₁ (unwrap [F′] (⊢Δ ∙ ⊢σF′) [↑σ′])
      [var0₁] = neuTerm {Γ = Δ ∙ σF′}
                       {A = F′ [ wk1Subst σ′ ]}
                       {n = var x0}
                       (proj₁ (unwrap [F′] (⊢Δ ∙ ⊢σF′) [↑σ′])) (var x0)
                       var0₁ (~-var var0₁)
      [σG′≡σ′G′] = proj₂ (unwrap [G′] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF′)
                               (liftSubstS {σ = σ} {F = F′} [Γ] ⊢Δ [F′] [σ]))
                         {σ′ = liftSubst σ′} (wk1SubstS [Γ] ⊢Δ ⊢σF′ [σ′] , [var0₁])
                         (liftSubstSEq {F = F′} [Γ] ⊢Δ [F′] [σ] [σ≡σ′])
      ⊢σG′≅σ′G′ = escapeEq [σG′] [σG′≡σ′G′]
      wk1⊢σG′≅σ′G′ = ≅-wk (step id) (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) ⊢σG′≅σ′G′
      var0₂ : _ ⊢ var x0 ∷ _
      var0₂ = var₀ ⊢σG′
      var0₂′ : _ ⊢ var x0 ∷ _
      var0₂′ = conv var0₂ (PE.subst (λ x → Δ ∙ σF′ ∙ σG′ ⊢ wk1 σG′ ≡ x)
                                  (wk-subst G′) (≅-eq wk1⊢σG′≅σ′G′))
      [var0₂] : Δ ∙ σF′ ∙ σG′ ⊩⟨ _ ⟩ var x0 ∷ G′ [ wk1Subst (liftSubst σ′) ]
                                       / proj₁ (unwrap [G′] (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) [↑⇑σ′])
      [var0₂] = neuTerm (proj₁ (unwrap [G′] (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) [↑⇑σ′]))
                       (var x0) var0₂′ (~-var var0₂′)
      [⇑²σ′] = [↑⇑σ′] , [var0₂]
      [σu′≡σ′u′] = proj₂ ([u′] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) [⇑²σ]′)
                         {σ′ = liftSubstn σ′ 2} [⇑²σ′]
                         (liftSubstSEq {σ = liftSubst σ} {σ′ = liftSubst σ′} {F = G′}
                                       (_∙_ {A = F′} [Γ] [F′]) (⊢Δ ∙ ⊢σF′) [G′]
                                       (liftSubstS {σ = σ} {F = F′} [Γ] ⊢Δ [F′] [σ])
                                       (liftSubstSEq {σ = σ} {σ′ = σ′} {F = F′}
                                                     [Γ] ⊢Δ [F′] [σ] [σ≡σ′]))
      [σA′₊] = proj₁ (unwrap [A′₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) [⇑²σ]′)
      ⊢σu′≅σ′u′ = PE.subst (λ (x : Term (2 + m)) → Δ ∙ σF′ ∙ σG′ ⊢ u′ [ liftSubstn σ 2 ]
                                                     ≅ u′ [ liftSubstn σ′ 2 ] ∷ x)
                           (subst-β-prodrec A′ σ) (escapeTermEq [σA′₊] [σu′≡σ′u′])

      σprᵣ~σ′prᵣ = ~-prodrec
        {q = q} {r = r} {A = A′ [ liftSubst σ ]}
        {A′ [ liftSubst σ′ ]} {rₜ} {rₜ}
        {u′ [ liftSubstn σ 2 ]} {u′ [ liftSubstn σ′ 2 ]}
        ⊢σF′ ⊢σG′ ⊢σA′≡σ′A′
        (PE.subst
           (λ (x : Term m) → Δ ⊢ x ~ x ∷ Σʷ _ , q ▷ F′ ▹ G′ [ σ ])
           r≡r′ r~r)
        ⊢σu′≅σ′u′ ok


      [A[t]]′ = proj₁ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] , [t]))
      [A[t]] = irrelevance′ (PE.sym (singleSubstComp t σ A)) [A[t]]′
      [p] = Σₜ pₜ ((idRedTerm:*: (⊢u-redₜ dₜ))) p≅p (ne xₜ) pProp
      _ , [t≡p] = redSubst*Term (redₜ dₜ) [σΣ] [p]
      [A[p]] , [prₚ] = prodrecTerm {r = r} {F = F} {G} {A} {pₜ} {u}
                         [Γ] [F] [G] ok [A] [A₊] [u] ⊢Δ [σ] [p]
      [At≡Ap]′ = proj₂ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] , [t]))
                       {σ′ = consSubst σ pₜ} ([σ] , [p]) (reflSubst [Γ] ⊢Δ [σ] , [t≡p])
      [At≡Ap] = irrelevanceEq″ (PE.sym (singleSubstComp t σ A))
                               (PE.sym (singleSubstComp pₜ σ A))
                               [A[t]]′ [A[t]] [At≡Ap]′
      [prₚ]′ = convTerm₂ [A[t]] [A[p]] [At≡Ap] [prₚ]
      red₁ = prodrec-subst* {r = r} {t = t} {pₜ} {u} {A} {F} {G}
               [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [p] (redₜ dₜ)
      [prₜ] , [prₜ≡prₚ] = redSubst*Term red₁ [A[t]] [prₚ]′

      [r] = Σₜ rₜ (idRedTerm:*: (⊢u-redₜ d′ₜ)) r≅r (ne yₜ) rProp
      [A′[t′]]′ = proj₁ (unwrap [A′] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]))
      [A′[t′]] = irrelevance′ (PE.sym (singleSubstComp t′ σ′ A′)) [A′[t′]]′
      _ , [t′≡r] = redSubst*Term (redₜ d′ₜ) [σ′Σ′] [r]
      [A′[r]] , [prᵣ] =
        prodrecTerm {r = r} {F = F′} {G′} {A′} {rₜ} {u′}
          [Γ] [F′] [G′] ok [A′] [A′₊] [u′] ⊢Δ [σ′] [r]

      [A′t′≡A′r]′ = proj₂ (unwrap [A′] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]))
                          {σ′ = consSubst σ′ rₜ} ([σ′] , [r]) (reflSubst [Γ] ⊢Δ [σ′] , [t′≡r])
      [A′t′≡A′r] = irrelevanceEq″ (PE.sym (singleSubstComp t′ σ′ A′))
                                  (PE.sym (singleSubstComp rₜ σ′ A′))
                                  [A′[t′]]′ [A′[t′]] [A′t′≡A′r]′
      [prᵣ]′ = convTerm₂ [A′[t′]] [A′[r]] [A′t′≡A′r] [prᵣ]
      red₂ =
        prodrec-subst* {r = r} {t = t′} {rₜ} {u′} {A′} {F′} {G′}
          [Γ] [F′] [G′] [Σ′] [A′] [A′₊] [u′] ⊢Δ [σ′] [r] (redₜ d′ₜ)
      [prₜ′] , [prₜ′≡prᵣ] = redSubst*Term red₂ [A′[t′]] [prᵣ]′

      ⊢σA = escape [σA]
      [σA′] = unwrap
        [A′] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ′)
        (liftSubstS {σ = σ} {F = Σʷ _ , q ▷ F′ ▹ G′} [Γ] ⊢Δ [Σ′] [σ])
        .proj₁
      ⊢σA′ = escape [σA′]
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
      [σu′] = proj₁ ([u′] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′)
                          (liftSubstS {σ = liftSubst σ} {F = G′}
                                      (_∙_ {A = F′} [Γ] [F′]) (⊢Δ ∙ ⊢σF′) [G′]
                                      (liftSubstS {σ = σ} {F = F′} [Γ] ⊢Δ [F′] [σ])))

      σF = F [ σ ]
      σG = G [ liftSubst σ ]
      σ′F′ = F′ [ σ′ ]
      σ′G′ = G′ [ liftSubst σ′ ]
      ⊢p = escapeTerm [σΣ] [p]
      ⊢r = escapeTerm [σ′Σ′] [r]
      ⊢σu = PE.subst (λ x → Δ ∙ σF ∙ σG ⊢ u [ liftSubstn σ 2 ] ∷ x)
                     (subst-β-prodrec A σ) (escapeTerm [σA₊] [σu])
      ⊢σu′ = PE.subst (λ x → Δ ∙ σF′ ∙ σG′ ⊢ u′ [ liftSubstn σ 2 ] ∷ x)
                       (subst-β-prodrec A′ σ) (escapeTerm [σA′₊] [σu′])

      [σΣ≡σ′Σ′] = transEq [σΣ] [σΣ′] [σ′Σ′] [σΣ≡σΣ′] [σΣ′≡σ′Σ′]
      [σ≡σ] = reflSubst [Γ] ⊢Δ [σ]
      [r]′ = convTerm₂ [σΣ] [σ′Σ′] [σΣ≡σ′Σ′] [r]
      [r]″ = convTerm₂ [σΣ′] [σ′Σ′] [σΣ′≡σ′Σ′] [r]
      [p≡r] : Δ ⊩⟨ l ⟩ pₜ ≡ rₜ ∷ Σʷ _ , q ▷ F ▹ G [ σ ] / [σΣ]
      [p≡r] = Σₜ₌ pₜ rₜ
        (idRedTerm:*: (⊢u-redₜ dₜ))
        (idRedTerm:*: (conv (⊢u-redₜ d′ₜ) (sym ⊢Σ≡Σ′)))
        (ne xₜ) (ne yₜ)
        (PE.subst₂
           (λ (x y : Term m) → Δ ⊢ x ≅ y ∷ Σʷ _ , q ▷ F ▹ G [ σ ])
           p≡p′ r≡r′ p≅r)
        [p] [r]′
        (PE.subst₂
           (λ (x y : Term m) → Δ ⊢ x ~ y ∷ Σʷ _ , q ▷ F ▹ G [ σ ])
           p≡p′ r≡r′ p~r)
      [σAp≡σAr]′ = proj₂ (unwrap [A] {σ = consSubst σ pₜ} ⊢Δ ([σ] , [p]))
                       {σ′ = consSubst σ rₜ} ([σ] , [r]′) ([σ≡σ] , [p≡r])
      [σAr≡σA′r]′ = [A≡A′] {σ = consSubst σ rₜ} ⊢Δ ([σ] , [r]′)
      [σA[p]]′ = proj₁ (unwrap [A] {σ = consSubst σ pₜ} ⊢Δ ([σ] , [p]))
      [σA[r]]′ = proj₁ (unwrap [A] {σ = consSubst σ rₜ} ⊢Δ ([σ] , [r]′))
      [σA′[r]]′ = proj₁ (unwrap [A′] {σ = consSubst σ rₜ} ⊢Δ ([σ] , [r]″))
      [σAp≡σA′r]′ = transEq [σA[p]]′ [σA[r]]′ [σA′[r]]′ [σAp≡σAr]′ [σAr≡σA′r]′
      [σAp≡σA′r] = irrelevanceEq″ (PE.sym (singleSubstComp pₜ σ A))
                                  (PE.sym (singleSubstComp rₜ σ A′))
                                  [σA[p]]′ [A[p]] [σAp≡σA′r]′
      ⊢Ap≅A′r = escapeEq [A[p]] [σAp≡σA′r]
      [σprₚ≡σprᵣ] =
        neuEqTerm [A[p]] (prodrecₙ xₜ) (prodrecₙ yₜ)
          (prodrecⱼ ⊢σF ⊢σG ⊢σA ⊢p ⊢σu ok)
          (conv
             (prodrecⱼ ⊢σF′ ⊢σG′ ⊢σA′
                (conv ⊢r (sym (≅-eq ⊢σΣ′≡σ′Σ′))) ⊢σu′ ok)
             (sym (≅-eq ⊢Ap≅A′r)))
          σprₚ~σprᵣ

      [σA′[r]] = irrelevance′ (PE.sym (singleSubstComp rₜ σ A′)) [σA′[r]]′
      [σ′A′] = proj₁ (unwrap [A′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢σΣ′) [⇑σ′]′)
      ⊢σ′A′ = escape [σ′A′]
      [σ′u′] = proj₁ ([u′] {σ = liftSubstn σ′ 2} (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) [⇑²σ′])
      [σ′A′₊] = proj₁ (unwrap [A′₊] {σ = liftSubstn σ′ 2} (⊢Δ ∙ ⊢σF′ ∙ ⊢σG′) [⇑²σ′])
      ⊢σ′u′ = PE.subst (λ x → Δ ∙ σF′ ∙ σG′ ⊢ u′ [ liftSubstn σ′ 2 ] ∷ x)
                       (subst-β-prodrec A′ σ′)
                       (escapeTerm [σ′A′₊] [σ′u′])
      [σA′r≡σ′A′r]′ = proj₂ (unwrap [A′] {σ = consSubst σ rₜ} ⊢Δ ([σ] , [r]″))
                           {σ′ = consSubst σ′ rₜ} ([σ′] , [r]) ([σ≡σ′] , reflEqTerm [σΣ′] [r]″)
      [σA′r≡σ′A′r] = irrelevanceEq″ (PE.sym (singleSubstComp rₜ σ A′))
                                    (PE.sym (singleSubstComp rₜ σ′ A′))
                                    [σA′[r]]′ [σA′[r]] [σA′r≡σ′A′r]′
      ⊢σA′r≅σ′A′r = escapeEq [σA′[r]] [σA′r≡σ′A′r]
      [σprᵣ≡σ′prᵣ] =
        neuEqTerm [σA′[r]] (prodrecₙ yₜ) (prodrecₙ yₜ)
          (prodrecⱼ ⊢σF′ ⊢σG′ ⊢σA′
             (conv ⊢r (sym (≅-eq ⊢σΣ′≡σ′Σ′))) ⊢σu′ ok)
          (conv
             (prodrecⱼ ⊢σF′ ⊢σG′ ⊢σ′A′
                 (conv ⊢r (sym (≅-eq ⊢σΣ′≡σ′Σ′))) ⊢σ′u′ ok)
             (sym (≅-eq ⊢σA′r≅σ′A′r)))
          σprᵣ~σ′prᵣ

      [σprₚ≡σprᵣ]′ = convEqTerm₂ [A[t]] [A[p]] [At≡Ap] [σprₚ≡σprᵣ]
      [σAt≡σA′r] = transEq [A[t]] [A[p]] [σA′[r]] [At≡Ap] [σAp≡σA′r]
      [σprᵣ≡σ′prᵣ]′ = convEqTerm₂ [A[t]] [σA′[r]] [σAt≡σA′r] [σprᵣ≡σ′prᵣ]
      [σ′Σ] = proj₁ (unwrap [Σ] ⊢Δ [σ′])
      [σ′Σ≡σ′Σ′] = [Σ≡Σ′] ⊢Δ [σ′]
      [t′]′ = convTerm₂ [σ′Σ] [σ′Σ′] [σ′Σ≡σ′Σ′] [t′]
      [A[t′]]′ = proj₁ (unwrap [A] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]′))
      [At′≡A′t′]′ = [A≡A′] {σ = consSubst σ′ t′} ⊢Δ ([σ′] , [t′]′)
      [At≡At′]′ = proj₂ (unwrap [A] {σ = consSubst σ t} ⊢Δ ([σ] , [t]))
                          {σ′ = consSubst σ′ t′} ([σ′] , [t′]′) ([σ≡σ′] , [t≡t′])
      [At≡A′t′]′ = transEq [A[t]]′ [A[t′]]′ [A′[t′]]′ [At≡At′]′ [At′≡A′t′]′
      [At≡A′t′] = irrelevanceEq″ (PE.sym (singleSubstComp t σ A))
                                 (PE.sym (singleSubstComp t′ σ′ A′))
                                 [A[t]]′ [A[t]] [At≡A′t′]′
      [prₜ′≡prᵣ]′ = convEqTerm₂ [A[t]] [A′[t′]] [At≡A′t′] [prₜ′≡prᵣ]
  in  [A[t]] , transEqTerm [A[t]] [prₜ≡prₚ]
                           (transEqTerm [A[t]] [σprₚ≡σprᵣ]′
                           (transEqTerm [A[t]] [σprᵣ≡σ′prᵣ]′ (symEqTerm [A[t]] [prₜ′≡prᵣ]′)))

prodrecCong
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (Σₜ₌ _ _ _ _ (ne _) prodₙ _ _ _ ())
prodrecCong
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (Σₜ₌ _ _ _ _ prodₙ (ne _) _ _ _ ())
prodrecCong
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (Σₜ _ d _ prodₙ _) _ (Σₜ₌ _ _ d₁ _ (ne x) _ _ _ _ _) =
  ⊥-elim (prod≢ne x (whrDet*Term (redₜ d , prodₙ) (redₜ d₁ , ne x)))
prodrecCong
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⊢Σ≡Σ′ _ _ _ _ _
  (Σₜ _ d′ _ (ne x) _) (Σₜ₌ _ _ _ d′₁ _ prodₙ _ _ _ _) =
  ⊥-elim
    (prod≢ne x
       (whrDet*Term (conv* (redₜ d′₁) ⊢Σ≡Σ′ , prodₙ) (redₜ d′ , ne x)))
prodrecCong
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (Σₜ _ d _ (ne x) _) _ (Σₜ₌ _ _ d₁ _ prodₙ _ _ _ _ _) =
  ⊥-elim (prod≢ne x (whrDet*Term (redₜ d₁ , prodₙ) (redₜ d , ne x)))
prodrecCong
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⊢Σ≡Σ′ _ _ _ _ _
  (Σₜ _ d′ _ prodₙ _) (Σₜ₌ _ _ _ d′₁ _ (ne x) _ _ _ _) =
  ⊥-elim
    (prod≢ne x
       (whrDet*Term (redₜ d′ , prodₙ)
          (conv* (redₜ d′₁) ⊢Σ≡Σ′ , ne x)))


-- Validity of product recursion
prodrecᵛ :
  ∀ {Γ : Con Term n} {F G A t u l} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σʷ p , q ▷ F ▹ G / [Γ])
  ([A] : Γ ∙ (Σ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G])
  ([Aₜ] : Γ ⊩ᵛ⟨ l ⟩ A [ t ]₀ / [Γ])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ p , q ▷ F ▹ G / [Γ] / [Σ])
  ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊]) →
  Γ ⊩ᵛ⟨ l ⟩ prodrec r p q′ A t u ∷ A [ t ]₀ / [Γ] / [Aₜ]
prodrecᵛ {n = n} {q = q} {r = r} {Γ = Γ} {F} {G} {A} {t} {u} {l}
         [Γ] [F] [G] [Σ] [A] [A₊] [Aₜ] [t] [u]
         {k} {Δ} {σ} ⊢Δ [σ] =
  let ok = ⊩ᵛΠΣ→ΠΣ-allowed [Σ]
      [Σ]′ = Σᵛ {F = F} {G = G} {q = q} {m = 𝕨} [Γ] [F] [G] ok
      [A]′ = S.irrelevance {A = A} (_∙_ {A = Σʷ _ , q ▷ F ▹ G} [Γ] [Σ])
               ([Γ] ∙ [Σ]′) [A]
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σt]′ = irrelevanceTerm (proj₁ (unwrap [Σ] ⊢Δ [σ])) (proj₁ (unwrap [Σ]′ ⊢Δ [σ])) [σt]
      [A[t]] , [σpr] = prodrecTerm
        {r = r} {F = F} {G} {A} {t [ σ ]} {u} {σ}
        [Γ] [F] [G] ok [A]′ [A₊] [u] ⊢Δ [σ] [σt]′
      [σAₜ] = proj₁ (unwrap [Aₜ] ⊢Δ [σ])
  in  irrelevanceTerm′ (PE.sym (singleSubstLift A t)) [A[t]] [σAₜ] [σpr]
      , λ {σ′} [σ′] [σ≡σ′] →
        let A₊ = A [ prodʷ _ (var (x0 +1)) (var x0) ]↑²
            [σ′t] = proj₁ ([t] ⊢Δ [σ′])
            [σ′t]′ = irrelevanceTerm (proj₁ (unwrap [Σ] ⊢Δ [σ′])) (proj₁ (unwrap [Σ]′ ⊢Δ [σ′])) [σ′t]
            [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σt≡σ′t]′ = irrelevanceEqTerm (proj₁ (unwrap [Σ] ⊢Δ [σ])) (proj₁ (unwrap [Σ]′ ⊢Δ [σ])) [σt≡σ′t]
            [σΣ≡σ′Σ] = proj₂ (unwrap [Σ]′ ⊢Δ [σ]) [σ′] [σ≡σ′]
            ⊢σΣ≡σ′Σ = ≅-eq (escapeEq (proj₁ (unwrap [Σ]′ ⊢Δ [σ])) [σΣ≡σ′Σ])
            [A[t]]′ , [σpr≡σ′pr] = prodrecCong
              {q = q} {r = r} {F = F} {F} {G} {G} {A} {A}
              {t [ σ ]} {t [ σ′ ]} {u} {u} {σ} {σ′}
              [Γ] [F] [F] (reflᵛ {A = F} [Γ] [F])
              [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G]) ok
              [A]′ [A]′ (reflᵛ {Γ = Γ ∙ (Σʷ _ , q ▷ F ▹ G)} {A = A}
                           ([Γ] ∙ [Σ]′) [A]′)
              [A₊] [A₊] (reflᵛ {Γ = Γ ∙ F ∙ G} {A = A₊}
                           ([Γ] ∙ [F] ∙ [G]) [A₊])
              [u] [u] (reflᵗᵛ {Γ = Γ ∙ F ∙ G} {A = A₊} {t = u}
                         ([Γ] ∙ [F] ∙ [G]) [A₊] [u])
              ⊢σΣ≡σ′Σ ⊢Δ [σ] [σ′] [σ≡σ′] [σt]′ [σ′t]′ [σt≡σ′t]′
        in  irrelevanceEqTerm′ (PE.sym (singleSubstLift A t))
                               [A[t]]′ [σAₜ] [σpr≡σ′pr]

prodrec-congᵛ :
  ∀ {F F′ G G′ A A′ t t′ u u′ l} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ])
  ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] / [F])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([G′] : Γ ∙ F′ ⊩ᵛ⟨ l ⟩ G′ / [Γ] ∙ [F′])
  ([G≡G′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] ∙ [F] / [G])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σʷ p , q ▷ F ▹ G / [Γ])
  ([Σ′] : Γ ⊩ᵛ⟨ l ⟩ Σʷ p , q ▷ F′ ▹ G′ / [Γ])
  ([Σ≡Σ′] : Γ ⊩ᵛ⟨ l ⟩ Σʷ p , q ▷ F ▹ G ≡ Σʷ p , q ▷ F′ ▹ G′ / [Γ] / [Σ])
  ([A] : Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A′] : Γ ∙ (Σʷ p , q ▷ F′ ▹ G′) ⊩ᵛ⟨ l ⟩ A′ / [Γ] ∙ [Σ′])
  ([A≡A′] : Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A ≡ A′ / [Γ] ∙ [Σ] / [A])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G])
  ([A′₊] : Γ ∙ F′ ∙ G′ ⊩ᵛ⟨ l ⟩ A′ [ prodʷ p (var x1) (var x0) ]↑² /
             [Γ] ∙ [F′] ∙ [G′])
  ([A₊≡A′₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prodʷ p (var x1) (var x0) ]↑² ≡
                A′ [ prodʷ p (var x1) (var x0) ]↑² /
                [Γ] ∙ [F] ∙ [G] / [A₊])
  ([Aₜ] : Γ ⊩ᵛ⟨ l ⟩ A [ t ]₀ / [Γ])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σʷ p , q ▷ F ▹ G / [Γ] / [Σ])
  ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Σʷ p , q ▷ F′ ▹ G′ / [Γ] / [Σ′])
  ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Σʷ p , q ▷ F ▹ G / [Γ] / [Σ])
  ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊])
  ([u′] : Γ ∙ F′ ∙ G′ ⊩ᵛ⟨ l ⟩ u′ ∷
            A′ [ prodʷ p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F′] ∙ [G′] / [A′₊])
  ([u≡u′] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷
              A [ prodʷ p (var x1) (var x0) ]↑² /
              [Γ] ∙ [F] ∙ [G] / [A₊]) →
  Γ ⊩ᵛ⟨ l ⟩ prodrec r p q′ A t u ≡ prodrec r p q′ A′ t′ u′ ∷
    A [ t ]₀ / [Γ] / [Aₜ]
prodrec-congᵛ {Γ = Γ} {q = q} {r = r}
              {F = F} {F′} {G} {G′} {A} {A′} {t} {t′} {u} {u′}
              [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] [Σ] [Σ′] [Σ≡Σ′]
              [A] [A′] [A≡A′] [A₊] [A′₊] [A₊≡A′₊] [Aₜ]
              [t] [t′] [t≡t′] [u] [u′] [u≡u′] {k} {Δ} {σ} ⊢Δ [σ] =
  let ok = ⊩ᵛΠΣ→ΠΣ-allowed [Σ]
      [Σ]′ = Σᵛ {F = F} {G = G} {q = q} {m = 𝕨} [Γ] [F] [G] ok
      [Σ′]′ = Σᵛ {F = F′} {G = G′} {q = q} {m = 𝕨} [Γ] [F′] [G′] ok
      [A]′ = S.irrelevance {A = A} (_∙_ {A = Σʷ _ , q ▷ F ▹ G} [Γ] [Σ])
               ([Γ] ∙ [Σ]′) [A]
      [A′]′ = S.irrelevance {A = A′}
                (_∙_ {A = Σʷ _ , q ▷ F′ ▹ G′} [Γ] [Σ′])
                ([Γ] ∙ [Σ′]′) [A′]
      [A≡A′]′ = S.irrelevanceEq {A = A} {B = A′}
                  (_∙_ {A = Σʷ _ , q ▷ F ▹ G} [Γ] [Σ])
                  (_∙_ {A = Σʷ _ , q ▷ F ▹ G} [Γ] [Σ]′)
                  [A] [A]′ [A≡A′]
      [t]′ = S.irrelevanceTerm {A = Σʷ _ , q ▷ F ▹ G} {t = t}
               [Γ] [Γ] [Σ] [Σ]′ [t]
      [t′]′ = S.irrelevanceTerm {A = Σʷ _ , q ▷ F′ ▹ G′} {t = t′}
                [Γ] [Γ] [Σ′] [Σ′]′ [t′]
      [σt] = proj₁ ([t]′ ⊢Δ [σ])
      [σt′] = proj₁ ([t′]′ ⊢Δ [σ])
      [σt≡σt′] = [t≡t′] ⊢Δ [σ]
      [σt≡σt′]′ = irrelevanceEqTerm (proj₁ (unwrap [Σ] ⊢Δ [σ])) (proj₁ (unwrap [Σ]′ ⊢Δ [σ])) [σt≡σt′]
      [Σ≡Σ′] = Σ-congᵛ {F = F} {G} {F′} {G′} {q = q}
                 [Γ] [F] [G] [F′] [G′] [F≡F′] [G≡G′] _
      [σΣ≡σΣ′] = [Σ≡Σ′] ⊢Δ [σ]
      ⊢σΣ≡σΣ′ = ≅-eq (escapeEq (proj₁ (unwrap [Σ]′ ⊢Δ [σ])) [σΣ≡σΣ′])
      [Aₜ]′ , [pr≡pr] = prodrecCong
        {F = F} {F′} {G} {G′} {A} {A′} {t [ σ ]} {t′ [ σ ]} {u} {u′}
        [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] ok [A]′ [A′]′ [A≡A′]′
        [A₊] [A′₊] [A₊≡A′₊] [u] [u′] [u≡u′] ⊢σΣ≡σΣ′
        ⊢Δ [σ] [σ] (reflSubst [Γ] ⊢Δ [σ]) [σt] [σt′] [σt≡σt′]′
  in  irrelevanceEqTerm′ (PE.sym (singleSubstLift A t)) [Aₜ]′ (proj₁ (unwrap [Aₜ] ⊢Δ [σ])) [pr≡pr]
