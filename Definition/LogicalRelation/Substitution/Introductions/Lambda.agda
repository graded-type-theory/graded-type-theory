------------------------------------------------------------------------
-- Validity of lambda abstractions.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Lambda
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U hiding (wk)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Weakening R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Application R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    Δ : Con Term m
    σ : Subst m n
    p p₁ p₂ q : M

-- Valid lambda term construction.
lamᵛ : ∀ {F G t l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ G / [Γ] ∙ [F] / [G])
       (ok : Π-allowed p q)
     → Γ ⊩ᵛ⟨ l ⟩ lam p t ∷ Π p , q ▷ F ▹ G / [Γ] / Πᵛ [Γ] [F] [G] ok
lamᵛ
  {n} {Γ = Γ} {p = p} {q = q} {F = F} {G} {t} {l}
  [Γ] [F] [G] [t] ok {k} {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let ⊢F = escape (proj₁ (unwrap [F] ⊢Δ [σ]))
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [ΠFG] = Πᵛ {F = F} {G} {p = p} {q = q} [Γ] [F] [G] ok
      _ , Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext _ =
        extractMaybeEmb (Π-elim (proj₁ (unwrap [ΠFG] ⊢Δ [σ])))
      lamt : ∀ {k : Nat} {Δ : Con Term k} {σ : Subst k n} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ l ⟩ lam p t [ σ ] ∷ Π p , q ▷ F ▹ G [ σ ] / proj₁ (unwrap [ΠFG] ⊢Δ [σ])
      lamt {_} {Δ} {σ} ⊢Δ [σ] =
        let [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
            [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
            ⊢F = escape [σF]
            ⊢wk1F = T.wk (step id) (⊢Δ ∙ ⊢F) ⊢F
            [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) [liftσ])
            ⊢G = escape [σG]
            ⊢wk1G = T.wk (lift (step id)) (⊢Δ ∙ ⊢F ∙ ⊢wk1F) ⊢G
            [σt] = proj₁ ([t] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) [liftσ])
            ⊢t = escapeTerm [σG] [σt]
            wk1t[0] = irrelevanceTerm″
                        PE.refl
                        (PE.sym (wkSingleSubstId (t [ liftSubst σ ])))
                        [σG] [σG] [σt]
            β-red′ :
              ∀ {p′} →
              p PE.≡ p′ →
              _ ⊢ wk1 (lam p (t [ liftSubst σ ])) ∘⟨ p′ ⟩ var x0 ⇒ _ ∷ _
            β-red′ p≡p′ = PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x)
                              (wkSingleSubstId (G [ liftSubst σ ]))
                              (β-red ⊢wk1F ⊢wk1G
                                 (T.wkTerm (lift (step id))
                                    (⊢Δ ∙ ⊢F ∙ ⊢wk1F) ⊢t)
                                 (var₀ ⊢F) p≡p′ ok)
            _ , Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext _ =
              extractMaybeEmb (Π-elim (proj₁ (unwrap [ΠFG] ⊢Δ [σ])))
        in  Πₜ (lam p (t [ liftSubst σ ]))
               (idRedTerm:*: (lamⱼ ⊢F ⊢t ok)) lamₙ
               (≅-η-eq ⊢F (lamⱼ ⊢F ⊢t ok) (lamⱼ ⊢F ⊢t ok) lamₙ lamₙ $
                escapeTermEq [σG] $
                transEqTerm [σG]
                  (proj₂ (redSubstTerm (β-red′ PE.refl) [σG] wk1t[0])) $
                symEqTerm [σG] $
                proj₂ (redSubstTerm (β-red′ PE.refl) [σG] wk1t[0]))
               (λ {_} {ρ₁} {Δ₁} {a} {b} ρ ⊢Δ₁ [a] [b] [a≡b] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                      [a]′ = irrelevanceTerm′ (wk-subst F) ([F]′ ρ ⊢Δ₁)
                                              (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a]
                      [b]′ = irrelevanceTerm′ (wk-subst F) ([F]′ ρ ⊢Δ₁)
                                              (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [b]
                      [a≡b]′ = irrelevanceEqTerm′ (wk-subst F) ([F]′ ρ ⊢Δ₁)
                                                  (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a≡b]
                      ⊢F₁′ = escape (proj₁ (unwrap [F] ⊢Δ₁ [ρσ]))
                      ⊢F₁ = escape ([F]′ ρ ⊢Δ₁)
                      [G]₁ = proj₁ (unwrap [G] {σ = liftSubst (ρ₁ •ₛ σ)} (⊢Δ₁ ∙ ⊢F₁′)
                                        (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                      [G]₁′ = irrelevanceΓ′
                                (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                                (PE.sym (wk-subst-lift G)) [G]₁
                      ⊢G₁ = escape [G]₁′
                      [t]′ = irrelevanceTermΓ″
                               (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                               (PE.sym (wk-subst-lift G))
                               (PE.sym (wk-subst-lift t))
                               [G]₁ [G]₁′
                               (proj₁ ([t] (⊢Δ₁ ∙ ⊢F₁′)
                                           (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                      ⊢a = escapeTerm ([F]′ ρ ⊢Δ₁) [a]
                      ⊢b = escapeTerm ([F]′ ρ ⊢Δ₁) [b]
                      ⊢t = escapeTerm [G]₁′ [t]′
                      G[a]′ = proj₁ (unwrap [G] {σ = consSubst (ρ₁ •ₛ σ) a} ⊢Δ₁ ([ρσ] , [a]′))
                      G[a] = [G]′ ρ ⊢Δ₁ [a]
                      t[a] = irrelevanceTerm″
                               (PE.sym (singleSubstWkComp a σ G))
                               (PE.sym (singleSubstWkComp a σ t))
                               G[a]′ G[a]
                               (proj₁ ([t] ⊢Δ₁ ([ρσ] , [a]′)))
                      G[b]′ = proj₁ (unwrap [G] {σ = consSubst (ρ₁ •ₛ σ) b} ⊢Δ₁ ([ρσ] , [b]′))
                      G[b] = [G]′ ρ ⊢Δ₁ [b]
                      t[b] = irrelevanceTerm″
                               (PE.sym (singleSubstWkComp b σ G))
                               (PE.sym (singleSubstWkComp b σ t))
                               G[b]′ G[b]
                               (proj₁ ([t] ⊢Δ₁ ([ρσ] , [b]′)))
                      lamt∘a≡t[a] = proj₂ $
                                    redSubstTerm
                                      (β-red ⊢F₁ ⊢G₁ ⊢t ⊢a PE.refl ok)
                                      G[a] t[a]
                      G[a]≡G[b] = G-ext ρ ⊢Δ₁ [a] [b] [a≡b]
                      t[a]≡t[b] = irrelevanceEqTerm″
                                    (PE.sym (singleSubstWkComp a σ t))
                                    (PE.sym (singleSubstWkComp b σ t))
                                    (PE.sym (singleSubstWkComp a σ G))
                                    G[a]′ G[a]
                                    (proj₂ ([t] ⊢Δ₁ ([ρσ] , [a]′)) ([ρσ] , [b]′)
                                                (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]′))
                      t[b]≡lamt∘b =
                        convEqTerm₂ G[a] G[b] G[a]≡G[b] $
                        symEqTerm G[b] $ proj₂ $
                        redSubstTerm (β-red ⊢F₁ ⊢G₁ ⊢t ⊢b PE.refl ok)
                          G[b] t[b]
                  in  transEqTerm G[a] lamt∘a≡t[a]
                                  (transEqTerm G[a] t[a]≡t[b] t[b]≡lamt∘b))
               (λ {_} {ρ₁} {Δ₁} {a} ρ ⊢Δ₁ [a] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                      [a]′ = irrelevanceTerm′ (wk-subst F) ([F]′ ρ ⊢Δ₁)
                                              (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a]
                      ⊢F₁′ = escape (proj₁ (unwrap [F] ⊢Δ₁ [ρσ]))
                      ⊢F₁ = escape ([F]′ ρ ⊢Δ₁)
                      [G]₁ = proj₁ (unwrap [G] {σ = liftSubst (ρ₁ •ₛ σ)} (⊢Δ₁ ∙ ⊢F₁′)
                                        (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                      [G]₁′ = irrelevanceΓ′
                                (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                                (PE.sym (wk-subst-lift G)) [G]₁
                      ⊢G₁ = escape [G]₁′
                      [t]′ = irrelevanceTermΓ″
                               (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                               (PE.sym (wk-subst-lift G))
                               (PE.sym (wk-subst-lift t))
                               [G]₁ [G]₁′
                               (proj₁ ([t] (⊢Δ₁ ∙ ⊢F₁′)
                                           (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                      ⊢a = escapeTerm ([F]′ ρ ⊢Δ₁) [a]
                      ⊢t = escapeTerm [G]₁′ [t]′
                      G[a]′ = proj₁ (unwrap [G] {σ = consSubst (ρ₁ •ₛ σ) a} ⊢Δ₁ ([ρσ] , [a]′))
                      G[a] = [G]′ ρ ⊢Δ₁ [a]
                      t[a] = irrelevanceTerm″ (PE.sym (singleSubstWkComp a σ G))
                                               (PE.sym (singleSubstWkComp a σ t))
                                               G[a]′ G[a]
                                               (proj₁ ([t] ⊢Δ₁ ([ρσ] , [a]′)))

                  in  proj₁ $
                      redSubstTerm (β-red ⊢F₁ ⊢G₁ ⊢t ⊢a PE.refl ok)
                        G[a] t[a])
  in  lamt ⊢Δ [σ]
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         let [liftσ′] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′]
             _ , Bᵣ F″ G″ D″ ⊢F″ ⊢G″ A≡A″ [F]″ [G]″ G-ext′ _ =
               extractMaybeEmb (Π-elim (proj₁ (unwrap [ΠFG] ⊢Δ [σ′])))
             ⊢F′ = escape (proj₁ (unwrap [F] ⊢Δ [σ′]))
             [G]₁ = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) [liftσ])
             [G]₁′ = proj₁ (unwrap [G] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F′) [liftσ′])
             [σΠFG≡σ′ΠFG] = proj₂ (unwrap [ΠFG] ⊢Δ [σ]) [σ′] [σ≡σ′]
             ⊢t = escapeTerm [G]₁ (proj₁ ([t] (⊢Δ ∙ ⊢F) [liftσ]))
             ⊢t′ = escapeTerm [G]₁′ (proj₁ ([t] (⊢Δ ∙ ⊢F′) [liftσ′]))
             neuVar = neuTerm ([F]′ (step id) (⊢Δ ∙ ⊢F))
                              (var x0) (var₀ ⊢F)
                              (~-var (var₀ ⊢F))
             σlamt∘a≡σ′lamt∘a : ∀ {ℓ} {ρ : Wk ℓ k} {Δ₁ a p₁ p₂}
                 → ([ρ] : ρ ∷ Δ₁ ⊇ Δ) (⊢Δ₁ : ⊢ Δ₁)
                 → ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ U.wk ρ (F [ σ ]) / [F]′ [ρ] ⊢Δ₁)
                 → p PE.≡ p₁
                 → p PE.≡ p₂
                 → Δ₁ ⊩⟨ l ⟩ U.wk ρ (lam p t [ σ ]) ∘⟨ p₁ ⟩ a
                           ≡ U.wk ρ (lam p t [ σ′ ]) ∘⟨ p₂ ⟩ a
                           ∷ U.wk (lift ρ) (G [ liftSubst σ ]) [ a ]₀
                           / [G]′ [ρ] ⊢Δ₁ [a]
             σlamt∘a≡σ′lamt∘a {_} {ρ₁} {Δ₁} {a} ρ ⊢Δ₁ [a] p≡p₁ p≡p₂ =
                let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                    [ρσ′] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ′]
                    [ρσ≡ρσ′] = wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ ρ [σ] [σ≡σ′]
                    ⊢F₁′ = escape (proj₁ (unwrap [F] ⊢Δ₁ [ρσ]))
                    ⊢F₁ = escape ([F]′ ρ ⊢Δ₁)
                    ⊢F₂′ = escape (proj₁ (unwrap [F] ⊢Δ₁ [ρσ′]))
                    ⊢F₂ = escape ([F]″ ρ ⊢Δ₁)
                    [σF≡σ′F] = proj₂ (unwrap [F] ⊢Δ₁ [ρσ]) [ρσ′] [ρσ≡ρσ′]
                    [a]′ = irrelevanceTerm′ (wk-subst F) ([F]′ ρ ⊢Δ₁)
                                            (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a]
                    [a]″ = convTerm₁ (proj₁ (unwrap [F] ⊢Δ₁ [ρσ]))
                                      (proj₁ (unwrap [F] ⊢Δ₁ [ρσ′]))
                                      [σF≡σ′F] [a]′
                    ⊢a = escapeTerm ([F]′ ρ ⊢Δ₁) [a]
                    ⊢a′ = escapeTerm ([F]″ ρ ⊢Δ₁)
                            (irrelevanceTerm′ (PE.sym (wk-subst F))
                                              (proj₁ (unwrap [F] ⊢Δ₁ [ρσ′]))
                                              ([F]″ ρ ⊢Δ₁)
                                              [a]″)
                    G[a]′ = proj₁ (unwrap [G] {σ = consSubst (ρ₁ •ₛ σ) a} ⊢Δ₁ ([ρσ] , [a]′))
                    G[a]₁′ = proj₁ (unwrap [G] {σ = consSubst (ρ₁ •ₛ σ′) a} ⊢Δ₁ ([ρσ′] , [a]″))
                    G[a] = [G]′ ρ ⊢Δ₁ [a]
                    G[a]″ = [G]″ ρ ⊢Δ₁
                                   (irrelevanceTerm′ (PE.sym (wk-subst F))
                                                     (proj₁ (unwrap [F] ⊢Δ₁ [ρσ′]))
                                                     ([F]″ ρ ⊢Δ₁)
                                                     [a]″)
                    [σG[a]≡σ′G[a]] = irrelevanceEq″
                                       (PE.sym (singleSubstWkComp a σ G))
                                       (PE.sym (singleSubstWkComp a σ′ G))
                                       G[a]′ G[a]
                                       (proj₂ (unwrap [G] ⊢Δ₁ ([ρσ] , [a]′))
                                              ([ρσ′] , [a]″)
                                              (consSubstSEq {t = a} {A = F}
                                                [Γ] ⊢Δ₁ [ρσ] [ρσ≡ρσ′] [F] [a]′))
                    [G]₁ = proj₁ (unwrap [G] {σ = liftSubst (ρ₁ •ₛ σ)} (⊢Δ₁ ∙ ⊢F₁′)
                                      (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]))
                    [G]₁′ = irrelevanceΓ′
                              (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                              (PE.sym (wk-subst-lift G)) [G]₁
                    [G]₂ = proj₁ (unwrap [G] {σ = liftSubst (ρ₁ •ₛ σ′)} (⊢Δ₁ ∙ ⊢F₂′)
                                      (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ′]))
                    [G]₂′ = irrelevanceΓ′
                              (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                              (PE.sym (wk-subst-lift G)) [G]₂
                    [t]′ = irrelevanceTermΓ″
                             (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                             (PE.sym (wk-subst-lift G)) (PE.sym (wk-subst-lift t))
                             [G]₁ [G]₁′
                             (proj₁ ([t] (⊢Δ₁ ∙ ⊢F₁′)
                                         (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ])))
                    [t]″ = irrelevanceTermΓ″
                              (PE.cong (λ x → _ ∙ x) (PE.sym (wk-subst F)))
                              (PE.sym (wk-subst-lift G)) (PE.sym (wk-subst-lift t))
                              [G]₂ [G]₂′
                              (proj₁ ([t] (⊢Δ₁ ∙ ⊢F₂′)
                                          (liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ′])))
                    ⊢t = escapeTerm [G]₁′ [t]′
                    ⊢t′ = escapeTerm [G]₂′ [t]″
                    t[a] = irrelevanceTerm″
                             (PE.sym (singleSubstWkComp a σ G))
                             (PE.sym (singleSubstWkComp a σ t)) G[a]′ G[a]
                             (proj₁ ([t] ⊢Δ₁ ([ρσ] , [a]′)))
                    t[a]′ = irrelevanceTerm″
                              (PE.sym (singleSubstWkComp a σ′ G))
                              (PE.sym (singleSubstWkComp a σ′ t))
                              G[a]₁′ G[a]″
                              (proj₁ ([t] ⊢Δ₁ ([ρσ′] , [a]″)))
                    ⊢G₁ = escape [G]₁′
                    ⊢G₂ = escape [G]₂′
                    [σlamt∘a≡σt[a]] = proj₂ $
                                      redSubstTerm
                                        (β-red ⊢F₁ ⊢G₁ ⊢t ⊢a p≡p₁ ok)
                                        G[a] t[a]
                    [σ′t[a]≡σ′lamt∘a] =
                      convEqTerm₂ G[a] G[a]″ [σG[a]≡σ′G[a]] $
                      symEqTerm G[a]″ $ proj₂ $
                      redSubstTerm (β-red ⊢F₂ ⊢G₂ ⊢t′ ⊢a′ p≡p₂ ok)
                        G[a]″ t[a]′
                    [σt[a]≡σ′t[a]] = irrelevanceEqTerm″
                                       (PE.sym (singleSubstWkComp a σ t))
                                       (PE.sym (singleSubstWkComp a σ′ t))
                                       (PE.sym (singleSubstWkComp a σ G))
                                       G[a]′ G[a]
                                       (proj₂ ([t] ⊢Δ₁ ([ρσ] , [a]′))
                                              ([ρσ′] , [a]″)
                                              (consSubstSEq {t = a} {A = F}
                                                [Γ] ⊢Δ₁ [ρσ] [ρσ≡ρσ′] [F] [a]′))
                in  transEqTerm G[a] [σlamt∘a≡σt[a]]
                                (transEqTerm G[a] [σt[a]≡σ′t[a]]
                                             [σ′t[a]≡σ′lamt∘a])
             ⊢λσt = lamⱼ {p = p} {q = q} ⊢F ⊢t ok
             ⊢λσ′t = conv (lamⱼ {p = p} {q = q} ⊢F′ ⊢t′ ok)
                           (sym (≅-eq (escapeEq (proj₁ (unwrap [ΠFG] ⊢Δ [σ]))
                                                [σΠFG≡σ′ΠFG])))
             [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) [liftσ])
         in Πₜ₌ (lam p (t [ liftSubst σ ])) (lam p (t [ liftSubst σ′ ]))
                (idRedTerm:*: ⊢λσt)
                (idRedTerm:*: ⊢λσ′t)
                lamₙ lamₙ
                (≅-η-eq ⊢F ⊢λσt ⊢λσ′t lamₙ lamₙ
                        (escapeTermEq [σG]
                           (irrelevanceEqTerm′
                              (idWkLiftSubstLemma σ G)
                              ([G]′ (step id) (⊢Δ ∙ ⊢F) neuVar)
                              [σG] (σlamt∘a≡σ′lamt∘a (step id) (⊢Δ ∙ ⊢F)
                                      neuVar PE.refl PE.refl))))
                (lamt ⊢Δ [σ])
                (convTerm₂ (proj₁ (unwrap [ΠFG] ⊢Δ [σ]))
                           (proj₁ (unwrap [ΠFG] ⊢Δ [σ′]))
                           [σΠFG≡σ′ΠFG]
                           (lamt ⊢Δ [σ′]))
                λ [ρ] ⊢Δ₁ [a] →
                  σlamt∘a≡σ′lamt∘a [ρ] ⊢Δ₁ [a] PE.refl PE.refl)


-- Reducibility of η-equality under a valid substitution.
η-eqEqTerm : ∀ {m′ n′} {σ : Subst m′ n′} {Γ Δ f g F G l}
             ([Γ] : ⊩ᵛ Γ)
             ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
             (ok : Π-allowed p q)
           → let [ΠFG] = Πᵛ [Γ] [F] [G] ok in
             Γ ∙ F ⊩ᵛ⟨ l ⟩ wk1 f ∘⟨ p ⟩ var x0 ≡ wk1 g ∘⟨ p ⟩ var x0 ∷ G
                          / [Γ] ∙ [F] / [G]
           → (⊢Δ   : ⊢ Δ)
             ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ l ⟩ f [ σ ] ∷ Π p , q ▷ F [ σ ] ▹ (G [ liftSubst σ ])
               / proj₁ (unwrap [ΠFG] ⊢Δ [σ])
           → Δ ⊩⟨ l ⟩ g [ σ ] ∷ Π p , q ▷ F [ σ ] ▹ (G [ liftSubst σ ])
               / proj₁ (unwrap [ΠFG] ⊢Δ [σ])
           → Δ ⊩⟨ l ⟩ f [ σ ] ≡ g [ σ ] ∷ Π p , q ▷ F [ σ ] ▹ (G [ liftSubst σ ])
               / proj₁ (unwrap [ΠFG] ⊢Δ [σ])
η-eqEqTerm
  {p = p} {q = q} {m′ = m′} {σ = σ} {Γ = Γ} {Δ = Δ}
  {f} {g} {F} {G} [Γ] [F] [G] ok [f0≡g0] ⊢Δ [σ]
  [σf]@(Πₜ f₁ [ ⊢t , ⊢u , d ] funcF f≡f [f] [f]₁)
  [σg]@(Πₜ g₁ [ ⊢t₁ , ⊢u₁ , d₁ ] funcG g≡g [g] [g]₁) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ ⊢t₁ , ⊢u₁ , d₁ ]
      [ΠFG] = Πᵛ [Γ] [F] [G] ok
      [σΠFG] = proj₁ (unwrap [ΠFG] ⊢Δ [σ])
      _ , Bᵣ F′ G′ D′ ⊢F ⊢G A≡A [F]′ [G]′ G-ext ok =
        extractMaybeEmb (Π-elim [σΠFG])
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [wk1F] = wk (step id) (⊢Δ ∙ ⊢F) [σF]
      var0′ = var₀ ⊢F
      var0 = neuTerm [wk1F] (var x0) var0′ (~-var var0′)
      var0≡0 = neuEqTerm [wk1F] (var x0) (var x0) var0′ var0′ (~-var var0′)
      [σG]′ = [G]′ (step id) (⊢Δ ∙ ⊢F) var0
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      σf0≡σg0 = escapeTermEq [σG]
                                 ([f0≡g0] (⊢Δ ∙ ⊢F)
                                          (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      σf0≡σg0′ =
        PE.subst₂
          (λ (x y : Term (1+ m′)) → Δ ∙ F [ σ ] ⊢ x ≅ y ∷ G [ liftSubst σ ])
          (PE.cong (λ (x : Term (1+ m′)) → x ∘⟨ p ⟩ var x0)
             (PE.trans (subst-wk f) (PE.sym (wk-subst f))))
          (PE.cong (λ (x : Term (1+ m′)) → x ∘⟨ p ⟩ var x0)
             (PE.trans (subst-wk g) (PE.sym (wk-subst g))))
          σf0≡σg0
      ⊢ΠFG = escape [σΠFG]
      f≡f₁′ = proj₂ (redSubst*Term d [σΠFG] (Πₜ f₁ (idRedTerm:*: ⊢u) funcF f≡f [f] [f]₁))
      g≡g₁′ = proj₂ (redSubst*Term d₁ [σΠFG] (Πₜ g₁ (idRedTerm:*: ⊢u₁) funcG g≡g [g] [g]₁))
  in Πₜ₌ f₁ g₁ [d] [d′] funcF funcG
          (≅-η-eq ⊢F ⊢u ⊢u₁ funcF funcG $
           ≅ₜ-trans
             (≅ₜ-sym $
              escapeTermEq [σG] $
              irrelevanceEqTerm′ (cons0wkLift1-id σ G) [σG]′ [σG] $
              app-congTerm [wk1F] [σG]′
                (wk (step id) (⊢Δ ∙ ⊢F) [σΠFG])
                (wkEqTerm (step id) (⊢Δ ∙ ⊢F) [σΠFG] f≡f₁′)
                var0 var0 var0≡0) $
           ≅ₜ-trans σf0≡σg0′ $
           escapeTermEq [σG] $
           irrelevanceEqTerm′ (cons0wkLift1-id σ G) [σG]′ [σG] $
           app-congTerm [wk1F] [σG]′
             (wk (step id) (⊢Δ ∙ ⊢F) [σΠFG])
             (wkEqTerm (step id) (⊢Δ ∙ ⊢F) [σΠFG] g≡g₁′)
             var0 var0 var0≡0)
          (Πₜ f₁ [d] funcF f≡f [f] [f]₁)
          (Πₜ g₁ [d′] funcG g≡g [g] [g]₁)
          (λ {m} {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
             let [F]″ = proj₁ (unwrap [F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))
                 [a]′ = irrelevanceTerm′
                          (wk-subst F) ([F]′ [ρ] ⊢Δ₁)
                          [F]″ [a]
                 fEq = PE.cong (λ (x : Term m) → x ∘⟨ p ⟩ a)
                               (PE.trans (subst-wk {ρ = step id} {σ = consSubst (ρ •ₛ σ) a} f)
                                         (PE.sym (wk-subst {ρ = ρ} {σ = σ} f)))
                 gEq = PE.cong (λ (x : Term m) → x ∘⟨ p ⟩ a)
                               (PE.trans (subst-wk {ρ = step id} {σ = consSubst (ρ •ₛ σ) a} g)
                                         (PE.sym (wk-subst {ρ = ρ} {σ = σ} g)))
                 GEq = PE.sym (PE.trans (subst-wk (G [ liftSubst σ ]))
                                        (PE.trans (substCompEq G)
                                                  (cons-wk-subst ρ σ a G)))
                 f≡g = irrelevanceEqTerm″ fEq gEq GEq
                         (proj₁ (unwrap [G] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] , [a]′)))
                        ([G]′ [ρ] ⊢Δ₁ [a])
                        ([f0≡g0] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] , [a]′))
                 [ρσΠFG] = wk [ρ] ⊢Δ₁ [σΠFG]
                 [f]′ : Δ ⊩⟨ _ ⟩ f₁ ∷ Π p , q ▷ F′ ▹ G′ / [σΠFG]
                 [f]′ = Πₜ f₁ (idRedTerm:*: ⊢u) funcF f≡f [f] [f]₁
                 [ρf]′ = wkTerm [ρ] ⊢Δ₁ [σΠFG] [f]′
                 [g]′ : Δ ⊩⟨ _ ⟩ g₁ ∷ Π p , q ▷ F′ ▹ G′ / [σΠFG]
                 [g]′ = Πₜ g₁ (idRedTerm:*: ⊢u₁) funcG g≡g [g] [g]₁
                 [ρg]′ = wkTerm [ρ] ⊢Δ₁ [σΠFG] [g]′
                 [f∘u] = appTerm ([F]′ [ρ] ⊢Δ₁) ([G]′ [ρ] ⊢Δ₁ [a])
                           [ρσΠFG] [ρf]′ [a]
                 [g∘u] = appTerm ([F]′ [ρ] ⊢Δ₁) ([G]′ [ρ] ⊢Δ₁ [a])
                           [ρσΠFG] [ρg]′ [a]
                 d′ = conv* d (ΠΣ-cong ⊢F (refl ⊢F) (refl ⊢G) ok)
                 d₁′ = conv* d₁ (ΠΣ-cong ⊢F (refl ⊢F) (refl ⊢G) ok)
                 [tu≡fu] = proj₂ (redSubst*Term (app-subst* (wkRed*Term [ρ] ⊢Δ₁ d′)
                                                            (escapeTerm ([F]′ [ρ] ⊢Δ₁) [a]))
                                                ([G]′ [ρ] ⊢Δ₁ [a]) [f∘u])
                 [gu≡t′u] = proj₂ (redSubst*Term (app-subst* (wkRed*Term [ρ] ⊢Δ₁ d₁′)
                                                             (escapeTerm ([F]′ [ρ] ⊢Δ₁) [a]))
                                                 ([G]′ [ρ] ⊢Δ₁ [a]) [g∘u])
                 [G[a]] = [G]′ [ρ] ⊢Δ₁ [a]
                 [ρσf] = wkTerm [ρ] ⊢Δ₁ [σΠFG] [σf]
                 [ρσg] = wkTerm [ρ] ⊢Δ₁ [σΠFG] [σg]
                 [fu≡fu′] = app-congTerm ([F]′ [ρ] ⊢Δ₁) ([G]′ [ρ] ⊢Δ₁ [a]) [ρσΠFG]
                                         (reflEqTerm [ρσΠFG] [ρσf])
                                         [a] [a] (reflEqTerm ([F]′ [ρ] ⊢Δ₁) [a])
                 [gu≡gu′] = app-congTerm ([F]′ [ρ] ⊢Δ₁) ([G]′ [ρ] ⊢Δ₁ [a]) [ρσΠFG]
                                         (reflEqTerm [ρσΠFG] [ρσg])
                                         [a] [a] (reflEqTerm ([F]′ [ρ] ⊢Δ₁) [a])
             in  transEqTerm [G[a]] (symEqTerm [G[a]] [tu≡fu])
                             (transEqTerm [G[a]] [fu≡fu′]
                             (transEqTerm [G[a]] f≡g
                             (transEqTerm [G[a]] [gu≡gu′] [gu≡t′u]))))

-- Validity of η-equality.
η-eqᵛ : ∀ {Γ : Con Term n} {f g F G l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        (ok : Π-allowed p q)
      → let [ΠFG] = Πᵛ [Γ] [F] [G] ok in
        Γ ⊩ᵛ⟨ l ⟩ f ∷ Π p , q ▷ F ▹ G / [Γ] / [ΠFG]
      → Γ ⊩ᵛ⟨ l ⟩ g ∷ Π p , q ▷ F ▹ G / [Γ] / [ΠFG]
      → Γ ∙ F ⊩ᵛ⟨ l ⟩ wk1 f ∘⟨ p ⟩ var x0 ≡ wk1 g ∘⟨ p ⟩ var x0 ∷ G
                     / [Γ] ∙ [F] / [G]
      → Γ ⊩ᵛ⟨ l ⟩ f ≡ g ∷ Π p , q ▷ F ▹ G / [Γ] / [ΠFG]
η-eqᵛ {f = f} {g} [Γ] [F] [G] ok [f] [g] [f0≡g0] ⊢Δ [σ] =
   η-eqEqTerm {f = f} {g} [Γ] [F] [G] ok [f0≡g0] ⊢Δ [σ]
     (proj₁ ([f] ⊢Δ [σ])) (proj₁ ([g] ⊢Δ [σ]))
