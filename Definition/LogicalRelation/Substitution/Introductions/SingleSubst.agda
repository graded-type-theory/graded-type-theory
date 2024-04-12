------------------------------------------------------------------------
-- Validity of substitutions of single variables
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.SingleSubst
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Weakening R using (id)
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Conversion R
open import Definition.LogicalRelation.Substitution.Weakening R

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Validity of substitution of single variable in types.
substS : ∀ {F G t l l′} ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
         ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
         ([t] : Γ ⊩ᵛ⟨ l′ ⟩ t ∷ F / [Γ] / [F])
       → Γ ⊩ᵛ⟨ l ⟩ G [ t ]₀ / [Γ]
substS {F = F} {G} {t} [Γ] [F] [G] [t] = wrap λ {_} {_} {σ} ⊢Δ [σ] →
  let Geq = substConsId G
      G[t] = proj₁ (unwrap [G] ⊢Δ ([σ] , (proj₁ ([t] ⊢Δ [σ]))))
      G[t]′ = irrelevance′ Geq G[t]
  in  G[t]′
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         irrelevanceEq″ Geq
                         (substConsId G)
                         G[t] G[t]′
                         (proj₂ (unwrap [G] ⊢Δ
                                     ([σ] , proj₁ ([t] ⊢Δ [σ])))
                                     ([σ′] , proj₁ ([t] ⊢Δ [σ′]))
                                     (([σ≡σ′] , (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])))))


-- Validity of substitution of single variable in type equality.
substSEq : ∀ {F F′ G G′ t t′ l l′} ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
           ([F′] : Γ ⊩ᵛ⟨ l′ ⟩ F′ / [Γ])
           ([F≡F′] : Γ ⊩ᵛ⟨ l′ ⟩ F ≡ F′ / [Γ] / [F])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
           ([G′] : Γ ∙ F′ ⊩ᵛ⟨ l ⟩ G′ / [Γ] ∙ [F′])
           ([G≡G′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] ∙ [F] / [G])
           ([t] : Γ ⊩ᵛ⟨ l′ ⟩ t ∷ F / [Γ] / [F])
           ([t′] : Γ ⊩ᵛ⟨ l′ ⟩ t′ ∷ F′ / [Γ] / [F′])
           ([t≡t′] : Γ ⊩ᵛ⟨ l′ ⟩ t ≡ t′ ∷ F / [Γ] / [F])
         → Γ ⊩ᵛ⟨ l ⟩ G [ t ]₀ ≡ G′ [ t′ ]₀ / [Γ]
                   / substS {F = F} {G} {t} [Γ] [F] [G] [t]
substSEq {F = F} {F′} {G} {G′} {t} {t′}
         [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] [t] [t′] [t≡t′] {σ = σ} ⊢Δ [σ] =
  let Geq = substConsId G
      G′eq = substConsId G′
      G[t] = (proj₁ (unwrap [G] ⊢Δ ([σ] , (proj₁ ([t] ⊢Δ [σ])))))
      G[t]′ = irrelevance′ Geq G[t]
      [t]′ = convᵛ {t = t} {F} {F′} [Γ] [F] [F′] [F≡F′] [t]
      G′[t] = (proj₁ (unwrap [G′] ⊢Δ ([σ] , proj₁ ([t]′ ⊢Δ [σ]))))
      G[t]≡G′[t] = irrelevanceEq′ Geq G[t] G[t]′
                                  ([G≡G′] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      G′[t]≡G′[t′] = irrelevanceEq″ PE.refl G′eq G′[t] G′[t]
                       (proj₂ (unwrap [G′] ⊢Δ ([σ] , proj₁ ([t]′ ⊢Δ [σ])))
                              ([σ] , proj₁ ([t′] ⊢Δ [σ]))
                              (reflSubst [Γ] ⊢Δ [σ] ,
                                convEqᵛ {t = t} {t′} {F} {F′}
                                        [Γ] [F] [F′] [F≡F′] [t≡t′] ⊢Δ [σ]))
      G′[t′] = (proj₁ (unwrap [G′] ⊢Δ ([σ] , proj₁ ([t′] ⊢Δ [σ]))))
      G′[t′]′ = irrelevance′ G′eq G′[t′]
  in  transEq G[t]′ G′[t] G′[t′]′ G[t]≡G′[t] G′[t]≡G′[t′]

-- Validity of substitution of single variable in terms.
substSTerm : ∀ {F G t f l l′} ([Γ] : ⊩ᵛ Γ)
             ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
             ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
             ([f] : Γ ∙ F ⊩ᵛ⟨ l ⟩ f ∷ G / [Γ] ∙ [F] / [G])
             ([t] : Γ ⊩ᵛ⟨ l′ ⟩ t ∷ F / [Γ] / [F])
           → Γ ⊩ᵛ⟨ l ⟩ f [ t ]₀ ∷ G [ t ]₀ / [Γ]
                      / substS {F = F} {G} {t} [Γ] [F] [G] [t]
substSTerm {F = F} {G} {t} {f} [Γ] [F] [G] [f] [t] {σ = σ} ⊢Δ [σ] =
  let prfG = substConsId G
      prff = substConsId f
      G[t] = proj₁ (unwrap [G] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      G[t]′ = irrelevance′ prfG G[t]
      f[t] = proj₁ ([f] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      f[t]′ = irrelevanceTerm″ prfG prff G[t] G[t]′ f[t]
  in  f[t]′
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         irrelevanceEqTerm″
           prff
           (substConsId f)
           prfG G[t] G[t]′
           (proj₂ ([f] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
                  ([σ′] , proj₁ ([t] ⊢Δ [σ′]))
                  ([σ≡σ′] , proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])))

-- Validity of substitution of single lifted variable in types.
subst↑S : ∀ {F G t l l′} ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
          ([t] : Γ ∙ F ⊩ᵛ⟨ l′ ⟩ t ∷ wk1 F / [Γ] ∙ [F]
                              / wk1ᵛ {A = F} {F} [Γ] [F] [F])
        → Γ ∙ F ⊩ᵛ⟨ l ⟩ G [ t ]↑ / [Γ] ∙ [F]
subst↑S {F = F} {G} {t} [Γ] [F] [G] [t] = wrap λ {_} {_} {σ} ⊢Δ [σ] →
  let [wk1F] = wk1ᵛ {A = F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ (unwrap [wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]′ = proj₁ (unwrap [F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]′ = irrelevanceTerm′ (subst-wk F) [σwk1F] [σwk1F]′ (proj₁ ([t] ⊢Δ [σ]))
      G[t] = proj₁ (unwrap [G] {σ = consSubst (tail σ) (t [ σ ])} ⊢Δ
                               (proj₁ [σ] , [t]′))
      G[t]′ = irrelevance′ (substConsTailId {σ = σ} {G} {t}) G[t]
  in  G[t]′
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         let [σ′t] = irrelevanceTerm′ (subst-wk F)
                                      (proj₁ (unwrap [wk1F] {σ = σ′} ⊢Δ [σ′]))
                                      (proj₁ (unwrap [F] ⊢Δ (proj₁ [σ′])))
                                      (proj₁ ([t] ⊢Δ [σ′]))
             [σt≡σ′t] = irrelevanceEqTerm′ (subst-wk F) [σwk1F] [σwk1F]′
                                           (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
             [σG[t]≡σ′G[t]] = proj₂ (unwrap [G] ⊢Δ (proj₁ [σ] , [t]′))
                                    (proj₁ [σ′] , [σ′t])
                                    (proj₁ [σ≡σ′] , [σt≡σ′t])
         in irrelevanceEq″ (substConsTailId {σ = σ} {G} {t} ) (substConsTailId {σ = σ′} {G} {t})
                            G[t] G[t]′ [σG[t]≡σ′G[t]])

-- Validity of substitution of single lifted variable in type equality.
subst↑SEq : ∀ {F G G′ t t′ l l′} ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
            ([G′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G′ / [Γ] ∙ [F])
            ([G≡G′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] ∙ [F] / [G])
            ([t] : Γ ∙ F ⊩ᵛ⟨ l′ ⟩ t ∷ wk1 F / [Γ] ∙ [F]
                                / wk1ᵛ {A = F} {F} [Γ] [F] [F])
            ([t′] : Γ ∙ F ⊩ᵛ⟨ l′ ⟩ t′ ∷ wk1 F / [Γ] ∙ [F]
                                 / wk1ᵛ {A = F} {F} [Γ] [F] [F])
            ([t≡t′] : Γ ∙ F ⊩ᵛ⟨ l′ ⟩ t ≡ t′ ∷ wk1 F / [Γ] ∙ [F]
                                   / wk1ᵛ {A = F} {F} [Γ] [F] [F])
          → Γ ∙ F ⊩ᵛ⟨ l ⟩ G [ t ]↑ ≡ G′ [ t′ ]↑ / [Γ] ∙ [F]
                        / subst↑S {F = F} {G} {t} [Γ] [F] [G] [t]
subst↑SEq {F = F} {G} {G′} {t} {t′}
          [Γ] [F] [G] [G′] [G≡G′] [t] [t′] [t≡t′] {σ = σ} ⊢Δ [σ] =
  let [wk1F] = wk1ᵛ {A = F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ (unwrap [wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]′ = proj₁ (unwrap [F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]′ = irrelevanceTerm′ (subst-wk F) [σwk1F] [σwk1F]′ (proj₁ ([t] ⊢Δ [σ]))
      [t′]′ = irrelevanceTerm′ (subst-wk F) [σwk1F] [σwk1F]′ (proj₁ ([t′] ⊢Δ [σ]))
      [t≡t′]′ = irrelevanceEqTerm′ (subst-wk F) [σwk1F] [σwk1F]′ ([t≡t′] ⊢Δ [σ])
      G[t] = proj₁ (unwrap [G] ⊢Δ (proj₁ [σ] , [t]′))
      G[t]′ = irrelevance′ (substConsTailId {σ = σ} {G} {t}) G[t]
      G′[t] = proj₁ (unwrap [G′] ⊢Δ (proj₁ [σ] , [t]′))
      G′[t]′ = irrelevance′ (substConsTailId {σ = σ} {G′} {t}) G′[t]
      G′[t′] = proj₁ (unwrap [G′] ⊢Δ (proj₁ [σ] , [t′]′))
      G′[t′]′ = irrelevance′ (substConsTailId {σ = σ} {G′} {t′}) G′[t′]
      G[t]≡G′[t] = irrelevanceEq″ (substConsTailId {σ = σ} {G} {t}) (substConsTailId {σ = σ} {G′} {t})
                                   G[t] G[t]′ ([G≡G′] ⊢Δ (proj₁ [σ] , [t]′))
      G′[t]≡G′[t′] = irrelevanceEq″ (substConsTailId {σ = σ} {G′} {t})
                                     (substConsTailId {σ = σ} {G′} {t′})
                                     G′[t] G′[t]′
                                     (proj₂ (unwrap [G′] ⊢Δ (proj₁ [σ] , [t]′))
                                            (proj₁ [σ] , [t′]′)
                                            (reflSubst [Γ] ⊢Δ (proj₁ [σ]) , [t≡t′]′))
  in  transEq G[t]′ G′[t]′ G′[t′]′ G[t]≡G′[t] G′[t]≡G′[t′]

-- Helper function for reducible substitution of Π-types with specific typing derivations.
substSΠ₁′ : ∀ {F G t l l′} W
           ([ΠFG] : Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G)
           ([F] : Γ ⊩⟨ l′ ⟩ F)
           ([t] : Γ ⊩⟨ l′ ⟩ t ∷ F / [F])
         → Γ ⊩⟨ l ⟩ G [ t ]₀
substSΠ₁′
  {t = t} W (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)) [F]₁ [t] =
  let F≡F′ , G≡G′ , _ = B-PE-injectivity W W (whnfRed* (red D) ⟦ W ⟧ₙ)
      Feq = PE.trans F≡F′ (PE.sym (wk-id _))
      Geq = PE.cong (λ x → x [ _ ]₀) (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      ⊢Γ = wf (escape [F]₁)
      [t]′ = irrelevanceTerm′ Feq [F]₁ ([F] id ⊢Γ) [t]
  in  irrelevance′ Geq ([G] id ⊢Γ [t]′)
substSΠ₁′ W (emb 0<1 x) [F]₁ [t] = emb 0<1 (substSΠ₁′ W x [F]₁ [t])

-- Reducible substitution of Π-types.
substSΠ₁ : ∀ {F G t l l′} W
           ([ΠFG] : Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G)
           ([F] : Γ ⊩⟨ l′ ⟩ F)
           ([t] : Γ ⊩⟨ l′ ⟩ t ∷ F / [F])
         → Γ ⊩⟨ l ⟩ G [ t ]₀
substSΠ₁ W [ΠFG] [F] [t] = substSΠ₁′ W (B-elim W [ΠFG]) [F] [t]

-- Helper function for reducible substitution of Π-congruence with specific typing derivations.
substSΠ₂′ : ∀ {F F′ G G′ t t′ l l′ l″ l‴} W
           ([ΠFG] : Γ ⊩⟨ l ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G)
           ([ΠFG≡ΠF′G′] : Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ F′ ▹ G′ / B-intr W [ΠFG])
           ([F] : Γ ⊩⟨ l′ ⟩ F)
           ([F′] : Γ ⊩⟨ l′ ⟩ F′)
           ([t] : Γ ⊩⟨ l′ ⟩ t ∷ F / [F])
           ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ F′ / [F′])
           ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ F / [F])
           ([G[t]] : Γ ⊩⟨ l″ ⟩ G [ t ]₀)
           ([G′[t′]] : Γ ⊩⟨ l‴ ⟩ G′ [ t′ ]₀)
         → Γ ⊩⟨ l″ ⟩ G [ t ]₀ ≡ G′ [ t′ ]₀ / [G[t]]
substSΠ₂′ W (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _))
          (B₌ F″ G″ D′ A≡B [F≡F′] [G≡G′])
          [F]₁ [F′] [t] [t′] [t≡t′] [G[t]] [G′[t′]] =
  let F≡F′  , G≡G′  , _ = B-PE-injectivity W W (whnfRed* (red D) (⟦ W ⟧ₙ))
      F′≡F″ , G′≡G″ , _ = B-PE-injectivity W W (whnfRed* D′ ⟦ W ⟧ₙ)
      Feq = PE.trans F≡F′ (PE.sym (wk-id _))
      F′eq = PE.trans F′≡F″ (PE.sym (wk-id _))
      Geq = PE.cong (λ x → x [ _ ]₀) (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      Geq′ = PE.cong (λ x → x [ _ ]₀) (PE.trans G′≡G″ (PE.sym (wk-lift-id _)))
      ⊢Γ = wf (escape [F]₁)
      [t]′ = irrelevanceTerm′ Feq [F]₁ ([F] id ⊢Γ) [t]
      [t′]′ = convTerm₂′ F′eq ([F] id ⊢Γ) [F′] ([F≡F′] id ⊢Γ) [t′]
      [t≡t′]′ = irrelevanceEqTerm′ Feq [F]₁ ([F] id ⊢Γ) [t≡t′]
      [Gt≡Gt′] = G-ext id ⊢Γ [t]′ [t′]′ [t≡t′]′
      [Gt′≡G′t′] = [G≡G′] id ⊢Γ [t′]′
  in  irrelevanceEq′ Geq ([G] id ⊢Γ [t]′) [G[t]]
        (transEq′ PE.refl Geq′ ([G] id ⊢Γ [t]′) ([G] id ⊢Γ [t′]′)
                  [G′[t′]] [Gt≡Gt′] [Gt′≡G′t′])
substSΠ₂′ W (emb 0<1 x) = substSΠ₂′ W x

-- Reducible substitution of Π-congruence.
substSΠ₂ : ∀ {F F′ G G′ t t′ l l′ l″ l‴} W
           ([ΠFG] : Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G)
           ([ΠFG≡ΠF′G′] : Γ ⊩⟨ l ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ F′ ▹ G′ / [ΠFG])
           ([F] : Γ ⊩⟨ l′ ⟩ F)
           ([F′] : Γ ⊩⟨ l′ ⟩ F′)
           ([t] : Γ ⊩⟨ l′ ⟩ t ∷ F / [F])
           ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ F′ / [F′])
           ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ F / [F])
           ([G[t]] : Γ ⊩⟨ l″ ⟩ G [ t ]₀)
           ([G′[t′]] : Γ ⊩⟨ l‴ ⟩ G′ [ t′ ]₀)
         → Γ ⊩⟨ l″ ⟩ G [ t ]₀ ≡ G′ [ t′ ]₀ / [G[t]]
substSΠ₂ W [ΠFG] [ΠFG≡ΠF′G′] =
  let [ΠFG≡ΠF′G′]′ = irrelevanceEq [ΠFG] (B-intr W (B-elim W [ΠFG])) [ΠFG≡ΠF′G′]
  in  substSΠ₂′ W (B-elim W [ΠFG]) [ΠFG≡ΠF′G′]′

-- Valid substitution of Π-types.
substSΠ : ∀ {F G t l l′} W
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
          ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ G / [Γ])
          ([t] : Γ ⊩ᵛ⟨ l′ ⟩ t ∷ F / [Γ] / [F])
        → Γ ⊩ᵛ⟨ l ⟩ G [ t ]₀ / [Γ]
substSΠ {F = F} {G} {t} BΠ! [Γ] [F] [ΠFG] [t] = wrap λ ⊢Δ [σ] →
  let ⊩σΠFG = unwrap [ΠFG] ⊢Δ [σ]
      [σΠFG] = proj₁ ⊩σΠFG
      [σG[t]] = substSΠ₁ BΠ! [σΠFG]
                           (proj₁ (unwrap [F] ⊢Δ [σ]))
                           (proj₁ ([t] ⊢Δ [σ]))
      [σG[t]]′ = irrelevance′ (PE.sym (singleSubstLift G t))
                          [σG[t]]
  in  [σG[t]]′
  ,   (λ [σ′] [σ≡σ′] →
         irrelevanceEq″ (PE.sym (singleSubstLift G t))
                         (PE.sym (singleSubstLift G t))
                         [σG[t]] [σG[t]]′
                         (substSΠ₂ BΠ!
                                   [σΠFG]
                                   (proj₂ ⊩σΠFG [σ′] [σ≡σ′])
                                   (proj₁ (unwrap [F] ⊢Δ [σ])) (proj₁ (unwrap [F] ⊢Δ [σ′]))
                                   (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ′]))
                                   (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]) [σG[t]]
                                   (substSΠ₁ BΠ!
                                             (proj₁ (unwrap [ΠFG] ⊢Δ [σ′]))
                                             (proj₁ (unwrap [F] ⊢Δ [σ′]))
                                             (proj₁ ([t] ⊢Δ [σ′])))))
substSΠ {F = F} {G} {t} BΣ! [Γ] [F] [ΠFG] [t] = wrap λ ⊢Δ [σ] →
  let ⊩σΠFG = unwrap [ΠFG] ⊢Δ [σ]
      [σΠFG] = proj₁ ⊩σΠFG
      [σG[t]] = substSΠ₁ BΣ! [σΠFG]
                           (proj₁ (unwrap [F] ⊢Δ [σ]))
                           (proj₁ ([t] ⊢Δ [σ]))
      [σG[t]]′ = irrelevance′ (PE.sym (singleSubstLift G t))
                          [σG[t]]
  in  [σG[t]]′
  ,   (λ [σ′] [σ≡σ′] →
         irrelevanceEq″ (PE.sym (singleSubstLift G t))
                         (PE.sym (singleSubstLift G t))
                         [σG[t]] [σG[t]]′
                         (substSΠ₂ BΣ!
                                   [σΠFG]
                                   (proj₂ ⊩σΠFG [σ′] [σ≡σ′])
                                   (proj₁ (unwrap [F] ⊢Δ [σ])) (proj₁ (unwrap [F] ⊢Δ [σ′]))
                                   (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ′]))
                                   (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]) [σG[t]]
                                   (substSΠ₁ BΣ!
                                             (proj₁ (unwrap [ΠFG] ⊢Δ [σ′]))
                                             (proj₁ (unwrap [F] ⊢Δ [σ′]))
                                             (proj₁ ([t] ⊢Δ [σ′])))))

-- Valid substitution of Π-congruence.
substSΠEq : ∀ {F G F′ G′ t u l l′} W
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l′ ⟩ F / [Γ])
            ([F′] : Γ ⊩ᵛ⟨ l′ ⟩ F′ / [Γ])
            ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ G / [Γ])
            ([ΠF′G′] : Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F′ ▹ G′ / [Γ])
            ([ΠFG≡ΠF′G′] : Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ F′ ▹ G′ / [Γ] / [ΠFG])
            ([t]   : Γ ⊩ᵛ⟨ l′ ⟩ t ∷ F / [Γ] / [F])
            ([u]   : Γ ⊩ᵛ⟨ l′ ⟩ u ∷ F′ / [Γ] / [F′])
            ([t≡u] : Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ F / [Γ] / [F])
          → Γ ⊩ᵛ⟨ l ⟩ G [ t ]₀ ≡ G′ [ u ]₀ / [Γ]
                    / substSΠ {F = F} {G} {t} W [Γ] [F] [ΠFG] [t]
substSΠEq {F = F} {G} {F′} {G′} {t} {u} BΠ! [Γ] [F] [F′] [ΠFG] [ΠF′G′] [ΠFG≡ΠF′G′]
           [t] [u] [t≡u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σΠFG] = proj₁ (unwrap [ΠFG] ⊢Δ [σ])
      _ , Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _ =
        extractMaybeEmb (Π-elim [σΠFG])
      F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΠ! BΠ! (whnfRed* (red D₁) ΠΣₙ)
      [σΠF′G′] = proj₁ (unwrap [ΠF′G′] ⊢Δ [σ])
      _ , Bᵣ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂ _ =
        extractMaybeEmb (Π-elim [σΠF′G′])
      F′≡F₂ , G′≡G₂ , _ = B-PE-injectivity BΠ! BΠ! (whnfRed* (red D₂) ΠΣₙ)
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [σF′] = proj₁ (unwrap [F′] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σt]′ = irrelevanceTerm′ (PE.trans F≡F₁ (PE.sym (wk-id F₁)))
                               [σF] ([F]₁ id ⊢Δ) [σt]
      [σu]′ = irrelevanceTerm′ (PE.trans F′≡F₂ (PE.sym (wk-id F₂)))
                               [σF′] ([F]₂ id ⊢Δ) [σu]
      [σt≡σu] = [t≡u] ⊢Δ [σ]
      [G[t]] = irrelevance′ (PE.cong (λ x → x [ t [ σ ] ]₀)
                                     (PE.trans (wk-lift-id G₁) (PE.sym G≡G₁)))
                            ([G]₁ id ⊢Δ [σt]′)
      [G′[u]] = irrelevance′ (PE.cong (λ x → x [ u [ σ ] ]₀)
                                      (PE.trans (wk-lift-id G₂) (PE.sym G′≡G₂)))
                             ([G]₂ id ⊢Δ [σu]′)
  in  irrelevanceEq″ (PE.sym (singleSubstLift G t))
                      (PE.sym (singleSubstLift G′ u))
                      [G[t]]
                        (proj₁ (unwrap (substSΠ {F = F} {G} {t} BΠ! [Γ] [F] [ΠFG] [t]) ⊢Δ [σ]))
                      (substSΠ₂ {F = F [ σ ]} {F′ [ σ ]}
                                {G [ liftSubst σ ]}
                                {G′ [ liftSubst σ ]}
                                BΠ!
                                (proj₁ (unwrap [ΠFG] ⊢Δ [σ]))
                                ([ΠFG≡ΠF′G′] ⊢Δ [σ])
                                [σF] [σF′] [σt] [σu] [σt≡σu] [G[t]] [G′[u]])

substSΠEq {F = F} {G} {F′} {G′} {t} {u} BΣ! [Γ] [F] [F′] [ΣFG] [ΣF′G′] [ΣFG≡ΣF′G′]
           [t] [u] [t≡u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σΣFG] = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
      _ , Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _ =
        extractMaybeEmb (Σ-elim [σΣFG])
      F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! (whnfRed* (red D₁) ΠΣₙ)
      [σΣF′G′] = proj₁ (unwrap [ΣF′G′] ⊢Δ [σ])
      _ , Bᵣ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂ _ =
        extractMaybeEmb (Σ-elim [σΣF′G′])
      F′≡F₂ , G′≡G₂ , _ = B-PE-injectivity BΣ! BΣ! (whnfRed* (red D₂) ΠΣₙ)
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [σF′] = proj₁ (unwrap [F′] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σt]′ = irrelevanceTerm′ (PE.trans F≡F₁ (PE.sym (wk-id F₁)))
                               [σF] ([F]₁ id ⊢Δ) [σt]
      [σu]′ = irrelevanceTerm′ (PE.trans F′≡F₂ (PE.sym (wk-id F₂)))
                               [σF′] ([F]₂ id ⊢Δ) [σu]
      [σt≡σu] = [t≡u] ⊢Δ [σ]
      [G[t]] = irrelevance′ (PE.cong (λ x → x [ t [ σ ] ]₀)
                                     (PE.trans (wk-lift-id G₁) (PE.sym G≡G₁)))
                            ([G]₁ id ⊢Δ [σt]′)
      [G′[u]] = irrelevance′ (PE.cong (λ x → x [ u [ σ ] ]₀)
                                      (PE.trans (wk-lift-id G₂) (PE.sym G′≡G₂)))
                             ([G]₂ id ⊢Δ [σu]′)
  in  irrelevanceEq″ (PE.sym (singleSubstLift G t))
                      (PE.sym (singleSubstLift G′ u))
                      [G[t]]
                        (proj₁ (unwrap (substSΠ {F = F} {G} {t} BΣ! [Γ] [F] [ΣFG] [t]) ⊢Δ [σ]))
                      (substSΠ₂ {F = F [ σ ]} {F′ [ σ ]}
                                {G [ liftSubst σ ]}
                                {G′ [ liftSubst σ ]}
                                BΣ!
                                (proj₁ (unwrap [ΣFG] ⊢Δ [σ]))
                                ([ΣFG≡ΣF′G′] ⊢Δ [σ])
                                [σF] [σF′] [σt] [σu] [σt≡σu] [G[t]] [G′[u]])
