------------------------------------------------------------------------
-- Validity of beta and eta equality of pairs.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.ProdBetaEta
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Reduction R
open import Definition.LogicalRelation.Substitution.Conversion R
open import Definition.LogicalRelation.Substitution.Reflexivity R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R
open import Definition.LogicalRelation.Substitution.Introductions.Prod R
open import Definition.LogicalRelation.Substitution.Introductions.Fst R
open import Definition.LogicalRelation.Substitution.Introductions.Snd R

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n      : Nat
    Γ      : Con Term n
    p p′ q : M

Σ-β₁ᵛ : ∀ {F G t u l}
        ([Γ] : ⊩ᵛ Γ)
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
        ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
        ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ]₀ / [Γ] / substS {F = F} {G} [Γ] [F] [G] [t])
      → Σₚ-allowed p q
      → Γ ⊩ᵛ⟨ l ⟩ fst p (prodₚ p t u) ≡ t ∷ F / [Γ] / [F]
Σ-β₁ᵛ {Γ = Γ} {F = F} {G} {t} {u} {l} [Γ] [F] [G] [t] [u] ok =
  let [Gt] = substS {F = F} {G} {t} [Γ] [F] [G] [t]
      fst⇒t : Γ ⊩ᵛ fst _ (prodₚ _ t u) ⇒ t ∷ F / [Γ]
      fst⇒t = (λ {_} {Δ} {σ} ⊢Δ [σ] →
                let ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
                    ⊢σF = escape ⊩σF

                    [Fσ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
                    ⊩σG : Δ ∙ F [ σ ] ⊩⟨ l ⟩ G [ liftSubst σ ]
                    ⊩σG = proj₁ (unwrap [G] (⊢Δ ∙ ⊢σF) [Fσ])
                    ⊢σG = escape ⊩σG

                    ⊩σt = proj₁ ([t] ⊢Δ [σ])
                    ⊢σt = escapeTerm ⊩σF ⊩σt

                    ⊩σGt₁ = proj₁ (unwrap [Gt] ⊢Δ [σ])
                    ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt₁

                    ⊩σu₁ = proj₁ ([u] ⊢Δ [σ])
                    ⊩σu = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt₁ ⊩σGt ⊩σu₁
                    ⊢σu = escapeTerm ⊩σGt ⊩σu
                in  Σ-β₁ ⊢σF ⊢σG ⊢σt ⊢σu PE.refl ok)
  in  redSubstTermᵛ {A = F} {fst _ (prodₚ _ t u)} {t} [Γ] fst⇒t [F] [t]
        .proj₂

Σ-β₂ᵛ :
  ∀ {F G t u l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ]₀ / [Γ] / substS [Γ] [F] [G] [t])
  (ok : Σₚ-allowed p q) →
  Γ ⊩ᵛ⟨ l ⟩ snd p (prodₚ p t u) ≡ u ∷ G [ fst p (prodₚ p t u) ]₀ / [Γ] /
    substS {F = F} {G} [Γ] [F] [G]
      (fstᵛ {q = q} {t = prodₚ p t u} [Γ] [F] [G] ok
         (prodᵛ {t = t} {u} [Γ] [F] [G] [t] [u] ok))
Σ-β₂ᵛ {Γ = Γ} {F = F} {G} {t} {u} {l} [Γ] [F] [G] [t] [u] ok =
  let [Gt] = substS {F = F} {G} {t} [Γ] [F] [G] [t]
      [prod] = prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u] ok
      [fst] = fstᵛ {t = prodₚ _ t u} [Γ] [F] [G] ok [prod]
      [Gfst] = substS [Γ] [F] [G] [fst]
      [fst≡t] = Σ-β₁ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u] ok
      [Gfst≡Gt] = substSEq [Γ] [F] [F] (reflᵛ {A = F} [Γ] [F])
                               [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                               [fst] [t] [fst≡t]

      [u]Gfst = conv₂ᵛ {t = u} [Γ] [Gfst] [Gt] [Gfst≡Gt] [u]

      snd⇒t : Γ ⊩ᵛ snd _ (prodₚ _ t u) ⇒ u ∷ G [ fst _ (prodₚ _ t u) ]₀ /
                [Γ]
      snd⇒t = (λ {_} {Δ} {σ} ⊢Δ [σ] →
                let ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
                    ⊢σF = escape ⊩σF

                    [Fσ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
                    ⊩σG : Δ ∙ F [ σ ] ⊩⟨ l ⟩ G [ liftSubst σ ]
                    ⊩σG = proj₁ (unwrap [G] (⊢Δ ∙ ⊢σF) [Fσ])
                    ⊢σG = escape ⊩σG

                    ⊩σt = proj₁ ([t] ⊢Δ [σ])
                    ⊢σt = escapeTerm ⊩σF ⊩σt

                    ⊩σGt₁ = proj₁ (unwrap [Gt] ⊢Δ [σ])
                    ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt₁

                    ⊩σu₁ = proj₁ ([u] ⊢Δ [σ])
                    ⊩σu = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt₁ ⊩σGt ⊩σu₁
                    ⊢σu = escapeTerm ⊩σGt ⊩σu

                    snd⇒t : Δ ⊢ _ ⇒ _ ∷ _
                    snd⇒t = Σ-β₂ ⊢σF ⊢σG ⊢σt ⊢σu PE.refl ok
                    σGfst≡σGfst = PE.subst
                      (λ x →
                         Δ ⊢ x ≡ G [ fst _ (prodₚ _ t u) ]₀ [ σ ])
                      (singleSubstLift G (fst _ (prodₚ _ t u)))
                      (refl (escape (proj₁ (unwrap [Gfst] ⊢Δ [σ]))))
              in  conv snd⇒t σGfst≡σGfst)
  in  redSubstTermᵛ {t = snd _ (prodₚ _ t u)} {u}
        [Γ] snd⇒t [Gfst] [u]Gfst .proj₂

Σ-η′ :
  ∀ {F G p r l l′}
  ([F] : Γ ⊩⟨ l′ ⟩ F)
  ([Gfstp] : Γ ⊩⟨ l′ ⟩ G [ fst p′ p ]₀)
  ([ΣFG]₁ : Γ ⊩⟨ l ⟩B⟨ BΣ Σₚ p′ q ⟩ Σₚ p′ , q ▷ F ▹ G )
  ([p] : Γ ⊩⟨ l ⟩ p ∷ Σ p′ , q ▷ F ▹ G / B-intr BΣ! [ΣFG]₁)
  ([r] : Γ ⊩⟨ l ⟩ r ∷ Σ p′ , q ▷ F ▹ G / B-intr BΣ! [ΣFG]₁)
  ([fst≡] : Γ ⊩⟨ l′ ⟩ fst p′ p ≡ fst p′ r ∷ F / [F])
  ([snd≡] : Γ ⊩⟨ l′ ⟩ snd p′ p ≡ snd p′ r ∷ G [ fst p′ p ]₀ / [Gfstp]) →
  Γ ⊩⟨ l ⟩ p ≡ r ∷ Σ p′ , q ▷ F ▹ G / B-intr BΣ! [ΣFG]₁
Σ-η′ {Γ = Γ} {q = q} {F = F} {G} {p} {r} {l} {l′}
     [F] [Gfstp]
     [ΣFG]₁@(noemb [Σ]@(Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext _))
     [p]@(Σₜ p′ dₚ p′≅p′ pProd p′Prop)
     [r]@(Σₜ r′ dᵣ r′≅r′ rProd r′Prop)
     [fst≡]
     [snd≡]
       with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let [ΣFG] = B-intr BΣ! [ΣFG]₁
      ⊢Γ = wf ⊢F
      wk[fstp′] , wk[sndp′] = p′Prop
      wk[fstr′] , wk[sndr′] = r′Prop
      wk[F] = [F]₁ id ⊢Γ
      wk[Gfstp′] = [G]₁ id ⊢Γ wk[fstp′]


      fstp⇒* : Γ ⊢ fst _ p ⇒* fst _ p′ ∷ U.wk id F
      fstp⇒* = PE.subst (λ x → Γ ⊢ _ ⇒* _ ∷ x)
                        (PE.sym (wk-id F))
                        (fst-subst* (redₜ dₚ) ⊢F ⊢G)
      fstr⇒* = PE.subst (λ x → Γ ⊢ _ ⇒* _ ∷ x)
                        (PE.sym (wk-id F))
                        (fst-subst* (redₜ dᵣ) ⊢F ⊢G)

      wk[fstp] , wk[fstp≡] = redSubst*Term fstp⇒* wk[F] wk[fstp′]
      wk[fstr] , wk[fstr≡] = redSubst*Term fstr⇒* wk[F] wk[fstr′]

      wk[fst≡] = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                    [F] wk[F]
                                    [fst≡]
      wk[fst′≡] : Γ ⊩⟨ l ⟩ fst _ p′ ≡ fst _ r′ ∷ U.wk id F / wk[F]
      wk[fst′≡] = transEqTerm wk[F]
                             (symEqTerm wk[F] wk[fstp≡])
                             (transEqTerm wk[F] wk[fst≡] wk[fstr≡])

      [p′] : Γ ⊩⟨ l ⟩ p′ ∷ Σ _ , _ ▷ F ▹ G / [ΣFG]
      [p′] = Σₜ p′ (idRedTerm:*: (⊢u-redₜ dₚ)) p′≅p′ pProd p′Prop
      [r′] = Σₜ r′ (idRedTerm:*: (⊢u-redₜ dᵣ)) r′≅r′ rProd r′Prop

      sndp⇒*₁ : Γ ⊢ snd _ p ⇒* snd _ p′ ∷ G [ fst _ p ]₀
      sndp⇒*₁ = snd-subst* [F] [ΣFG] [p′] (redₜ dₚ)
      sndr⇒*₁ = snd-subst* [F] [ΣFG] [r′] (redₜ dᵣ)

      wk[Gfstp] = [G]₁ id ⊢Γ wk[fstp]
      wk[Gfstr] = [G]₁ id ⊢Γ wk[fstr]
      [Gfstr] = irrelevance′
        (PE.cong (λ x → x [ fst _ r ]₀) (wk-lift-id G))
        wk[Gfstr]
      wk[Gfstr′] = [G]₁ id ⊢Γ wk[fstr′]

      [Gfstp≡wkGfstp′] :
        Γ ⊩⟨ l′ ⟩ G [ fst _ p ]₀ ≡ U.wk (lift id) G [ fst _ p′ ]₀ /
          [Gfstp]
      [Gfstp≡wkGfstp′] = irrelevanceEq′
        (PE.cong (λ x → x [ fst _ p ]₀) (wk-lift-id G))
        ([G]₁ id ⊢Γ wk[fstp]) [Gfstp]
        (G-ext id ⊢Γ wk[fstp] wk[fstp′] wk[fstp≡])
      [Gfstr≡Gfstp] : Γ ⊩⟨ _ ⟩ G [ fst _ r ]₀ ≡ G [ fst _ p ]₀ / [Gfstr]
      [Gfstr≡Gfstp] = irrelevanceEq″
        (PE.cong (λ x → x [ fst _ r ]₀) (wk-lift-id G))
        (PE.cong (λ x → x [ fst _ p ]₀) (wk-lift-id G))
        wk[Gfstr] [Gfstr]
        (symEq wk[Gfstp] wk[Gfstr]
           (G-ext id ⊢Γ wk[fstp] wk[fstr] wk[fst≡]))
      [Gfstr≡wkGfstp′] :
        Γ ⊩⟨ l ⟩ G [ fst _ r ]₀ ≡ U.wk (lift id) G [ fst _ p′ ]₀ / [Gfstr]
      [Gfstr≡wkGfstp′] = transEq [Gfstr] [Gfstp] wk[Gfstp′]
                                 [Gfstr≡Gfstp] [Gfstp≡wkGfstp′]
      [wkGfstr′≡wkGfstp′] :
        Γ ⊩⟨ l ⟩ U.wk (lift id) G [ fst _ r′ ]₀ ≡
          U.wk (lift id) G [ fst _ p′ ]₀ / wk[Gfstr′]
      [wkGfstr′≡wkGfstp′] = G-ext id ⊢Γ wk[fstr′] wk[fstp′] (symEqTerm wk[F] wk[fst′≡])

      sndp⇒* : Γ ⊢ snd _ p ⇒* snd _ p′ ∷ U.wk (lift id) G [ fst _ p′ ]₀
      sndp⇒* = conv* sndp⇒*₁ (≅-eq (escapeEq [Gfstp] [Gfstp≡wkGfstp′]))
      sndr⇒* = conv* sndr⇒*₁ (≅-eq (escapeEq [Gfstr] [Gfstr≡wkGfstp′]))

      wk[sndp≡] :
        Γ ⊩⟨ l ⟩ snd _ p ≡ snd _ p′ ∷ U.wk (lift id) G [ fst _ p′ ]₀ /
          wk[Gfstp′]
      wk[sndp≡] = proj₂ (redSubst*Term sndp⇒* wk[Gfstp′] wk[sndp′])
      wk[sndr≡] = proj₂ (redSubst*Term sndr⇒* wk[Gfstp′]
                                       (convTerm₁ wk[Gfstr′] wk[Gfstp′]
                                                  [wkGfstr′≡wkGfstp′]
                                                  wk[sndr′]))

      wk[snd≡] :
        Γ ⊩⟨ l ⟩ snd _ p ≡ snd _ r ∷ U.wk (lift id) G [ fst _ p′ ]₀ /
          wk[Gfstp′]
      wk[snd≡] = convEqTerm₁ [Gfstp] wk[Gfstp′] [Gfstp≡wkGfstp′] [snd≡]

      wk[snd′≡] :
        Γ ⊩⟨ l ⟩ snd _ p′ ≡ snd _ r′ ∷ U.wk (lift id) G [ fst _ p′ ]₀ /
          wk[Gfstp′]
      wk[snd′≡] = transEqTerm wk[Gfstp′]
                              (symEqTerm wk[Gfstp′] wk[sndp≡])
                              (transEqTerm wk[Gfstp′] wk[snd≡] wk[sndr≡])

      p′≅r′ : Γ ⊢ p′ ≅ r′ ∷ Σ _ , _ ▷ F ▹ G
      p′≅r′ = ≅-Σ-η ⊢F ⊢G (⊢u-redₜ dₚ) (⊢u-redₜ dᵣ)
                    pProd rProd
                    (PE.subst (λ x → Γ ⊢ _ ≅ _ ∷ x)
                              (wk-id F)
                              (escapeTermEq wk[F] wk[fst′≡]))
                    (PE.subst (λ x → Γ ⊢ _ ≅ _ ∷ x [ fst _ p′ ]₀)
                              (wk-lift-id G)
                              (escapeTermEq wk[Gfstp′] wk[snd′≡]))
  in  Σₜ₌ p′ r′ dₚ dᵣ pProd rProd p′≅r′ [p] [r]
         (wk[fstp′] , wk[fstr′] , wk[fst′≡] , wk[snd′≡])
Σ-η′ [F] [Gfst] (emb 0<1 x) = Σ-η′ [F] [Gfst] x

Σ-η″ :
  ∀ {F G p r l}
  ([F] : Γ ⊩⟨ l ⟩ F)
  ([Gfst] : Γ ⊩⟨ l ⟩ G [ fst p′ p ]₀)
  ([ΣFG] : Γ ⊩⟨ l ⟩ Σₚ p′ , q ▷ F ▹ G)
  ([p] : Γ ⊩⟨ l ⟩ p ∷ Σ p′ , q ▷ F ▹ G / [ΣFG])
  ([r] : Γ ⊩⟨ l ⟩ r ∷ Σ p′ , q ▷ F ▹ G / [ΣFG])
  ([fst≡] : Γ ⊩⟨ l ⟩ fst p′ p ≡ fst p′ r ∷ F / [F])
  ([snd≡] : Γ ⊩⟨ l ⟩ snd p′ p ≡ snd p′ r ∷ G [ fst p′ p ]₀ / [Gfst]) →
  Γ ⊩⟨ l ⟩ p ≡ r ∷ Σ p′ , q ▷ F ▹ G / [ΣFG]
Σ-η″
  {Γ = Γ} {F = F} {G} {t} {l}
  [F] [Gfst] [ΣFG] [p] [r] [fst≡] [snd≡] =
  let [ΣFG]′ = B-intr BΣ! (B-elim BΣ! [ΣFG])
      [p]′ = irrelevanceTerm [ΣFG] [ΣFG]′ [p]
      [r]′ = irrelevanceTerm [ΣFG] [ΣFG]′ [r]
      [p≡]′ = Σ-η′ [F] [Gfst] (B-elim BΣ! [ΣFG])
                [p]′ [r]′ [fst≡] [snd≡]
  in  irrelevanceEqTerm [ΣFG]′ [ΣFG] [p≡]′

Σ-ηᵛ :
  ∀ {F G p r l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σₚ-allowed p′ q) →
  let [ΣFG] = Σᵛ {q = q} [Γ] [F] [G] ok in
  ([p] : Γ ⊩ᵛ⟨ l ⟩ p ∷ Σ _ , _ ▷ F ▹ G / [Γ] / [ΣFG])
  ([r] : Γ ⊩ᵛ⟨ l ⟩ r ∷ Σ _ , _ ▷ F ▹ G / [Γ] / [ΣFG])
  ([fst≡] : Γ ⊩ᵛ⟨ l ⟩ fst p′ p ≡ fst p′ r ∷ F / [Γ] / [F]) →
  let [Gfst] = substS [Γ] [F] [G] (fstᵛ {t = p} [Γ] [F] [G] ok [p]) in
  ([snd≡] : Γ ⊩ᵛ⟨ l ⟩ snd p′ p ≡ snd p′ r ∷ G [ fst p′ p ]₀ / [Γ] /
              [Gfst]) →
  Γ ⊩ᵛ⟨ l ⟩ p ≡ r ∷ Σ p′ , q ▷ F ▹ G / [Γ] / [ΣFG]
Σ-ηᵛ
  {Γ = Γ} {F = F} {G} {p} {r} {l} [Γ] [F] [G] ok [p] [r] [fst≡] [snd≡]
  {Δ} {σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G] ok
      [Gfst] = substS [Γ] [F] [G] (fstᵛ {t = p} [Γ] [F] [G] ok [p])
      ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊩σGfst₁ = proj₁ (unwrap [Gfst] ⊢Δ [σ])
      ⊩σGfst = irrelevance′ (singleSubstLift G (fst _ p)) ⊩σGfst₁
      ⊩σΣFG = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
      ⊩σp = proj₁ ([p] ⊢Δ [σ])
      ⊩σr = proj₁ ([r] ⊢Δ [σ])
      σfst≡ = [fst≡] ⊢Δ [σ]
      σsnd≡₁ = [snd≡] ⊢Δ [σ]
      σsnd≡ = irrelevanceEqTerm′ (singleSubstLift G (fst _ p))
                ⊩σGfst₁ ⊩σGfst σsnd≡₁
  in  Σ-η″ ⊩σF ⊩σGfst ⊩σΣFG ⊩σp ⊩σr σfst≡ σsnd≡
