------------------------------------------------------------------------
-- Validity of the second projection.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Snd
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
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R
open import Definition.LogicalRelation.Substitution.Introductions.Fst R

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n   : Nat
    Γ   : Con Term n
    p q : M

snd-subst*′ :
  ∀ {l l′ F G t t′}
  ([F] : Γ ⊩⟨ l ⟩ F)
  ([ΣFG] : Γ ⊩⟨ l′ ⟩B⟨ BΣ 𝕤 p q ⟩ Σˢ p , q ▷ F ▹ G)
  ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ Σ p , q ▷ F ▹ G / B-intr (BΣ 𝕤 p q) [ΣFG]) →
  Γ ⊢ t ⇒* t′ ∷ Σˢ p , q ▷ F ▹ G →
  Γ ⊢ snd p t ⇒* snd p t′ ∷ G [ fst p t ]₀
snd-subst*′ [F] (noemb (Bᵣ F G D ⊢F ⊢G A≡A [F]₁ [G] G-ext _)) _ (id x)
  with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ = id (sndⱼ ⊢F ⊢G x)
snd-subst*′
  {Γ = Γ} {p = p} {q = q} {F = F} {G = G} {t = t} {t′ = t″} [F]
  [ΣFG]₀@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G] G-ext _))
  [t″]
  t⇒*t″@(_⇨_ {t′ = t′} t⇒t′ t′⇒*t″)
  with B-PE-injectivity (BΣ 𝕤 p q) (BΣ 𝕤 p q) (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let [ΣFG] = B-intr (BΣ 𝕤 p q) [ΣFG]₀
      [t] , _ = redSubst*Term t⇒*t″ [ΣFG] [t″]
      [t′] , _ = redSubst*Term t′⇒*t″ [ΣFG] [t″]
      [t≡t′] : Γ ⊩⟨ _ ⟩ t ≡ t′ ∷ Σ _ , _ ▷ F ▹ G / [ΣFG]
      [t≡t′] = proj₂ (redSubstTerm t⇒t′ [ΣFG] [t′])
      [fstt] : Γ ⊩⟨ _ ⟩ fst p t ∷ F / [F]
      [fstt] = fst″ [F] [ΣFG] [t]
      [fstt′] : Γ ⊩⟨ _ ⟩ fst p t′ ∷ F / [F]
      [fstt′] = fst″ [F] [ΣFG] [t′]
      [Gfstt] : Γ ⊩⟨ _ ⟩ G [ fst p t ]₀
      [Gfstt] = substSΠ₁ BΣ! [ΣFG] [F] [fstt]
      [Gfstt′] : Γ ⊩⟨ _ ⟩ G [ fst p t′ ]₀
      [Gfstt′] = substSΠ₁ BΣ! [ΣFG] [F] [fstt′]
      [fstt′≡fstt] : Γ ⊩⟨ _ ⟩ fst p t′ ≡ fst p t ∷ F / [F]
      [fstt′≡fstt] = symEqTerm [F] (fst-cong″ [F] [ΣFG] [t≡t′])
      [Gfstt′≡Gfstt] :
        Γ ⊩⟨ _ ⟩ G [ fst p t′ ]₀ ≡ G [ fst p t ]₀ / [Gfstt′]
      [Gfstt′≡Gfstt] = substSΠ₂ BΣ! [ΣFG] (reflEq [ΣFG]) [F] [F] [fstt′] [fstt] [fstt′≡fstt] [Gfstt′] [Gfstt]
  in  snd-subst ⊢F ⊢G t⇒t′ ⇨ conv* (snd-subst*′ [F] [ΣFG]₀ [t″] t′⇒*t″)
                                               (≅-eq (escapeEq [Gfstt′] [Gfstt′≡Gfstt]))
snd-subst*′ [F] (emb 0<1 x) = snd-subst*′ [F] x

-- NOTE this has a horrible interface (and implementation)
snd-subst* : ∀ {l l′ F G t t′}
             ([F] : Γ ⊩⟨ l ⟩ F)
             ([ΣFG] : Γ ⊩⟨ l′ ⟩ Σˢ p , q ▷ F ▹ G)
             ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ Σˢ p , q ▷ F ▹ G / [ΣFG])
             → Γ ⊢ t ⇒* t′ ∷ Σˢ p , q ▷ F ▹ G
             → Γ ⊢ snd p t ⇒* snd p t′ ∷ G [ fst p t ]₀
snd-subst* [F] [ΣFG] [t′] t⇒*t′ =
  let [t′]′ = irrelevanceTerm [ΣFG] (B-intr BΣ! (B-elim BΣ! [ΣFG])) [t′]
  in  snd-subst*′ [F] (B-elim BΣ! [ΣFG]) [t′]′ t⇒*t′

snd′ : ∀ {F G t l l′}
       ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ 𝕤 p q ⟩ Σˢ p , q ▷ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σˢ p , q ▷ F ▹ G / B-intr BΣ! [ΣFG])
       ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst p t ]₀)
       → Γ ⊩⟨ l′ ⟩ snd p t ∷ G [ fst p t ]₀ / [Gfst]
snd′ {Γ = Γ} {p = p′} {q = q} {F = F} {G = G} {t = t} {l = l} {l′ = l′}
     [ΣFG]@(noemb [Σ]@(Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext _))
     [t]@(Σₜ p d p≅p pProd pProp) [Gfst] with
       B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let ⊢Γ = wf ⊢F
      [fstp] , [sndp] = pProp
      [p] = Σₜ p (idRedTerm:*: (⊢u-redₜ d)) p≅p pProd pProp
      [fstt] , [fstt≡fstp] = redSubst*Term
                               (PE.subst
                                  (λ x → Γ ⊢ fst p′ t ⇒* fst p′ p ∷ x)
                                  (PE.sym (wk-id F))
                                  (fst-subst* (redₜ d) ⊢F ⊢G))
                               ([F'] id ⊢Γ) [fstp]

      [Gfstt] = [G'] id ⊢Γ [fstt]
      [Gfstp] = [G'] id ⊢Γ [fstp]
      [Gfstt≡Gfstp] = G-ext id ⊢Γ [fstt] [fstp] [fstt≡fstp]

      [sndp] = convTerm₂ [Gfstt] [Gfstp] [Gfstt≡Gfstp] [sndp]

      [sndp] : Γ ⊩⟨ l′ ⟩ snd p′ p ∷ G [ fst p′ t ]₀ / [Gfst]
      [sndp] = irrelevanceTerm′ (PE.cong (λ x → x [ fst p′ t ]₀) (wk-lift-id G))
                                [Gfstt] [Gfst] [sndp]
  in  redSubst*Term
        (snd-subst*
           (PE.subst (λ x → Γ ⊩⟨ l ⟩ x) (wk-id F) ([F'] id ⊢Γ))
           (B-intr BΣ! [ΣFG])
           [p] (redₜ d))
        [Gfst] [sndp] .proj₁
snd′ (emb 0<1 x) = snd′ x

snd″ : ∀ {F G t l l′}
       ([ΣFG] : Γ ⊩⟨ l ⟩ Σˢ p , q ▷ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σˢ p , q ▷ F ▹ G / [ΣFG])
       ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst p t ]₀)
       → Γ ⊩⟨ l′ ⟩ snd p t ∷ G [ fst p t ]₀ / [Gfst]
snd″ {Γ = Γ} {t = t} {l = l} [ΣFG] [t] [Gfst] =
  let [t]′ = irrelevanceTerm [ΣFG] (B-intr BΣ! (Σ-elim [ΣFG])) [t]
  in  snd′ (Σ-elim [ΣFG]) [t]′ [Gfst]

snd-cong′ :
  ∀ {F G t t′ l l′}
  ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ 𝕤 p q ⟩ Σˢ p , q ▷ F ▹ G)
  ([t] : Γ ⊩⟨ l ⟩ t ∷ Σˢ p , q ▷ F ▹ G / B-intr BΣ! [ΣFG])
  ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ Σˢ p , q ▷ F ▹ G / B-intr BΣ! [ΣFG])
  ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σˢ _ , _ ▷ F ▹ G / B-intr BΣ! [ΣFG])
  ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst p t ]₀) →
  Γ ⊩⟨ l′ ⟩ snd p t ≡ snd p t′ ∷ G [ fst p t ]₀ / [Gfst]
snd-cong′ {Γ = Γ} {p = p″} {q = q} {F = F} {G} {t} {t′} {l} {l′}
          [ΣFG]@(noemb [Σ]@(Bᵣ F' G' D ⊢F ⊢G A≡A [F] [G] G-ext _))
          [t]@(Σₜ p d p≅p pProd pProp)
          [t′]@(Σₜ p′ d′ p′≅p′ pProd′ pProp′)
          [t≡t′]@(Σₜ₌ p₁ p′₁ d₁ d′₁ pProd₁ pProd′₁ p≅p′ [t]₁ [t′]₁ prop)
          [Gfst] with
            B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
          | whrDet*Term (redₜ d , productWhnf pProd) (redₜ d₁ , productWhnf pProd₁)
          | whrDet*Term (redₜ d′ , productWhnf pProd′) (redₜ d′₁ , productWhnf pProd′₁)
... | PE.refl , PE.refl , _ | PE.refl | PE.refl =
  let ⊢Γ = wf ⊢F
      [fstp] , [sndp] = pProp
      [fstp′] , [sndp′] = pProp′
      [fstp]₁ , [fstr]₁ , [fst≡] , [snd≡] = prop
      [p] : Γ ⊩⟨ l ⟩ p ∷ Σ _ , _ ▷ F ▹ G / B-intr BΣ! [ΣFG]
      [p] = Σₜ p (idRedTerm:*: (⊢u-redₜ d)) p≅p pProd pProp
      [p′] : Γ ⊩⟨ l ⟩ p′ ∷ Σ _ , _ ▷ F ▹ G / B-intr BΣ! [ΣFG]
      [p′] = Σₜ p′ (idRedTerm:*: (⊢u-redₜ d′)) p′≅p′ pProd′ pProp′
      [F]′ = irrelevance′ (wk-id F) ([F] id ⊢Γ)

      [fstt] , [fstt≡fstp] = redSubst*Term
        (PE.subst (λ x → Γ ⊢ fst p″ t ⇒* fst p″ p ∷ x)
           (PE.sym (wk-id F))
           (fst-subst* (redₜ d) ⊢F ⊢G))
        ([F] id ⊢Γ) [fstp]
      [Gfstt≡Gfstp] = G-ext id ⊢Γ [fstt] [fstp] [fstt≡fstp]

      [sndp]′ : Γ ⊩⟨ l ⟩ snd p″ p ∷ U.wk (lift id) G [ fst p″ t ]₀ /
                  [G] id ⊢Γ [fstt]
      [sndp]′ = convTerm₂ ([G] id ⊢Γ [fstt]) ([G] id ⊢Γ [fstp]) [Gfstt≡Gfstp] [sndp]
      sndt⇒*sndp = snd-subst* [F]′ (B-intr BΣ! [ΣFG]) [p] (redₜ d)
      [sndp]″ = irrelevanceTerm′
        (PE.cong (λ x → x [ fst p″ t ]₀) (wk-lift-id G))
        ([G] id ⊢Γ [fstt]) [Gfst]
        [sndp]′
      [sndt≡sndp] : Γ ⊩⟨ l′ ⟩ snd p″ t ≡ snd p″ p ∷ G [ fst p″ t ]₀ /
                      [Gfst]
      [sndt≡sndp] = proj₂ (redSubst*Term sndt⇒*sndp [Gfst] [sndp]″)

      [snd≡]′ = convEqTerm₂ ([G] id ⊢Γ [fstt]) ([G] id ⊢Γ [fstp]₁) [Gfstt≡Gfstp] [snd≡]
      [sndp≡sndp′] : Γ ⊩⟨ l′ ⟩ snd p″ p ≡ snd p″ p′ ∷ G [ fst p″ t ]₀ /
                       [Gfst]
      [sndp≡sndp′] = irrelevanceEqTerm′
        (PE.cong (λ x → x [ fst p″ t ]₀) (wk-lift-id G))
        ([G] id ⊢Γ [fstt]) [Gfst]
        [snd≡]′

      [fstt′] , [fstt′≡fstp′] = redSubst*Term
        (PE.subst (λ x → Γ ⊢ fst p″ t′ ⇒* fst p″ p′ ∷ x)
           (PE.sym (wk-id F))
           (fst-subst* (redₜ d′) ⊢F ⊢G))
        ([F] id ⊢Γ) [fstp′]
      [fstt≡fstt′] = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                        [F]′ ([F] id ⊢Γ)
                                        (fst-cong′ [F]′ [ΣFG] [t≡t′])
      [fstt≡fstp′] = transEqTerm ([F] id ⊢Γ) [fstt≡fstt′] [fstt′≡fstp′]
      [Gfstt≡Gfstp′] = G-ext id ⊢Γ [fstt] [fstp′] [fstt≡fstp′]
      [sndp′]′ : Γ ⊩⟨ l ⟩ snd p″ p′ ∷ U.wk (lift id) G [ fst p″ t ]₀ /
                   [G] id ⊢Γ [fstt]
      [sndp′]′ = convTerm₂ ([G] id ⊢Γ [fstt]) ([G] id ⊢Γ [fstp′]) [Gfstt≡Gfstp′] [sndp′]
      [sndp′]″ = irrelevanceTerm′
        (PE.cong (λ x → x [ fst p″ t ]₀) (wk-lift-id G))
        ([G] id ⊢Γ [fstt]) [Gfst]
        [sndp′]′
      [Gfstt]′ = irrelevance′
        (PE.cong (λ x → x [ fst p″ t ]₀) (wk-lift-id G))
        ([G] id ⊢Γ [fstt])
      [Gfstt≡Gfstt′] = irrelevanceEq″
        (PE.cong (λ x → x [ fst p″ t ]₀) (wk-lift-id G))
        (PE.cong (λ x → x [ fst p″ t′ ]₀) (wk-lift-id G))
        ([G] id ⊢Γ [fstt]) [Gfstt]′
        (G-ext id ⊢Γ [fstt] [fstt′] [fstt≡fstt′])
      sndt′⇒*sndp′ : Γ ⊢ snd p″ t′ ⇒* snd p″ p′ ∷ G [ fst p″ t ]₀
      sndt′⇒*sndp′ = conv* (snd-subst* [F]′ (B-intr BΣ! [ΣFG]) [p′] (redₜ d′))
                           (≅-eq (≅-sym (escapeEq [Gfstt]′ [Gfstt≡Gfstt′])))
      [sndt′≡sndp′] : Γ ⊩⟨ l′ ⟩ snd p″ t′ ≡ snd p″ p′ ∷ G [ fst p″ t ]₀ /
                        [Gfst]
      [sndt′≡sndp′] = proj₂ (redSubst*Term sndt′⇒*sndp′ [Gfst] [sndp′]″)

  in  transEqTerm [Gfst] [sndt≡sndp] (transEqTerm [Gfst] [sndp≡sndp′] (symEqTerm [Gfst] [sndt′≡sndp′]))
snd-cong′ {F} {G} (emb 0<1 x) = snd-cong′ x

snd-cong″ : ∀ {F G t t′ l l′}
            ([ΣFG] : Γ ⊩⟨ l ⟩ Σˢ p , q ▷ F ▹ G)
            ([t] : Γ ⊩⟨ l ⟩ t ∷ Σˢ p , q ▷ F ▹ G / [ΣFG])
            ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ Σˢ p , q ▷ F ▹ G / [ΣFG])
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σˢ p , q ▷ F ▹ G / [ΣFG])
            ([Gfst] : Γ ⊩⟨ l′ ⟩ G [ fst p t ]₀)
            → Γ ⊩⟨ l′ ⟩ snd p t ≡ snd p t′ ∷ G [ fst p t ]₀ / [Gfst]
snd-cong″ {F} {G} [ΣFG] [t] [t′] [t≡t′] [Gfst] =
  let [t] = irrelevanceTerm [ΣFG] (B-intr BΣ! (Σ-elim [ΣFG])) [t]
      [t′] = irrelevanceTerm [ΣFG] (B-intr BΣ! (Σ-elim [ΣFG])) [t′]
      [t≡t′] = irrelevanceEqTerm [ΣFG] (B-intr BΣ! (Σ-elim [ΣFG])) [t≡t′]
  in  snd-cong′ (B-elim BΣ! [ΣFG]) [t] [t′] [t≡t′] [Gfst]

snd-congᵛ :
  ∀ {F G t t′ l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σˢ-allowed p q)
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σˢ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G] ok)
  ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Σˢ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G] ok)
  ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Σˢ p , q ▷ F ▹ G / [Γ] /
              Σᵛ [Γ] [F] [G] ok) →
  Γ ⊩ᵛ⟨ l ⟩ snd p t ≡ snd p t′ ∷ G [ fst p t ]₀ / [Γ] /
    substS [Γ] [F] [G] (fstᵛ {t = t} [Γ] [F] [G] ok [t])
snd-congᵛ
  {Γ = Γ} {F = F} {G} {t} {t′} {l}
  [Γ] [F] [G] ok [t] [t′] [t≡t′] {Δ} {σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G] ok
      [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] ok [t]
      [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]

      ⊩σΣFG = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
      ⊩σt = proj₁ ([t] ⊢Δ [σ])
      ⊩σt′ = proj₁ ([t′] ⊢Δ [σ])
      σt≡σt′ = [t≡t′] ⊢Δ [σ]

      ⊩σGfst₁ = proj₁ (unwrap [Gfst] ⊢Δ [σ])
      ⊩σGfst = irrelevance′ (singleSubstLift G (fst _ t)) ⊩σGfst₁

      σsnd≡₁ = snd-cong″ ⊩σΣFG ⊩σt ⊩σt′ σt≡σt′ ⊩σGfst
      σsnd≡ = irrelevanceEqTerm′ (PE.sym (singleSubstLift G (fst _ t)))
                ⊩σGfst ⊩σGfst₁ σsnd≡₁
  in  σsnd≡

-- Validity of second projection
sndᵛ :
  ∀ {F G t l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σˢ-allowed p q)
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G] ok) →
  Γ ⊩ᵛ⟨ l ⟩ snd p t ∷ G [ fst p t ]₀ / [Γ] /
    substS [Γ] [F] [G] (fstᵛ {t = t} [Γ] [F] [G] ok [t])
sndᵛ
  {Γ = Γ} {F = F} {G} {t} {l}
  [Γ] [F] [G] ok [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G] ok
      [Gfst] : Γ ⊩ᵛ⟨ l ⟩ G [ fst _ t ]₀ / [Γ]
      [Gfst] = substS [Γ] [F] [G] (fstᵛ {t = t} [Γ] [F] [G] ok [t])

      σsnd : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ l ⟩ snd _ t [ σ ] ∷ G [ fst _ t ]₀ [ σ ] /
               proj₁ (unwrap [Gfst] ⊢Δ [σ])
      σsnd {Δ} {σ} ⊢Δ [σ] =
        let ⊩σΣFG = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
            ⊩σt = proj₁ ([t] ⊢Δ [σ])
            ⊩σGfstt = proj₁ (unwrap [Gfst] ⊢Δ [σ])
            ⊩σGfstt′ = PE.subst (λ x → Δ ⊩⟨ l ⟩ x)
                         (singleSubstLift G (fst _ t)) ⊩σGfstt
            ⊩σsnd = snd″ ⊩σΣFG ⊩σt ⊩σGfstt′
        in  irrelevanceTerm′
              (PE.sym (singleSubstLift G (fst _ t)))
              ⊩σGfstt′  ⊩σGfstt
              ⊩σsnd

  in  σsnd ⊢Δ [σ] ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
            [σΣFG] = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
            [σ′ΣFG] = proj₁ (unwrap [ΣFG] ⊢Δ [σ′])
            [σΣFG≡σ′ΣFG] = proj₂ (unwrap [ΣFG] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σt] = proj₁ ([t] ⊢Δ [σ])
            [σ′t] = proj₁ ([t] ⊢Δ [σ′])
            [σ′t] : Δ ⊩⟨ l ⟩ t [ σ′ ] ∷ (Σ _ , _ ▷ F ▹ G) [ σ ] /
                      [σΣFG]
            [σ′t] = convTerm₂ [σΣFG] [σ′ΣFG] [σΣFG≡σ′ΣFG] [σ′t]
            [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
            [σGfstt] = proj₁ (unwrap [Gfst] ⊢Δ [σ])
            [σGfstt]′ = PE.subst (λ x → _ ⊩⟨ l ⟩ x)
                                (singleSubstLift G (fst _ t))
                                [σGfstt]
            [sndt≡sndt′] = snd-cong″ [σΣFG] [σt] [σ′t] [σt≡σ′t] [σGfstt]′
        in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G (fst _ t)))
                               [σGfstt]′ [σGfstt]
                               [sndt≡sndt′])
