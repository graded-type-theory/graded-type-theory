------------------------------------------------------------------------
-- Validity of pairs.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Prod
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
open import Definition.Typed.Weakening R as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Reflexivity R
open import
  Definition.LogicalRelation.Substitution.Introductions.DoubleSubst R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
import Definition.LogicalRelation.Substitution.Irrelevance R as IS
open import Definition.LogicalRelation.Substitution.Weakening R

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n   : Nat
    p q : M
    Γ   : Con Term n
    A F G : Term n
    m   : Strength

prod′ : ∀ {Γ : Con Term n} {F : Term n} {G t u l l′ l″}
       ([F] : Γ ⊩⟨ l ⟩ F)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
       ([Gt] : Γ ⊩⟨ l″ ⟩ G [ t ]₀)
       ([u] : Γ ⊩⟨ l″ ⟩ u ∷ G [ t ]₀ / [Gt])
       ([ΣFG] : Γ ⊩⟨ l′ ⟩B⟨ BΣ m p q ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G)
     → Γ ⊩⟨ l′ ⟩ prod m p t u ∷ Σ p , q ▷ F ▹ G / B-intr BΣ! [ΣFG]
prod′
  {m = 𝕤} {p = p} {q = q} {Γ = Γ} {F} {G} {t} {u} {l} {l′} {l″}
  [F] [t] [Gt] [u]
  [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext ok))
  with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let ⊢t = escapeTerm [F] [t]
      ⊢u = escapeTerm [Gt] [u]
      ⊢Γ = wf ⊢F
      ⊢prod = prodⱼ ⊢F ⊢G ⊢t ⊢u ok

      fst⇒t : Γ ⊢ fst _ (prodˢ _ t u) ⇒ t ∷ F
      fst⇒t = Σ-β₁ ⊢F ⊢G ⊢t ⊢u PE.refl ok
      [fstprod] , [fstprod≡t] = redSubstTerm fst⇒t [F] [t]
      [fstprod]′ = irrelevanceTerm′ (PE.sym (wk-id F))
                                    [F] ([F]₁ id ⊢Γ)
                                    [fstprod]

      wkLiftIdEq = PE.cong (λ x → x [ fst _ (prodˢ _ t u ) ]₀)
                     (wk-lift-id G)
      [Gfst] = [G]₁ id ⊢Γ [fstprod]′
      [Gfst]′ = irrelevance′ wkLiftIdEq [Gfst]

      [t]′ = irrelevanceTerm′ (PE.sym (wk-id F))
                              [F] ([F]₁ id ⊢Γ)
                              [t]
      [fstprod≡t]′ = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                        [F] ([F]₁ id ⊢Γ)
                                        [fstprod≡t]
      [Gt]′ = [G]₁ id ⊢Γ [t]′

      [Gfst≡Gt] = irrelevanceEq″ wkLiftIdEq (PE.cong (λ x → x [ t ]₀) (wk-lift-id G))
                                 [Gfst] [Gfst]′
                                 (G-ext id ⊢Γ [fstprod]′ [t]′ [fstprod≡t]′)
      [u]′ = convTerm₂ [Gfst]′ [Gt] [Gfst≡Gt] [u]

      snd⇒u : Γ ⊢ snd _ (prodˢ _ t u) ⇒ u ∷ G [ fst _ (prodˢ _ t u) ]₀
      snd⇒u = Σ-β₂ ⊢F ⊢G ⊢t ⊢u PE.refl ok
      [sndprod] , [sndprod≡u] = redSubstTerm snd⇒u [Gfst]′ [u]′
      [sndprod]′ = irrelevanceTerm′ (PE.cong (_[ _ ]₀) (PE.sym (wk-lift-id G)))
                                    [Gfst]′ [Gfst] [sndprod]


      [fstRefl] = transEqTerm [F] [fstprod≡t] (symEqTerm [F] [fstprod≡t])
      [sndRefl] = transEqTerm [Gfst]′ [sndprod≡u] (symEqTerm [Gfst]′ [sndprod≡u])
  in  Σₜ (prodˢ _ t u) (idRedTerm:*: ⊢prod)
         (≅-Σ-η ⊢F ⊢G ⊢prod ⊢prod prodₙ prodₙ
                (escapeTermEq [F] [fstRefl])
                (escapeTermEq [Gfst]′ [sndRefl]))
         prodₙ ([fstprod]′ , [sndprod]′)

prod′ {m = 𝕨} {q = q} {Γ = Γ} {F} {G} {t} {u} {l} {l′} {l″} [F] [t] [Gt] [u]
      [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext ok)) with
        B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let ⊢t = escapeTerm [F] [t]
      ⊢u = escapeTerm [Gt] [u]
      ⊢Γ = wf ⊢F
      ⊢prod = prodⱼ ⊢F ⊢G ⊢t ⊢u ok

      [t≡t] = reflEqTerm [F] [t]
      [u≡u] = reflEqTerm [Gt] [u]

      [t]′ = irrelevanceTerm′ (PE.sym (wk-id F)) [F] ([F]₁ id ⊢Γ) [t]
      [u]′ = irrelevanceTerm′ (PE.cong (_[ _ ]₀) (PE.sym (wk-lift-id G)))
                              [Gt] ([G]₁ id ⊢Γ [t]′) [u]

  in  Σₜ (prodʷ _ t u) (idRedTerm:*: ⊢prod)
         (≅-prod-cong ⊢F ⊢G (escapeTermEq [F] [t≡t])
            (escapeTermEq [Gt] [u≡u]) ok)
         prodₙ
         (PE.refl , [t]′ , [u]′ , PE.refl)
prod′ {Γ = Γ} {F} {G} {t} {u} {l} {l′} [F] [t] [Gt] [u]
      [ΣFG]@(emb 0<1 x) = prod′ [F] [t] [Gt] [u] x

prod″ : ∀ {Γ : Con Term n} {F : Term n} {G t u l l′}
       ([F] : Γ ⊩⟨ l ⟩ F)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
       ([Gt] : Γ ⊩⟨ l ⟩ G [ t ]₀)
       ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ]₀ / [Gt])
       ([ΣFG] : Γ ⊩⟨ l′ ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G)
     → Γ ⊩⟨ l′ ⟩ prod m p t u ∷ Σ _ , _ ▷ F ▹ G / [ΣFG]
prod″ {m = m} [F] [t] [Gt] [u] [ΣFG] =
      let [prod] = prod′ {m = m} [F] [t] [Gt] [u] (B-elim BΣ! [ΣFG])
      in  irrelevanceTerm (B-intr BΣ! (B-elim BΣ! [ΣFG])) [ΣFG] [prod]

prod-cong′ :
  ∀ {Γ : Con Term n} {F : Term n} {G t t′ u u′ l l′}
  ([F] : Γ ⊩⟨ l ⟩ F)
  ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
  ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ F / [F])
  ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ F / [F])
  ([Gt] : Γ ⊩⟨ l ⟩ G [ t ]₀)
  ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ]₀ / [Gt])
  ([u′] : Γ ⊩⟨ l ⟩ u′ ∷ G [ t ]₀ / [Gt])
  ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ G [ t ]₀ / [Gt])
  ([ΣFG] : Γ ⊩⟨ l′ ⟩B⟨ BΣ m p q ⟩ Σ⟨ m ⟩ p , q  ▷ F ▹ G) →
  Γ ⊩⟨ l′ ⟩ prod m p t u ≡ prod m p t′ u′ ∷ Σ p , q ▷ F ▹ G /
    B-intr BΣ! [ΣFG]
prod-cong′
  {m = 𝕤} {p = p} {q = q} {Γ = Γ} {F} {G} {t} {t′} {u} {u′} {l} {l′}
  [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′]
  [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext ok))
  with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let [prod] = prod′ {m = 𝕤} [F] [t] [Gt] [u] [ΣFG]

      ⊢Γ = wf ⊢F
      wk[F] = [F]₁ id ⊢Γ
      wk[t] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [t]
      wk[t′] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [t′]
      wk[t≡t′] = irrelevanceEqTerm′ (PE.sym (wk-id F)) [F] wk[F] [t≡t′]
      wk[Gt] = [G]₁ id ⊢Γ wk[t]
      wk[Gt′] = [G]₁ id ⊢Γ wk[t′]
      wk[Gt≡Gt′] = G-ext id ⊢Γ wk[t] wk[t′] wk[t≡t′]
      wk[u] = irrelevanceTerm′ (PE.cong (_[ t ]₀) (PE.sym (wk-lift-id G))) [Gt] wk[Gt] [u]

      [Gt′] = irrelevance′ (PE.cong (λ x → x [ t′ ]₀) (wk-lift-id G)) wk[Gt′]
      [Gt≡Gt′] = irrelevanceEq″ (PE.cong (λ x → x [ t ]₀) (wk-lift-id G))
                                (PE.cong (λ x → x [ t′ ]₀) (wk-lift-id G))
                                wk[Gt] [Gt]
                                wk[Gt≡Gt′]

      [u′]Gt′ = convTerm₁ [Gt] [Gt′] [Gt≡Gt′] [u′]
      wk[u′] = irrelevanceTerm′ (PE.sym (PE.cong (_[ t′ ]₀) (wk-lift-id G)))
                                [Gt′] wk[Gt′] [u′]Gt′

      [prod′] = prod′ [F] [t′] [Gt′] [u′]Gt′ [ΣFG]

      ⊢t = escapeTerm [F] [t]
      ⊢t′ = escapeTerm [F] [t′]
      ⊢u = escapeTerm [Gt] [u]
      ⊢u′ = escapeTerm [Gt′] [u′]Gt′

      fst⇒t = Σ-β₁ ⊢F ⊢G ⊢t ⊢u PE.refl ok
      [fst] , [fst≡t] = redSubstTerm fst⇒t [F] [t]
      fst⇒t′ = Σ-β₁ ⊢F ⊢G ⊢t′ ⊢u′ PE.refl ok
      [fst′] , [fst≡t′] = redSubstTerm fst⇒t′ [F] [t′]

      wk[fst≡t] = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                      [F] wk[F]
                                      [fst≡t]
      wk[fst≡t′] = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                      [F] wk[F]
                                      [fst≡t′]

      wk[fst] = irrelevanceTerm′ (PE.sym (wk-id F))
                                 [F] wk[F]
                                 [fst]
      wk[fst′] = irrelevanceTerm′ (PE.sym (wk-id F))
                                 [F] wk[F]
                                 [fst′]

      -- fst t ≡ fst t′ ∷ F
      [fst≡fst′] = transEqTerm [F] [fst≡t] (transEqTerm [F] [t≡t′] (symEqTerm [F] [fst≡t′]))
      wk[fst≡fst′] = irrelevanceEqTerm′ (PE.sym (wk-id F))
                                        [F] wk[F]
                                        [fst≡fst′]

      -- snd (prod t u) ≡ u ∷ G [ fst (prod t u) ]₀
      wkLiftIdEq = PE.cong (λ x → x [ fst _ (prodˢ _ t u ) ]₀)
                     (wk-lift-id G)
      wk[Gfst] = [G]₁ id ⊢Γ wk[fst]
      [Gfst] = irrelevance′ wkLiftIdEq wk[Gfst]
      [Gfst≡Gt] = irrelevanceEq″ wkLiftIdEq (PE.cong (λ x → x [ t ]₀)
                                                     (wk-lift-id G))
                                 wk[Gfst] [Gfst]
                                 (G-ext id ⊢Γ wk[fst] wk[t] wk[fst≡t])

      [u]fst = convTerm₂ [Gfst] [Gt] [Gfst≡Gt] [u]
      snd⇒u = Σ-β₂ ⊢F ⊢G ⊢t ⊢u PE.refl ok
      [snd] , [snd≡u] = redSubstTerm snd⇒u [Gfst] [u]fst

      -- u ≡ u′ ∷ G [ fst (prod t u) ]₀
      [u≡u′]Gfst = convEqTerm₂ [Gfst] [Gt] [Gfst≡Gt] [u≡u′]

      -- u′ ≡ snd (prod t′ u′) ∷ G [ fst (prod t u) ]₀
      wkLiftIdEq′ = PE.cong (λ x → x [ fst _ (prodˢ _ t′ u′) ]₀)
                      (wk-lift-id G)
      wk[Gfst′] = [G]₁ id ⊢Γ wk[fst′]
      [Gfst′] = irrelevance′ wkLiftIdEq′ wk[Gfst′]
      [Gfst′≡Gt′] = irrelevanceEq″ wkLiftIdEq′ (PE.cong (λ x → x [ t′ ]₀)
                                                        (wk-lift-id G))
                                   wk[Gfst′] [Gfst′]
                                   (G-ext id ⊢Γ wk[fst′] wk[t′] wk[fst≡t′])

      snd⇒u′ = Σ-β₂ ⊢F ⊢G ⊢t′ ⊢u′ PE.refl ok

      [u′]Gfst′ = convTerm₂ [Gfst′] [Gt′] [Gfst′≡Gt′] [u′]Gt′
      [snd≡u′]Gfst′ = proj₂ (redSubstTerm snd⇒u′ [Gfst′] [u′]Gfst′)

      [Gfst≡Gfst′] = irrelevanceEq″ wkLiftIdEq wkLiftIdEq′
                                    wk[Gfst] [Gfst]
                                    (G-ext id ⊢Γ wk[fst] wk[fst′] wk[fst≡fst′])

      [snd≡u′]Gfst = convEqTerm₂ [Gfst] [Gfst′] [Gfst≡Gfst′] [snd≡u′]Gfst′

      [snd≡snd′] = transEqTerm [Gfst] [snd≡u]
                               (transEqTerm [Gfst] [u≡u′]Gfst
                                            (symEqTerm [Gfst] [snd≡u′]Gfst))
      wk[snd≡snd′] = irrelevanceEqTerm′
        (PE.cong (λ x → x [ fst _ (prodˢ _ t u) ]₀)
           (PE.sym (wk-lift-id G)))
        [Gfst] wk[Gfst]
        [snd≡snd′]

      ⊢prod = escapeTerm (B-intr BΣ! [ΣFG]) [prod]
      ⊢prod′ = escapeTerm (B-intr BΣ! [ΣFG]) [prod′]

  in  Σₜ₌ (prodˢ _ t u) (prodˢ _ t′ u′)
          (idRedTerm:*: ⊢prod) (idRedTerm:*: ⊢prod′)
          prodₙ prodₙ
          (≅-Σ-η ⊢F ⊢G ⊢prod ⊢prod′ prodₙ prodₙ
                 (escapeTermEq [F] [fst≡fst′])
                 (escapeTermEq [Gfst] [snd≡snd′]))
          [prod] [prod′]
          (wk[fst] , wk[fst′] , wk[fst≡fst′] , wk[snd≡snd′])

prod-cong′ {m = 𝕨} {q = q} {Γ = Γ} {F} {G} {t} {t′} {u} {u′} {l} {l′}
           [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′]
           [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext ok))
           with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let ⊢Γ = wf ⊢F
      wk[F] = [F]₁ id ⊢Γ
      wk[t] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [t]
      wk[t′] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [t′]
      wk[t≡t′] = irrelevanceEqTerm′ (PE.sym (wk-id F)) [F] wk[F] [t≡t′]
      wk[Gt] = [G]₁ id ⊢Γ wk[t]
      wk[Gt′] = [G]₁ id ⊢Γ wk[t′]
      wk[Gt≡Gt′] = G-ext id ⊢Γ wk[t] wk[t′] wk[t≡t′]
      wk[u] = irrelevanceTerm′ (PE.cong (_[ t ]₀) (PE.sym (wk-lift-id G))) [Gt] wk[Gt] [u]
      wk[u≡u′] = irrelevanceEqTerm′ (PE.cong (_[ t ]₀) (PE.sym (wk-lift-id G))) [Gt] wk[Gt] [u≡u′]

      [Gt′] = irrelevance′ (PE.cong (λ x → x [ t′ ]₀) (wk-lift-id G)) wk[Gt′]
      [Gt≡Gt′] = irrelevanceEq″ (PE.cong (λ x → x [ t ]₀) (wk-lift-id G))
                                (PE.cong (λ x → x [ t′ ]₀) (wk-lift-id G))
                                wk[Gt] [Gt]
                                wk[Gt≡Gt′]

      [u′]Gt′ = convTerm₁ [Gt] [Gt′] [Gt≡Gt′] [u′]
      wk[u′] = irrelevanceTerm′ (PE.sym (PE.cong (_[ t′ ]₀) (wk-lift-id G)))
                                [Gt′] wk[Gt′] [u′]Gt′

      [prod] = prod′ {m = 𝕨} [F] [t] [Gt] [u] [ΣFG]
      [prod′] = prod′ [F] [t′] [Gt′] [u′]Gt′ [ΣFG]
      ⊢prod = escapeTerm (B-intr BΣ! [ΣFG]) [prod]
      ⊢prod′ = escapeTerm (B-intr BΣ! [ΣFG]) [prod′]
  in  Σₜ₌ (prodʷ _ t u) (prodʷ _ t′ u′)
          (idRedTerm:*: ⊢prod)
          (idRedTerm:*: ⊢prod′)
          prodₙ prodₙ
          (≅-prod-cong ⊢F ⊢G
             (escapeTermEq [F] [t≡t′]) (escapeTermEq [Gt] [u≡u′])
             ok)
          [prod] [prod′]
          (PE.refl , PE.refl ,
           wk[t] , wk[t′] , wk[u] , wk[u′] , wk[t≡t′] , wk[u≡u′])
prod-cong′ [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] (emb 0<1 x) =
  prod-cong′ [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] x

prod-cong″ :
  ∀ {Γ : Con Term n} {F : Term n} {G t t′ u u′ l l′}
  ([F] : Γ ⊩⟨ l ⟩ F)
  ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
  ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ F / [F])
  ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ F / [F])
  ([Gt] : Γ ⊩⟨ l ⟩ G [ t ]₀)
  ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ]₀ / [Gt])
  ([u′] : Γ ⊩⟨ l ⟩ u′ ∷ G [ t ]₀ / [Gt])
  ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ G [ t ]₀ / [Gt])
  ([ΣFG] : Γ ⊩⟨ l′ ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G) →
  Γ ⊩⟨ l′ ⟩ prod m p t u ≡ prod m p t′ u′ ∷ Σ p , q ▷ F ▹ G / [ΣFG]
prod-cong″ {m = m} [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] [ΣFG] =
  let [prod≡] = prod-cong′ {m = m} [F] [t] [t′] [t≡t′] [Gt] [u] [u′]
                  [u≡u′] (B-elim BΣ! [ΣFG])
  in  irrelevanceEqTerm (B-intr BΣ! (B-elim BΣ! [ΣFG])) [ΣFG] [prod≡]

prod-congᵛ :
  ∀ {Γ : Con Term n} {F : Term n} {G t t′ u u′ l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ F / [Γ] / [F])
  ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ F / [Γ] / [F])
  ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ]₀ / [Γ] / substS [Γ] [F] [G] [t])
  ([u′] : Γ ⊩ᵛ⟨ l ⟩ u′ ∷ G [ t′ ]₀ / [Γ] / substS [Γ] [F] [G] [t′])
  ([u≡u′] : Γ ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷ G [ t ]₀ / [Γ] / substS [Γ] [F] [G] [t])
  (ok : Σ-allowed m p q) →
  Γ ⊩ᵛ⟨ l ⟩ prod m p t u ≡ prod m p t′ u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ] /
    Σᵛ [Γ] [F] [G] ok
prod-congᵛ
  {Γ = Γ} {F} {G} {t} {t′} {u} {u′}
  [Γ] [F] [G] [t] [t′] [t≡t′] [u] [u′] [u≡u′] ok {Δ = Δ} {σ} ⊢Δ [σ] =
  let ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊩σt = proj₁ ([t] ⊢Δ [σ])
      ⊩σt′ = proj₁ ([t′] ⊢Δ [σ])
      σt≡σt′ = [t≡t′] ⊢Δ [σ]

      [Gt] = substS {F = F} {G} [Γ] [F] [G] [t]
      ⊩σGt₁ = proj₁ (unwrap [Gt] ⊢Δ [σ])
      ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt₁

      ⊩σu = irrelevanceTerm′ (singleSubstLift G t)
                             ⊩σGt₁ ⊩σGt
                             (proj₁ ([u] ⊢Δ [σ]))

      [Gt≡Gt′] = substSEq {F = F} {F′ = F} {G = G} {G′ = G} {t = t} {t′ = t′} [Γ]
                          [F] [F] (reflᵛ {A = F} [Γ] [F])
                          [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                          [t] [t′] [t≡t′]
      σGt≡σGt′ = [Gt≡Gt′] ⊢Δ [σ]

      ⊩σGt′ = proj₁ (unwrap (substS {F = F} {G} [Γ] [F] [G] [t′]) ⊢Δ [σ])
      ⊩σu′₂ = proj₁ ([u′] ⊢Δ [σ])
      ⊩σu′₁ = convTerm₂ ⊩σGt₁ ⊩σGt′ σGt≡σGt′ ⊩σu′₂
      ⊩σu′ = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt₁ ⊩σGt ⊩σu′₁

      σu≡σu′ = irrelevanceEqTerm′ (singleSubstLift G t)
                                  ⊩σGt₁ ⊩σGt
                                  ([u≡u′] ⊢Δ [σ])

      ⊩σΣFG = proj₁ (unwrap (Σᵛ {F = F} {G} [Γ] [F] [G] ok) ⊢Δ [σ])
  in prod-cong″ ⊩σF ⊩σt ⊩σt′ σt≡σt′ ⊩σGt ⊩σu ⊩σu′ σu≡σu′ ⊩σΣFG

prodᵛ :
  ∀ {Γ : Con Term n} {F : Term n} {G t u l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ]₀ / [Γ] / substS [Γ] [F] [G] [t])
  (ok : Σ-allowed m p q) →
  Γ ⊩ᵛ⟨ l ⟩ prod m p t u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ] /
    Σᵛ [Γ] [F] [G] ok
prodᵛ
  {Γ = Γ} {F} {G} {t} {u} {l} [Γ] [F] [G] [t] [u] ok
  {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [Gt] = substS {F = F} {G} [Γ] [F] [G] [t]
      [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G] ok

      ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape ⊩σF
      ⊩σt = proj₁ ([t] ⊢Δ [σ])
      ⊩σGt′ : Δ ⊩⟨ l ⟩ G [ t ]₀ [ σ ]
      ⊩σGt′ = proj₁ (unwrap [Gt] ⊢Δ [σ])
      ⊩σGt : Δ ⊩⟨ l ⟩ G [ liftSubst σ ] [ t [ σ ] ]₀
      ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt′
      ⊩σu′ = proj₁ ([u] ⊢Δ [σ])
      ⊩σu : Δ ⊩⟨ l ⟩ u [ σ ] ∷ G [ liftSubst σ ] [ t [ σ ] ]₀ / ⊩σGt
      ⊩σu = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt′ ⊩σGt ⊩σu′
      ⊩σΣFG = proj₁ (unwrap [ΣFG] ⊢Δ [σ])

  in  prod″ ⊩σF ⊩σt ⊩σGt ⊩σu ⊩σΣFG ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let ⊩σ′F = proj₁ (unwrap [F] ⊢Δ [σ′])
            σF≡σ′F = proj₂ (unwrap [F] ⊢Δ [σ]) [σ′] [σ≡σ′]

            ⊩σ′t = proj₁ ([t] ⊢Δ [σ′])
            ⊩σ′t = convTerm₂ ⊩σF ⊩σ′F σF≡σ′F ⊩σ′t
            σt≡σ′t = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]

            ⊩σ′Gt′ = proj₁ (unwrap [Gt] ⊢Δ [σ′])
            ⊩σ′Gt = irrelevance′ (singleSubstLift G t) ⊩σ′Gt′

            σGt≡σ′Gt = proj₂ (unwrap [Gt] ⊢Δ [σ]) [σ′] [σ≡σ′]

            ⊩σ′u″ = proj₁ ([u] ⊢Δ [σ′])
            ⊩σ′u′ = convTerm₂ ⊩σGt′ ⊩σ′Gt′ σGt≡σ′Gt ⊩σ′u″
            ⊩σ′u = irrelevanceTerm′ (singleSubstLift G t) ⊩σGt′ ⊩σGt ⊩σ′u′

            σu≡σ′u : Δ ⊩⟨ l ⟩ u [ σ ] ≡ u [ σ′ ] ∷ G [ liftSubst σ ] [ t [ σ ] ]₀ / ⊩σGt
            σu≡σ′u = irrelevanceEqTerm′ (singleSubstLift G t) ⊩σGt′ ⊩σGt (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′])
        in  prod-cong″ ⊩σF ⊩σt ⊩σ′t σt≡σ′t ⊩σGt ⊩σu ⊩σ′u σu≡σ′u ⊩σΣFG)

private

  [prod] : ∀ {l m}
         → ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
           ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ])
           ([A] : Γ ∙ (Σ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ]) →
           Σ-allowed m p q →
           Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ prod m p (var x1) (var x0) ∷ wk1 (wk1 (Σ⟨ m ⟩ p , q ▷ F ▹ G))
                           / [Γ] ∙ [F] ∙ [G] / wk1ᵛ ([Γ] ∙ [F]) [G] (wk1ᵛ [Γ] [F] [Σ])
  [prod] {Γ} {F} {G} {l} [Γ] [F] [G] [Σ] _ ok =
    let [ΓF] = [Γ] ∙ [F]
        [ΓFG] = [ΓF] ∙ [G]
        wk[F] = wk1ᵛ [ΓF] [G] (wk1ᵛ [Γ] [F] [F])
        wk[G] : Γ ∙ F ∙ G ∙ wk1 (wk1 F) ⊩ᵛ⟨ l ⟩ U.wk (lift (step (step id))) G / [Γ] ∙ [F] ∙ [G] ∙ wk[F]
        wk[G] = wrap λ {_} {Δ} {σ} ⊢Δ [σ] →
          let [tail] = proj₁ (proj₁ (proj₁ [σ]))
              [σF] = proj₁ (unwrap [F] ⊢Δ [tail])
              wk2[σF] = proj₁ (unwrap wk[F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
              [head] = proj₂ [σ]
              [head]′ = irrelevanceTerm′ (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)) wk2[σF] [σF] [head]
              [ρσ] : Δ ⊩ˢ consSubst (tail (tail (tail σ))) (head σ) ∷ Γ ∙ F / [ΓF] / ⊢Δ
              [ρσ] = [tail] , [head]′
              [ρσG] = proj₁ (unwrap [G] {σ = consSubst (tail (tail (tail σ))) (head σ)} ⊢Δ [ρσ])
              [ρσG]′ = irrelevance′ (PE.sym (PE.trans (subst-wk {ρ = lift (step (step id))} {σ = σ} G)
                                                      (substVar-to-subst (λ {x0 → PE.refl
                                                                            ;(x +1) → PE.refl}) G)))
                                    [ρσG]
          in  [ρσG]′ , λ {σ′} [σ′] [σ≡σ′] →
            let [tail′] = proj₁ (proj₁ (proj₁ [σ′]))
                [head′] = proj₂ [σ′]
                [σ′F] = proj₁ (unwrap [F] ⊢Δ [tail′])
                wk2[σ′F] = proj₁ (unwrap wk[F] {σ = tail σ′} ⊢Δ (proj₁ [σ′]))
                [head′]′ = irrelevanceTerm′ (wk2-tail F) wk2[σ′F] [σ′F] [head′]
                [ρσ′] : Δ ⊩ˢ consSubst (tail (tail (tail σ′))) (head σ′) ∷ Γ ∙ F / [ΓF] / ⊢Δ
                [ρσ′] = [tail′] , [head′]′
                [tail≡] = proj₁ (proj₁ (proj₁ [σ≡σ′]))
                [head≡] = proj₂ [σ≡σ′]
                [head≡]′ = irrelevanceEqTerm′ (wk2-tail F) wk2[σF] [σF] [head≡]
                [ρσ≡] : Δ ⊩ˢ consSubst (tail (tail (tail σ))) (head σ)
                           ≡ consSubst (tail (tail (tail σ′))) (head σ′) ∷ Γ ∙ F / [ΓF] / ⊢Δ / [ρσ]
                [ρσ≡] = [tail≡] , [head≡]′
                [ρσG≡] = proj₂ (unwrap [G] {σ = consSubst (tail (tail (tail σ))) (head σ)} ⊢Δ [ρσ])
                               {σ′ = consSubst (tail (tail (tail σ′))) (head σ′)} [ρσ′] [ρσ≡]
            in  irrelevanceEq″ (PE.sym (PE.trans (subst-wk G) (substVar-to-subst (λ { x0 → PE.refl ; (x +1) → PE.refl }) G)))
                               (PE.sym (PE.trans (subst-wk G) (substVar-to-subst (λ { x0 → PE.refl ; (x +1) → PE.refl }) G)))
                               [ρσG] [ρσG]′ [ρσG≡]
        [x1] = var-⊩ᵛ∷// (there here) [ΓFG] wk[F]
        [x0]′ = var-⊩ᵛ∷// here [ΓFG] (wk1ᵛ [ΓF] [G] [G])
        wk[G[x1]] = substS [ΓFG] wk[F] wk[G] [x1]
        [x0] = IS.irrelevanceTerm′ (PE.sym (wkSingleSubstWk1 G)) [ΓFG] [ΓFG]
                                   (wk1ᵛ [ΓF] [G] [G]) wk[G[x1]] [x0]′
        [prod]′ = prodᵛ {F = wk1 (wk1 F)} {U.wk (lift (step (step id))) G} {var x1} {var x0}
                        [ΓFG] wk[F] wk[G] [x1] [x0] ok
        wk[Σ] = wk1ᵛ [ΓF] [G] (wk1ᵛ [Γ] [F] [Σ])
        wk[Σ]′ = Σᵛ [ΓFG] wk[F] wk[G] ok
    in  IS.irrelevanceTerm′ {t = prod _ _ (var x1) (var x0)}
                            (wk2-B BΣ! F G) [ΓFG] [ΓFG] wk[Σ]′ wk[Σ] [prod]′

subst↑²S-prod :
  ∀ {Γ : Con Term n} {F G A m l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ])
  ([A] : Γ ∙ (Σ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ]) →
  Σ-allowed m p q →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod m p (var x1) (var x0) ]↑² /
    [Γ] ∙ [F] ∙ [G]
subst↑²S-prod [Γ] [F] [G] [Σ] [A] ok =
  subst↑²S [Γ] [F] [G] [Σ] [A] ([prod] [Γ] [F] [G] [Σ] [A] ok)

subst↑²SEq-prod :
  ∀ {Γ : Con Term n} {F G A A′ m l} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ])
  ([A] : Γ ∙ (Σ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A′] : Γ ∙ (Σ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A′ / [Γ] ∙ [Σ])
  ([A≡A′] : Γ ∙ (Σ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A ≡ A′ / [Γ] ∙ [Σ] / [A])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod m p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G]) →
  Σ-allowed m p q →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A  [ prod m p (var x1) (var x0) ]↑² ≡
    A′ [ prod m p (var x1) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊]
subst↑²SEq-prod
  {n = n} {q = q} {Γ = Γ} {F} {G} {A} {A′} {m} {l}
  [Γ] [F] [G] [Σ] [A] [A′] [A≡A′] [A₊] ok =
    let [A₊≡A′₊] = subst↑²SEq {t = prod! (var x1) (var x0)} [Γ] [F] [G] [Σ] [A] [A′] [A≡A′] ([prod] [Γ] [F] [G] [Σ] [A] ok)
        [A₊]′ = subst↑²S-prod [Γ] [F] [G] [Σ] [A] ok
    in  IS.irrelevanceEq {B = A′ [ prod! (var x1) (var x0) ]↑²}
                         ([Γ] ∙ [F] ∙ [G]) ([Γ] ∙ [F] ∙ [G]) [A₊]′ [A₊] [A₊≡A′₊]
