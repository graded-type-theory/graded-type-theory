open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Prod
  {a} (M : Set a) {{eqrel : EqRelSet M}} where

open EqRelSet {{...}}

open import Definition.Untyped M as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.Weakening M as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.LogicalRelation M
open import Definition.LogicalRelation.ShapeView M
open import Definition.LogicalRelation.Irrelevance M
open import Definition.LogicalRelation.Properties M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Reflexivity M
open import Definition.LogicalRelation.Substitution.Introductions.Pi M
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst M

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n   : Nat
    p q : M
    Γ   : Con Term n
    F   : Term n
    m   : SigmaMode

prod′ : ∀ {Γ : Con Term n} {F : Term n} {G t u l l′ l″}
       ([F] : Γ ⊩⟨ l ⟩ F)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
       ([Gt] : Γ ⊩⟨ l″ ⟩ G [ t ])
       ([u] : Γ ⊩⟨ l″ ⟩ u ∷ G [ t ] / [Gt])
       ([ΣFG] : Γ ⊩⟨ l′ ⟩B⟨ BΣ m p q ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G)
     → Γ ⊩⟨ l′ ⟩ prod m p t u ∷ Σ p , q ▷ F ▹ G / B-intr BΣ! [ΣFG]
prod′
  {m = Σₚ} {p = p} {q = q} {Γ = Γ} {F} {G} {t} {u} {l} {l′} {l″}
  [F] [t] [Gt] [u]
  [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext))
  with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let ⊢t = escapeTerm [F] [t]
      ⊢u = escapeTerm [Gt] [u]
      ⊢Γ = wf ⊢F
      ⊢prod = prodⱼ ⊢F ⊢G ⊢t ⊢u

      fst⇒t : Γ ⊢ fst _ (prodₚ _ t u) ⇒ t ∷ F
      fst⇒t = Σ-β₁ ⊢F ⊢G ⊢t ⊢u PE.refl
      [fstprod] , [fstprod≡t] = redSubstTerm fst⇒t [F] [t]
      [fstprod]′ = irrelevanceTerm′ (PE.sym (wk-id F))
                                    [F] ([F]₁ id ⊢Γ)
                                    [fstprod]

      wkLiftIdEq = PE.cong (λ x → x [ fst _ (prodₚ _ t u ) ])
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

      [Gfst≡Gt] = irrelevanceEq″ wkLiftIdEq (PE.cong (λ x → x [ t ]) (wk-lift-id G))
                                 [Gfst] [Gfst]′
                                 (G-ext id ⊢Γ [fstprod]′ [t]′ [fstprod≡t]′)
      [u]′ = convTerm₂ [Gfst]′ [Gt] [Gfst≡Gt] [u]

      snd⇒u : Γ ⊢ snd _ (prodₚ _ t u) ⇒ u ∷ G [ fst _ (prodₚ _ t u) ]
      snd⇒u = Σ-β₂ ⊢F ⊢G ⊢t ⊢u PE.refl
      [sndprod] , [sndprod≡u] = redSubstTerm snd⇒u [Gfst]′ [u]′
      [sndprod]′ = irrelevanceTerm′ (PE.cong (_[ _ ]) (PE.sym (wk-lift-id G)))
                                    [Gfst]′ [Gfst] [sndprod]


      [fstRefl] = transEqTerm [F] [fstprod≡t] (symEqTerm [F] [fstprod≡t])
      [sndRefl] = transEqTerm [Gfst]′ [sndprod≡u] (symEqTerm [Gfst]′ [sndprod≡u])
  in  Σₜ (prodₚ _ t u) (idRedTerm:*: ⊢prod)
         (≅-Σ-η ⊢F ⊢G ⊢prod ⊢prod prodₙ prodₙ
                (escapeTermEq [F] [fstRefl])
                (escapeTermEq [Gfst]′ [sndRefl]))
         prodₙ ([fstprod]′ , [sndprod]′)

prod′ {m = Σᵣ} {q = q} {Γ = Γ} {F} {G} {t} {u} {l} {l′} {l″} [F] [t] [Gt] [u]
      [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext)) with
        B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let ⊢t = escapeTerm [F] [t]
      ⊢u = escapeTerm [Gt] [u]
      ⊢Γ = wf ⊢F
      ⊢prod = prodⱼ ⊢F ⊢G ⊢t ⊢u

      [t≡t] = reflEqTerm [F] [t]
      [u≡u] = reflEqTerm [Gt] [u]

      [t]′ = irrelevanceTerm′ (PE.sym (wk-id F)) [F] ([F]₁ id ⊢Γ) [t]
      [u]′ = irrelevanceTerm′ (PE.cong (_[ _ ]) (PE.sym (wk-lift-id G)))
                              [Gt] ([G]₁ id ⊢Γ [t]′) [u]

  in  Σₜ (prodᵣ _ t u) (idRedTerm:*: ⊢prod)
         (≅-prod-cong ⊢F ⊢G (escapeTermEq [F] [t≡t])
            (escapeTermEq [Gt] [u≡u]))
         prodₙ
         (PE.refl , [t]′ , [u]′ , PE.refl)
prod′ {Γ = Γ} {F} {G} {t} {u} {l} {l′} [F] [t] [Gt] [u]
      [ΣFG]@(emb 0<1 x) = prod′ [F] [t] [Gt] [u] x

prod″ : ∀ {Γ : Con Term n} {F : Term n} {G t u l l′}
       ([F] : Γ ⊩⟨ l ⟩ F)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ F / [F])
       ([Gt] : Γ ⊩⟨ l ⟩ G [ t ])
       ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ] / [Gt])
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
  ([Gt] : Γ ⊩⟨ l ⟩ G [ t ])
  ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ] / [Gt])
  ([u′] : Γ ⊩⟨ l ⟩ u′ ∷ G [ t ] / [Gt])
  ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ G [ t ] / [Gt])
  ([ΣFG] : Γ ⊩⟨ l′ ⟩B⟨ BΣ m p q ⟩ Σ⟨ m ⟩ p , q  ▷ F ▹ G) →
  Γ ⊩⟨ l′ ⟩ prod m p t u ≡ prod m p t′ u′ ∷ Σ p , q ▷ F ▹ G /
    B-intr BΣ! [ΣFG]
prod-cong′
  {m = Σₚ} {p = p} {q = q} {Γ = Γ} {F} {G} {t} {t′} {u} {u′} {l} {l′}
  [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′]
  [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext))
  with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let [prod] = prod′ {m = Σₚ} [F] [t] [Gt] [u] [ΣFG]

      ⊢Γ = wf ⊢F
      wk[F] = [F]₁ id ⊢Γ
      wk[t] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [t]
      wk[t′] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [t′]
      wk[t≡t′] = irrelevanceEqTerm′ (PE.sym (wk-id F)) [F] wk[F] [t≡t′]
      wk[Gt] = [G]₁ id ⊢Γ wk[t]
      wk[Gt′] = [G]₁ id ⊢Γ wk[t′]
      wk[Gt≡Gt′] = G-ext id ⊢Γ wk[t] wk[t′] wk[t≡t′]
      wk[u] = irrelevanceTerm′ (PE.cong (_[ t ]) (PE.sym (wk-lift-id G))) [Gt] wk[Gt] [u]

      [Gt′] = irrelevance′ (PE.cong (λ x → x [ t′ ]) (wk-lift-id G)) wk[Gt′]
      [Gt≡Gt′] = irrelevanceEq″ (PE.cong (λ x → x [ t ]) (wk-lift-id G))
                                (PE.cong (λ x → x [ t′ ]) (wk-lift-id G))
                                wk[Gt] [Gt]
                                wk[Gt≡Gt′]

      [u′]Gt′ = convTerm₁ [Gt] [Gt′] [Gt≡Gt′] [u′]
      wk[u′] = irrelevanceTerm′ (PE.sym (PE.cong (_[ t′ ]) (wk-lift-id G)))
                                [Gt′] wk[Gt′] [u′]Gt′

      [prod′] = prod′ [F] [t′] [Gt′] [u′]Gt′ [ΣFG]

      ⊢t = escapeTerm [F] [t]
      ⊢t′ = escapeTerm [F] [t′]
      ⊢u = escapeTerm [Gt] [u]
      ⊢u′ = escapeTerm [Gt′] [u′]Gt′

      fst⇒t = Σ-β₁ ⊢F ⊢G ⊢t ⊢u PE.refl
      [fst] , [fst≡t] = redSubstTerm fst⇒t [F] [t]
      fst⇒t′ = Σ-β₁ ⊢F ⊢G ⊢t′ ⊢u′ PE.refl
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

      -- snd (prod t u) ≡ u ∷ G [ fst (prod t u) ]
      wkLiftIdEq = PE.cong (λ x → x [ fst _ (prodₚ _ t u ) ])
                     (wk-lift-id G)
      wk[Gfst] = [G]₁ id ⊢Γ wk[fst]
      [Gfst] = irrelevance′ wkLiftIdEq wk[Gfst]
      [Gfst≡Gt] = irrelevanceEq″ wkLiftIdEq (PE.cong (λ x → x [ t ])
                                                     (wk-lift-id G))
                                 wk[Gfst] [Gfst]
                                 (G-ext id ⊢Γ wk[fst] wk[t] wk[fst≡t])

      [u]fst = convTerm₂ [Gfst] [Gt] [Gfst≡Gt] [u]
      snd⇒u = Σ-β₂ ⊢F ⊢G ⊢t ⊢u PE.refl
      [snd] , [snd≡u] = redSubstTerm snd⇒u [Gfst] [u]fst

      -- u ≡ u′ ∷ G [ fst (prod t u) ]
      [u≡u′]Gfst = convEqTerm₂ [Gfst] [Gt] [Gfst≡Gt] [u≡u′]

      -- u′ ≡ snd (prod t′ u′) ∷ G [ fst (prod t u) ]
      wkLiftIdEq′ = PE.cong (λ x → x [ fst _ (prodₚ _ t′ u′) ])
                      (wk-lift-id G)
      wk[Gfst′] = [G]₁ id ⊢Γ wk[fst′]
      [Gfst′] = irrelevance′ wkLiftIdEq′ wk[Gfst′]
      [Gfst′≡Gt′] = irrelevanceEq″ wkLiftIdEq′ (PE.cong (λ x → x [ t′ ])
                                                        (wk-lift-id G))
                                   wk[Gfst′] [Gfst′]
                                   (G-ext id ⊢Γ wk[fst′] wk[t′] wk[fst≡t′])

      snd⇒u′ = Σ-β₂ ⊢F ⊢G ⊢t′ ⊢u′ PE.refl

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
        (PE.cong (λ x → x [ fst _ (prodₚ _ t u) ])
           (PE.sym (wk-lift-id G)))
        [Gfst] wk[Gfst]
        [snd≡snd′]

      ⊢prod = escapeTerm (B-intr BΣ! [ΣFG]) [prod]
      ⊢prod′ = escapeTerm (B-intr BΣ! [ΣFG]) [prod′]

  in  Σₜ₌ (prodₚ _ t u) (prodₚ _ t′ u′)
          (idRedTerm:*: ⊢prod) (idRedTerm:*: ⊢prod′)
          prodₙ prodₙ
          (≅-Σ-η ⊢F ⊢G ⊢prod ⊢prod′ prodₙ prodₙ
                 (escapeTermEq [F] [fst≡fst′])
                 (escapeTermEq [Gfst] [snd≡snd′]))
          [prod] [prod′]
          (wk[fst] , wk[fst′] , wk[fst≡fst′] , wk[snd≡snd′])

prod-cong′ {m = Σᵣ} {q = q} {Γ = Γ} {F} {G} {t} {t′} {u} {u′} {l} {l′}
           [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′]
           [ΣFG]@(noemb (Bᵣ F₁ G₁ D ⊢F ⊢G A≡A [F]₁ [G]₁ G-ext)) with
             B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let ⊢Γ = wf ⊢F
      wk[F] = [F]₁ id ⊢Γ
      wk[t] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [t]
      wk[t′] = irrelevanceTerm′ (PE.sym (wk-id F)) [F] wk[F] [t′]
      wk[t≡t′] = irrelevanceEqTerm′ (PE.sym (wk-id F)) [F] wk[F] [t≡t′]
      wk[Gt] = [G]₁ id ⊢Γ wk[t]
      wk[Gt′] = [G]₁ id ⊢Γ wk[t′]
      wk[Gt≡Gt′] = G-ext id ⊢Γ wk[t] wk[t′] wk[t≡t′]
      wk[u] = irrelevanceTerm′ (PE.cong (_[ t ]) (PE.sym (wk-lift-id G))) [Gt] wk[Gt] [u]
      wk[u≡u′] = irrelevanceEqTerm′ (PE.cong (_[ t ]) (PE.sym (wk-lift-id G))) [Gt] wk[Gt] [u≡u′]

      [Gt′] = irrelevance′ (PE.cong (λ x → x [ t′ ]) (wk-lift-id G)) wk[Gt′]
      [Gt≡Gt′] = irrelevanceEq″ (PE.cong (λ x → x [ t ]) (wk-lift-id G))
                                (PE.cong (λ x → x [ t′ ]) (wk-lift-id G))
                                wk[Gt] [Gt]
                                wk[Gt≡Gt′]

      [u′]Gt′ = convTerm₁ [Gt] [Gt′] [Gt≡Gt′] [u′]
      wk[u′] = irrelevanceTerm′ (PE.sym (PE.cong (_[ t′ ]) (wk-lift-id G)))
                                [Gt′] wk[Gt′] [u′]Gt′

      [prod] = prod′ {m = Σᵣ} [F] [t] [Gt] [u] [ΣFG]
      [prod′] = prod′ [F] [t′] [Gt′] [u′]Gt′ [ΣFG]
      ⊢prod = escapeTerm (B-intr BΣ! [ΣFG]) [prod]
      ⊢prod′ = escapeTerm (B-intr BΣ! [ΣFG]) [prod′]
  in  Σₜ₌ (prodᵣ _ t u) (prodᵣ _ t′ u′)
          (idRedTerm:*: ⊢prod)
          (idRedTerm:*: ⊢prod′)
          prodₙ prodₙ
          (≅-prod-cong ⊢F ⊢G
             (escapeTermEq [F] [t≡t′]) (escapeTermEq [Gt] [u≡u′]))
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
  ([Gt] : Γ ⊩⟨ l ⟩ G [ t ])
  ([u] : Γ ⊩⟨ l ⟩ u ∷ G [ t ] / [Gt])
  ([u′] : Γ ⊩⟨ l ⟩ u′ ∷ G [ t ] / [Gt])
  ([u≡u′] : Γ ⊩⟨ l ⟩ u ≡ u′ ∷ G [ t ] / [Gt])
  ([ΣFG] : Γ ⊩⟨ l′ ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G) →
  Γ ⊩⟨ l′ ⟩ prod m p t u ≡ prod m p t′ u′ ∷ Σ p , q ▷ F ▹ G / [ΣFG]
prod-cong″ {m = m} [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] [ΣFG] =
  let [prod≡] = prod-cong′ {m = m} [F] [t] [t′] [t≡t′] [Gt] [u] [u′] [u≡u′] (B-elim BΣ! [ΣFG])
  in  irrelevanceEqTerm (B-intr BΣ! (B-elim BΣ! [ΣFG])) [ΣFG] [prod≡]

prod-congᵛ :
  ∀ {Γ : Con Term n} {F : Term n} {G t t′ u u′ l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ F / [Γ] / [F])
  ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ F / [Γ] / [F])
  ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substS [Γ] [F] [G] [t])
  ([u′] : Γ ⊩ᵛ⟨ l ⟩ u′ ∷ G [ t′ ] / [Γ] / substS [Γ] [F] [G] [t′])
  ([u≡u′] : Γ ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷ G [ t ] / [Γ] / substS [Γ] [F] [G] [t]) →
  Γ ⊩ᵛ⟨ l ⟩ prod m p t u ≡ prod m p t′ u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ] /
    Σᵛ [Γ] [F] [G]
prod-congᵛ {Γ = Γ} {F} {G} {t} {t′} {u} {u′} [Γ] [F] [G] [t] [t′] [t≡t′] [u] [u′] [u≡u′] {Δ = Δ} {σ} ⊢Δ [σ] =
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

      ⊩σΣFG = proj₁ (unwrap (Σᵛ {F = F} {G} [Γ] [F] [G]) ⊢Δ [σ])
  in prod-cong″ ⊩σF ⊩σt ⊩σt′ σt≡σt′ ⊩σGt ⊩σu ⊩σu′ σu≡σu′ ⊩σΣFG

prodᵛ :
  ∀ {Γ : Con Term n} {F : Term n} {G t u l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] / [Γ] / substS [Γ] [F] [G] [t]) →
  Γ ⊩ᵛ⟨ l ⟩ prod m p t u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G]
prodᵛ {Γ = Γ} {F} {G} {t} {u} {l} [Γ] [F] [G] [t] [u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [Gt] = substS {F = F} {G} [Γ] [F] [G] [t]
      [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]

      ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape ⊩σF
      ⊩σt = proj₁ ([t] ⊢Δ [σ])
      ⊩σGt′ : Δ ⊩⟨ l ⟩ subst σ (G [ t ])
      ⊩σGt′ = proj₁ (unwrap [Gt] ⊢Δ [σ])
      ⊩σGt : Δ ⊩⟨ l ⟩ subst (liftSubst σ) G [ subst σ t ]
      ⊩σGt = irrelevance′ (singleSubstLift G t) ⊩σGt′
      ⊩σu′ = proj₁ ([u] ⊢Δ [σ])
      ⊩σu : Δ ⊩⟨ l ⟩ subst σ u ∷ subst (liftSubst σ) G [ subst σ t ] / ⊩σGt
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

            σu≡σ′u : Δ ⊩⟨ l ⟩ subst σ u ≡ subst σ′ u ∷ subst (liftSubst σ) G [ subst σ t ] / ⊩σGt
            σu≡σ′u = irrelevanceEqTerm′ (singleSubstLift G t) ⊩σGt′ ⊩σGt (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′])
        in  prod-cong″ ⊩σF ⊩σt ⊩σ′t σt≡σ′t ⊩σGt ⊩σu ⊩σ′u σu≡σ′u ⊩σΣFG)
