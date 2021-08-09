{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Prodrec (M : Set) {{eqrel : EqRelSet M}} where
open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.RedSteps M

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Irrelevance M
open import Definition.LogicalRelation.Properties M
open import Definition.LogicalRelation.ShapeView M
open import Definition.LogicalRelation.Substitution M
open import Definition.LogicalRelation.Substitution.Introductions.Pi M
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst M
open import Definition.LogicalRelation.Substitution.Properties M

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Δ : Con Term n
    p q : M

prodrec-subst* : ∀ {l t t′ u A F G}
               → Γ ⊢ F
               → Γ ∙ F ⊢ G
               → Γ ∙ (Σ q ▷ F ▹ G) ⊢ A
               → Γ ∙ F ∙ G ⊢ u ∷ A [ prod (var (x0 +1)) (var x0) ]↑²
               → Γ ⊢ t ⇒* t′ ∷ (Σ q ▷ F ▹ G)
               → ([Σ] : Γ ⊩⟨ l ⟩ Σ q ▷ F ▹ G)
               → ([t′] : Γ ⊩⟨ l ⟩ t′ ∷ Σ q ▷ F ▹ G / [Σ])
               → (∀ {t t′} → Γ ⊩⟨ l ⟩ t  ∷ Σ q ▷ F ▹ G / [Σ]
                           → Γ ⊩⟨ l ⟩ t′ ∷ Σ q ▷ F ▹ G / [Σ]
                           → Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ q ▷ F ▹ G / [Σ]
                           → Γ ⊢ A [ t ] ≡ A [ t′ ])
               → Γ ⊢ prodrec p A t u ⇒* prodrec p A t′ u ∷ A [ t ]
prodrec-subst* ⊢F ⊢G ⊢A ⊢u (id x) [Σ] [t′] prop = id (prodrecⱼ ⊢F ⊢G x ⊢A ⊢u)
prodrec-subst* ⊢F ⊢G ⊢A ⊢u (x ⇨ t⇒t′) [Σ] [t′] prop =
  let q , w = redSubst*Term t⇒t′ [Σ] [t′]
      a , s = redSubstTerm x [Σ] q
  in  (prodrec-subst ⊢F ⊢G ⊢u ⊢A x) ⇨ conv* (prodrec-subst* ⊢F ⊢G ⊢A ⊢u t⇒t′ [Σ] [t′] prop)
                                            (prop q a (symEqTerm [Σ] s))


prodrecTerm : ∀ {F G A t u σ l}
              ([Γ] : ⊩ᵛ Γ)
              ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
              ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
              ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ q ▷ F ▹ G / [Γ])
              ([A] : Γ ∙ (Σ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
              ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
              ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
              (⊢Δ : ⊢ Δ)
              ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
              ([σt] : Δ ⊩⟨ l ⟩ t ∷ subst σ (Σ q ▷ F ▹ G) / proj₁ ([Σ] ⊢Δ [σ]))
            → Δ ⊩⟨ l ⟩ prodrec p (subst (liftSubst σ) A) (subst σ t) (subst (liftSubstn σ 2) u)
                ∷ subst (liftSubst σ) A [ t ]
                / irrelevance′ (PE.sym (singleSubstComp t σ A))
                               (proj₁ ([A] ⊢Δ ([σ] , [σt])))
prodrecTerm {n} {Γ} {q} {Δ} {p} {F} {G} {A} {t} {u} {σ} {l}
            [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [σt]
            with irrelevanceTerm (proj₁ ([Σ] ⊢Δ [σ]))
                                 (B-intr BΣ! (Σ-elim {F = subst σ F}
                                                     {G = subst (liftSubst σ) G}
                                                     (proj₁ ((Σᵛ {F = F} {G = G} [Γ] [F] [G]) ⊢Δ [σ]))))
                                 [σt]
prodrecTerm {n} {Γ} {q} {Δ} {p} {F} {G} {A} {t} {u} {σ} {l}
            [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [σt]
            | Σₜ t′ t⇒t′ prodₙ t′≡t′ [fstp] [sndp] =
  let [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σG = escape [σG]
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G]
                         (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ])
      [σΣ] = proj₁ ([Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ ([A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ)
                        (liftSubstS {σ = σ} {F = Σ q ▷ F ▹ G} [Γ] ⊢Δ [Σ] [σ]))
      ⊢σA = escape [σA]
      [σA₊] = proj₁ ([A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])
      ⊢σA₊ = escape [σA₊]
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x) {!t⇒t′!} ⊢σu
      [t′] = irrelevanceTerm (B-intr BΣ! (Σ-elim (proj₁ ((Σᵛ {F = F} {G = G} [Γ] [F] [G]) ⊢Δ [σ]))))
                             [σΣ] (Σₜ t′ (idRedTerm:*: (⊢u-redₜ t⇒t′)) prodₙ t′≡t′ [fstp] [sndp])
      ⊢t′ = escapeTerm [σΣ] [t′]
      [u₊] = proj₁ ([u] {!⊢Δ!} (([σ] , {!!}) , {!!}))
      reduction₁ = prodrec-subst* {p = p} ⊢σF ⊢σG ⊢σA ⊢σu′ (redₜ t⇒t′) [σΣ] [t′]
                                  λ {t₁} {t₂} [t₁] [t₂] [t₁≡t₂] →
                                    PE.subst₂ (Δ ⊢_≡_) (PE.sym (singleSubstComp t₁ σ A))
                                              (PE.sym (singleSubstComp t₂ σ A))
                                              (≅-eq (escapeEq (proj₁ ([A] ⊢Δ ([σ] , [t₁])))
                                                              (proj₂ ([A] ⊢Δ ([σ] , [t₁]))
                                                                     ([σ] , [t₂])
                                                                     (reflSubst [Γ] ⊢Δ [σ] , [t₁≡t₂]))))
      reduction₂ : _ ⊢ _ ⇒* _ ∷ _
      reduction₂ = prodrec-β {p = p} ⊢σF ⊢σG {!!} {!!} ⊢σA ⊢σu′ ⇨ id {!⊢t′!}
      reduction₂′ = conv* reduction₂ {!!}
      reduction : _ ⊢ _ ⇒* _ ∷ _
      reduction = reduction₁ ⇨∷* reduction₂′
  in  {!redSubst*Term!}
  -- proj₁ (redSubst*Term {!reduction!} {!!} {!IH!})

prodrecTerm {n} {Γ} {q} {Δ} {p} {F} {G} {A} {t} {u} {σ} {l}
            [Γ] [F] [G] [Σ] [A] [A₊] [u] ⊢Δ [σ] [σt]
            | Σₜ t′ t⇒t′ (ne x) t′≡t′ [fstp] [sndp] =
  let 
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σG = escape [σG]
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = G} (_∙_ {A = F} [Γ] [F]) (⊢Δ ∙ ⊢σF) [G]
                         (liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ])
      [σΣ] = proj₁ ([Σ] ⊢Δ [σ])
      ⊢σΣ = escape [σΣ]
      [σA] = proj₁ ([A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ)
                        (liftSubstS {σ = σ} {F = Σ q ▷ F ▹ G} [Γ] ⊢Δ [Σ] [σ]))
      ⊢σA = escape [σA]
      [σA₊] = proj₁ ([A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])
      ⊢σA₊ = escape [σA₊]
      [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [σ⇑⇑])
      ⊢σu = escapeTerm [σA₊] [σu]
      ⊢σu′ = PE.subst (λ x → _ ⊢ subst (liftSubstn σ 2) u ∷ x) {!t⇒t′!} ⊢σu
      [t′] = irrelevanceTerm (B-intr BΣ! (Σ-elim (proj₁ ((Σᵛ {F = F} {G = G} [Γ] [F] [G]) ⊢Δ [σ]))))
                             [σΣ] (Σₜ t′ (idRedTerm:*: (⊢u-redₜ t⇒t′)) (ne x) t′≡t′ [fstp] [sndp])
      reduction = prodrec-subst* {p = p} ⊢σF ⊢σG ⊢σA ⊢σu′ (redₜ t⇒t′) [σΣ] [t′]
                                  λ {t₁} {t₂} [t₁] [t₂] [t₁≡t₂] →
                                    PE.subst₂ (Δ ⊢_≡_) (PE.sym (singleSubstComp t₁ σ A))
                                              (PE.sym (singleSubstComp t₂ σ A))
                                              (≅-eq (escapeEq (proj₁ ([A] ⊢Δ ([σ] , [t₁])))
                                                              (proj₂ ([A] ⊢Δ ([σ] , [t₁]))
                                                                     ([σ] , [t₂])
                                                                     (reflSubst [Γ] ⊢Δ [σ] , [t₁≡t₂]))))
      prodrecT′ = neuTerm {!!} (prodrecₙ x) (prodrecⱼ ⊢σF ⊢σG (⊢u-redₜ t⇒t′) ⊢σA ⊢σu′)
                          (~-prodrec ⊢σF ⊢σG (escapeEq [σA] (reflEq [σA])) {!!} {!!})
      prodrecT = convTerm₂ {!!} {!!} {!!} prodrecT′
      in  proj₁ (redSubst*Term reduction {!!} prodrecT)

