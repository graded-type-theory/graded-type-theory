{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Introductions.Natrec {a ℓ} (M′ : Setoid a ℓ)
                                                                    {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using (_≈_) renaming (Carrier to M; refl to ≈-refl)

open import Definition.Untyped M hiding (_∷_) renaming (_[_,_] to _[_,,_])
open import Definition.Untyped.Properties M
open import Definition.Typed M′ hiding (_,_)
open import Definition.Typed.Properties M′
open import Definition.Typed.RedSteps M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.Properties M′
open import Definition.LogicalRelation.Application M′
open import Definition.LogicalRelation.Substitution M′
open import Definition.LogicalRelation.Substitution.Properties M′
import Definition.LogicalRelation.Substitution.Irrelevance M′ as S
open import Definition.LogicalRelation.Substitution.Reflexivity M′
open import Definition.LogicalRelation.Substitution.Weakening M′
open import Definition.LogicalRelation.Substitution.Introductions.Nat M′
open import Definition.LogicalRelation.Substitution.Introductions.Pi M′
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst M′

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

private
  variable
    m : Nat
    Γ Δ : Con Term m
    p p′ r r′ : M

-- Natural recursion closure reduction (requires reducible terms and equality).
natrec-subst* : ∀ {C c g n n′ l} → Γ ∙ ℕ ⊢ C → Γ ⊢ c ∷ C [ zero ]
              → Γ ∙ ℕ ∙ C ⊢ g ∷  wk1 (C [ suc (var x0) ]↑)
              → Γ ⊢ n ⇒* n′ ∷ ℕ
              → ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
              → Γ ⊩⟨ l ⟩ n′ ∷ ℕ / [ℕ]
              → (∀ {t t′} → Γ ⊩⟨ l ⟩ t  ∷ ℕ / [ℕ]
                          → Γ ⊩⟨ l ⟩ t′ ∷ ℕ / [ℕ]
                          → Γ ⊩⟨ l ⟩ t ≡ t′ ∷ ℕ / [ℕ]
                          → Γ ⊢ C [ t ] ≡ C [ t′ ])
              → Γ ⊢ natrec p r C c g n ⇒* natrec p r C c g n′ ∷ C [ n ]
natrec-subst* C c g (id x) [ℕ] [n′] prop = id (natrecⱼ C c g x)
natrec-subst* {p = p} C c g (x ⇨ n⇒n′) [ℕ] [n′] prop =
  let q , w = redSubst*Term n⇒n′ [ℕ] [n′]
      a , s = redSubstTerm  x [ℕ] q
  in  natrec-subst C c g x ⇨ conv* (natrec-subst* C c g n⇒n′ [ℕ] [n′] prop)
                   (prop q a (symEqTerm [ℕ] s))

-- Helper lemmata for substitution equalities

sucCaseSubst :  ∀ {m′ σ} {t : Term m′} (x : Fin (1+ m))
             → (consSubst σ t ₛ•ₛ consSubst (λ x₁ → wk1 (var x₁)) (suc (var x0))) x
             PE.≡ (sgSubst (suc t) ₛ•ₛ liftSubst σ) x
sucCaseSubst x0 = PE.refl
sucCaseSubst {σ = σ} {t = t} (x +1) = PE.trans (PE.sym (subst-id (σ x)))
                                               (PE.sym (wk1-tail (σ x)))

sucCaseSubstEq : ∀ {m′ σ} {t u : Term m′} (F : Term (1+ m))
               → subst (consSubst (consSubst σ t) u) (wk1 (F [ suc (var x0) ]↑))
               PE.≡ subst (liftSubst σ) F [ suc t ]
sucCaseSubstEq F = PE.trans (wk1-tail (F [ suc (var x0) ]↑))
                            (PE.trans (substCompEq F)
                            (PE.trans (substVar-to-subst sucCaseSubst F) (PE.sym (substCompEq F))))


-- Reducibility of natural recursion under a valid substitution.
natrecTerm : ∀ {F z s n σ l}
             ([Γ]  : ⊩ᵛ Γ)
             ([F]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
             ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] / [Γ])
             ([F₊] : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ wk1 (F [ suc (var x0) ]↑) / ((_∙_ {l = l} [Γ] (ℕᵛ [Γ])) ∙ [F]))
             ([z]  : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero ] / [Γ] / [F₀])
             ([s]  : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ s ∷ wk1 (F [ suc (var x0) ]↑)
                       / [Γ] ∙ (ℕᵛ {l = l} [Γ]) ∙ [F] / [F₊])
             (⊢Δ   : ⊢ Δ)
             ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σn] : Δ ⊩⟨ l ⟩ n ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
           → Δ ⊩⟨ l ⟩ natrec p r (subst (liftSubst σ) F) (subst σ z) (subst (liftSubstn σ 2) s) n
               ∷ subst (liftSubst σ) F [ n ]
               / irrelevance′ (PE.sym (singleSubstComp n σ F))
                              (proj₁ ([F] ⊢Δ ([σ] , [σn])))
natrecTerm {Γ = Γ} {Δ = Δ} {p = p} {r = r} {F = F} {z} {s} {n} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ .(suc m) d n≡n (sucᵣ {m} [m])) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [Γℕ] = _∙_ {A = ℕ} [Γ] [ℕ]
      ⊢ℕ = escape [σℕ]
      ⊢Δℕ = ⊢Δ ∙ ⊢ℕ
      [σF] = proj₁ ([F] ⊢Δℕ (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = F} [Γℕ] ⊢Δℕ [F]
                         (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      ⊢Γ = soundContext [Γ]
      ⊢F = escape [σF]
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → (Δ ∙ ℕ ∙ subst (liftSubst σ) F) ⊢ subst (liftSubstn σ 2) s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] (⊢Δℕ ∙ ⊢F)
                                             (liftSubstS {σ = liftSubst σ} {F = F} [Γℕ] ⊢Δℕ [F]
                                                         (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))))
                                (proj₁ ([s] (⊢Δℕ ∙ ⊢F)
                                       (liftSubstS {σ = liftSubst σ} {F = F} [Γℕ] ⊢Δℕ [F]
                                                   (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))))
      ⊢m = escapeTerm {l = l} [σℕ] [m]
      [σsm] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) [σℕ]
                              (ℕₜ (suc m) (idRedTerm:*: (sucⱼ ⊢m)) n≡n (sucᵣ [m]))
      [σn] = ℕₜ (suc m) d n≡n (sucᵣ [m])
      [σn]′ , [σn≡σsm] = redSubst*Term (redₜ d) [σℕ] [σsm]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₛₘ] = irrelevance′ (PE.sym (singleSubstComp (suc m) σ F))
                                    (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [Fₙ≡Fₛₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                 (PE.sym (singleSubstComp (suc m) σ F))
                                 [σFₙ]′ [σFₙ]
                                 (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsm])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsm]))
      [σFₛₘ]′ = irrelevance′ (natrecIrrelevantSubst p r F z s m σ)
                             (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [natrecM]′ = natrecTerm {p = p} {r = r} {F = F} {z = z} {s = s}
                              [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [m]
      [natrecM] = irrelevanceTerm′ (singleSubstComp m σ F)
                                   (irrelevance′ (PE.sym (singleSubstComp m σ F)) (proj₁ ([F] ⊢Δ ([σ] , [m]))))
                                   (proj₁ ([F] ⊢Δ ([σ] , [m])) )
                                   [natrecM]′
      [natrec]′ = proj₁ ([s] {σ = consSubst (consSubst σ m) (natrec p r _ _ _ m)}
                            ⊢Δ (([σ] , [m]) , [natrecM]))
      [natrec] = irrelevanceTerm′ (sucCaseSubstEq F)
                                  (proj₁ ([F₊] ⊢Δ (([σ] , [m]) , [natrecM])))
                                  [σFₛₘ] [natrec]′
      [natrec]″ = irrelevanceTerm″ PE.refl (PE.sym (doubleSubstComp s m (natrec p r _ _ _ m) σ))
                                   [σFₛₘ] [σFₛₘ] [natrec]
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsm] (λ {t} {t′} [t] [t′] [t≡t′] →
        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                  (PE.sym (singleSubstComp t σ F))
                  (PE.sym (singleSubstComp t′ σ F))
                  (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t]))) (proj₂ ([F] ⊢Δ ([σ] , [t])) ([σ] , [t′]) ((reflSubst [Γ] ⊢Δ [σ]) , [t≡t′])))))
      reduction′ = conv* ((natrec-suc ⊢m ⊢F ⊢z ⊢s) ⇨ (id (escapeTerm [σFₛₘ] [natrec]″))) (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡Fₛₘ])))
      reduction″ = PE.subst (Δ ⊢ _ ⇒*_∷ _)
                            (doubleSubstComp s m (natrec p r (subst (liftSubst σ) F) (subst σ z)
                                                             (subst (liftSubstn σ 2) s) m) σ)
                            (reduction ⇨∷* reduction′)
  in proj₁ (redSubst*Term reduction″ [σFₙ]
                          (convTerm₂ [σFₙ] [σFₛₘ] [Fₙ≡Fₛₘ] [natrec]))

natrecTerm {Γ = Γ} {Δ = Δ} {r = r} {F = F} {z} {s} {n} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ .zero d n≡n zeroᵣ) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [Γℕ] = _∙_ {A = ℕ} [Γ] [ℕ]
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢Δℕ = ⊢Δ ∙ ⊢ℕ
      [σF] = proj₁ ([F] ⊢Δℕ (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = F} [Γℕ] ⊢Δℕ [F]
                         (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      ⊢F = escape [σF]
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → (Δ ∙ ℕ ∙ subst (liftSubst σ) F) ⊢ subst (liftSubstn σ 2) s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] (⊢Δℕ ∙ ⊢F) [σ⇑⇑]))
                                (proj₁ ([s] (⊢Δℕ ∙ ⊢F) [σ⇑⇑]) ))
      [σ0] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) [σℕ]
                             (ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) n≡n zeroᵣ)
      [σn]′ , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
      [σn] = ℕₜ zero d n≡n zeroᵣ
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [Fₙ≡F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0])
                       (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [Fₙ≡F₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.trans (substConcatSingleton′ F)
                                            (PE.sym (singleSubstComp zero σ F)))
                                  [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [σz] = proj₁ ([z] ⊢Δ [σ])
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t′])))))
                  ⇨∷* (conv* (natrec-zero ⊢F ⊢z ⊢s ⇨ id ⊢z)
                             (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡F₀]″))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀] [σz]))

natrecTerm {Γ = Γ} {Δ = Δ} {p = p} {r = r} {F = F} {z} {s} {n} {σ} {l} [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))) =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [Γℕ] = _∙_ {A = ℕ} [Γ] [ℕ]
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢Δℕ = ⊢Δ ∙ ⊢ℕ
      [σn] = ℕₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = F} [Γℕ] ⊢Δℕ [F]
                         (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢z≡z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x) (singleSubstLift F zero)
                      (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₁ ([z] ⊢Δ [σ]))))
      ⊢s = PE.subst (λ x → (Δ ∙ ℕ ∙ subst (liftSubst σ) F) ⊢ subst (liftSubstn σ 2) s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] (⊢Δℕ ∙ ⊢F) [σ⇑⇑]))
                                (proj₁ ([s] (⊢Δℕ ∙ ⊢F) [σ⇑⇑])))
      ⊢s≡s = PE.subst (λ x → (Δ ∙ ℕ ∙ subst (liftSubst σ) F) ⊢ subst (liftSubstn σ 2) s ≅ subst (liftSubstn σ 2) s ∷ x) (natrecSucCase σ F)
                      (escapeTermEq (proj₁ ([F₊] (⊢Δℕ ∙ ⊢F) [σ⇑⇑]))
                                    (reflEqTerm (proj₁ ([F₊] (⊢Δℕ ∙ ⊢F) [σ⇑⇑]))
                                                ( (proj₁ ([s] (⊢Δℕ ∙ ⊢F) [σ⇑⇑])))))
      [σm] = neuTerm [σℕ] neM ⊢m m≡m
      [σn]′ , [σn≡σm] = redSubst*Term (redₜ d) [σℕ] [σm]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₘ] = irrelevance′ (PE.sym (singleSubstComp m σ F))
                           (proj₁ ([F] ⊢Δ ([σ] , [σm])))
      [Fₙ≡Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (singleSubstComp m σ F)) [σFₙ]′ [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn]))) ([σ] , [σm])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σm]))
      natrecM = neuTerm [σFₘ] (natrecₙ neM) (natrecⱼ ⊢F ⊢z ⊢s ⊢m)
                        (~-natrec ⊢F ⊢F≡F ⊢z≡z ⊢s≡s m≡m ≈-refl ≈-refl)
      reduction = natrec-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σm]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t′])))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] [σFₘ] [Fₙ≡Fₘ] natrecM))


-- Reducibility of natural recursion congruence under a valid substitution equality.
natrec-congTerm : ∀ {F F′ z z′ s s′ n m σ σ′ l}
                  ([Γ]      : ⊩ᵛ Γ)
                  ([F]      : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
                  ([F′]     : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F′ / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
                  ([F≡F′]   : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ F′ / _∙_ {l = l} [Γ] (ℕᵛ [Γ])
                                    / [F])
                  ([F₀]     : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] / [Γ])
                  ([F′₀]    : Γ ⊩ᵛ⟨ l ⟩ F′ [ zero ] / [Γ])
                  ([F₀≡F′₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] ≡ F′ [ zero ] / [Γ] / [F₀])
                  ([F₊]     : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ wk1 (F [ suc (var x0) ]↑)
                                /  _∙_ {l = l} [Γ] (ℕᵛ [Γ]) ∙ [F])
                  ([F′₊]    : Γ ∙ ℕ ∙ F′ ⊩ᵛ⟨ l ⟩ wk1 (F′ [ suc (var x0) ]↑)
                                / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) ∙ [F′])
                  ([F₊≡F₊′] : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ wk1 (F [ suc (var x0) ]↑)
                                ≡ wk1 (F′ [ suc (var x0) ]↑)
                                / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) ∙ [F] / [F₊])
                  ([z]      : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero ] / [Γ] / [F₀])
                  ([z′]     : Γ ⊩ᵛ⟨ l ⟩ z′ ∷ F′ [ zero ] / [Γ] / [F′₀])
                  ([z≡z′]   : Γ ⊩ᵛ⟨ l ⟩ z ≡ z′ ∷ F [ zero ] / [Γ] / [F₀])
                  ([s]      : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ s ∷ wk1 (F [ suc (var x0) ]↑)
                                / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) ∙ [F] / [F₊])
                  ([s′]     : Γ ∙ ℕ ∙ F′ ⊩ᵛ⟨ l ⟩ s′
                                ∷ wk1 (F′ [ suc (var x0) ]↑)
                                / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) ∙ [F′] / [F′₊])
                  ([s≡s′]   : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ s ≡ s′
                                ∷ wk1 (F [ suc (var x0) ]↑)
                                / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) ∙ [F] / [F₊])
                  (⊢Δ       : ⊢ Δ)
                  ([σ]      : Δ ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
                  ([σ′]     : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                  ([σ≡σ′]   : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                  ([σn]     : Δ ⊩⟨ l ⟩ n ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                  ([σm]     : Δ ⊩⟨ l ⟩ m ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                  ([σn≡σm]  : Δ ⊩⟨ l ⟩ n ≡ m ∷ ℕ / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                → p ≈ p′
                → r ≈ r′
                → Δ ⊩⟨ l ⟩ natrec p r (subst (liftSubst σ) F)
                                  (subst σ z) (subst (liftSubst (liftSubst σ)) s) n
                    ≡ natrec p′ r′ (subst (liftSubst σ′) F′)
                             (subst σ′ z′) (subst (liftSubst (liftSubst σ′)) s′) m
                    ∷ subst (liftSubst σ) F [ n ]
                    / irrelevance′ (PE.sym (singleSubstComp n σ F))
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn])))
natrec-congTerm {Γ = Γ} {Δ = Δ} {p = p} {p′ = p′} {r = r} {r′ = r′}
                {F = F} {F′ = F′} {z = z} {z′ = z′}
                {s = s} {s′ = s′} {n = n} {m = m} {σ = σ} {σ′ = σ′} {l = l}
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ .(suc n′) d n≡n (sucᵣ {n′} [n′]))
                (ℕₜ .(suc m′) d′ m≡m (sucᵣ {m′} [m′]))
                (ℕₜ₌ .(suc n″) .(suc m″) d₁ d₁′
                     t≡u (sucᵣ {n″} {m″} [n″≡m″]))
                p≈p′ r≈r′ =
  let n″≡n′ = suc-PE-injectivity (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d , sucₙ))
      m″≡m′ = suc-PE-injectivity (whrDet*Term (redₜ d₁′ , sucₙ) (redₜ d′ , sucₙ))
      [ℕ] = ℕᵛ {l = l} [Γ]
      [Γℕ] = _∙_ {A = ℕ} [Γ] [ℕ]
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢Δℕ = ⊢Δ ∙ ⊢ℕ
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [σ′ℕ] = proj₁ ([ℕ] ⊢Δ [σ′])
      [n′≡m′] = irrelevanceEqTerm″ n″≡n′ m″≡m′ PE.refl [σℕ] [σℕ] [n″≡m″]
      [σn] = ℕₜ (suc n′) d n≡n (sucᵣ [n′])
      [σ′m] = ℕₜ (suc m′) d′ m≡m (sucᵣ [m′])
      [σn≡σ′m] = ℕₜ₌ (suc n″) (suc m″) d₁ d₁′ t≡u (sucᵣ [n″≡m″])
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = F} [Γℕ] ⊢Δℕ [F]
                         (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      [σ′⇑⇑] = liftSubstS {σ = liftSubst σ′} {F = F′} [Γℕ] ⊢Δℕ [F′]
                         (liftSubstS {σ = σ′} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])
      ⊢ℕ = escape [σℕ]
      ⊢F = escape (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢ΔℕF = ⊢Δ ∙ ⊢ℕ ∙ ⊢F
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ) F ⊢ subst (liftSubst (liftSubst σ)) s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢ΔℕF [σ⇑⇑])) (proj₁ ([s] ⊢ΔℕF [σ⇑⇑])))
      ⊢n′ = escapeTerm {l = l} [σℕ] [n′]
      ⊢ℕ′ = escape [σ′ℕ]
      ⊢F′ = escape (proj₁ ([F′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢ℕ′)
                      (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])))
      ⊢ΔℕF′ = ⊢Δ ∙ ⊢ℕ′ ∙ ⊢F′
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F′ zero)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′]))
                                    (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢s′ = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ′) F′ ⊢ subst (liftSubst (liftSubst σ′)) s′ ∷ x) (natrecSucCase σ′ F′)
                     (escapeTerm (proj₁ ([F′₊] ⊢ΔℕF′ [σ′⇑⇑]))
                                    (proj₁ ([s′] ⊢ΔℕF′  [σ′⇑⇑])))
      ⊢m′ = escapeTerm {l = l} [σ′ℕ] [m′]
      [σsn′] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) [σℕ]
                               (ℕₜ (suc n′) (idRedTerm:*: (sucⱼ ⊢n′)) n≡n (sucᵣ [n′]))
      [σn]′ , [σn≡σsn′] = redSubst*Term (redₜ d) [σℕ] [σsn′]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₛₙ′] = irrelevance′ (PE.sym (singleSubstComp (suc n′) σ F))
                             (proj₁ ([F] ⊢Δ ([σ] , [σsn′])))
      [Fₙ≡Fₛₙ′] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.sym (singleSubstComp (suc n′) σ F))
                                  [σFₙ]′ [σFₙ]
                                  (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn′])
                                         (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn′]))
      [Fₙ≡Fₛₙ′]′ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (natrecIrrelevantSubst p r F z s n′ σ)
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn′])
                                          (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn′]))
      [σFₙ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                              (substSingletonComp F)))
                            (proj₁ ([F] ⊢Δ ([σ] , [n′])))
      [σFₙ′]′ = proj₁ ([F] ⊢Δ ([σ] , [n′]))
      [σ′sm′] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) [σ′ℕ]
                                (ℕₜ (suc m′) (idRedTerm:*: (sucⱼ ⊢m′)) m≡m (sucᵣ [m′]))
      [σ′m]′ , [σ′m≡σ′sm′] = redSubst*Term (redₜ d′) [σ′ℕ] [σ′sm′]
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′Fₘ′]′ = proj₁ ([F] {σ = consSubst σ′ m′} ⊢Δ ([σ′] , [m′]))
      [σ′F′ₛₘ′] = irrelevance′ (PE.sym (singleSubstComp (suc m′) σ′ F′))
                               (proj₁ ([F′] ⊢Δ ([σ′] , [σ′sm′])))
      [σ′Fₛₘ′] = irrelevance′ (PE.sym (singleSubstComp (suc m′) σ′ F))
                               (proj₁ ([F] ⊢Δ ([σ′] , [σ′sm′])))
      [F′ₘ≡F′ₛₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                    (PE.sym (singleSubstComp (suc m′) σ′ F′))
                                    [σ′F′ₘ]′ [σ′F′ₘ]
                                    (proj₂ ([F′] ⊢Δ ([σ′] , [σ′m]))
                                           ([σ′] , [σ′sm′])
                                           (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′sm′]))
      [Fₘ≡Fₛₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                 (PE.sym (singleSubstComp (suc m′) σ′ F))
                                 [σ′Fₘ]′ [σ′Fₘ]
                                 (proj₂ ([F] ⊢Δ ([σ′] , [σ′m]))
                                        ([σ′] , [σ′sm′])
                                        (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′sm′]))
      [σ′Fₘ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                               (substSingletonComp F)))
                             (proj₁ ([F] ⊢Δ ([σ′] , [m′])))
      [σ′F′ₘ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F′)
                                                (substSingletonComp F′)))
                              (proj₁ ([F′] ⊢Δ ([σ′] , [m′])))
      [σ′F′ₘ′]′ = proj₁ ([F′] {σ = consSubst σ′ m′} ⊢Δ ([σ′] , [m′]))
      [σFₙ′≡σ′Fₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp n′ σ F))
                                     (PE.sym (singleSubstComp m′ σ′ F))
                                     (proj₁ ([F] ⊢Δ ([σ] , [n′]))) [σFₙ′]
                                     (proj₂ ([F] ⊢Δ ([σ] , [n′]))
                                            ([σ′] , [m′]) ([σ≡σ′] , [n′≡m′]))
      [σ′Fₘ′≡σ′F′ₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m′ σ′ F))
                                       (PE.sym (singleSubstComp m′ σ′ F′))
                                       (proj₁ ([F] ⊢Δ ([σ′] , [m′])))
                                       [σ′Fₘ′] ([F≡F′] ⊢Δ ([σ′] , [m′]))
      [σFₙ′≡σ′F′ₘ′] = transEq [σFₙ′] [σ′Fₘ′] [σ′F′ₘ′] [σFₙ′≡σ′Fₘ′] [σ′Fₘ′≡σ′F′ₘ′]
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F))
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn]))) [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn]))
                                          ([σ′] , [σ′m]) ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′))
                                     [σ′Fₘ]′ [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [σFₙ≡σ′Fₛₘ′] = transEq [σFₙ] [σ′Fₘ] [σ′Fₛₘ′] [σFₙ≡σ′Fₘ] [Fₘ≡Fₛₘ′]
      natrecN = natrecTerm {p = p} {r = r} {F = F} {z} {s} {n′} {σ = σ}
                           [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [n′]
      natrecN′ = irrelevanceTerm′ (singleSubstComp n′ σ F) [σFₙ′] [σFₙ′]′ natrecN
      natrecM = natrecTerm {p = p′} {r = r′} {F = F′} {z′} {s′} {m′} {σ = σ′}
                           [Γ] [F′] [F′₀] [F′₊] [z′] [s′] ⊢Δ [σ′] [m′]
      natrecM′ = irrelevanceTerm′ (singleSubstComp m′ σ′ F′) [σ′F′ₘ′] [σ′F′ₘ′]′ natrecM
      natrecM″ = convTerm₂  [σ′Fₘ′] [σ′F′ₘ′] [σ′Fₘ′≡σ′F′ₘ′] natrecM
      natrecM‴ = irrelevanceTerm′ (singleSubstComp m′ σ′ F) [σ′Fₘ′] [σ′Fₘ′]′ natrecM″
      [σF₊] = (proj₁ ([F₊] ⊢Δ (([σ] , [n′]) , natrecN′)))
      [σF₊]′ = irrelevance′ (sucCaseSubstEq F) [σF₊]
      [nr≡nr′] = natrec-congTerm {p = p} {r = r} {F = F} {F′} {z} {z′}
                                 {s} {s′} {n′} {m′} {σ = σ}
                                 [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀]
                                 [F₊] [F′₊] [F₊≡F′₊] [z] [z′] [z≡z′]
                                 [s] [s′] [s≡s′]
                                 ⊢Δ [σ] [σ′] [σ≡σ′] [n′] [m′] [n′≡m′] p≈p′ r≈r′
      [nr≡nr′]′ = irrelevanceEqTerm′ (singleSubstComp n′ σ F) [σFₙ′] [σFₙ′]′ [nr≡nr′]
      σ₊ = consSubst (consSubst σ n′) (natrec p r (subst (liftSubst σ) F)
                                              (subst σ z) (subst (liftSubstn σ 2) s) n′)
      [σ₊] = ([σ] , [n′]) , natrecN′
      σ′₊ = consSubst (consSubst σ′ m′) (natrec p′ r′ (subst (liftSubst σ′) F′)
                                                (subst σ′ z′) (subst (liftSubstn σ′ 2) s′) m′)
      [σ′₊] = ([σ′] , [m′]) , natrecM‴
      [σ₊≡σ′₊] = ([σ≡σ′] , [n′≡m′]) , [nr≡nr′]′
      [s₊≡s′₊] = proj₂ ([s] {σ = σ₊} ⊢Δ [σ₊]) {σ′ = σ′₊} [σ′₊] [σ₊≡σ′₊]
      [s₊] = proj₁ ([s] {σ = σ₊} ⊢Δ [σ₊])
      [s₊]′ = irrelevanceTerm″ (sucCaseSubstEq F)
                               (PE.sym (doubleSubstComp s n′ (natrec p r (subst (liftSubst σ) F) (subst σ z) (subst (liftSubst (liftSubst σ)) s) n′) σ))
                               [σF₊] [σF₊]′ [s₊]
      [σ′₊]′ = ([σ′] , [m′]) ,  natrecM′
      [s′₊] = proj₁ ([s′] {σ = σ′₊} ⊢Δ [σ′₊]′)
      [s′₊]′ = irrelevanceTerm″ (sucCaseSubstEq F′)
                                (PE.sym (doubleSubstComp s′ m′ (natrec p′ r′ _ _ _ _) σ′))
                                (proj₁ ([F′₊] ⊢Δ [σ′₊]′)) [σ′F′ₛₘ′] [s′₊]
      reduction₁ = natrec-subst* {p = p} {r = r} ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsn′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstComp t σ F))
                                  (PE.sym (singleSubstComp t′ σ F))
                                  (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                               (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                      ([σ] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
                   ⇨∷* (conv* (natrec-suc ⊢n′ ⊢F ⊢z ⊢s
                   ⇨   id (escapeTerm [σF₊]′ [s₊]′))
                          (sym (≅-eq ((escapeEq [σFₙ] [Fₙ≡Fₛₙ′])))))
      reduction₂ = natrec-subst* {p = p′} {r = r′} ⊢F′ ⊢z′ ⊢s′ (redₜ d′) [σ′ℕ] [σ′sm′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstComp t σ′ F′))
                                  (PE.sym (singleSubstComp t′ σ′ F′))
                                  (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                               (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                      ([σ′] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
                   ⇨∷* (conv* (natrec-suc ⊢m′ ⊢F′ ⊢z′ ⊢s′
                   ⇨   id (escapeTerm [σ′F′ₛₘ′] [s′₊]′))
                          (sym (≅-eq (escapeEq [σ′F′ₘ] [F′ₘ≡F′ₛₘ′]))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] [σF₊]′
                                            [Fₙ≡Fₛₙ′] [s₊]′))
      eq₁′ = irrelevanceEqTerm″ PE.refl
                                (doubleSubstComp s n′ (natrec p r (subst (liftSubst σ) F)
                                                 (subst σ z) (subst (liftSubst (liftSubst σ)) s) n′) σ)
                                PE.refl [σFₙ] [σFₙ] eq₁
      eq₂ = proj₂ ([s] {σ = σ₊} ⊢Δ [σ₊]) {σ′ = σ′₊} [σ′₊] [σ₊≡σ′₊]
      eq₂′ = irrelevanceEqTerm′ (sucCaseSubstEq F) [σF₊] [σFₛₙ′] eq₂
      eq₂″ = convEqTerm₂ [σFₙ] [σFₛₙ′] [Fₙ≡Fₛₙ′] eq₂′
      eq₃ = [s≡s′] {σ = σ′₊} ⊢Δ [σ′₊]
      eq₃′ = irrelevanceEqTerm″ PE.refl (PE.sym (doubleSubstComp s′ m′ _ σ′))
                                (sucCaseSubstEq F) (proj₁ ([F₊] ⊢Δ [σ′₊])) [σ′Fₛₘ′] eq₃
      eq₃″ = convEqTerm₂ [σFₙ] [σ′Fₛₘ′] [σFₙ≡σ′Fₛₘ′] eq₃′
      eq₄ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] [σ′F′ₛₘ′]
                                            [F′ₘ≡F′ₛₘ′] [s′₊]′))
      eq₄′ = convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ] eq₄
  in  transEqTerm [σFₙ] eq₁′
                  (transEqTerm [σFₙ] eq₂″
                               (transEqTerm [σFₙ] eq₃″ (symEqTerm [σFₙ] eq₄′)))

natrec-congTerm {Γ = Γ} {Δ = Δ} {p = p} {p′ = p′} {r = r} {r′ = r′}
                {F = F} {F′ = F′} {z = z} {z′ = z′} {s = s}
                {s′ = s′} {n = n} {m = m} {σ = σ} {σ′ = σ′} {l = l}
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ .zero d n≡n zeroᵣ) (ℕₜ .zero d₁ m≡m zeroᵣ)
                (ℕₜ₌ .zero .zero d₂ d′ t≡u zeroᵣ)
                p≈p′ r≈r′ =
  let [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      ⊢F = escape (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ)
                                 (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])))
      ⊢Δℕ = ⊢Δ ∙ ℕⱼ ⊢Δ
      [Γℕ] = _∙_ {A = ℕ} [Γ] [ℕ]
      ⊢ΔℕF = ⊢Δ ∙ ⊢ℕ ∙ ⊢F
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = F} [Γℕ] ⊢Δℕ [F]
                         (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ) F ⊢ subst (liftSubst (liftSubst σ)) s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢ΔℕF [σ⇑⇑])) (proj₁ ([s] ⊢ΔℕF [σ⇑⇑])))
      ⊢F′ = escape (proj₁ ([F′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢ℕ)
                                   (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])))
      ⊢ΔℕF′ = ⊢Δ ∙ ⊢ℕ ∙ ⊢F′
      [σ′⇑⇑] = liftSubstS {σ = liftSubst σ′} {F = F′} [Γℕ] ⊢Δℕ [F′]
                         (liftSubstS {σ = σ′} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F′ zero)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′])) (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢s′ = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ′) F′ ⊢ subst (liftSubst (liftSubst σ′)) s′ ∷ x) (natrecSucCase σ′ F′)
                    (escapeTerm (proj₁ ([F′₊] ⊢ΔℕF′ [σ′⇑⇑])) (proj₁ ([s′] ⊢ΔℕF′ [σ′⇑⇑])))
      [σ0] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([ℕ] ⊢Δ [σ]))
                             (ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) n≡n zeroᵣ)
      [σ′0] = irrelevanceTerm {l = l} (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([ℕ] ⊢Δ [σ′]))
                              (ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) m≡m zeroᵣ)
      [σn]′ , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
      [σ′m]′ , [σ′m≡σ′0] = redSubst*Term (redₜ d′) (proj₁ ([ℕ] ⊢Δ [σ′])) [σ′0]
      [σn] = ℕₜ zero d n≡n zeroᵣ
      [σ′m] = ℕₜ zero d′ m≡m zeroᵣ
      [σn≡σ′m] = ℕₜ₌ zero zero d₂ d′ t≡u zeroᵣ
      [σn≡σ′0] = transEqTerm [σℕ] [σn≡σ′m] [σ′m≡σ′0]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F))
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′m])
                                          ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′))
                                     [σ′Fₘ]′ [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [Fₙ≡F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0]) (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [σFₙ≡σ′F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′0]) ([σ≡σ′] , [σn≡σ′0])
      [σFₙ≡σ′F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F))
                                [σFₙ]′ [σFₙ] [σFₙ≡σ′F₀]′
      [F′ₘ≡F′₀]′ = proj₂ ([F′] ⊢Δ ([σ′] , [σ′m])) ([σ′] , [σ′0])
                         (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′0])
      [F′ₘ≡F′₀] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                  (PE.sym (substCompEq F′))
                                  [σ′F′ₘ]′ [σ′F′ₘ] [F′ₘ≡F′₀]′
      [Fₙ≡F₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.trans (substConcatSingleton′ F)
                                            (PE.sym (singleSubstComp zero σ F)))
                                  [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [F′ₘ≡F′₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                    (PE.trans (substConcatSingleton′ F′)
                                              (PE.sym (singleSubstComp zero σ′ F′)))
                                    [σ′F′ₘ]′ [σ′F′ₘ] [F′ₘ≡F′₀]′
      [σz] = proj₁ ([z] ⊢Δ [σ])
      [σ′z′] = proj₁ ([z′] ⊢Δ [σ′])
      [σz≡σ′z] = convEqTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀]
                             (proj₂ ([z] ⊢Δ [σ]) [σ′] [σ≡σ′])
      [σ′z≡σ′z′] = convEqTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ′])) [σFₙ≡σ′F₀]
                               ([z≡z′] ⊢Δ [σ′])
      [σz≡σ′z′] = transEqTerm [σFₙ] [σz≡σ′z] [σ′z≡σ′z′]
      reduction₁ = natrec-subst* {p = p} {r = r} ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ] ⊢Δ [σ])) [σ0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
                  ⇨∷* (conv* (natrec-zero ⊢F ⊢z ⊢s ⇨ id ⊢z)
                             (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡F₀]″))))
      reduction₂ = natrec-subst* {p = p′} {r = r′} ⊢F′ ⊢z′ ⊢s′ (redₜ d′) (proj₁ ([ℕ] ⊢Δ [σ′])) [σ′0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                 (PE.sym (singleSubstComp t σ′ F′))
                                 (PE.sym (singleSubstComp t′ σ′ F′))
                                 (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                              (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                     ([σ′] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
                  ⇨∷* (conv* (natrec-zero ⊢F′ ⊢z′ ⊢s′ ⇨ id ⊢z′)
                             (sym (≅-eq (escapeEq [σ′F′ₘ] [F′ₘ≡F′₀]″))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ]))
                                            [Fₙ≡F₀] [σz]))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] (proj₁ ([F′₀] ⊢Δ [σ′]))
                                            [F′ₘ≡F′₀] [σ′z′]))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] [σz≡σ′z′]
                               (convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ]
                                            (symEqTerm [σ′F′ₘ] eq₂)))

natrec-congTerm {Γ = Γ} {Δ = Δ} {p = p} {p′ = p′} {r = r} {r′ = r′}
                {F = F} {F′} {z} {z′} {s} {s′} {n} {m} {σ} {σ′} {l}
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁)))
                (ℕₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁)))
                (ℕₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂)))
                p≈p′ r≈r′ =
  let n″≡n′ = whrDet*Term (redₜ d₁ , ne x₂) (redₜ d , ne neN′)
      m″≡m′ = whrDet*Term (redₜ d₁′ , ne x₃) (redₜ d′ , ne neM′)
      [ℕ] = ℕᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ] ⊢Δ [σ])
      [σ′ℕ] = proj₁ ([ℕ] ⊢Δ [σ′])
      [σn] = ℕₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁))
      [σ′m] = ℕₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁))
      [σn≡σ′m] = ℕₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))
      ⊢ℕ = escape (proj₁ ([ℕ] ⊢Δ [σ]))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
      [σ′F] = proj₁ ([F] {σ = liftSubst σ′} (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′]))
      [σ′F′] = proj₁ ([F′] (⊢Δ ∙ ⊢ℕ) (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′]))
      ⊢F = escape [σF]
      ⊢Δℕ = ⊢Δ ∙ ℕⱼ ⊢Δ
      [Γℕ] = _∙_ {A = ℕ} [Γ] [ℕ]
      ⊢ΔℕF = ⊢Δ ∙ ⊢ℕ ∙ ⊢F
      [σ⇑⇑] = liftSubstS {σ = liftSubst σ} {F = F} [Γℕ] ⊢Δℕ [F]
                         (liftSubstS {σ = σ} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F zero)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢z≡z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x) (singleSubstLift F zero)
                      (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₁ ([z] ⊢Δ [σ]))))
      ⊢s = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ) F ⊢ subst (liftSubst (liftSubst σ)) s ∷ x) (natrecSucCase σ F)
                    (escapeTerm (proj₁ ([F₊] ⊢ΔℕF [σ⇑⇑])) (proj₁ ([s] ⊢ΔℕF [σ⇑⇑])))
      ⊢s≡s = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ) F ⊢ subst (liftSubstn σ 2) s ≅ subst (liftSubstn σ 2) s ∷ x) (natrecSucCase σ F)
                      (escapeTermEq (proj₁ ([F₊] ⊢ΔℕF [σ⇑⇑]))
                                        (reflEqTerm (proj₁ ([F₊] ⊢ΔℕF [σ⇑⇑]))
                                                    (proj₁ ([s] ⊢ΔℕF [σ⇑⇑]))))
      ⊢F′ = escape [σ′F′]
      ⊢ΔℕF′ = ⊢Δ ∙ ⊢ℕ ∙ ⊢F′
      [σ′⇑⇑] = liftSubstS {σ = liftSubst σ′} {F = F′} [Γℕ] ⊢Δℕ [F′]
                         (liftSubstS {σ = σ′} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])
      [σ′⇑⇑]′ = liftSubstS {σ = liftSubst σ′} {F = F} [Γℕ] ⊢Δℕ [F]
                         (liftSubstS {σ = σ′} {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])
      ⊢F′≡F′ = escapeEq [σ′F′] (reflEq [σ′F′])
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x) (singleSubstLift F′ zero)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′])) (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢z′≡z′ = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x) (singleSubstLift F′ zero)
                        (escapeTermEq (proj₁ ([F′₀] ⊢Δ [σ′]))
                                          (reflEqTerm (proj₁ ([F′₀] ⊢Δ [σ′]))
                                                      (proj₁ ([z′] ⊢Δ [σ′]))))
      ⊢s′ = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ′) F′ ⊢ subst (liftSubst (liftSubst σ′)) s′ ∷ x) (natrecSucCase σ′ F′)
                    (escapeTerm (proj₁ ([F′₊] ⊢ΔℕF′ [σ′⇑⇑])) (proj₁ ([s′] ⊢ΔℕF′ [σ′⇑⇑])))
      ⊢s′≡s′ = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ′) F′ ⊢ subst (liftSubstn σ′ 2) s′ ≅ subst (liftSubstn σ′ 2) s′ ∷ x) (natrecSucCase σ′ F′)
                      (escapeTermEq (proj₁ ([F′₊] ⊢ΔℕF′ [σ′⇑⇑]))
                                        (reflEqTerm (proj₁ ([F′₊] ⊢ΔℕF′ [σ′⇑⇑]))
                                                    (proj₁ ([s′] ⊢ΔℕF′ [σ′⇑⇑]))))
      ⊢σF≡σ′F = escapeEq [σF] (proj₂ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ)
                                           (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
                                      {σ′ = liftSubst σ′}
                                      (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])
                                      (liftSubstSEq {F = ℕ} [Γ] ⊢Δ [ℕ] [σ] [σ≡σ′]))
      ⊢σz≡σ′z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x) (singleSubstLift F zero)
                         (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                          (proj₂ ([z] ⊢Δ [σ]) [σ′] [σ≡σ′]))
      [σ⇑↑] = wk1SubstS {σ = liftSubst σ} [Γℕ] ⊢Δℕ ⊢F (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
      [σ′⇑↑] = wk1SubstS {σ = liftSubst σ′} [Γℕ] ⊢Δℕ ⊢F (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′])
      [σ⇑≡σ′⇑] = liftSubstSEq {F = ℕ} [Γ] ⊢Δ [ℕ] [σ] [σ≡σ′]
      var0 = conv (var ⊢ΔℕF (PE.subst (λ x → x0 ∷ x ∈ (Δ ∙ ℕ ∙ subst (liftSubst σ) F))
                                       (wk-subst F) here))
                  (≅-eq (escapeEq (proj₁ ([F] ⊢ΔℕF [σ⇑↑]))
                                  (proj₂ ([F] ⊢ΔℕF [σ⇑↑]) {σ′ = wk1Subst (liftSubst σ′)} [σ′⇑↑]
                                         (wk1SubstSEq {σ = liftSubst σ} {σ′ = liftSubst σ′} [Γℕ] ⊢Δℕ ⊢F
                                           (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]) [σ⇑≡σ′⇑]))))
      [σ′⇑⇑]′ = [σ′⇑↑] , neuTerm (proj₁ ([F] ⊢ΔℕF [σ′⇑↑])) (var x0) var0 (~-var var0)
      [σ⇑⇑≡σ′⇑⇑] = liftSubstSEq {σ′ = liftSubst σ′} {F = F} [Γℕ] ⊢Δℕ [F]
                                (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]) [σ⇑≡σ′⇑]
      ⊢σs≡σ′s = PE.subst (λ x → Δ ∙ ℕ ∙ subst (liftSubst σ) F ⊢ subst (liftSubstn σ 2) s ≅ subst (liftSubstn σ′ 2) s ∷ x)
                         (natrecSucCase σ F)
                         (escapeTermEq (proj₁ ([F₊] ⊢ΔℕF [σ⇑⇑]))
                                       (proj₂ ([s] ⊢ΔℕF [σ⇑⇑]) [σ′⇑⇑]′ [σ⇑⇑≡σ′⇑⇑]))
      ⊢σ′F≡⊢σ′F′ = escapeEq [σ′F] ([F≡F′] (⊢Δ ∙ ⊢ℕ)
                               (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ′]))
      ⊢σ′z≡⊢σ′z′ = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x)
                            (singleSubstLift F zero)
                            (≅-conv (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ′]))
                                                   ([z≡z′] ⊢Δ [σ′]))
                                  (sym (≅-eq (escapeEq (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₂ ([F₀] ⊢Δ [σ]) [σ′] [σ≡σ′])))))
      ⊢σ′s≡⊢σ′s′ = PE.subst (λ x → (Δ ∙ ℕ ∙ subst (liftSubst σ) F) ⊢ subst (liftSubstn σ′ 2) s ≅ subst (liftSubstn σ′ 2) s′ ∷ x)
                     (natrecSucCase σ F)
                     (≅-conv (escapeTermEq (proj₁ ([F₊] ⊢ΔℕF [σ′⇑⇑]′)) ([s≡s′] ⊢ΔℕF [σ′⇑⇑]′))
                             (sym (≅-eq (escapeEq (proj₁ ([F₊] ⊢ΔℕF [σ⇑⇑]))
                                                  (proj₂ ([F₊] ⊢ΔℕF [σ⇑⇑]) [σ′⇑⇑]′ [σ⇑⇑≡σ′⇑⇑] )))))
      ⊢F≡F′ = ≅-trans ⊢σF≡σ′F ⊢σ′F≡⊢σ′F′
      ⊢z≡z′ = ≅ₜ-trans ⊢σz≡σ′z ⊢σ′z≡⊢σ′z′
      ⊢s≡s′ = ≅ₜ-trans ⊢σs≡σ′s ⊢σ′s≡⊢σ′s′
      [σn′] = neuTerm [σℕ] neN′ ⊢n′ n≡n₁
      [σn]′ , [σn≡σn′] = redSubst*Term (redₜ d) [σℕ] [σn′]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₙ′] = irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                            (proj₁ ([F] ⊢Δ ([σ] , [σn′])))
      [Fₙ≡Fₙ′] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (singleSubstComp n′ σ F)) [σFₙ]′ [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn])))
                                        ([σ] , [σn′])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σn′]))
      [σ′m′] = neuTerm [σ′ℕ] neM′ ⊢m′ m≡m₁
      [σ′m]′ , [σ′m≡σ′m′] = redSubst*Term (redₜ d′) [σ′ℕ] [σ′m′]
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₘ′] = irrelevance′ (PE.sym (singleSubstComp m′ σ′ F′))
                              (proj₁ ([F′] ⊢Δ ([σ′] , [σ′m′])))
      [F′ₘ≡F′ₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                   (PE.sym (singleSubstComp m′ σ′ F′))
                                   [σ′F′ₘ]′ [σ′F′ₘ]
                                   ((proj₂ ([F′] ⊢Δ ([σ′] , [σ′m])))
                                           ([σ′] , [σ′m′])
                                           (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′m′]))
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F))
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′m])
                                          ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′))
                                     (proj₁ ([F] ⊢Δ ([σ′] , [σ′m])))
                                     [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [σFₙ′≡σ′Fₘ′] = transEq [σFₙ′] [σFₙ] [σ′F′ₘ′] (symEq [σFₙ] [σFₙ′] [Fₙ≡Fₙ′])
                             (transEq [σFₙ] [σ′F′ₘ] [σ′F′ₘ′] [σFₙ≡σ′F′ₘ] [F′ₘ≡F′ₘ′])
      natrecN = neuTerm [σFₙ′] (natrecₙ neN′) (natrecⱼ ⊢F ⊢z ⊢s ⊢n′)
                        (~-natrec ⊢F ⊢F≡F ⊢z≡z ⊢s≡s n≡n₁ ≈-refl ≈-refl)
      natrecM = neuTerm [σ′F′ₘ′] (natrecₙ neM′) (natrecⱼ ⊢F′ ⊢z′ ⊢s′ ⊢m′)
                        (~-natrec ⊢F′ ⊢F′≡F′ ⊢z′≡z′ ⊢s′≡s′ m≡m₁ ≈-refl ≈-refl)
      natrecN≡M =
        convEqTerm₂ [σFₙ] [σFₙ′] [Fₙ≡Fₙ′]
          (neuEqTerm [σFₙ′] (natrecₙ neN′) (natrecₙ neM′)
                     (natrecⱼ ⊢F ⊢z ⊢s ⊢n′)
                     (conv (natrecⱼ ⊢F′ ⊢z′ ⊢s′ ⊢m′)
                            (sym (≅-eq (escapeEq [σFₙ′] [σFₙ′≡σ′Fₘ′]))))
                     ((~-natrec ⊢F ⊢F≡F′ ⊢z≡z′ ⊢s≡s′
                               (PE.subst₂ (λ x y → _ ⊢ x ~ y ∷ _)
                                          n″≡n′ m″≡m′ prop₂)
                               p≈p′ r≈r′)))
      reduction₁ = natrec-subst* {p = p} {r = r} ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σn′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstComp t σ F))
                                  (PE.sym (singleSubstComp t′ σ F))
                                  (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                               (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                      ([σ] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
      reduction₂ = natrec-subst* {p = p′} {r = r′} ⊢F′ ⊢z′ ⊢s′ (redₜ d′) [σ′ℕ] [σ′m′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y)
                                  (PE.sym (singleSubstComp t σ′ F′))
                                  (PE.sym (singleSubstComp t′ σ′ F′))
                                  (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                               (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                      ([σ′] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] [σFₙ′] [Fₙ≡Fₙ′] natrecN))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] [σ′F′ₘ′] [F′ₘ≡F′ₘ′] natrecM))
  in  transEqTerm [σFₙ] eq₁
                 (transEqTerm [σFₙ] natrecN≡M
                              (convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ] (symEqTerm [σ′F′ₘ] eq₂)))

-- Refuting cases
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ _ d₁ _ zeroᵣ)
                (ℕₜ₌ _ _ d₂ d′ t≡u (sucᵣ prop₂)) _ _ with whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d′ , sucₙ)
... | ()
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ n d₁ _ (ne (neNfₜ neK ⊢k k≡k)))
                (ℕₜ₌ _ _ d₂ d′ t≡u (sucᵣ prop₂)) _ _ =
  ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d′ , sucₙ) (redₜ d₁ , ne neK)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ _ d _ zeroᵣ) [σm]
                (ℕₜ₌ _ _ d₁ d′ t≡u (sucᵣ prop₂)) _ _ with whrDet*Term (redₜ d , zeroₙ) (redₜ d₁ , sucₙ)
... | ()
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ n d _ (ne (neNfₜ neK ⊢k k≡k))) [σm]
                (ℕₜ₌ _ _ d₁ d′ t≡u (sucᵣ prop₂)) _ _ =
  ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d , ne neK)))

natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ _ d _ (sucᵣ prop)) [σm]
                (ℕₜ₌ _ _ d₂ d′ t≡u zeroᵣ) _ _ with whrDet*Term (redₜ d₂ , zeroₙ) (redₜ d , sucₙ)
... | ()
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ _ d₁ _ (sucᵣ prop₁))
                (ℕₜ₌ _ _ d₂ d′ t≡u zeroᵣ) _ _ with whrDet*Term (redₜ d′ , zeroₙ) (redₜ d₁ , sucₙ)
... | ()
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ n d₁ _ (ne (neNfₜ neK ⊢k k≡k)))
                (ℕₜ₌ _ _ d₂ d′ t≡u zeroᵣ) _ _ =
  ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d′ , zeroₙ) (redₜ d₁ , ne neK)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ n d _ (ne (neNfₜ neK ⊢k k≡k))) [σm]
                (ℕₜ₌ _ _ d₂ d′ t≡u zeroᵣ) _ _ =
  ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d₂ , zeroₙ) (redₜ d , ne neK)))

natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ _ d _ (sucᵣ prop)) [σm]
                (ℕₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x x₁ prop₂))) _ _ =
  ⊥-elim (suc≢ne x (whrDet*Term (redₜ d , sucₙ) (redₜ d₂ , ne x)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕₜ _ d _ zeroᵣ) [σm]
                (ℕₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x x₁ prop₂))) _ _ =
  ⊥-elim (zero≢ne x (whrDet*Term (redₜ d , zeroₙ) (redₜ d₂ , ne x)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ _ d₁ _ (sucᵣ prop₁))
                (ℕₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x₁ x₂ prop₂))) _ _ =
  ⊥-elim (suc≢ne x₂ (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d′ , ne x₂)))
natrec-congTerm [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕₜ _ d₁ _ zeroᵣ)
                (ℕₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x₁ x₂ prop₂))) _ _ =
  ⊥-elim (zero≢ne x₂ (whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d′ , ne x₂)))


-- Validity of natural recursion.
natrecᵛ : ∀ {F z s n l} ([Γ] : ⊩ᵛ Γ)
          ([ℕ]  : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
          ([F]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
          ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] / [Γ])
          ([F₊] : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ wk1 (F [ suc (var x0) ]↑) / [Γ] ∙ [ℕ] ∙ [F])
          ([Fₙ] : Γ ⊩ᵛ⟨ l ⟩ F [ n ] / [Γ])
        → Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero ] / [Γ] / [F₀]
        → Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ s ∷ wk1 (F [ suc (var x0) ]↑) / [Γ] ∙ [ℕ] ∙ [F] / [F₊]
        → ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ / [Γ] / [ℕ])
        → Γ ⊩ᵛ⟨ l ⟩ natrec p r F z s n ∷ F [ n ] / [Γ] / [Fₙ]
natrecᵛ {F = F} {z = z} {s = s} {n = n} {l = l}
        [Γ] [ℕ] [F] [F₀] [F₊] [Fₙ] [z] [s] [n]
        {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]′ = S.irrelevance {A = F} (_∙_ {A = ℕ} [Γ] [ℕ])
                           (_∙_ {l = l} [Γ] (ℕᵛ [Γ])) [F]
      [σn]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                              (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
      n′ = subst σ n
      eqPrf = PE.trans (singleSubstComp n′ σ F)
                       (PE.sym (PE.trans (substCompEq F)
                               (substConcatSingleton′ F)))
      [ℕ]′ = ℕᵛ [Γ]
      [F₊]′ = S.irrelevance {A = wk1 (F [ suc (var x0) ]↑)}
                            (_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F])
                            (_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F]′) [F₊]
      [s]′ = S.irrelevanceTerm {A = wk1 (F [ suc (var x0) ]↑)} {t = s}
                               ((_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F]))
                               (_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F]′)
                               [F₊] [F₊]′ [s]
  in  irrelevanceTerm′ eqPrf (irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                                           (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′))))
                        (proj₁ ([Fₙ] ⊢Δ [σ]))
                   (natrecTerm {F = F} {z} {s} {n′} {σ = σ} [Γ]
                               [F]′
                               [F₀] [F₊]′ [z] [s]′ ⊢Δ [σ]
                               [σn]′)
 ,   (λ {σ′} [σ′] [σ≡σ′] →
        let [σ′n]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ′]))
                                     (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                                     (proj₁ ([n] ⊢Δ [σ′]))
            [σn≡σ′n] = irrelevanceEqTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                                         (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ)))
                                         (proj₂ ([n] ⊢Δ [σ]) [σ′] [σ≡σ′])
            [ℕ]′ = ℕᵛ [Γ]
            [F₊]′ = S.irrelevance {A = wk1 (F [ suc (var x0) ]↑)}
                                  (_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F])
                                  (_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F]′) [F₊]
            [s]′ = S.irrelevanceTerm {A = wk1 (F [ suc (var x0) ]↑)} {t = s}
                                     ((_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F]))
                                     (_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F]′)
                                     [F₊] [F₊]′ [s]
        in  irrelevanceEqTerm′ eqPrf
              (irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                            (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′))))
              (proj₁ ([Fₙ] ⊢Δ [σ]))
              (natrec-congTerm {F = F} {F} {z} {z} {s} {s} {n′} {subst σ′ n} {σ = σ}
                               [Γ] [F]′ [F]′ (reflᵛ {A = F} (_∙_ {A = ℕ} {l = l}
                               [Γ] (ℕᵛ [Γ])) [F]′) [F₀] [F₀]
                               (reflᵛ {A = F [ zero ]} [Γ] [F₀]) [F₊]′ [F₊]′
                               (reflᵛ {A = wk1 (F [ suc (var x0) ]↑)}
                                      (_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]′) [F]′) [F₊]′)
                               [z] [z] (reflᵗᵛ {A = F [ zero ]} {z} [Γ] [F₀] [z])
                               [s]′ [s]′
                               (reflᵗᵛ {A = wk1 (F [ suc (var x0) ]↑)} {s}
                                       (_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]′) [F]′) [F₊]′ [s]′)
                               ⊢Δ [σ] [σ′] [σ≡σ′] [σn]′ [σ′n]′ [σn≡σ′n] ≈-refl ≈-refl))

-- Validity of natural recursion congruence.
natrec-congᵛ : ∀ {F F′ z z′ s s′ n n′ l} ([Γ] : ⊩ᵛ Γ)
          ([ℕ]  : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
          ([F]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / [Γ] ∙ [ℕ])
          ([F′]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F′ / [Γ] ∙ [ℕ])
          ([F≡F′]  : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] ∙ [ℕ] / [F])
          ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] / [Γ])
          ([F′₀] : Γ ⊩ᵛ⟨ l ⟩ F′ [ zero ] / [Γ])
          ([F₀≡F′₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero ] ≡ F′ [ zero ] / [Γ] / [F₀])
          ([F₊] : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ wk1 (F [ suc (var x0) ]↑) / [Γ] ∙ [ℕ] ∙ [F])
          ([F′₊] : Γ ∙ ℕ ∙ F′ ⊩ᵛ⟨ l ⟩ wk1 (F′ [ suc (var x0) ]↑) / [Γ] ∙ [ℕ] ∙ [F′])
          ([F₊≡F′₊] : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ wk1 (F [ suc (var x0) ]↑)
                              ≡  wk1 (F′ [ suc (var x0) ]↑) / [Γ] ∙ [ℕ] ∙ [F]
                              / [F₊])
          ([Fₙ] : Γ ⊩ᵛ⟨ l ⟩ F [ n ] / [Γ])
          ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero ] / [Γ] / [F₀])
          ([z′] : Γ ⊩ᵛ⟨ l ⟩ z′ ∷ F′ [ zero ] / [Γ] / [F′₀])
          ([z≡z′] : Γ ⊩ᵛ⟨ l ⟩ z ≡ z′ ∷ F [ zero ] / [Γ] / [F₀])
          ([s] : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ s ∷ wk1 (F [ suc (var x0) ]↑) / [Γ] ∙ [ℕ] ∙ [F] / [F₊])
          ([s′] : Γ ∙ ℕ ∙ F′ ⊩ᵛ⟨ l ⟩ s′ ∷ wk1 (F′ [ suc (var x0) ]↑) / [Γ] ∙ [ℕ] ∙ [F′]
                           / [F′₊])
          ([s≡s′] : Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ s ≡ s′ ∷ wk1 (F [ suc (var x0) ]↑)
                             / [Γ] ∙ [ℕ] ∙ [F] / [F₊])
          ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ / [Γ] / [ℕ])
          ([n′] : Γ ⊩ᵛ⟨ l ⟩ n′ ∷ ℕ / [Γ] / [ℕ])
          ([n≡n′] : Γ ⊩ᵛ⟨ l ⟩ n ≡ n′ ∷ ℕ / [Γ] / [ℕ])
        → p ≈ p′
        → r ≈ r′
        → Γ ⊩ᵛ⟨ l ⟩ natrec p r F z s n ≡ natrec p′ r′ F′ z′ s′ n′ ∷ F [ n ] / [Γ] / [Fₙ]
natrec-congᵛ {p = p} {r = r} {F = F} {F′ = F′} {z = z} {z′ = z′}
             {s = s} {s′ = s′} {n = n} {n′ = n′} {l = l}
             [Γ] [ℕ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
             [Fₙ] [z] [z′] [z≡z′] [s] [s′] [s≡s′] [n] [n′]
             [n≡n′] p≈p′ r≈r′ {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ℕ]′ = ℕᵛ [Γ]
      [F]′ = S.irrelevance {A = F} (_∙_ {A = ℕ} [Γ] [ℕ])
                           (_∙_ {l = l} [Γ] (ℕᵛ [Γ])) [F]
      [F′]′ = S.irrelevance {A = F′} (_∙_ {A = ℕ} [Γ] [ℕ])
                            (_∙_ {l = l} [Γ] (ℕᵛ [Γ])) [F′]
      [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′} (_∙_ {A = ℕ} [Γ] [ℕ])
                                (_∙_ {l = l} [Γ] (ℕᵛ [Γ])) [F] [F]′ [F≡F′]
      [σn]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                              (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
      [σn′]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                               (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) (proj₁ ([n′] ⊢Δ [σ]))
      [σn≡σn′]′ = irrelevanceEqTerm {l′ = l} (proj₁ ([ℕ] ⊢Δ [σ]))
                                    (ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))) ([n≡n′] ⊢Δ [σ])
      [Fₙ]′ = irrelevance′ (PE.sym (singleSubstComp (subst σ n) σ F))
                           (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′)))
      [F₊]′ = S.irrelevance {A = wk1 (F [ suc (var x0) ]↑)}
                            (_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F])
                            (_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F]′) [F₊]
      [F′₊]′ = S.irrelevance {A = wk1 (F′ [ suc (var x0) ]↑)}
                             (_∙_ {A = F′} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F′])
                             (_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F′]′) [F′₊]
      [F₊≡F′₊]′ = S.irrelevanceEq {A = wk1 (F [ suc (var x0) ]↑)}
                                  {B = wk1 (F′ [ suc (var x0) ]↑)}
                                  ((_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F]))
                                  ((_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F]′))
                                  [F₊] [F₊]′ [F₊≡F′₊]
      [s]′ = S.irrelevanceTerm {A = wk1 (F [ suc (var x0) ]↑)} {t = s}
                               ((_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F]))
                               (_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F]′)
                               [F₊] [F₊]′ [s]
      [s′]′ = S.irrelevanceTerm {A = wk1 (F′ [ suc (var x0) ]↑)} {t = s′}
                               ((_∙_ {A = F′} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F′]))
                               (_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F′]′)
                               [F′₊] [F′₊]′ [s′]
      [s≡s′]′ = S.irrelevanceEqTerm {A = wk1 (F [ suc (var x0) ]↑)} {t = s} {u = s′}
                                    (((_∙_ {A = F} {l = l} (_∙_ {A = ℕ} {l = l} [Γ] [ℕ]) [F])))
                                    ((_∙_ {l = l} (_∙_ {l = l} [Γ] [ℕ]′) [F]′))
                                    [F₊] [F₊]′ [s≡s′]
  in irrelevanceEqTerm′ (PE.sym (singleSubstLift F n))
                        [Fₙ]′ (proj₁ ([Fₙ] ⊢Δ [σ]))
                        (natrec-congTerm {p = p} {r = r} {F = F} {F′ = F′} {z = z} {z′ = z′}
                               {s = s} {s′ = s′} {n = subst σ n} {m = subst σ n′}
                               [Γ] [F]′ [F′]′ [F≡F′]′
                               [F₀] [F′₀] [F₀≡F′₀]
                               [F₊]′ [F′₊]′ [F₊≡F′₊]′
                               [z] [z′] [z≡z′]
                               [s]′ [s′]′ [s≡s′]′ ⊢Δ
                               [σ] [σ] (reflSubst [Γ] ⊢Δ [σ])
                               [σn]′ [σn′]′ [σn≡σn′]′ p≈p′ r≈r′)
