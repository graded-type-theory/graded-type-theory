------------------------------------------------------------------------
-- Validity of Π and Σ-types.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Substitution.Introductions.Pi
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Weakening R using (_∷_⊆_)
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Weakening R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Weakening R
open import Definition.LogicalRelation.Substitution.Properties R
import Definition.LogicalRelation.Substitution.Irrelevance R as S
open import Definition.LogicalRelation.Substitution.Introductions.Universe R

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    l : TypeLevel
    F F′ H : Term n
    E G G′ : Term (1+ n)
    Γ : Con Term n
    p q : M
    b : BinderMode

-- Validity of W.
⟦_⟧ᵛ : ∀ W {n} {Γ : Con Term n} {F G l}
     ([Γ] : ⊩ᵛ Γ)
     ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
   → Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F]
   → BindingType-allowed W
   → Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ G / [Γ]
⟦ W ⟧ᵛ {n = n} {Γ} {F} {G} {l} [Γ] [F] [G] ok =
  wrap λ {k} {Δ = Δ} {σ = σ} ⊢Δ [σ] →
  let [F]σ {σ′} [σ′] = unwrap [F] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ′} [σ′] = escape (proj₁ ([F]σ {σ′} [σ′]))
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      [G]σ {σ′} [σ′] = unwrap [G] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F [σ′])
                           (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′])
      ⊢G {σ′} [σ′] = escape (proj₁ ([G]σ {σ′} [σ′]))
      ⊢G≡G = escapeEq (proj₁ ([G]σ [σ])) (reflEq (proj₁ ([G]σ [σ])))
      ⊢ΠF▹G = ⟦ W ⟧ⱼ (⊢F [σ]) (⊢G [σ]) ok
      [G]a : ∀ {m} {ρ : Wk m k} {Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
             ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ F [ ρ •ₛ σ ]
                / proj₁ (unwrap [F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
           → Σ (Δ₁ ⊩⟨ l ⟩ G [ consSubst (ρ •ₛ σ) a ])
               (λ [Aσ] →
               {σ′ : Subst m (1+ n)} →
               (Σ (Δ₁ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] →
                  Δ₁ ⊩⟨ l ⟩ head σ′ ∷ F [ tail σ′ ] / proj₁ (unwrap [F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ˢ consSubst (ρ •ₛ σ) a ≡ σ′ ∷ Γ ∙ F /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ l ⟩ G [ consSubst (ρ •ₛ σ) a ] ≡
               G [ σ′ ] / [Aσ])
      [G]a {_} {ρ} a [ρ] ⊢Δ₁ [a] = (unwrap [G] {σ = consSubst (ρ •ₛ σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                          [F] [a]))
      [G]a′ : ∀ {m} {ρ : Wk m k} {Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
            → Δ₁ ⊩⟨ l ⟩ a ∷ F [ ρ •ₛ σ ]
                 / proj₁ (unwrap [F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))
            → Δ₁ ⊩⟨ l ⟩ U.wk (lift ρ) (G [ liftSubst σ ]) [ a ]₀
      [G]a′ a ρ ⊢Δ₁ [a] = irrelevance′ (PE.sym (singleSubstWkComp a σ G))
                                   (proj₁ ([G]a a ρ ⊢Δ₁ [a]))
  in  Bᵣ′ W (F [ σ ]) (G [ liftSubst σ ])
         (PE.subst
           (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ F [ σ ] ▹ (G [ liftSubst σ ]))
           (PE.sym (B-subst _ W F G))
           (idRed:*: ⊢ΠF▹G))
         (⊢F [σ]) (⊢G [σ])
         (≅-W-cong W (⊢F [σ]) ⊢F≡F ⊢G≡G ok)
         (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
         (λ {_} {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
            let [a]′ = irrelevanceTerm′
                         (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ (unwrap [F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))) [a]
            in  [G]a′ a [ρ] ⊢Δ₁ [a]′)
         (λ {_} {ρ} {Δ₁} {a} {b} [ρ] ⊢Δ₁ [a] [b] [a≡b] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′
                         (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a]
                [b]′ = irrelevanceTerm′
                         (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [b]
                [a≡b]′ = irrelevanceEqTerm′
                           (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                           (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a≡b]
            in  irrelevanceEq″
                  (PE.sym (singleSubstWkComp a σ G))
                  (PE.sym (singleSubstWkComp b σ G))
                  (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]′))
                  ([G]a′ a [ρ] ⊢Δ₁ [a]′)
                  (proj₂ ([G]a a [ρ] ⊢Δ₁ [a]′)
                         ([ρσ] , [b]′)
                         (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]′)))
         ok
  ,  (λ {σ′} [σ′] [σ≡σ′] →
        let var0 = var (⊢Δ ∙ ⊢F [σ])
                       (PE.subst (λ x → x0 ∷ x ∈ Δ ∙ F [ σ ])
                                 (wk-subst F) here)
            [wk1σ] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ]
            [wk1σ′] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ′]
            [wk1σ≡wk1σ′] = wk1SubstSEq [Γ] ⊢Δ (⊢F [σ]) [σ] [σ≡σ′]
            [F][wk1σ] = proj₁ (unwrap [F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
            [F][wk1σ′] = proj₁ (unwrap [F] (⊢Δ ∙ ⊢F [σ]) [wk1σ′])
            var0′ = conv var0
                         (≅-eq (escapeEq [F][wk1σ]
                                             (proj₂ (unwrap [F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
                                                    [wk1σ′] [wk1σ≡wk1σ′])))
        in  B₌ (F [ σ′ ]) (G [ liftSubst σ′ ])
               (PE.subst
                 (λ x → Δ ⊢ x ⇒* ⟦ W ⟧ F [ σ′ ] ▹ (G [ liftSubst σ′ ]))
                 (PE.sym (B-subst _ W F G))
                 (id (⟦ W ⟧ⱼ (⊢F [σ′]) (⊢G [σ′]) ok)))
               (≅-W-cong W (⊢F [σ])
                       (escapeEq (proj₁ (unwrap [F] ⊢Δ [σ]))
                                    (proj₂ (unwrap [F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
                       (escapeEq (proj₁ ([G]σ [σ])) (proj₂ ([G]σ [σ])
                         ([wk1σ′] , neuTerm [F][wk1σ′] (var x0) var0′ (~-var var0′))
                         ([wk1σ≡wk1σ′] , neuEqTerm [F][wk1σ]
                           (var x0) (var x0) var0 var0 (~-var var0))))
                       ok)
               (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ (unwrap [F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
               (λ {_} {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                      [ρσ′] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′]
                      [a]′ = irrelevanceTerm′ (wk-subst F) (wk [ρ] ⊢Δ₁ [σF])
                                 (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a]
                      [a]″ = convTerm₁ (proj₁ (unwrap [F] ⊢Δ₁ [ρσ]))
                                        (proj₁ (unwrap [F] ⊢Δ₁ [ρσ′]))
                                        (proj₂ (unwrap [F] ⊢Δ₁ [ρσ]) [ρσ′]
                                               (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′]))
                                        [a]′
                      [ρσa≡ρσ′a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁
                                                (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                                (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′])
                                                [F] [a]′
                  in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                      (PE.sym (singleSubstWkComp a σ′ G))
                                      (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]′))
                                      ([G]a′ a [ρ] ⊢Δ₁ [a]′)
                                      (proj₂ ([G]a a [ρ] ⊢Δ₁ [a]′)
                                             (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′] , [a]″)
                                             [ρσa≡ρσ′a])))

-- A variant of ⟦_⟧ᵛ.
ΠΣᵛ :
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ]) →
  Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F] →
  ΠΣ-allowed b p q →
  Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G / [Γ]
ΠΣᵛ {b = BMΠ}   = ⟦ BΠ _ _ ⟧ᵛ
ΠΣᵛ {b = BMΣ _} = ⟦ BΣ _ _ _ ⟧ᵛ

-- Validity of W-congruence.
W-congᵛ : ∀ {F G H E l} W
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
          ([H] : Γ ⊩ᵛ⟨ l ⟩ H / [Γ])
          ([E] : Γ ∙ H ⊩ᵛ⟨ l ⟩ E / [Γ] ∙ [H])
          ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H / [Γ] / [F])
          ([G≡E] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ E / [Γ] ∙ [F] / [G])
          (ok : BindingType-allowed W)
        → Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ H ▹ E / [Γ] /
            ⟦ W ⟧ᵛ {F = F} {G} [Γ] [F] [G] ok
W-congᵛ
  {Γ = Γ} {F} {G} {H} {E} {l}
  (BΠ p q) [Γ] [F] [G] [H] [E] [F≡H] [G≡E] ok {σ = σ} ⊢Δ [σ] =
  let [ΠFG] = ⟦ BΠ p q ⟧ᵛ {F = F} {G} [Γ] [F] [G] ok
      [σΠFG] = proj₁ (unwrap [ΠFG] ⊢Δ [σ])
      l′ , Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ _ =
        extractMaybeEmb (Π-elim [σΠFG])
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = escape (proj₁ (unwrap [H] ⊢Δ [σ]))
      ⊢σE = escape (proj₁ (unwrap [E] {σ = liftSubst σ} (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
  in  B₌ (H [ σ ]) (E [ liftSubst σ ])
         (id (ΠΣⱼ ⊢σH ⊢σE ok)) (≅-ΠΣ-cong ⊢σF ⊢σF≡σH ⊢σG≡σE ok)
         (λ ρ ⊢Δ₁ →
           let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
               eqA = PE.sym (wk-subst F)
               eqB = PE.sym (wk-subst H)
               p = proj₁ (unwrap [F] ⊢Δ₁ [ρσ])
               wut : _ ⊩⟨ _ ⟩ U.wk _ (F [ σ ])
               wut = [F]′ ρ ⊢Δ₁
               A≡B = [F≡H] ⊢Δ₁ [ρσ]
           in  irrelevanceEq″ eqA eqB p wut A≡B)
         (λ {_} {ρ} {Δ} {a} [ρ] ⊢Δ₁ [a] →
                let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                    [a]′ = irrelevanceTerm′ (wk-subst F)
                                            ([F]′ [ρ] ⊢Δ₁)
                                            (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a]
                    [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]′
                in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                   (PE.sym (singleSubstWkComp a σ E))
                                   (proj₁ (unwrap [G] ⊢Δ₁ [aρσ]))
                                   ([G]′ [ρ] ⊢Δ₁ [a])
                                   ([G≡E] ⊢Δ₁ [aρσ]))

W-congᵛ
  {Γ = Γ} {F = F} {G} {H} {E} {l}
  (BΣ m p q) [Γ] [F] [G] [H] [E] [F≡H] [G≡E] ok {σ = σ} ⊢Δ [σ] =
  let [ΠFG] = ⟦ BΣ m p q ⟧ᵛ {F = F} {G} [Γ] [F] [G] ok
      [σΠFG] = proj₁ (unwrap [ΠFG] ⊢Δ [σ])
      l′ , Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ _ =
        extractMaybeEmb (Σ-elim [σΠFG])
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ (unwrap [G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = escape (proj₁ (unwrap [H] ⊢Δ [σ]))
      ⊢σE = escape (proj₁ (unwrap [E] (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
  in  B₌ (H [ σ ]) (E [ liftSubst σ ])
         (id (ΠΣⱼ ⊢σH ⊢σE ok))
         (≅-ΠΣ-cong ⊢σF ⊢σF≡σH ⊢σG≡σE ok)
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                        eqA = PE.sym (wk-subst F)
                        eqB = PE.sym (wk-subst H)
                        p = proj₁ (unwrap [F] ⊢Δ₁ [ρσ])
                        wut : _ ⊩⟨ _ ⟩ U.wk _ (F [ σ ])
                        wut = [F]′ ρ ⊢Δ₁
                        A≡B = [F≡H] ⊢Δ₁ [ρσ]
                    in  irrelevanceEq″ eqA eqB p wut A≡B)
         (λ {_} {ρ} {Δ} {a} [ρ] ⊢Δ₁ [a] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′ (wk-subst F)
                                        ([F]′ [ρ] ⊢Δ₁)
                                        (proj₁ (unwrap [F] ⊢Δ₁ [ρσ])) [a]
                [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]′
            in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                (PE.sym (singleSubstWkComp a σ E))
                                (proj₁ (unwrap [G] ⊢Δ₁ [aρσ]))
                                ([G]′ [ρ] ⊢Δ₁ [a])
                                ([G≡E] ⊢Δ₁ [aρσ]))

-- Validity of ⟦ W ⟧ as a term.
Wᵗᵛ : ∀ {Γ : Con Term n} {F G} W ([Γ] : ⊩ᵛ_ {n = n} Γ)
      ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
      ([U] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
    → Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ]
    → Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ∷ U / [Γ] ∙ [F] / [U]
    → BindingType-allowed W
    → Γ ⊩ᵛ⟨ ¹ ⟩ ⟦ W ⟧ F ▹ G ∷ U / [Γ] / Uᵛ [Γ]
Wᵗᵛ {Γ = Γ} {F} {G} W [Γ] [F] [U] [Fₜ] [Gₜ] ok {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      ⊢F = escape (proj₁ (unwrap [F] ⊢Δ [σ]))
      ⊢Fₜ = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢F≡Fₜ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ)
                               (reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ])))
      ⊢Gₜ = escapeTerm (proj₁ (unwrap [U] (⊢Δ ∙ ⊢F) [liftσ]))
                           (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
      ⊢G≡Gₜ = escapeTermEq (proj₁ (unwrap [U] (⊢Δ ∙ ⊢F) [liftσ]))
                               (reflEqTerm (proj₁ (unwrap [U] (⊢Δ ∙ ⊢F) [liftσ]))
                                           (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ])))
      [F]₀ = univᵛ {A = F} [Γ] (Uᵛ [Γ]) [Fₜ]
      [Gₜ]′ = S.irrelevanceTerm {A = U} {t = G}
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                [U] (Uᵛ ([Γ] ∙ [F]₀)) [Gₜ]
      [G]₀ = univᵛ {A = G} (_∙_ {A = F} [Γ] [F]₀)
                   (Uᵛ ([Γ] ∙ [F]₀)) [Gₜ]′
      [ΠFG] = unwrap (⟦ W ⟧ᵛ {F = F} {G} [Γ] [F]₀ [G]₀ ok) ⊢Δ [σ]
  in  Uₜ (⟦ W ⟧ F [ σ ] ▹ (G [ liftSubst σ ]))
         (PE.subst
            (Δ ⊢_:⇒*: ⟦ W ⟧ F [ σ ] ▹ (G [ liftSubst σ ]) ∷ U)
            (PE.sym (B-subst σ W F G))
            (idRedTerm:*: (⟦ W ⟧ⱼᵤ ⊢Fₜ ⊢Gₜ ok)))
         ⟦ W ⟧-type (≅ₜ-W-cong W ⊢F ⊢F≡Fₜ ⊢G≡Gₜ ok) (proj₁ [ΠFG])
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         let [liftσ′] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′]
             [wk1σ] = wk1SubstS [Γ] ⊢Δ ⊢F [σ]
             [wk1σ′] = wk1SubstS [Γ] ⊢Δ ⊢F [σ′]
             var0 = conv (var (⊢Δ ∙ ⊢F)
                         (PE.subst (λ x → x0 ∷ x ∈ Δ ∙ F [ σ ])
                                   (wk-subst F) here))
                    (≅-eq (escapeEq (proj₁ (unwrap [F] (⊢Δ ∙ ⊢F) [wk1σ]))
                                        (proj₂ (unwrap [F] (⊢Δ ∙ ⊢F) [wk1σ]) [wk1σ′]
                                               (wk1SubstSEq [Γ] ⊢Δ ⊢F [σ] [σ≡σ′]))))
             [liftσ′]′ = [wk1σ′]
                       , neuTerm (proj₁ (unwrap [F] (⊢Δ ∙ ⊢F) [wk1σ′])) (var x0)
                                 var0 (~-var var0)
             ⊢F′ = escape (proj₁ (unwrap [F] ⊢Δ [σ′]))
             ⊢Fₜ′ = escapeTerm (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ′]))
             ⊢Gₜ′ = escapeTerm (proj₁ (unwrap [U] (⊢Δ ∙ ⊢F′) [liftσ′]))
                                  (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F′) [liftσ′]))
             ⊢F≡F′ = escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ)
                                     (proj₂ ([Fₜ] ⊢Δ [σ]) [σ′] [σ≡σ′])
             ⊢G≡G′ = escapeTermEq (proj₁ (unwrap [U] (⊢Δ ∙ ⊢F) [liftσ]))
                                     (proj₂ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]) [liftσ′]′
                                            (liftSubstSEq {F = F} [Γ] ⊢Δ [F] [σ] [σ≡σ′]))
             [ΠFG]′ = unwrap (⟦ W ⟧ᵛ {F = F} {G} [Γ] [F]₀ [G]₀ ok)
                        ⊢Δ [σ′]
         in  Uₜ₌ (⟦ W ⟧ F [ σ ] ▹ (G [ liftSubst σ ]))
                 (⟦ W ⟧ F [ σ′ ] ▹ (G [ liftSubst σ′ ]))
                 (PE.subst
                   (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ F [ σ ] ▹ (G [ liftSubst σ ]) ∷ U)
                   (PE.sym (B-subst σ W F G))
                   (idRedTerm:*: (⟦ W ⟧ⱼᵤ ⊢Fₜ ⊢Gₜ ok)))
                 (PE.subst
                   (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ F [ σ′ ] ▹ (G [ liftSubst σ′ ]) ∷ U)
                   (PE.sym (B-subst σ′ W F G))
                   (idRedTerm:*: (⟦ W ⟧ⱼᵤ ⊢Fₜ′ ⊢Gₜ′ ok)))
                 ⟦ W ⟧-type ⟦ W ⟧-type (≅ₜ-W-cong W ⊢F ⊢F≡F′ ⊢G≡G′ ok)
                 (proj₁ [ΠFG]) (proj₁ [ΠFG]′) (proj₂ [ΠFG] [σ′] [σ≡σ′]))

-- Validity of W-congruence as a term equality.
W-congᵗᵛ : ∀ {Γ : Con Term n} {F G H E} W
           ([Γ] : ⊩ᵛ_ {n = n} Γ)
           ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
           ([H] : Γ ⊩ᵛ⟨ ¹ ⟩ H / [Γ])
           ([UF] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
           ([UH] : Γ ∙ H ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [H])
           ([F]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ])
           ([G]ₜ : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ∷ U / [Γ] ∙ [F] / [UF])
           ([H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ H ∷ U / [Γ] / Uᵛ [Γ])
           ([E]ₜ : Γ ∙ H ⊩ᵛ⟨ ¹ ⟩ E ∷ U / [Γ] ∙ [H] / [UH])
           ([F≡H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ≡ H ∷ U / [Γ] / Uᵛ [Γ])
           ([G≡E]ₜ : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ≡ E ∷ U / [Γ] ∙ [F] / [UF])
         → BindingType-allowed W
         → Γ ⊩ᵛ⟨ ¹ ⟩ ⟦ W ⟧ F ▹ G ≡ ⟦ W ⟧ H ▹ E ∷ U / [Γ] / Uᵛ [Γ]
W-congᵗᵛ
  {F = F} {G} {H} {E} W [Γ] [F] [H] [UF] [UH] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ
  [G≡E]ₜ ok {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let ⊢F = escape (proj₁ (unwrap [F] ⊢Δ [σ]))
      ⊢H = escape (proj₁ (unwrap [H] ⊢Δ [σ]))
      [liftFσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [liftHσ] = liftSubstS {F = H} [Γ] ⊢Δ [H] [σ]
      [F]ᵤ = univᵛ {A = F} [Γ] (Uᵛ [Γ]) [F]ₜ
      [G]ᵤ₁ = univᵛ {A = G} {l′ = ⁰} (_∙_ {A = F} [Γ] [F]) [UF] [G]ₜ
      [G]ᵤ = S.irrelevance {A = G} (_∙_ {A = F} [Γ] [F])
                           (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁
      [H]ᵤ = univᵛ {A = H} [Γ] (Uᵛ [Γ]) [H]ₜ
      [E]ᵤ = S.irrelevance {A = E} (_∙_ {A = H} [Γ] [H]) (_∙_ {A = H} [Γ] [H]ᵤ)
                           (univᵛ {A = E} {l′ = ⁰} (_∙_ {A = H} [Γ] [H]) [UH] [E]ₜ)
      [F≡H]ᵤ = univEqᵛ {A = F} {H} [Γ] (Uᵛ [Γ]) [F]ᵤ [F≡H]ₜ
      [G≡E]ᵤ = S.irrelevanceEq {A = G} {B = E} (_∙_ {A = F} [Γ] [F])
                               (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁ [G]ᵤ
                 (univEqᵛ {A = G} {E} (_∙_ {A = F} [Γ] [F]) [UF] [G]ᵤ₁ [G≡E]ₜ)
      ΠFGₜ =
        ⟦ W ⟧ⱼᵤ
          (escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([F]ₜ ⊢Δ [σ])))
          (escapeTerm (proj₁ (unwrap [UF] (⊢Δ ∙ ⊢F) [liftFσ]))
             (proj₁ ([G]ₜ (⊢Δ ∙ ⊢F) [liftFσ])))
          ok
      ΠHEₜ =
        ⟦ W ⟧ⱼᵤ
          (escapeTerm {l = ¹} (Uᵣ′ ⁰ 0<1 ⊢Δ) (proj₁ ([H]ₜ ⊢Δ [σ])))
          (escapeTerm (proj₁ (unwrap [UH] (⊢Δ ∙ ⊢H) [liftHσ]))
             (proj₁ ([E]ₜ (⊢Δ ∙ ⊢H) [liftHσ])))
          ok
  in  Uₜ₌ (⟦ W ⟧ F [ σ ] ▹ (G [ liftSubst σ ]))
          (⟦ W ⟧ H [ σ ] ▹ (E [ liftSubst σ ]))
          (PE.subst
            (λ x → Δ ⊢ x :⇒*: ⟦ W ⟧ F [ σ ] ▹ (G [ liftSubst σ ]) ∷ U)
            (PE.sym (B-subst σ W F G))
            (idRedTerm:*: ΠFGₜ))
          (PE.subst
             (Δ ⊢_:⇒*: ⟦ W ⟧ H [ σ ] ▹ (E [ liftSubst σ ]) ∷ U)
             (PE.sym (B-subst σ W H E))
             (idRedTerm:*: ΠHEₜ))
          ⟦ W ⟧-type ⟦ W ⟧-type
          (≅ₜ-W-cong W ⊢F (escapeTermEq (Uᵣ′ ⁰ 0<1 ⊢Δ) ([F≡H]ₜ ⊢Δ [σ]))
                        (escapeTermEq (proj₁ (unwrap [UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                                          ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftFσ]))
                        ok)
          (proj₁ (unwrap (⟦ W ⟧ᵛ {F = F} {G} [Γ] [F]ᵤ [G]ᵤ ok) ⊢Δ [σ]))
          (proj₁ (unwrap (⟦ W ⟧ᵛ {F = H} {E} [Γ] [H]ᵤ [E]ᵤ ok) ⊢Δ [σ]))
          (W-congᵛ {F = F} {G} {H} {E} W [Γ] [F]ᵤ [G]ᵤ [H]ᵤ [E]ᵤ
             [F≡H]ᵤ [G≡E]ᵤ ok ⊢Δ [σ])

-- Validity of non-dependent binding types.
ndᵛ : ∀ {F G l} W
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ G / [Γ]
    → BindingType-allowed W
    → Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ wk1 G / [Γ]
ndᵛ {F = F} {G} W [Γ] [F] [G] =
  ⟦ W ⟧ᵛ {F = F} {wk1 G} [Γ] [F] (wk1ᵛ {A = G} {F} [Γ] [F] [G])

-- Validity of non-dependent binding type congruence.
nd-congᵛ : ∀ {F F′ G G′ l} W
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ])
           ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] / [F])
           ([G] : Γ ⊩ᵛ⟨ l ⟩ G / [Γ])
           ([G′] : Γ ⊩ᵛ⟨ l ⟩ G′ / [Γ])
           ([G≡G′] : Γ ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] / [G])
         → (ok : BindingType-allowed W)
         → Γ ⊩ᵛ⟨ l ⟩ ⟦ W ⟧ F ▹ wk1 G ≡ ⟦ W ⟧ F′ ▹ wk1 G′ / [Γ] /
             ndᵛ {F = F} {G} W [Γ] [F] [G] ok
nd-congᵛ
  {F = F} {F′} {G} {G′}
  W [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] ok ⊢Δ [σ] =
  W-congᵛ W [Γ] [F] (wk1ᵛ {A = G} {F} [Γ] [F] [G])
    [F′] (wk1ᵛ {A = G′} {F′} [Γ] [F′] [G′])
    [F≡F′] (wk1Eqᵛ {A = G} {G′} {F} [Γ] [F] [G] [G≡G′])
    ok ⊢Δ [σ]

-- Respecialized declarations at Π and Σ
Πᵛ :
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ]) →
  Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F] →
  Π-allowed p q →
  Γ ⊩ᵛ⟨ l ⟩ Π p , q ▷ F ▹ G / [Γ]
Πᵛ = ⟦ BΠ _ _ ⟧ᵛ

Π-congᵛ :
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([H] : Γ ⊩ᵛ⟨ l ⟩ H / [Γ]) →
  Γ ∙ H ⊩ᵛ⟨ l ⟩ E / [Γ] ∙ [H] →
  Γ ⊩ᵛ⟨ l ⟩ F ≡ H / [Γ] / [F] →
  Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ E / [Γ] ∙ [F] / [G] →
  (ok : Π-allowed p q) →
  Γ ⊩ᵛ⟨ l ⟩ Π p , q ▷ F ▹ G ≡ Π p , q ▷ H ▹ E / [Γ] / Πᵛ [Γ] [F] [G] ok
Π-congᵛ = W-congᵛ (BΠ _ _)

Πᵗᵛ :
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
  ([U] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [F]) →
  Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ] →
  Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ∷ U / [Γ] ∙ [F] / [U] →
  Π-allowed p q →
  Γ ⊩ᵛ⟨ ¹ ⟩ Π p , q ▷ F ▹ G ∷ U / [Γ] / Uᵛ [Γ]
Πᵗᵛ {G = G} = Wᵗᵛ {G = G} (BΠ _ _)

Π-congᵗᵛ :
  ([Γ] : ⊩ᵛ_ {n = n} Γ)
  ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F / [Γ])
  ([H] : Γ ⊩ᵛ⟨ ¹ ⟩ H / [Γ])
  ([UF] : Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [F])
  ([UH] : Γ ∙ H ⊩ᵛ⟨ ¹ ⟩ U / [Γ] ∙ [H]) →
  Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ U / [Γ] / Uᵛ [Γ] →
  Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ∷ U / [Γ] ∙ [F] / [UF] →
  Γ ⊩ᵛ⟨ ¹ ⟩ H ∷ U / [Γ] / Uᵛ [Γ] →
  Γ ∙ H ⊩ᵛ⟨ ¹ ⟩ E ∷ U / [Γ] ∙ [H] / [UH] →
  Γ ⊩ᵛ⟨ ¹ ⟩ F ≡ H ∷ U / [Γ] / Uᵛ [Γ] →
  Γ ∙ F ⊩ᵛ⟨ ¹ ⟩ G ≡ E ∷ U / [Γ] ∙ [F] / [UF] →
  Π-allowed p q →
  Γ ⊩ᵛ⟨ ¹ ⟩ Π p , q ▷ F ▹ G ≡ Π p , q ▷ H ▹ E ∷ U / [Γ] / Uᵛ [Γ]
Π-congᵗᵛ {G = G} {E = E} = W-congᵗᵛ {G = G} {E = E} (BΠ _ _)

▹▹ᵛ :
  ([Γ] : ⊩ᵛ Γ) →
  Γ ⊩ᵛ⟨ l ⟩ F / [Γ] →
  Γ ⊩ᵛ⟨ l ⟩ G / [Γ] →
  Π-allowed p q →
  Γ ⊩ᵛ⟨ l ⟩ Π p , q ▷ F ▹ wk1 G / [Γ]
▹▹ᵛ = ndᵛ (BΠ _ _)

▹▹-congᵛ :
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ]) →
  Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ] →
  Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] / [F] →
  ([G] : Γ ⊩ᵛ⟨ l ⟩ G / [Γ]) →
  Γ ⊩ᵛ⟨ l ⟩ G′ / [Γ] →
  Γ ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] / [G] →
  (ok : Π-allowed p q) →
  Γ ⊩ᵛ⟨ l ⟩ Π p , q ▷ F ▹ wk1 G ≡ Π p , q ▷ F′ ▹ wk1 G′ / [Γ] /
    ▹▹ᵛ [Γ] [F] [G] ok
▹▹-congᵛ = nd-congᵛ (BΠ _ _)

Σᵛ : ∀ {Γ : Con Term n} {F G l p q m} → _
Σᵛ {Γ = Γ} {F} {G} {l} {p} {q} {m} = ⟦ BΣ m p q ⟧ᵛ {Γ = Γ} {F} {G} {l}

Σ-congᵛ : ∀ {Γ : Con Term n} {F G H E l p q m} → _
Σ-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} {p} {q} {m} =
  W-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} (BΣ m p q)

Σᵗᵛ : ∀ {Γ : Con Term n} {F G p q m} → _
Σᵗᵛ {Γ = Γ} {F} {G} {p} {q} {m} = Wᵗᵛ {Γ = Γ} {F} {G} (BΣ m p q)

Σ-congᵗᵛ : ∀ {Γ : Con Term n} {F G H E p q m} → _
Σ-congᵗᵛ {Γ = Γ} {F} {G} {H} {E} {p} {q} {m} =
  W-congᵗᵛ {Γ = Γ} {F} {G} {H} {E} (BΣ m p q)

××ᵛ : ∀ {Γ : Con Term n} {F G l p q m} → _
××ᵛ {Γ = Γ} {F} {G} {l} {p} {q} {m} = ndᵛ {Γ = Γ} {F} {G} {l} (BΣ m p q)

××-congᵛ : ∀ {Γ : Con Term n} {F F′ G G′ l p q m} → _
××-congᵛ {Γ = Γ} {F} {F′} {G} {G′} {l} {p} {q} {m} =
  nd-congᵛ {Γ = Γ} {F} {F′} {G} {G′} {l} (BΣ m p q)
