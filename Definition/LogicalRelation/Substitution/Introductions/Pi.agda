------------------------------------------------------------------------
-- Validity of Π and Σ-types.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Pi
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
open import Definition.Typed.Weakening R using (_∷_⊇_)
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
      [G]a : ∀ {m} {ρ : Wk m k} {Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊇ Δ) (⊢Δ₁ : ⊢ Δ₁)
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
      [G]a′ : ∀ {m} {ρ : Wk m k} {Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊇ Δ) (⊢Δ₁ : ⊢ Δ₁)
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

Σᵛ : ∀ {Γ : Con Term n} {F G l p q m} → _
Σᵛ {Γ = Γ} {F} {G} {l} {p} {q} {m} = ⟦ BΣ m p q ⟧ᵛ {Γ = Γ} {F} {G} {l}

Σ-congᵛ : ∀ {Γ : Con Term n} {F G H E l p q m} → _
Σ-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} {p} {q} {m} =
  W-congᵛ {Γ = Γ} {F} {G} {H} {E} {l} (BΣ m p q)
