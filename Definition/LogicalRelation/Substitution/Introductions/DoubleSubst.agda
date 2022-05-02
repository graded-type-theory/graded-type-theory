{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Introductions.DoubleSubst {a ℓ} (M′ : Setoid a ℓ)
                                                                         {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M as U hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.Properties M′
open import Definition.LogicalRelation.Substitution M′
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst M′
open import Definition.LogicalRelation.Substitution.Introductions.Prod M′
open import Definition.LogicalRelation.Substitution.Introductions.Pi M′
open import Definition.LogicalRelation.Substitution.Weakening M′

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    q : M


subst↑²S : ∀ {F G A m l}
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
          ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ q ▷ F ▹ G / [Γ])
          ([A] : Γ ∙ (Σ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
        → Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G]
subst↑²S {n} {Γ} {q} {F} {G} {A} {m} {l} [Γ] [F] [G] [Σ] [A] {k} {Δ} {σ} ⊢Δ [σ]@(([σ₋] , [σ₁]) , [σ₀]) =
  let [σF] = proj₁ ([F] ⊢Δ [σ₋])
      ⊢σF = escape [σF]
      [ΓF] = _∙_ {A = F} [Γ] [F]
      [ΓFG] = _∙_ {A = G} [ΓF] [G]
      σ₊ = consSubst (tail (tail σ)) (subst σ (prod (var (x0 +1)) (var x0)))

      wk1[F] = wk1ᵛ {A = F} {F = F} [Γ] [F] [F]
      wk2[F] = wk1ᵛ {A = wk1 F} {F = G} [ΓF] [G] wk1[F]
      wk[G] : Γ ∙ F ∙ G ∙ wk1 (wk1 F) ⊩ᵛ⟨ l ⟩ U.wk (lift (step (step id))) G / [Γ] ∙ [F] ∙ [G] ∙ wk2[F]
      wk[G] = λ {_} {Δ} {σ} ⊢Δ [σ] →
        let [tail] = proj₁ (proj₁ (proj₁ [σ]))
            [σF] = proj₁ ([F] ⊢Δ [tail])
            wk2[σF] = proj₁ (wk2[F] ⊢Δ (proj₁ [σ]))
            [head] = proj₂ [σ]
            [head]′ = irrelevanceTerm′ (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)) wk2[σF] [σF] [head]
            [ρσ] : Δ ⊩ˢ consSubst (tail (tail (tail σ))) (head σ) ∷ Γ ∙ F / [ΓF] / ⊢Δ
            [ρσ] = [tail] , [head]′
            [ρσG] = proj₁ ([G] {σ = consSubst (tail (tail (tail σ))) (head σ)} ⊢Δ [ρσ])
            [ρσG]′ = irrelevance′ (PE.sym (PE.trans (subst-wk G)
                                                    (substVar-to-subst (λ {x0 → PE.refl; (x +1) → PE.refl}) G)))
                                  [ρσG]
        in  [ρσG]′ , λ {σ′} [σ′] [σ≡σ′] →
          let [tail′] = proj₁ (proj₁ (proj₁ [σ′]))
              [head′] = proj₂ [σ′]
              [σ′F] = proj₁ ([F] ⊢Δ [tail′])
              wk2[σ′F] = proj₁ (wk2[F] ⊢Δ (proj₁ [σ′]))
              [head′]′ = irrelevanceTerm′ (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)) wk2[σ′F] [σ′F] [head′]
              [ρσ′] : Δ ⊩ˢ consSubst (tail (tail (tail σ′))) (head σ′) ∷ Γ ∙ F / [ΓF] / ⊢Δ
              [ρσ′] = [tail′] , [head′]′
              [tail≡] = proj₁ (proj₁ (proj₁ [σ≡σ′]))
              [head≡] = proj₂ [σ≡σ′]
              [head≡]′ = irrelevanceEqTerm′ (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)) wk2[σF] [σF] [head≡]
              [ρσ≡] : Δ ⊩ˢ consSubst (tail (tail (tail σ))) (head σ)
                         ≡ consSubst (tail (tail (tail σ′))) (head σ′) ∷ Γ ∙ F / [ΓF] / ⊢Δ / [ρσ]
              [ρσ≡] = [tail≡] , [head≡]′
              [ρσG≡] = proj₂ ([G] {σ = consSubst (tail (tail (tail σ))) (head σ)} ⊢Δ [ρσ])
                             {σ′ = consSubst (tail (tail (tail σ′))) (head σ′)} [ρσ′] [ρσ≡]
          in  irrelevanceEq″ (PE.sym (PE.trans (subst-wk G) (substVar-to-subst (λ { x0 → PE.refl ; (x +1) → PE.refl }) G)))
                             (PE.sym (PE.trans (subst-wk G) (substVar-to-subst (λ { x0 → PE.refl ; (x +1) → PE.refl }) G)))
                             [ρσG] [ρσG]′ [ρσG≡]
      [x1] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ var (x0 +1) ∷ wk1 (wk1 F) / [ΓFG] / wk2[F]
      [x1] = λ ⊢Δ [σ] →
        let σx₁ = proj₂ (proj₁ [σ])
            σwk2[F] = proj₁ (wk2[F] ⊢Δ [σ])
            [σF] = proj₁ ([F] ⊢Δ (proj₁ (proj₁ [σ])))
        in irrelevanceTerm′ (PE.sym (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)))
                            [σF] σwk2[F] σx₁
           , λ [σ′] [σ≡σ′] →
          let σx₁≡σ′x₁ = proj₂ (proj₁ [σ≡σ′])
          in  irrelevanceEqTerm′ (PE.sym (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)))
                                 [σF] σwk2[F] σx₁≡σ′x₁
      [G[x1]] = substS {F = wk1 (wk1 F)} {U.wk (lift (step (step id))) G} {var (x0 +1)} [ΓFG] wk2[F] wk[G] [x1]
      [x0] : (Γ ∙ F ∙ G) ⊩ᵛ⟨ l ⟩ var x0 ∷ U.wk (lift (step (step id))) G [ var (x0 +1) ] / [ΓFG] / [G[x1]]
      [x0] = λ ⊢Δ [σ] →
        let σx₀ = proj₂ [σ]
            [σG[x1]] = proj₁ ([G[x1]] ⊢Δ [σ])
            [σG] = proj₁ ([G] ⊢Δ (proj₁ [σ]))
        in  irrelevanceTerm′ (PE.sym (PE.trans (substCompEq (U.wk (lift (step (step id))) G))
                                               (PE.trans (subst-wk G)
                                                         (substVar-to-subst (λ {x0 → PE.refl; (x +1) → PE.refl}) G))))
                             [σG] [σG[x1]] σx₀ ,
            λ [σ′] [σ≡σ′] → irrelevanceEqTerm′ (PE.sym (PE.trans (substCompEq (U.wk (lift (step (step id))) G))
                                                                 (PE.trans (subst-wk G)
                                                                           (substVar-to-subst (λ {x0 → PE.refl; (x +1) → PE.refl}) G))))
                                               [σG] [σG[x1]] (proj₂ [σ≡σ′])

      [x1x0] = prodᵛ {m = m} {q = q} {F = wk1 (wk1 F)} {U.wk (lift (step (step id))) G} {var (x0 +1)} {var x0} [ΓFG] wk2[F] wk[G] [x1] [x0]
      [σx1x0] = proj₁ ([x1x0] {σ = σ} ⊢Δ [σ])
      wk[Σ] = Σᵛ {F = wk1 (wk1 F)} {U.wk (lift (step (step id))) G} [ΓFG] wk2[F] wk[G]
      σwk[Σ] = proj₁ (wk[Σ] {σ = σ} ⊢Δ [σ])
      [σΣ] = proj₁ ([Σ] ⊢Δ [σ₋])
      [σx1x0]′ = irrelevanceTerm′ (PE.cong₂ (λ F G → Σ q ▷ F ▹ G)
                                            (PE.trans (wk1-tail (wk1 F)) (wk1-tail F))
                                            (PE.trans (subst-wk G) (substVar-to-subst (λ { x0 → PE.refl; (x +1) → PE.refl}) G)))
                                  σwk[Σ] [σΣ] [σx1x0]
      [σ₊] : Δ ⊩ˢ σ₊ ∷ Γ ∙ (Σ q ▷ F ▹ G) / [Γ] ∙ [Σ] / ⊢Δ
      [σ₊] = [σ₋] , [σx1x0]′
      [σ₊A] = proj₁ ([A] {σ = σ₊} ⊢Δ [σ₊])
      [σ₊A]′ = irrelevance′ (PE.trans (substVar-to-subst (substeq σ) A) (PE.sym (substCompEq A))) [σ₊A]
  in  [σ₊A]′ , λ {σ′} [σ′] [σ≡σ′] →
    let σ′₊ = consSubst (tail (tail σ′)) (subst σ′ (prod (var (x0 +1)) (var x0)))
        [σ′₋] = proj₁ (proj₁ [σ′])
        σ′wk[Σ] = proj₁ (wk[Σ] {σ = σ′} ⊢Δ [σ′])
        [σ′Σ] = proj₁ ([Σ] ⊢Δ [σ′₋])
        [σ′x1x0] = proj₁ ([x1x0] {σ = σ′} ⊢Δ [σ′])
        [σ′x1x0]′ = irrelevanceTerm′ (PE.cong₂ (λ F G → Σ q ▷ F ▹ G)
                                               (PE.trans (wk1-tail (wk1 F)) (wk1-tail F))
                                               (PE.trans (subst-wk G) (substVar-to-subst (λ{ x0 → PE.refl; (x +1) → PE.refl }) G)))
                                     σ′wk[Σ] [σ′Σ] [σ′x1x0]
        [σ′₊] : Δ ⊩ˢ σ′₊ ∷ Γ ∙ (Σ q ▷ F ▹ G) / [Γ] ∙ [Σ] / ⊢Δ
        [σ′₊] = [σ′₋] , [σ′x1x0]′
        [σp≡σ′p] = proj₂ ([x1x0] {σ = σ} ⊢Δ [σ])
                         {σ′ = σ′} [σ′] [σ≡σ′]
        [σp≡σ′p]′ = irrelevanceEqTerm′ (PE.cong₂ (λ F G → Σ q ▷ F ▹ G)
                                                 (PE.trans (wk1-tail (wk1 F)) (wk1-tail F))
                                                 (PE.trans (subst-wk G) (substVar-to-subst (λ{ x0 → PE.refl; (x +1) → PE.refl }) G)))
                                       σwk[Σ] [σΣ] [σp≡σ′p]
        [σ₊A≡σ′₊A] = proj₂ ([A] {σ = σ₊} ⊢Δ [σ₊])
                           {σ′ = σ′₊} [σ′₊] (proj₁ (proj₁ [σ≡σ′]) , [σp≡σ′p]′)
    in  irrelevanceEq″ (PE.trans (substVar-to-subst (substeq σ) A) (PE.sym (substCompEq A)))
                       (PE.trans (substVar-to-subst (substeq σ′) A) (PE.sym (substCompEq A)))
                       [σ₊A] [σ₊A]′ [σ₊A≡σ′₊A]
  where
  substeq : (σ : Subst k (1+ (1+ n))) (x : Fin (1+ n))
          → consSubst (tail (tail σ)) (subst σ (prod (var (x0 +1)) (var x0))) x
          PE.≡ (σ ₛ•ₛ (consSubst (wk1Subst (wk1Subst idSubst)) (prod (var (x0 +1)) (var x0)))) x
  substeq σ x0 = PE.refl
  substeq σ (x +1) = PE.refl


subst↑²SEq : ∀ {F G A A′ m l}
           → ([Γ] : ⊩ᵛ Γ)
             ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
             ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ q ▷ F ▹ G / [Γ])
             ([A] : Γ ∙ (Σ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
             ([A′] : Γ ∙ (Σ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A′ / [Γ] ∙ [Σ])
             ([A≡A′] : Γ ∙ (Σ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A ≡ A′ / [Γ] ∙ [Σ] / [A])
             ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
           → Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod (var (x0 +1)) (var x0) ]↑² ≡ A′ [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊]
subst↑²SEq {n} {Γ} {q} {F} {G} {A} {A′} {m} {l} [Γ] [F] [G] [Σ] [A] [A′] [A≡A′] [A₊] {k} {Δ} {σ} ⊢Δ [σ]@(([σ₋] , [σ₁]) , [σ₀]) =
  let [σF] = proj₁ ([F] ⊢Δ [σ₋])
      ⊢σF = escape [σF]
      [ΓF] = _∙_ {A = F} [Γ] [F]
      [ΓFG] = _∙_ {A = G} [ΓF] [G]
      σ₊ = consSubst (tail (tail σ)) (subst σ (prod (var (x0 +1)) (var x0)))

      wk1[F] = wk1ᵛ {A = F} {F = F} [Γ] [F] [F]
      wk2[F] = wk1ᵛ {A = wk1 F} {F = G} [ΓF] [G] wk1[F]
      wk[G] : Γ ∙ F ∙ G ∙ wk1 (wk1 F) ⊩ᵛ⟨ l ⟩ U.wk (lift (step (step id))) G / [Γ] ∙ [F] ∙ [G] ∙ wk2[F]
      wk[G] = λ {_} {Δ} {σ} ⊢Δ [σ] →
        let [tail] = proj₁ (proj₁ (proj₁ [σ]))
            [σF] = proj₁ ([F] ⊢Δ [tail])
            wk2[σF] = proj₁ (wk2[F] ⊢Δ (proj₁ [σ]))
            [head] = proj₂ [σ]
            [head]′ = irrelevanceTerm′ (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)) wk2[σF] [σF] [head]
            [ρσ] : Δ ⊩ˢ consSubst (tail (tail (tail σ))) (head σ) ∷ Γ ∙ F / [ΓF] / ⊢Δ
            [ρσ] = [tail] , [head]′
            [ρσG] = proj₁ ([G] {σ = consSubst (tail (tail (tail σ))) (head σ)} ⊢Δ [ρσ])
            [ρσG]′ = irrelevance′ (PE.sym (PE.trans (subst-wk G)
                                                    (substVar-to-subst (λ {x0 → PE.refl; (x +1) → PE.refl}) G)))
                                  [ρσG]
        in  [ρσG]′ , λ {σ′} [σ′] [σ≡σ′] →
          let [tail′] = proj₁ (proj₁ (proj₁ [σ′]))
              [head′] = proj₂ [σ′]
              [σ′F] = proj₁ ([F] ⊢Δ [tail′])
              wk2[σ′F] = proj₁ (wk2[F] ⊢Δ (proj₁ [σ′]))
              [head′]′ = irrelevanceTerm′ (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)) wk2[σ′F] [σ′F] [head′]
              [ρσ′] : Δ ⊩ˢ consSubst (tail (tail (tail σ′))) (head σ′) ∷ Γ ∙ F / [ΓF] / ⊢Δ
              [ρσ′] = [tail′] , [head′]′
              [tail≡] = proj₁ (proj₁ (proj₁ [σ≡σ′]))
              [head≡] = proj₂ [σ≡σ′]
              [head≡]′ = irrelevanceEqTerm′ (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)) wk2[σF] [σF] [head≡]
              [ρσ≡] : Δ ⊩ˢ consSubst (tail (tail (tail σ))) (head σ)
                         ≡ consSubst (tail (tail (tail σ′))) (head σ′) ∷ Γ ∙ F / [ΓF] / ⊢Δ / [ρσ]
              [ρσ≡] = [tail≡] , [head≡]′
              [ρσG≡] = proj₂ ([G] {σ = consSubst (tail (tail (tail σ))) (head σ)} ⊢Δ [ρσ])
                             {σ′ = consSubst (tail (tail (tail σ′))) (head σ′)} [ρσ′] [ρσ≡]
          in  irrelevanceEq″ (PE.sym (PE.trans (subst-wk G) (substVar-to-subst (λ { x0 → PE.refl ; (x +1) → PE.refl }) G)))
                             (PE.sym (PE.trans (subst-wk G) (substVar-to-subst (λ { x0 → PE.refl ; (x +1) → PE.refl }) G)))
                             [ρσG] [ρσG]′ [ρσG≡]
      [x1] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ var (x0 +1) ∷ wk1 (wk1 F) / [ΓFG] / wk2[F]
      [x1] = λ ⊢Δ [σ] →
        let σx₁ = proj₂ (proj₁ [σ])
            σwk2[F] = proj₁ (wk2[F] ⊢Δ [σ])
            [σF] = proj₁ ([F] ⊢Δ (proj₁ (proj₁ [σ])))
        in irrelevanceTerm′ (PE.sym (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)))
                            [σF] σwk2[F] σx₁
           , λ [σ′] [σ≡σ′] →
          let σx₁≡σ′x₁ = proj₂ (proj₁ [σ≡σ′])
          in  irrelevanceEqTerm′ (PE.sym (PE.trans (wk1-tail (wk1 F)) (wk1-tail F)))
                                 [σF] σwk2[F] σx₁≡σ′x₁
      [G[x1]] = substS {F = wk1 (wk1 F)} {U.wk (lift (step (step id))) G} {var (x0 +1)} [ΓFG] wk2[F] wk[G] [x1]
      [x0] : (Γ ∙ F ∙ G) ⊩ᵛ⟨ l ⟩ var x0 ∷ U.wk (lift (step (step id))) G [ var (x0 +1) ] / [ΓFG] / [G[x1]]
      [x0] = λ ⊢Δ [σ] →
        let σx₀ = proj₂ [σ]
            [σG[x1]] = proj₁ ([G[x1]] ⊢Δ [σ])
            [σG] = proj₁ ([G] ⊢Δ (proj₁ [σ]))
        in  irrelevanceTerm′ (PE.sym (PE.trans (substCompEq (U.wk (lift (step (step id))) G))
                                               (PE.trans (subst-wk G)
                                                         (substVar-to-subst (λ {x0 → PE.refl; (x +1) → PE.refl}) G))))
                             [σG] [σG[x1]] σx₀ ,
            λ [σ′] [σ≡σ′] → irrelevanceEqTerm′ (PE.sym (PE.trans (substCompEq (U.wk (lift (step (step id))) G))
                                                                 (PE.trans (subst-wk G)
                                                                           (substVar-to-subst (λ {x0 → PE.refl; (x +1) → PE.refl}) G))))
                                               [σG] [σG[x1]] (proj₂ [σ≡σ′])

      [x1x0] = prodᵛ {m = m} {q = q} {F = wk1 (wk1 F)} {U.wk (lift (step (step id))) G} {var (x0 +1)} {var x0} [ΓFG] wk2[F] wk[G] [x1] [x0]
      [σx1x0] = proj₁ ([x1x0] {σ = σ} ⊢Δ [σ])
      wk[Σ] = Σᵛ {F = wk1 (wk1 F)} {U.wk (lift (step (step id))) G} [ΓFG] wk2[F] wk[G]
      σwk[Σ] = proj₁ (wk[Σ] {σ = σ} ⊢Δ [σ])
      [σΣ] = proj₁ ([Σ] ⊢Δ [σ₋])
      [σx1x0]′ = irrelevanceTerm′ (PE.cong₂ (λ F G → Σ q ▷ F ▹ G)
                                            (PE.trans (wk1-tail (wk1 F)) (wk1-tail F))
                                            (PE.trans (subst-wk G) (substVar-to-subst (λ { x0 → PE.refl; (x +1) → PE.refl}) G)))
                                  σwk[Σ] [σΣ] [σx1x0]
      [σ₊] : Δ ⊩ˢ σ₊ ∷ Γ ∙ (Σ q ▷ F ▹ G) / [Γ] ∙ [Σ] / ⊢Δ
      [σ₊] = [σ₋] , [σx1x0]′
      σ₊[A≡A′] = [A≡A′] {σ = σ₊} ⊢Δ [σ₊]
      [σA₊] = proj₁ ([A₊] ⊢Δ [σ])
      [σ₊A] = proj₁ ([A] {σ = σ₊} ⊢Δ [σ₊])
  in  irrelevanceEq″ (PE.sym (PE.trans (substCompEq A) (substVar-to-subst (λ{ x0 → PE.refl; (x +1) → PE.refl}) A)))
                     (PE.sym (PE.trans (substCompEq A′) (substVar-to-subst (λ{ x0 → PE.refl; (x +1) → PE.refl}) A′)))
                     [σ₊A] [σA₊] σ₊[A≡A′]


subst↑²STerm : ∀ {F G A t t′ u m l}
             → ([Γ] : ⊩ᵛ Γ)
               ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
               ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
               ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ q ▷ F ▹ G / [Γ])
               ([A] : Γ ∙ (Σ q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
               ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G])
               ([Ap] : Γ ⊩ᵛ⟨ l ⟩ A [ prod t t′ ] / [Γ])
               ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
               ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ G [ t ] / [Γ] / substS {F = F} {G} {t} [Γ] [F] [G] [t])
               ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prod (var (x0 +1)) (var x0) ]↑² / [Γ] ∙ [F] ∙ [G] / [A₊])
             → Γ ⊩ᵛ⟨ l ⟩ subst (consSubst (consSubst idSubst t) t′) u ∷ A [ prod t t′ ] / [Γ] / [Ap]
subst↑²STerm {Γ = Γ} {F = F} {G} {A} {t} {t′} {u}
             [Γ] [F] [G] [Σ] [A] [A₊] [Ap] [t] [t′] [u]
             {k} {Δ} {σ} ⊢Δ [σ] =
  let [ΓF] = _∙_ {A = F} [Γ] [F]
      [ΓFG] = _∙_ {A = G} [ΓF] [G]
      [Gt] = substS  {F = F} {G} {t} [Γ] [F] [G] [t]
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σGt] = proj₁ ([G] {σ = consSubst σ (subst σ t)} ⊢Δ ([σ] , [σt]))
      [σt′]′ = proj₁ ([t′] ⊢Δ [σ])
      [σGt]′ = proj₁ ([Gt] ⊢Δ [σ])
      [σt′] = irrelevanceTerm′ (PE.trans (substCompEq G) (substVar-to-subst (λ{x0 → PE.refl; (x +1) → PE.refl}) G))
                               [σGt]′ [σGt] [σt′]′
      σ₊ = consSubst (consSubst σ (subst σ t)) (subst σ t′)
      [σ₊] : Δ ⊩ˢ σ₊ ∷ Γ ∙ F ∙ G / [ΓFG] / ⊢Δ
      [σ₊] = ([σ] , [σt]) , [σt′]
      [σ₊u] = proj₁ ([u] {σ = σ₊} ⊢Δ [σ₊])
      [σAp] = proj₁ ([Ap] ⊢Δ [σ])
      [σ₊A₊] = proj₁ ([A₊] ⊢Δ [σ₊])
      [σ₊u]′ = irrelevanceTerm″ (PE.sym (PE.trans (singleSubstLift A (prod t t′)) (substCompProdrec A (subst σ t) (subst σ t′) σ)))
                                (substEq σ)
                                [σ₊A₊] [σAp] [σ₊u]
  in  [σ₊u]′ , λ {σ′} [σ′] [σ≡σ′] →
    let [σ′t] = proj₁ ([t] ⊢Δ [σ′])
        [σ′t′]′ = proj₁ ([t′] ⊢Δ [σ′])
        [σ′Gt] = proj₁ ([G] {σ = consSubst σ′ (subst σ′ t)} ⊢Δ ([σ′] , [σ′t]))
        [σ′Gt]′ = proj₁ ([Gt] ⊢Δ [σ′])
        [σ′t′] = irrelevanceTerm′ (PE.trans (singleSubstLift G t) (singleSubstComp (subst σ′ t) σ′ G))
                                  [σ′Gt]′ [σ′Gt] [σ′t′]′
        σ′₊ = consSubst (consSubst σ′ (subst σ′ t)) (subst σ′ t′)
        [σ′₊] : Δ ⊩ˢ σ′₊ ∷ Γ ∙ F ∙ G / [ΓFG] / ⊢Δ
        [σ′₊] = ([σ′] , [σ′t]) , [σ′t′]
        [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        [σt′≡σ′t′]′ = proj₂ ([t′] ⊢Δ [σ]) [σ′] [σ≡σ′]
        [σt′≡σ′t′] = irrelevanceEqTerm′ (PE.trans (singleSubstLift G t) (singleSubstComp (subst σ t) σ G))
                                        [σGt]′ [σGt] [σt′≡σ′t′]′
        [σ₊≡σ′₊] = ([σ≡σ′] , [σt≡σ′t]) , [σt′≡σ′t′]
        [σ₊u≡σ′₊u] = proj₂ ([u] {σ = σ₊} ⊢Δ [σ₊])
                           {σ′ = σ′₊} [σ′₊] [σ₊≡σ′₊]
    in  irrelevanceEqTerm″ (substEq σ)
                           (substEq σ′)
                           (PE.sym (PE.trans (singleSubstLift A (prod t t′)) (substCompProdrec A (subst σ t) (subst σ t′) σ)))
                           [σ₊A₊] [σAp] [σ₊u≡σ′₊u]
    where
    substEq : (σ : Subst k _) → subst ((consSubst (consSubst σ (subst σ t))) (subst σ t′)) u
                              PE.≡ subst σ (subst (consSubst (consSubst idSubst t) t′) u)
    substEq σ = PE.trans (substVar-to-subst (λ{x0 → PE.refl; (x0 +1) → PE.refl; (x +1 +1) → PE.refl}) u)
                         (PE.sym (substCompEq u))
