------------------------------------------------------------------------
-- Validity of some two-variable substitutions.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Substitution.Introductions.DoubleSubst
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U
  hiding (_∷_) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Substitution.Irrelevance R as IS
open import Definition.LogicalRelation.Substitution.Introductions.Nat R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R
open import Definition.LogicalRelation.Substitution.Introductions.Prod R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Weakening R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n   : Nat
    Γ   : Con Term n
    p q : M
    F G A B B₁ B₂ C C₁ C₂ t t₁ t₂ u u₁ u₂ : Term n
    l : TypeLevel
    ⊩Γ : ⊩ᵛ _

opaque

  -- If C, t and u are valid, then C [ t , u ]₁₀ is valid.

  substD :
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A}
    (⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A)
    (⊩B[t] : Γ ⊩ᵛ⟨ l ⟩ B [ t ]₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ t ]₀ / ⊩Γ / ⊩B[t] →
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A ∙ ⊩B →
    Γ ⊩ᵛ⟨ l ⟩ C [ t , u ]₁₀ / ⊩Γ
  substD {B = B} {C = C} {⊩B = ⊩B} ⊩t ⊩B[t] ⊩u ⊩C = wrap λ _ ⊩σ →
    let ⊩C[σ,t,u]₁ , ⊩C[σ,t,u]₂ =
          ⊩C .unwrap
            _
            ( (⊩σ , ⊩t _ _ .proj₁)
            , irrelevanceTerm′
                (PE.sym (substConsId B))
                (⊩B[t] .unwrap _ _ .proj₁)
                (⊩B .unwrap _ _ .proj₁)
                (⊩u _ ⊩σ .proj₁)
            )
    in
    case irrelevance′ (PE.sym ([,]-[]-fusion C)) ⊩C[σ,t,u]₁ of λ {
      ⊩C[t,u][σ] →
      ⊩C[t,u][σ]
    , λ {_} ⊩σ′ ⊩σ≡σ′ →
        irrelevanceEq″
          (PE.sym ([,]-[]-fusion C))
          (PE.sym ([,]-[]-fusion C))
          ⊩C[σ,t,u]₁
          ⊩C[t,u][σ]
          (⊩C[σ,t,u]₂
             ( (⊩σ′ , ⊩t _ _ .proj₁)
             , irrelevanceTerm′
                 (PE.sym (substConsId B))
                 (⊩B[t] .unwrap _ _ .proj₁)
                 (⊩B .unwrap _ _ .proj₁)
                 (⊩u _ ⊩σ′ .proj₁)
             )
             ( (⊩σ≡σ′ , ⊩t _ _ .proj₂ ⊩σ′ ⊩σ≡σ′)
             , irrelevanceEqTerm′
                 (PE.sym (substConsId B))
                 (⊩B[t] .unwrap _ _ .proj₁)
                 (⊩B .unwrap _ _ .proj₁)
                 (⊩u _ _ .proj₂ ⊩σ′ ⊩σ≡σ′)
             )) }

opaque

  -- A variant of substD for equality.

  substDEq :
    {A₁ A₂ : Term n}
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ}
    {⊩B₁ : Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ / ⊩Γ ∙ ⊩A₁}
    {⊩B₂ : Γ ∙ A₂ ⊩ᵛ⟨ l ⟩ B₂ / ⊩Γ ∙ ⊩A₂}
    {⊩t₁ : Γ ⊩ᵛ⟨ l ⟩ t₁ ∷ A₁ / ⊩Γ / ⊩A₁}
    {⊩B₁[t₁] : Γ ⊩ᵛ⟨ l ⟩ B₁ [ t₁ ]₀ / ⊩Γ}
    {⊩u₁ : Γ ⊩ᵛ⟨ l ⟩ u₁ ∷ B₁ [ t₁ ]₀ / ⊩Γ / ⊩B₁[t₁]}
    {⊩C₁ : Γ ∙ A₁ ∙ B₁ ⊩ᵛ⟨ l ⟩ C₁ / ⊩Γ ∙ ⊩A₁ ∙ ⊩B₁} →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩A₁ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ / ⊩Γ ∙ ⊩A₁ / ⊩B₁ →
    (⊩t₂ : Γ ⊩ᵛ⟨ l ⟩ t₂ ∷ A₂ / ⊩Γ / ⊩A₂) →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    (⊩B₂[t₂] : Γ ⊩ᵛ⟨ l ⟩ B₂ [ t₂ ]₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ u₂ ∷ B₂ [ t₂ ]₀ / ⊩Γ / ⊩B₂[t₂] →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ≡ u₂ ∷ B₁ [ t₁ ]₀ / ⊩Γ / ⊩B₁[t₁] →
    (⊩C₁[t₁,u₁] : Γ ⊩ᵛ⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ / ⊩Γ) →
    Γ ∙ A₂ ∙ B₂ ⊩ᵛ⟨ l ⟩ C₂ / ⊩Γ ∙ ⊩A₂ ∙ ⊩B₂ →
    Γ ∙ A₁ ∙ B₁ ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ / ⊩Γ ∙ ⊩A₁ ∙ ⊩B₁ / ⊩C₁ →
    Γ ⊩ᵛ⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ ≡ C₂ [ t₂ , u₂ ]₁₀ / ⊩Γ / ⊩C₁[t₁,u₁]
  substDEq
    {B₁ = B₁} {B₂ = B₂} {C₁ = C₁} {C₂ = C₂}
    {⊩A₁ = ⊩A₁} {⊩A₂ = ⊩A₂} {⊩B₁ = ⊩B₁} {⊩B₂ = ⊩B₂} {⊩t₁ = ⊩t₁}
    {⊩B₁[t₁] = ⊩B₁[t₁]} {⊩u₁ = ⊩u₁} {⊩C₁ = ⊩C₁}
    ⊩A₁≡A₂ ⊩B₁≡B₂ ⊩t₂ ⊩t₁≡t₂ ⊩B₂[t₂] ⊩u₂ ⊩u₁≡u₂ ⊩C₁[t₁,u₁] ⊩C₂ ⊩C₁≡C₂
    _ ⊩σ =
    let ⊩C₁[σ,t₁,u₁]₁ , ⊩C₁[σ,t₁,u₁]₂ =
          ⊩C₁ .unwrap _
            ( (⊩σ , ⊩t₁ _ _ .proj₁)
            , irrelevanceTerm′
                (PE.sym (substConsId B₁))
                (⊩B₁[t₁] .unwrap _ _ .proj₁)
                (⊩B₁ .unwrap _ _ .proj₁)
                (⊩u₁ _ ⊩σ .proj₁)
            )
    in
    case convTerm₂
           (⊩A₁ .unwrap _ ⊩σ .proj₁)
           (⊩A₂ .unwrap _ ⊩σ .proj₁)
           (⊩A₁≡A₂ _ _)
           (⊩t₂ _ _ .proj₁) of λ {
      ⊩t₂[σ] →
    case convTerm₂′
           (PE.sym (substConsId B₂))
           (⊩B₁ .unwrap _ _ .proj₁)
           (⊩B₂[t₂] .unwrap _ _ .proj₁)
           (⊩B₁≡B₂ _ (_ , ⊩t₂[σ]))
           (⊩u₂ _ ⊩σ .proj₁) of λ {
      ⊩u₂[σ] →
    irrelevanceEq″
       (PE.sym ([,]-[]-fusion C₁))
       (PE.sym ([,]-[]-fusion C₂))
       ⊩C₁[σ,t₁,u₁]₁
       (⊩C₁[t₁,u₁] .unwrap _ _ .proj₁) $
    transEq
       ⊩C₁[σ,t₁,u₁]₁
       (⊩C₁ .unwrap _ (_ , ⊩u₂[σ]) .proj₁)
       (⊩C₂ .unwrap _
          ( (⊩σ , ⊩t₂ _ _ .proj₁)
          , irrelevanceTerm′
              (PE.sym (substConsId B₂))
              (⊩B₂[t₂] .unwrap _ _ .proj₁)
              (⊩B₂ .unwrap _ _ .proj₁)
              (⊩u₂ _ ⊩σ .proj₁)
          ) .proj₁)
       (⊩C₁[σ,t₁,u₁]₂
          (_ , ⊩u₂[σ])
          ( (reflSubst _ _ ⊩σ , ⊩t₁≡t₂ _ _)
          , irrelevanceEqTerm′
              (PE.sym (substConsId B₁))
              (⊩B₁[t₁] .unwrap _ _ .proj₁)
              (⊩B₁ .unwrap _ _ .proj₁)
              (⊩u₁≡u₂ _ ⊩σ)
          ))
       (⊩C₁≡C₂ _ _) }}

private
  [suc] : ∀ {l}
        → ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
        → Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ suc (var x1) ∷ ℕ / [Γ] ∙ ℕᵛ [Γ] ∙ [F] / ℕᵛ ([Γ] ∙ ℕᵛ [Γ] ∙ [F])
  [suc] {l = l} [Γ] [F] {σ = σ} ⊢Δ [σ] =
    let [ℕ] = ℕᵛ [Γ]
        [ΓℕF] = [Γ] ∙ [ℕ] ∙ [F]
        [ℕ]′ = ℕᵛ {l = l} [ΓℕF]
        [x1] = varᵛ (there here) [ΓℕF] [ℕ]′
    in  sucᵛ {n = var x1} [ΓℕF] [ℕ]′ (λ {_} {_} {σ₁} ⊢Δ₁ [σ]₁ → [x1] {σ = σ₁} ⊢Δ₁ [σ]₁) {σ = σ} ⊢Δ [σ]

  [prod] : ∀ {l m}
         → ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
           ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ])
           ([A] : Γ ∙ (Σ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ]) →
           Σ-allowed m p q →
           Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ prod m p (var x1) (var x0) ∷ wk1 (wk1 (Σ⟨ m ⟩ p , q ▷ F ▹ G))
                           / [Γ] ∙ [F] ∙ [G] / wk1ᵛ ([Γ] ∙ [F]) [G] (wk1ᵛ [Γ] [F] [Σ])
  [prod] {n} {Γ} {F} {G} {p} {q} {A} {l} {m} [Γ] [F] [G] [Σ] [A] ok =
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
        [x1] = varᵛ (there here) [ΓFG] wk[F]
        [x0]′ = varᵛ here [ΓFG] (wk1ᵛ [ΓF] [G] [G])
        wk[G[x1]] = substS [ΓFG] wk[F] wk[G] [x1]
        [x0] = IS.irrelevanceTerm′ (PE.sym (wkSingleSubstWk1 G)) [ΓFG] [ΓFG]
                                   (wk1ᵛ [ΓF] [G] [G]) wk[G[x1]] [x0]′
        [prod]′ = prodᵛ {F = wk1 (wk1 F)} {U.wk (lift (step (step id))) G} {var x1} {var x0}
                        [ΓFG] wk[F] wk[G] [x1] [x0] ok
        wk[Σ] = wk1ᵛ [ΓF] [G] (wk1ᵛ [Γ] [F] [Σ])
        wk[Σ]′ = Σᵛ [ΓFG] wk[F] wk[G] ok
    in  IS.irrelevanceTerm′ {t = prod _ _ (var x1) (var x0)}
                            (wk2-B BΣ! F G) [ΓFG] [ΓFG] wk[Σ]′ wk[Σ] [prod]′

subst↑²S :
  ∀ {l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
  ([B] : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / [Γ] ∙ [A])
  ([t] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ t ∷ wk1 (wk1 A) / [Γ] ∙ [F] ∙ [G] / wk1ᵛ ([Γ] ∙ [F]) [G] (wk1ᵛ [Γ] [F] [A])) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ B [ t ]↑² / [Γ] ∙ [F] ∙ [G]
subst↑²S {A = A} {B = B} {t = t} [Γ] [F] [G] [A] [B] [t] = wrap λ {k} {Δ} {σ} ⊢Δ [σ]@(([σ₋] , [σ₁]) , [σ₀]) →
  let [wk2A] = wk1ᵛ ([Γ] ∙ [F]) [G] (wk1ᵛ [Γ] [F] [A])
      [σwk2A] = proj₁ (unwrap [wk2A] {σ = σ} ⊢Δ [σ])
      [σ₋A] = proj₁ (unwrap [A] {σ = tail (tail σ)} ⊢Δ [σ₋])
      [σt]′ = proj₁ ([t] {σ = σ} ⊢Δ [σ])
      [σt] = irrelevanceTerm′ (wk2-tail A) [σwk2A] [σ₋A] [σt]′
      σ₊ = consSubst (tail (tail σ)) (t [ σ ])
      [σ₊] = [σ₋] , [σt]
      [σB]′ = proj₁ (unwrap [B] {σ = σ₊} ⊢Δ [σ₊])
      [σB] = irrelevance′ (substComp↑² B t) [σB]′
  in  [σB] , λ {σ′} [σ′]@(([σ′₋] , [σ′₁]) , [σ′₀]) [σ≡σ′]@(([σ₋≡σ′₋] , _) , _) →
    let [σ′wk2A] = proj₁ (unwrap [wk2A] {σ = σ′} ⊢Δ [σ′])
        [σ′₋A] = proj₁ (unwrap [A] {σ = tail (tail σ′)} ⊢Δ [σ′₋])
        [σ′t]′ = proj₁ ([t] {σ = σ′} ⊢Δ [σ′])
        [σ′t] = irrelevanceTerm′ (wk2-tail A) [σ′wk2A] [σ′₋A] [σ′t]′
        σ′₊ = consSubst (tail (tail σ′)) (t [ σ′ ])
        [σ′₊] = [σ′₋] , [σ′t]
        [σt≡σ′t]′ = proj₂ ([t] {σ = σ} ⊢Δ [σ])
                          {σ′ = σ′} [σ′] [σ≡σ′]
        [σt≡σ′t] = irrelevanceEqTerm′ (wk2-tail A) [σwk2A] [σ₋A] [σt≡σ′t]′
        [σB≡σ′B] = proj₂ (unwrap [B] {σ = σ₊} ⊢Δ [σ₊])
                         {σ′ = σ′₊} [σ′₊] ([σ₋≡σ′₋] , [σt≡σ′t])
    in  irrelevanceEq″ (substComp↑² B t) (substComp↑² B t) [σB]′ [σB] [σB≡σ′B]

opaque
  unfolding wk1ᵛ

  subst↑²S-suc :
    ∀ {Γ : Con Term n} {F l}
    ([Γ] : ⊩ᵛ Γ)
    ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ])) →
    Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ F [ suc (var x1) ]↑² / [Γ] ∙ ℕᵛ [Γ] ∙ [F]
  subst↑²S-suc {n} {Γ} {F} {l} [Γ] [F] =
    let [ℕ] = ℕᵛ [Γ]
    in  subst↑²S {t = suc (var x1)} [Γ] [ℕ] [F] [ℕ] [F] (λ {_} {_} {σ} → [suc] [Γ] [F] {σ = σ})

opaque
  unfolding wk1ᵛ

  subst↑²S-suc′ :
    ∀ {Γ : Con Term n} {F G l}
    ([Γ] : ⊩ᵛ Γ)
    ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ])) →
    ([G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ])) →
    Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ G [ suc (var x1) ]↑² / [Γ] ∙ ℕᵛ [Γ] ∙ [F]
  subst↑²S-suc′ {n} {Γ} {F} {l} [Γ] [F] [G] =
    let [ℕ] = ℕᵛ [Γ]
    in  subst↑²S {t = suc (var x1)} [Γ] [ℕ] [F] [ℕ] [G] (λ {_} {_} {σ} → [suc] [Γ] [F] {σ = σ})


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

subst↑²SEq :
  ∀ {l} {Γ : Con Term n}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
  ([B] : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / [Γ] ∙ [A])
  ([C] : Γ ∙ A ⊩ᵛ⟨ l ⟩ C / [Γ] ∙ [A])
  ([B≡C] : Γ ∙ A ⊩ᵛ⟨ l ⟩ B ≡ C / [Γ] ∙ [A] / [B])
  ([t] : (Γ ∙ F ∙ G) ⊩ᵛ⟨ l ⟩ t ∷ wk1 (wk1 A) / [Γ] ∙ [F] ∙ [G] / wk1ᵛ ([Γ] ∙ [F]) [G] (wk1ᵛ [Γ] [F] [A])) →
  Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ B [ t ]↑² ≡ C [ t ]↑² / [Γ] ∙ [F] ∙ [G] / subst↑²S [Γ] [F] [G] [A] [B] [t]
subst↑²SEq {Γ} {F} {G} {A} {B} {C} {t} [Γ] [F] [G] [A] [B] [C] [B≡C] [t] {k} {Δ} {σ} ⊢Δ [σ]@(([σ₋] , [σ₁]) , [σ₀]) =
  let [wk2A] = wk1ᵛ ([Γ] ∙ [F]) [G] (wk1ᵛ [Γ] [F] [A])
      [σwk2A] = proj₁ (unwrap [wk2A] {σ = σ} ⊢Δ [σ])
      [σ₋A] = proj₁ (unwrap [A] {σ = tail (tail σ)} ⊢Δ [σ₋])
      [σt]′ = proj₁ ([t] {σ = σ} ⊢Δ [σ])
      [σt] = irrelevanceTerm′ (wk2-tail A) [σwk2A] [σ₋A] [σt]′
      σ₊ = consSubst (tail (tail σ)) (t [ σ ])
      [σ₊] = [σ₋] , [σt]
      [σB] = proj₁ (unwrap [B] {σ = σ₊} ⊢Δ [σ₊])
      [B↑²] = subst↑²S [Γ] [F] [G] [A] [B] [t]
      [σB↑²] = proj₁ (unwrap [B↑²] ⊢Δ [σ])
      [σB≡σC] = [B≡C] {σ = σ₊} ⊢Δ [σ₊]
  in  irrelevanceEq″ (substComp↑² B t) (substComp↑² C t) [σB] [σB↑²] [σB≡σC]

opaque
  unfolding subst↑²S-suc

  subst↑²SEq-suc : ∀ {Γ : Con Term n} {F l}
    ([Γ] : ⊩ᵛ Γ)
    ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
    ([G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
    ([F≡G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) / [F]) →
    Γ ∙ ℕ ∙ F ⊩ᵛ⟨ l ⟩ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑² / [Γ] ∙ ℕᵛ [Γ] ∙ [F] / subst↑²S-suc [Γ] [F]
  subst↑²SEq-suc {l = l} [Γ] [F] [G] [F≡G] =
    let [ℕ] = ℕᵛ [Γ]
    in  subst↑²SEq [Γ] [ℕ] [F] [ℕ] [F] [G] [F≡G] (λ {_} {_} {σ} → [suc] [Γ] [F] {σ = σ})

opaque
  unfolding subst↑²S-suc′

  subst↑²SEq-suc′ : ∀ {Γ : Con Term n} {F l}
    ([Γ] : ⊩ᵛ Γ)
    ([F] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
    ([G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ]))
    ([F≡G] : Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ F ≡ G / _∙_ {l = l} [Γ] (ℕᵛ [Γ]) / [F]) →
    Γ ∙ ℕ ∙ G ⊩ᵛ⟨ l ⟩ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑² / [Γ] ∙ ℕᵛ [Γ] ∙ [G] / subst↑²S-suc′ [Γ] [G] [F]
  subst↑²SEq-suc′ {l = l} [Γ] [F] [G] [F≡G] =
    let [ℕ] = ℕᵛ [Γ]
    in  subst↑²SEq [Γ] [ℕ] [G] [ℕ] [F] [G] [F≡G] (λ {_} {_} {σ} → [suc] [Γ] [G] {σ = σ})

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


subst↑²STerm :
  ∀ {F G A t t′ u m l} →
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  ([Σ] : Γ ⊩ᵛ⟨ l ⟩ Σ⟨ m ⟩ p , q ▷ F ▹ G / [Γ])
  ([A] : Γ ∙ (Σ p , q ▷ F ▹ G) ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Σ])
  ([A₊] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ A [ prod m p (var x1) (var x0) ]↑² /
            [Γ] ∙ [F] ∙ [G])
  ([Ap] : Γ ⊩ᵛ⟨ l ⟩ A [ prod m p t t′ ]₀ / [Γ])
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
  ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ G [ t ]₀ / [Γ] / substS [Γ] [F] [G] [t])
  ([u] : Γ ∙ F ∙ G ⊩ᵛ⟨ l ⟩ u ∷ A [ prod m p (var x1) (var x0) ]↑² /
           [Γ] ∙ [F] ∙ [G] / [A₊]) →
  Γ ⊩ᵛ⟨ l ⟩ u [ consSubst (consSubst idSubst t) t′ ] ∷
    A [ prod m p t t′ ]₀ / [Γ] / [Ap]
subst↑²STerm {Γ = Γ} {F = F} {G} {A} {t} {t′} {u}
             [Γ] [F] [G] [Σ] [A] [A₊] [Ap] [t] [t′] [u]
             {k} {Δ} {σ} ⊢Δ [σ] =
  let [ΓF] = _∙_ {A = F} [Γ] [F]
      [ΓFG] = _∙_ {A = G} [ΓF] [G]
      [Gt] = substS {F = F} {G} {t} [Γ] [F] [G] [t]
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σGt] = proj₁ (unwrap [G] {σ = consSubst σ (t [ σ ])} ⊢Δ ([σ] , [σt]))
      [σt′]′ = proj₁ ([t′] ⊢Δ [σ])
      [σGt]′ = proj₁ (unwrap [Gt] ⊢Δ [σ])
      [σt′] = irrelevanceTerm′ (PE.trans (substCompEq G) (substVar-to-subst (λ{x0 → PE.refl; (x +1) → PE.refl}) G))
                               [σGt]′ [σGt] [σt′]′
      σ₊ = consSubst (consSubst σ (t [ σ ])) (t′ [ σ ])
      [σ₊] : Δ ⊩ˢ σ₊ ∷ Γ ∙ F ∙ G / [ΓFG] / ⊢Δ
      [σ₊] = ([σ] , [σt]) , [σt′]
      [σ₊u] = proj₁ ([u] {σ = σ₊} ⊢Δ [σ₊])
      [σAp] = proj₁ (unwrap [Ap] ⊢Δ [σ])
      [σ₊A₊] = proj₁ (unwrap [A₊] {σ = σ₊} ⊢Δ [σ₊])
      [σ₊u]′ = irrelevanceTerm″ (PE.sym (PE.trans (singleSubstLift A (prod! t t′))
                                                  (substCompProdrec A (t [ σ ]) (t′ [ σ ]) σ)))
                                (substEq σ)
                                [σ₊A₊] [σAp] [σ₊u]
  in  [σ₊u]′ , λ {σ′} [σ′] [σ≡σ′] →
    let [σ′t] = proj₁ ([t] ⊢Δ [σ′])
        [σ′t′]′ = proj₁ ([t′] ⊢Δ [σ′])
        [σ′Gt] = proj₁ (unwrap [G] {σ = consSubst σ′ (t [ σ′ ])} ⊢Δ ([σ′] , [σ′t]))
        [σ′Gt]′ = proj₁ (unwrap [Gt] ⊢Δ [σ′])
        [σ′t′] = irrelevanceTerm′ (PE.trans (singleSubstLift G t) (singleSubstComp (t [ σ′ ]) σ′ G))
                                  [σ′Gt]′ [σ′Gt] [σ′t′]′
        σ′₊ = consSubst (consSubst σ′ (t [ σ′ ])) (t′ [ σ′ ])
        [σ′₊] : Δ ⊩ˢ σ′₊ ∷ Γ ∙ F ∙ G / [ΓFG] / ⊢Δ
        [σ′₊] = ([σ′] , [σ′t]) , [σ′t′]
        [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        [σt′≡σ′t′]′ = proj₂ ([t′] ⊢Δ [σ]) [σ′] [σ≡σ′]
        [σt′≡σ′t′] = irrelevanceEqTerm′ (PE.trans (singleSubstLift G t) (singleSubstComp (t [ σ ]) σ G))
                                        [σGt]′ [σGt] [σt′≡σ′t′]′
        [σ₊≡σ′₊] = ([σ≡σ′] , [σt≡σ′t]) , [σt′≡σ′t′]
        [σ₊u≡σ′₊u] = proj₂ ([u] {σ = σ₊} ⊢Δ [σ₊])
                           {σ′ = σ′₊} [σ′₊] [σ₊≡σ′₊]
    in  irrelevanceEqTerm″ (substEq σ) (substEq σ′)
                           (PE.sym (PE.trans (singleSubstLift A (prod! t t′))
                                             (substCompProdrec A (t [ σ ]) (t′ [ σ ]) σ)))
                           [σ₊A₊] [σAp] [σ₊u≡σ′₊u]
    where
    substEq : (σ : Subst k _) → u [ consSubst (consSubst σ (t [ σ ])) (t′ [ σ ]) ]
                           PE.≡ (u [ consSubst (sgSubst t) t′ ]) [ σ ]
    substEq σ = PE.trans (substVar-to-subst (λ{x0 → PE.refl; (x0 +1) → PE.refl; (x +1 +1) → PE.refl}) u)
                         (PE.sym (substCompEq u))
