------------------------------------------------------------------------
-- Irrelevance lemmata for the logical relation
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Substitution.Irrelevance
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.LogicalRelation R
import Definition.LogicalRelation.Irrelevance R as LR
open import Definition.LogicalRelation.Substitution R

open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    A A₁ A₂ A′ B₁ B₂ C t u : Term _
    σ : Subst m n
    l l′ : TypeLevel
    ⊩Γ ⊩Γ′ : ⊩ᵛ _

-- Irrelevance of valid substitutions with different derivations of contexts
irrelevanceSubst : ∀ {Γ Δ}
                   ([Γ] [Γ]′ : ⊩ᵛ Γ)
                   (⊢Δ ⊢Δ′ : ⊢ Δ)
                 → Δ ⊩ˢ σ ∷ Γ / [Γ]  / ⊢Δ
                 → Δ ⊩ˢ σ ∷ Γ / [Γ]′ / ⊢Δ′
irrelevanceSubst ε ε ⊢Δ ⊢Δ′ [σ] = lift tt
irrelevanceSubst ([Γ] ∙ [A]) ([Γ]′ ∙ [A]′) ⊢Δ ⊢Δ′ ([tailσ] , [headσ]) =
  let [tailσ]′ = irrelevanceSubst [Γ] [Γ]′ ⊢Δ ⊢Δ′ [tailσ]
  in  [tailσ]′
  ,   LR.irrelevanceTerm (proj₁ (unwrap [A] ⊢Δ [tailσ]))
                         (proj₁ (unwrap [A]′ ⊢Δ′ [tailσ]′))
                         [headσ]

-- Irrelevance of valid substitutions with different contexts
-- that are propositionally equal
irrelevanceSubst′ : ∀ {Γ Δ Δ′}
                    (eq : Δ PE.≡ Δ′)
                    ([Γ] [Γ]′ : ⊩ᵛ Γ)
                    (⊢Δ  : ⊢ Δ)
                    (⊢Δ′ : ⊢ Δ′)
                  → Δ  ⊩ˢ σ ∷ Γ / [Γ]  / ⊢Δ
                  → Δ′ ⊩ˢ σ ∷ Γ / [Γ]′ / ⊢Δ′
irrelevanceSubst′ PE.refl [Γ] [Γ]′ ⊢Δ ⊢Δ′ [σ] = irrelevanceSubst [Γ] [Γ]′ ⊢Δ ⊢Δ′ [σ]

-- Irrelevance of valid substitution equality
-- with different derivations of contexts
irrelevanceSubstEq : ∀ {σ′ Γ Δ}
                     ([Γ] [Γ]′ : ⊩ᵛ Γ)
                     (⊢Δ ⊢Δ′ : ⊢ Δ)
                     ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ]  / ⊢Δ)
                     ([σ]′ : Δ ⊩ˢ σ ∷ Γ / [Γ]′ / ⊢Δ′)
                   → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ]  / ⊢Δ  / [σ]
                   → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ]′ / ⊢Δ′ / [σ]′
irrelevanceSubstEq ε ε ⊢Δ ⊢Δ′ [σ] [σ]′ [σ≡σ′] = lift tt
irrelevanceSubstEq ([Γ] ∙ [A]) ([Γ]′ ∙ [A]′) ⊢Δ ⊢Δ′ [σ] [σ]′ [σ≡σ′] =
  irrelevanceSubstEq [Γ] [Γ]′ ⊢Δ ⊢Δ′ (proj₁ [σ]) (proj₁ [σ]′) (proj₁ [σ≡σ′])
  , LR.irrelevanceEqTerm (proj₁ (unwrap [A] ⊢Δ  (proj₁ [σ])))
                            (proj₁ (unwrap [A]′ ⊢Δ′ (proj₁ [σ]′)))
                            (proj₂ [σ≡σ′])

-- Irrelevance of valid types with different derivations of contexts
irrelevance : ∀ {l A}
              ([Γ] [Γ]′ : ⊩ᵛ Γ)
            → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
            → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]′
irrelevance [Γ] [Γ]′ [A] = wrap λ ⊢Δ [σ] →
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
  in  proj₁ (unwrap [A] ⊢Δ [σ]′)
   ,  λ [σ′] [σ≡σ′] → proj₂ (unwrap [A] ⊢Δ [σ]′)
                       (irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′])
                       (irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ] [σ]′ [σ≡σ′])

open import Definition.LogicalRelation.Properties R

-- Irrelevance of valid types with different derivations of contexts
-- with lifting of eqaul types
irrelevanceLift : ∀ {l A F H}
              ([Γ] : ⊩ᵛ Γ)
              ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
              ([H] : Γ ⊩ᵛ⟨ l ⟩ H / [Γ])
              ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H / [Γ] / [F])
            → Γ ∙ F ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [F]
            → Γ ∙ H ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [H]
irrelevanceLift [Γ] [F] [H] [F≡H] [A] = wrap λ { ⊢Δ ([tailσ] , [headσ]) →
  let [σ]′ = [tailσ] , convTerm₂ (proj₁ (unwrap [F] ⊢Δ [tailσ]))
                                 (proj₁ (unwrap [H] ⊢Δ [tailσ]))
                                 ([F≡H] ⊢Δ [tailσ]) [headσ]
  in  proj₁ (unwrap [A] ⊢Δ [σ]′)
  ,   (λ [σ′] x →
         let [σ′]′ = proj₁ [σ′] , convTerm₂ (proj₁ (unwrap [F] ⊢Δ (proj₁ [σ′])))
                                            (proj₁ (unwrap [H] ⊢Δ (proj₁ [σ′])))
                                            ([F≡H] ⊢Δ (proj₁ [σ′]))
                                            (proj₂ [σ′])
             [tailσ′] = proj₁ [σ′]
         in  proj₂ (unwrap [A] ⊢Δ [σ]′) [σ′]′
                   (proj₁ x , convEqTerm₂ (proj₁ (unwrap [F] ⊢Δ [tailσ]))
                                          (proj₁ (unwrap [H] ⊢Δ [tailσ]))
                                          ([F≡H] ⊢Δ [tailσ])
                                          (proj₂ x)))}

opaque

  -- A variant of irrelevanceLift.

  irrelevanceLift₂ :
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ}
    {⊩B₁ : Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ / ⊩Γ ∙ ⊩A₁}
    {⊩B₂ : Γ ∙ A₂ ⊩ᵛ⟨ l ⟩ B₂ / ⊩Γ ∙ ⊩A₂} →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩A₁ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ / ⊩Γ ∙ ⊩A₁ / ⊩B₁ →
    Γ ∙ A₁ ∙ B₁ ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A₁ ∙ ⊩B₁ →
    Γ ∙ A₂ ∙ B₂ ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A₂ ∙ ⊩B₂
  irrelevanceLift₂ {⊩A₁} {⊩A₂} {⊩B₁} {⊩B₂} ⊩A₁≡A₂ ⊩B₁≡B₂ ⊩C =
    wrap λ _ ((⊩σ , ⊩t) , ⊩u) →
    let ⊩C[σ,t,u]₁ , ⊩C[σ,t,u]₂ =
          ⊩C .unwrap _
            ( ( ⊩σ
              , convTerm₂ (⊩A₁ .unwrap _ _ .proj₁)
                  (⊩A₂ .unwrap _ _ .proj₁) (⊩A₁≡A₂ _ _) ⊩t
              )
            , convTerm₂ (⊩B₁ .unwrap _ _ .proj₁)
                (⊩B₂ .unwrap _ _ .proj₁) (⊩B₁≡B₂ _ _) ⊩u
            )
    in
      ⊩C[σ,t,u]₁
    , λ ((⊩σ′ , ⊩t′) , ⊩u′) ((⊩σ≡σ′ , ⊩t≡t′) , ⊩u≡u′) →
        ⊩C[σ,t,u]₂
          ( ( ⊩σ′
            , convTerm₂ (⊩A₁ .unwrap _ _ .proj₁)
                (⊩A₂ .unwrap _ _ .proj₁) (⊩A₁≡A₂ _ _) ⊩t′
            )
          , convTerm₂ (⊩B₁ .unwrap _ _ .proj₁)
              (⊩B₂ .unwrap _ _ .proj₁) (⊩B₁≡B₂ _ _) ⊩u′
          )
          ( ( ⊩σ≡σ′
            , convEqTerm₂ (⊩A₁ .unwrap _ _ .proj₁)
                (⊩A₂ .unwrap _ _ .proj₁) (⊩A₁≡A₂ _ _) ⊩t≡t′
            )
          , convEqTerm₂ (⊩B₁ .unwrap _ _ .proj₁)
              (⊩B₂ .unwrap _ _ .proj₁) (⊩B₁≡B₂ _ _) ⊩u≡u′
          )

-- Irrelevance of valid type equality with different derivations of
-- contexts and types
irrelevanceEq : ∀ {l l′ A B}
                ([Γ] [Γ]′ : ⊩ᵛ Γ)
                ([A]  : Γ ⊩ᵛ⟨ l  ⟩ A / [Γ])
                ([A]′ : Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]′)
              → Γ ⊩ᵛ⟨ l  ⟩ A ≡ B / [Γ]  / [A]
              → Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B / [Γ]′ / [A]′
irrelevanceEq [Γ] [Γ]′ [A] [A]′ [A≡B] ⊢Δ [σ] =
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
  in  LR.irrelevanceEq (proj₁ (unwrap [A] ⊢Δ [σ]′))
                       (proj₁ (unwrap [A]′ ⊢Δ [σ]))
                       ([A≡B] ⊢Δ [σ]′)

-- Irrelevance of valid terms with different derivations of contexts and types
irrelevanceTerm : ∀ {l l′ A t}
                  ([Γ] [Γ]′ : ⊩ᵛ Γ)
                  ([A]  : Γ ⊩ᵛ⟨ l  ⟩ A / [Γ])
                  ([A]′ : Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]′)
                → Γ ⊩ᵛ⟨ l  ⟩ t ∷ A / [Γ]  / [A]
                → Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A / [Γ]′ / [A]′
irrelevanceTerm [Γ] [Γ]′ [A] [A]′ [t] ⊢Δ [σ]′ =
  let [σ]   = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]′
      [σA]  = proj₁ (unwrap [A] ⊢Δ [σ])
      [σA]′ = proj₁ (unwrap [A]′ ⊢Δ [σ]′)
  in  LR.irrelevanceTerm [σA] [σA]′ (proj₁ ([t] ⊢Δ [σ]))
   ,  (λ [σ′] x → LR.irrelevanceEqTerm [σA] [σA]′ ((proj₂ ([t] ⊢Δ [σ]))
                    (irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′])
                    (irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]′ [σ] x)))

-- Irrelevance of valid terms with different derivations of
-- contexts and types which are propositionally equal
irrelevanceTerm′ : ∀ {l l′ A A′ t}
                   (eq : A PE.≡ A′)
                   ([Γ] [Γ]′ : ⊩ᵛ Γ)
                   ([A]  : Γ ⊩ᵛ⟨ l  ⟩ A / [Γ])
                   ([A′] : Γ ⊩ᵛ⟨ l′ ⟩ A′ / [Γ]′)
                 → Γ ⊩ᵛ⟨ l  ⟩ t ∷ A / [Γ]  / [A]
                 → Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A′ / [Γ]′ / [A′]
irrelevanceTerm′ {A = A} {t = t} PE.refl [Γ] [Γ]′ [A] [A]′ [t] =
  irrelevanceTerm {A = A} {t = t} [Γ] [Γ]′ [A] [A]′ [t]

-- Irrelevance of valid terms with different derivations of
-- contexts and types with a lifting of equal types
irrelevanceTermLift : ∀ {l A F H t}
              ([Γ] : ⊩ᵛ Γ)
              ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
              ([H] : Γ ⊩ᵛ⟨ l ⟩ H / [Γ])
              ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H / [Γ] / [F])
              ([A] : Γ ∙ F ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [F])
            → Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] ∙ [F] / [A]
            → Γ ∙ H ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] ∙ [H]
                           / irrelevanceLift {A = A} {F = F} {H = H}
                                             [Γ] [F] [H] [F≡H] [A]
irrelevanceTermLift [Γ] [F] [H] [F≡H] [A] [t] ⊢Δ ([tailσ] , [headσ]) =
  let [σ]′ = [tailσ] , convTerm₂ (proj₁ (unwrap [F] ⊢Δ [tailσ]))
                                 (proj₁ (unwrap [H] ⊢Δ [tailσ]))
                                 ([F≡H] ⊢Δ [tailσ]) [headσ]
  in  proj₁ ([t] ⊢Δ [σ]′)
  , (λ [σ′] x →
       let [σ′]′ = proj₁ [σ′] , convTerm₂ (proj₁ (unwrap [F] ⊢Δ (proj₁ [σ′])))
                                          (proj₁ (unwrap [H] ⊢Δ (proj₁ [σ′])))
                                          ([F≡H] ⊢Δ (proj₁ [σ′]))
                                          (proj₂ [σ′])
           [tailσ′] = proj₁ [σ′]
       in  proj₂ ([t] ⊢Δ [σ]′) [σ′]′
                 (proj₁ x , convEqTerm₂ (proj₁ (unwrap [F] ⊢Δ [tailσ]))
                                        (proj₁ (unwrap [H] ⊢Δ [tailσ]))
                                        ([F≡H] ⊢Δ [tailσ])
                                        (proj₂ x)))

-- Irrelevance of valid term equality with different derivations of
-- contexts and types
irrelevanceEqTerm : ∀ {l l′ A t u}
                  ([Γ] [Γ]′ : ⊩ᵛ Γ)
                  ([A]  : Γ ⊩ᵛ⟨ l  ⟩ A / [Γ])
                  ([A]′ : Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]′)
                → Γ ⊩ᵛ⟨ l  ⟩ t ≡ u ∷ A / [Γ]  / [A]
                → Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A / [Γ]′ / [A]′
irrelevanceEqTerm {A = A} {t = t} {u = u} [Γ] [Γ]′ [A] [A]′ [t≡u] ⊢Δ [σ] =
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
  in  LR.irrelevanceEqTerm (proj₁ (unwrap [A] ⊢Δ [σ]′))
                           (proj₁ (unwrap [A]′ ⊢Δ [σ]))
                           ([t≡u] ⊢Δ [σ]′)

opaque

  -- A variant of irrelevanceEqTerm.

  irrelevanceEqTerm′ :
    ∀ t u →
    A PE.≡ A′ →
    (⊩A  : Γ ⊩ᵛ⟨ l  ⟩ A / ⊩Γ)
    (⊩A′ : Γ ⊩ᵛ⟨ l′ ⟩ A′ / ⊩Γ′) →
    Γ ⊩ᵛ⟨ l  ⟩ t ≡ u ∷ A / ⊩Γ  / ⊩A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A′ / ⊩Γ′ / ⊩A′
  irrelevanceEqTerm′ t u PE.refl =
    irrelevanceEqTerm {t = t} {u = u} _ _
