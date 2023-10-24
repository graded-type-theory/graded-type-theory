------------------------------------------------------------------------
-- Lemmata on valid substitutions
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Substitution.Properties
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
  hiding (_∷_) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Irrelevance R
     using (irrelevanceSubst′)
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
import Definition.LogicalRelation.Weakening R as LR

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Unit
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private
  variable
    k m n : Nat
    A A₁ A₂ B B₁ B₂ C C₁ C₂ t t₁ t₂ u u₁ u₂ : Term _
    Γ Δ : Con Term n
    σ σ₁ σ₂ σ′ : Subst m n
    ρ : Wk k n
    l : TypeLevel
    ⊢Δ : ⊢ _
    ⊩Γ : ⊩ᵛ _

-- Valid substitutions are well-formed
wellformedSubst : ∀ {Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
      → Δ ⊢ˢ σ ∷ Γ
wellformedSubst ε ⊢Δ [σ] = id
wellformedSubst ([Γ] ∙ [A]) ⊢Δ ([tailσ] , [headσ]) =
  wellformedSubst [Γ] ⊢Δ [tailσ]
  , escapeTerm (proj₁ (unwrap [A] ⊢Δ [tailσ])) [headσ]

-- Valid substitution equality is well-formed
wellformedSubstEq : ∀ {Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
      ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ
wellformedSubstEq ε ⊢Δ [σ] [σ≡σ′] = id
wellformedSubstEq ([Γ] ∙ [A]) ⊢Δ ([tailσ] , [headσ]) ([tailσ≡σ′] , [headσ≡σ′]) =
  wellformedSubstEq [Γ] ⊢Δ [tailσ] [tailσ≡σ′]
  , ≅ₜ-eq (escapeTermEq (proj₁ (unwrap [A] ⊢Δ [tailσ])) [headσ≡σ′])

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→⊢[]≡[] :
    {⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ} →
    Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ →
    Δ ⊩ˢ σ₂ ∷ Γ / ⊩Γ / ⊢Δ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁ →
    Δ ⊢ A [ σ₁ ] ≡ A [ σ₂ ]
  ⊩ᵛ→⊢[]≡[] {⊩σ₁} ⊩A ⊩σ₂ ⊩σ₁≡σ₂ =
    ≅-eq $ escapeEq (⊩A .unwrap _ ⊩σ₁ .proj₁) $
    ⊩A .unwrap _ ⊩σ₁ .proj₂ ⊩σ₂ ⊩σ₁≡σ₂

-- Extend a valid substitution with a term
consSubstS : ∀ {l t A Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
           ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
           ([t] : Δ ⊩⟨ l ⟩ t ∷ A [ σ ] / proj₁ (unwrap [A] ⊢Δ [σ]))
         → Δ ⊩ˢ consSubst σ t ∷ Γ ∙ A / [Γ] ∙ [A] / ⊢Δ
consSubstS [Γ] ⊢Δ [σ] [A] [t] = [σ] , [t]

-- Extend a valid substitution equality with a term
consSubstSEq : ∀ {l t A Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             ([σ]    : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
             ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
             ([t] : Δ ⊩⟨ l ⟩ t ∷ A [ σ ] / proj₁ (unwrap [A] ⊢Δ [σ]))
           → Δ ⊩ˢ consSubst σ t ≡ consSubst σ′ t ∷ Γ ∙ A / [Γ] ∙ [A] / ⊢Δ
               / consSubstS {t = t} {A = A} [Γ] ⊢Δ [σ] [A] [t]
consSubstSEq [Γ] ⊢Δ [σ] [σ≡σ′] [A] [t] =
  [σ≡σ′] , reflEqTerm (proj₁ (unwrap [A] ⊢Δ [σ])) [t]

-- Weakening of valid substitutions
wkSubstS : ∀ {Γ Δ Δ′} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
           ([ρ] : ρ ∷ Δ′ ⊇ Δ)
           ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
         → Δ′ ⊩ˢ ρ •ₛ σ ∷ Γ / [Γ] / ⊢Δ′
wkSubstS ε ⊢Δ ⊢Δ′ ρ [σ] = lift tt
wkSubstS {σ = σ} {Γ = Γ ∙ A} ([Γ] ∙ x) ⊢Δ ⊢Δ′ ρ [σ] =
  let [tailσ] = wkSubstS [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ])
  in  [tailσ]
   ,  irrelevanceTerm′ (wk-subst A)
        (LR.wk ρ ⊢Δ′ (proj₁ (unwrap x ⊢Δ (proj₁ [σ]))))
        (proj₁ (unwrap x ⊢Δ′ [tailσ]))
        (LR.wkTerm ρ ⊢Δ′ (proj₁ (unwrap x ⊢Δ (proj₁ [σ]))) (proj₂ [σ]))

-- Weakening of valid substitution equality
wkSubstSEq : ∀ {Γ Δ Δ′} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
             ([ρ] : ρ ∷ Δ′ ⊇ Δ)
             ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
           → Δ′ ⊩ˢ ρ •ₛ σ ≡ ρ •ₛ σ′ ∷ Γ / [Γ]
                / ⊢Δ′ / wkSubstS [Γ] ⊢Δ ⊢Δ′ [ρ] [σ]
wkSubstSEq ε ⊢Δ ⊢Δ′ ρ [σ] [σ≡σ′] = lift tt
wkSubstSEq {Γ = Γ ∙ A} ([Γ] ∙ x) ⊢Δ ⊢Δ′ ρ [σ] [σ≡σ′] =
  wkSubstSEq [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ]) (proj₁ [σ≡σ′])
  , irrelevanceEqTerm′ (wk-subst A) (LR.wk ρ ⊢Δ′ (proj₁ (unwrap x ⊢Δ (proj₁ [σ]))))
                            (proj₁ (unwrap x ⊢Δ′ (wkSubstS [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ]))))
                            (LR.wkEqTerm ρ ⊢Δ′ (proj₁ (unwrap x ⊢Δ (proj₁ [σ]))) (proj₂ [σ≡σ′]))

-- Weaken a valid substitution by one type
wk1SubstS : ∀ {F Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → (Δ ∙ F) ⊩ˢ wk1Subst σ ∷ Γ / [Γ]
                            / (⊢Δ ∙ ⊢F)
wk1SubstS [Γ] ⊢Δ ⊢F [σ] =
  wkSubstS [Γ] ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ]

-- Weaken a valid substitution equality by one type
wk1SubstSEq : ∀ {F Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
              (⊢F : Δ ⊢ F)
              ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
              ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
            → (Δ ∙ F) ⊩ˢ wk1Subst σ ≡ wk1Subst σ′ ∷ Γ / [Γ]
                            / (⊢Δ ∙ ⊢F) / wk1SubstS [Γ] ⊢Δ ⊢F [σ]
wk1SubstSEq [Γ] ⊢Δ ⊢F [σ] [σ≡σ′] =
  wkSubstSEq [Γ] ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ] [σ≡σ′]

-- Lift a valid substitution
liftSubstS : ∀ {l F Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → (Δ ∙ F [ σ ]) ⊩ˢ liftSubst σ ∷ Γ ∙ F / [Γ] ∙ [F]
                             / (⊢Δ ∙ escape (proj₁ (unwrap [F] ⊢Δ [σ])))
liftSubstS {σ = σ} {F = F} {Δ = Δ} [Γ] ⊢Δ [F] [σ] =
  let ⊢F = escape (proj₁ (unwrap [F] ⊢Δ [σ]))
      [tailσ] = wk1SubstS {F = F [ σ ]} [Γ] ⊢Δ (escape (proj₁ (unwrap [F] ⊢Δ [σ]))) [σ]
      var0 = var (⊢Δ ∙ ⊢F) (PE.subst (λ x → x0 ∷ x ∈ Δ ∙ F [ σ ])
                                     (wk-subst F) here)
  in  [tailσ] , neuTerm (proj₁ (unwrap [F] (⊢Δ ∙ ⊢F) [tailσ])) (var x0)
                        var0 (~-var var0)

opaque

  -- A variant of liftSubstS.

  liftSubstS′ :
    {σ₁ σ₂ : Subst m n}
    {⊢Δ : ⊢ Δ}
    {⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ}
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ)
    (⊩σ₂ : Δ ⊩ˢ σ₂ ∷ Γ / ⊩Γ / ⊢Δ) →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁ →
    Δ ∙ A [ σ₁ ] ⊩ˢ liftSubst σ₂ ∷ Γ ∙ A / ⊩Γ ∙ ⊩A /
      ⊢Δ ∙ escape (⊩A .unwrap ⊢Δ ⊩σ₁ .proj₁)
  liftSubstS′ {A} {σ₁} {⊢Δ} {⊩σ₁} ⊩A ⊩σ₂ ⊩σ₁≡σ₂ =
    case wk1SubstS _ _ _ ⊩σ₂ of λ {
      ⊩wk1Subst-σ₂ →
    case conv (var (⊢Δ ∙ escape (⊩A .unwrap _ ⊩σ₁ .proj₁)) here)
           (PE.subst
              (_ ∙ A [ σ₁ ] ⊢_≡ _)
              (wk1Subst-wk1 A)
              (⊩ᵛ→⊢[]≡[] ⊩A ⊩wk1Subst-σ₂
                 (wk1SubstSEq _ _ _ _ ⊩σ₁≡σ₂))) of λ {
      ⊢0 →
      ⊩wk1Subst-σ₂
    , neuTerm
        (⊩A .unwrap _ ⊩wk1Subst-σ₂ .proj₁)
        (var x0)
        ⊢0
        (~-var ⊢0) }}

-- Lift a valid substitution equality
liftSubstSEq : ∀ {l F Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
           → (Δ ∙ F [ σ ]) ⊩ˢ liftSubst σ ≡ liftSubst σ′ ∷ Γ ∙ F / [Γ] ∙ [F]
                             / (⊢Δ ∙ escape (proj₁ (unwrap [F] ⊢Δ [σ])))
                             / liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
liftSubstSEq {σ = σ} {σ′ = σ′} {F = F} {Δ = Δ} [Γ] ⊢Δ [F] [σ] [σ≡σ′] =
  let ⊢F = escape (proj₁ (unwrap [F] ⊢Δ [σ]))
      [tailσ] = wk1SubstS {F = F [ σ ]} [Γ] ⊢Δ (escape (proj₁ (unwrap [F] ⊢Δ [σ]))) [σ]
      [tailσ≡σ′] = wk1SubstSEq [Γ] ⊢Δ (escape (proj₁ (unwrap [F] ⊢Δ [σ]))) [σ] [σ≡σ′]
      var0 = var (⊢Δ ∙ ⊢F) (PE.subst (λ x → x0 ∷ x ∈ (Δ ∙ F [ σ ])) (wk-subst F) here)
  in  [tailσ≡σ′] , neuEqTerm (proj₁ (unwrap [F] (⊢Δ ∙ ⊢F) [tailσ])) (var x0) (var x0)
                         var0 var0 (~-var var0)

opaque

  -- Another variant of liftSubstS.

  liftSubstS″ :
    {σ₁ σ₂ : Subst m n}
    {⊢Δ : ⊢ Δ}
    {⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    (⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A)
    (⊩σ₂ : Δ ⊩ˢ σ₂ ∷ Γ / ⊩Γ / ⊢Δ) →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁ →
    let ⊢A = escape (⊩A .unwrap _ ⊩σ₁ .proj₁)
        ⊢B = escape (⊩B .unwrap _ (liftSubstS _ _ ⊩A ⊩σ₁) .proj₁)
    in
    Δ ∙ A [ σ₁ ] ∙ B [ liftSubst σ₁ ] ⊩ˢ liftSubstn σ₂ 2 ∷ Γ ∙ A ∙ B /
      ⊩Γ ∙ ⊩A ∙ ⊩B / ⊢Δ ∙ ⊢A ∙ ⊢B
  liftSubstS″ {A} {B} {σ₁} {σ₂} {⊢Δ} {⊩σ₁} {⊩A} ⊩B ⊩σ₂ ⊩σ₁≡σ₂ =
    case escape (⊩A .unwrap _ ⊩σ₁ .proj₁) of λ {
      ⊢A[σ₁] →
    case escape (⊩B .unwrap _ (liftSubstS _ _ ⊩A ⊩σ₁) .proj₁) of λ {
      ⊢B[⇑σ₁] →
    case wk1SubstS _ _ _ (wk1SubstS _ _ _ ⊩σ₂) of λ {
      ⊩wk2Subst-σ₂ →
    case conv (var (⊢Δ ∙ ⊢A[σ₁] ∙ ⊢B[⇑σ₁]) (there here))
           (PE.subst
              (_ ∙ A [ _ ] ∙ _ ⊢_≡ _)
              (A [ wk1Subst (wk1Subst σ₁) ]  ≡⟨ wk1Subst-wk1 A ⟩
               wk1 (A [ wk1Subst σ₁ ])       ≡⟨ PE.cong wk1 (wk1Subst-wk1 A) ⟩
               wk1 (wk1 (A [ σ₁ ]))          ∎) $
            ⊩ᵛ→⊢[]≡[] ⊩A
              (wk1SubstS _ _ ⊢B[⇑σ₁] (wk1SubstS _ _ ⊢A[σ₁] ⊩σ₂))
              (wk1SubstSEq _ _ _ _ (wk1SubstSEq _ _ _ _ ⊩σ₁≡σ₂))) of λ {
      ⊢1 →
    case conv (var (⊢Δ ∙ ⊢A[σ₁] ∙ ⊢B[⇑σ₁]) here)
           (PE.subst
              (_ ∙ _ ∙ B [ _ ] ⊢_≡ _)
              (wk1Subst-wk1 B)
              (⊩ᵛ→⊢[]≡[]
                 {⊩σ₁ = wk1SubstS {σ = liftSubst σ₁}
                          (_ ∙ ⊩A) _ _ (liftSubstS _ _ ⊩A ⊩σ₁)}
                 ⊩B
                 (wk1SubstS {σ = liftSubst σ₂} (_ ∙ ⊩A) _ ⊢B[⇑σ₁] $
                  liftSubstS′ ⊩A ⊩σ₂ ⊩σ₁≡σ₂)
                 (wk1SubstSEq {σ = liftSubst σ₁} {σ′ = liftSubst σ₂}
                    (_ ∙ ⊩A) _ _ (liftSubstS _ _ ⊩A ⊩σ₁) $
                  liftSubstSEq _ _ ⊩A _ ⊩σ₁≡σ₂))) of λ {
      ⊢0 →
      ( ⊩wk2Subst-σ₂
      , neuTerm
          (⊩A .unwrap _ _ .proj₁)
          (var (x0 +1))
          ⊢1
          (~-var ⊢1)
      )
    , neuTerm
        (⊩B .unwrap _ _ .proj₁)
        (var x0)
        ⊢0
        (~-var ⊢0) }}}}}

mutual
  -- Valid contexts are well-formed
  soundContext : ⊩ᵛ Γ → ⊢ Γ
  soundContext ε = ε
  soundContext (x ∙ x₁) =
    soundContext x ∙ escape (irrelevance′ (subst-id _)
                                             (proj₁ (unwrap x₁ (soundContext x)
                                                        (idSubstS x))))

  -- From a valid context we can constuct a valid identity substitution
  idSubstS : ([Γ] : ⊩ᵛ Γ) → Γ ⊩ˢ idSubst ∷ Γ / [Γ] / soundContext [Γ]
  idSubstS ε = lift tt
  idSubstS {Γ = Γ ∙ A} ([Γ] ∙ [A]) =
    let ⊢Γ = soundContext [Γ]
        ⊢Γ∙A = soundContext ([Γ] ∙ [A])
        ⊢Γ∙A′ = ⊢Γ ∙ escape (proj₁ (unwrap [A] ⊢Γ (idSubstS [Γ])))
        [A]′ = wk1SubstS {F = A [ idSubst ]} [Γ] ⊢Γ
                         (escape (proj₁ (unwrap [A] (soundContext [Γ])
                                                (idSubstS [Γ]))))
                         (idSubstS [Γ])
        [tailσ] = irrelevanceSubst′ (PE.cong (_∙_ Γ) (subst-id A))
                                    [Γ] [Γ] ⊢Γ∙A′ ⊢Γ∙A [A]′
        var0 = var ⊢Γ∙A (PE.subst (λ x → x0 ∷ x ∈ Γ ∙ A)
                                  (wk-subst A)
                                  (PE.subst (λ x → x0 ∷ wk1 (A [ idSubst ])
                                                     ∈ Γ ∙ x)
                                            (subst-id A) here))
    in  [tailσ]
    ,   neuTerm (proj₁ (unwrap [A] ⊢Γ∙A [tailσ]))
                (var x0)
                var0 (~-var var0)

-- Reflexivity valid substitutions
reflSubst : ∀ {Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
            ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → Δ ⊩ˢ σ ≡ σ ∷ Γ / [Γ] / ⊢Δ / [σ]
reflSubst ε ⊢Δ [σ] = lift tt
reflSubst ([Γ] ∙ x) ⊢Δ [σ] =
  reflSubst [Γ] ⊢Δ (proj₁ [σ]) , reflEqTerm (proj₁ (unwrap x ⊢Δ (proj₁ [σ]))) (proj₂ [σ])

-- Reflexivity of valid identity substitution
reflIdSubst : ([Γ] : ⊩ᵛ Γ)
            → Γ ⊩ˢ idSubst ≡ idSubst ∷ Γ / [Γ] / soundContext [Γ] / idSubstS [Γ]
reflIdSubst [Γ] = reflSubst [Γ] (soundContext [Γ]) (idSubstS [Γ])

-- Symmetry of valid substitution
symS : ∀ {Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
       ([σ]  : Δ ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
       ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
     → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
     → Δ ⊩ˢ σ′ ≡ σ ∷ Γ / [Γ] / ⊢Δ / [σ′]
symS ε ⊢Δ [σ] [σ′] [σ≡σ′] = lift tt
symS ([Γ] ∙ x) ⊢Δ [σ] [σ′] [σ≡σ′] =
  symS [Γ] ⊢Δ (proj₁ [σ]) (proj₁ [σ′]) (proj₁ [σ≡σ′])
  , let [σA]           = proj₁ (unwrap x ⊢Δ (proj₁ [σ]))
        [σ′A]          = proj₁ (unwrap x ⊢Δ (proj₁ [σ′]))
        [σA≡σ′A]       = (proj₂ (unwrap x ⊢Δ (proj₁ [σ]))) (proj₁ [σ′]) (proj₁ [σ≡σ′])
        [headσ′≡headσ] = symEqTerm [σA] (proj₂ [σ≡σ′])
    in  convEqTerm₁ [σA] [σ′A] [σA≡σ′A] [headσ′≡headσ]

-- Transitivity of valid substitution
transS : ∀ {σ″ Γ Δ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
         ([σ]   : Δ ⊩ˢ σ   ∷ Γ / [Γ] / ⊢Δ)
         ([σ′]  : Δ ⊩ˢ σ′  ∷ Γ / [Γ] / ⊢Δ)
         ([σ″] : Δ ⊩ˢ σ″ ∷ Γ / [Γ] / ⊢Δ)
       → Δ ⊩ˢ σ  ≡ σ′  ∷ Γ / [Γ] / ⊢Δ / [σ]
       → Δ ⊩ˢ σ′ ≡ σ″ ∷ Γ / [Γ] / ⊢Δ / [σ′]
       → Δ ⊩ˢ σ  ≡ σ″ ∷ Γ / [Γ] / ⊢Δ / [σ]
transS ε ⊢Δ [σ] [σ′] [σ″] [σ≡σ′] [σ′≡σ″] = lift tt
transS ([Γ] ∙ x) ⊢Δ [σ] [σ′] [σ″] [σ≡σ′] [σ′≡σ″] =
  transS [Γ] ⊢Δ (proj₁ [σ]) (proj₁ [σ′]) (proj₁ [σ″])
         (proj₁ [σ≡σ′]) (proj₁ [σ′≡σ″])
  , let [σA]   = proj₁ (unwrap x ⊢Δ (proj₁ [σ]))
        [σ′A]  = proj₁ (unwrap x ⊢Δ (proj₁ [σ′]))
        [σ″A] = proj₁ (unwrap x ⊢Δ (proj₁ [σ″]))
        [σ′≡σ″]′ = convEqTerm₂ [σA] [σ′A]
                                ((proj₂ (unwrap x ⊢Δ (proj₁ [σ]))) (proj₁ [σ′])
                                        (proj₁ [σ≡σ′])) (proj₂ [σ′≡σ″])
    in  transEqTerm [σA] (proj₂ [σ≡σ′]) [σ′≡σ″]′

opaque

  -- A validity lemma for sgSubst.

  sgSubstS :
    (⊩ᵛA : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ)
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩ˢ sgSubst t ∷ Γ ∙ A / ⊩Γ ∙ ⊩ᵛA / soundContext ⊩Γ
  sgSubstS ⊩ᵛA ⊩A ⊩t =
      idSubstS _
    , irrelevanceTerm′ (PE.sym (subst-id _))
        ⊩A (⊩ᵛA .unwrap _ _ .proj₁) ⊩t

opaque
  unfolding sgSubstS

  -- An equality preservation lemma for sgSubst.

  sgSubstSEq :
    {⊩ᵛA : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩A : Γ ⊩⟨ l ⟩ A}
    {⊩t : Γ ⊩⟨ l ⟩ t ∷ A / ⊩A} →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A /
      ⊩Γ ∙ ⊩ᵛA / soundContext ⊩Γ / sgSubstS ⊩ᵛA ⊩A ⊩t
  sgSubstSEq {⊩ᵛA = ⊩ᵛA} {⊩A = ⊩A} t≡u =
      reflIdSubst _
    , irrelevanceEqTerm′ (PE.sym (subst-id _))
        ⊩A (⊩ᵛA .unwrap _ _ .proj₁) t≡u

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→⊩[⇑]≡[⇑] :
    {σ₁ σ₂ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ} →
    (⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A) →
    Δ ⊩ˢ σ₂ ∷ Γ / ⊩Γ / ⊢Δ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁ →
    Δ ∙ A [ σ₁ ] ⊩⟨ l ⟩ B [ liftSubst σ₁ ] ≡ B [ liftSubst σ₂ ] /
      ⊩B .unwrap _ (liftSubstS _ _ ⊩A ⊩σ₁) .proj₁
  ⊩ᵛ→≡→⊩[⇑]≡[⇑] {⊩A} {⊩σ₁} ⊩B ⊩σ₂ ⊩σ₁≡σ₂ =
    ⊩B .unwrap _ (liftSubstS _ _ ⊩A ⊩σ₁) .proj₂
      (liftSubstS′ ⊩A ⊩σ₂ ⊩σ₁≡σ₂)
      (liftSubstSEq _ _ ⊩A _ ⊩σ₁≡σ₂)

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→≡→⊩[⇑][]₀≡[⇑][]₀ :
    {σ₁ σ₂ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ}
    {⊩σ₂ : Δ ⊩ˢ σ₂ ∷ Γ / ⊩Γ / ⊢Δ} →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A →
    (⊩B[⇑σ₁][t₁] : Δ ⊩⟨ l ⟩ B [ liftSubst σ₁ ] [ t₁ ]₀) →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁ →
    let ⊩A₁ , _ = ⊩A .unwrap ⊢Δ ⊩σ₁
        ⊩A₂ , _ = ⊩A .unwrap ⊢Δ ⊩σ₂
    in
    Δ ⊩⟨ l ⟩ t₁ ∷ A [ σ₁ ] / ⊩A₁ →
    Δ ⊩⟨ l ⟩ t₂ ∷ A [ σ₂ ] / ⊩A₂ →
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] / ⊩A₁ →
    Δ ⊩⟨ l ⟩ B [ liftSubst σ₁ ] [ t₁ ]₀ ≡ B [ liftSubst σ₂ ] [ t₂ ]₀
      / ⊩B[⇑σ₁][t₁]
  ⊩ᵛ→≡→≡→⊩[⇑][]₀≡[⇑][]₀
    {B} {⊩σ₁} {⊩σ₂} ⊩B ⊩B[⇑σ₁][t₁] ⊩σ₁≡σ₂ ⊩t₁ ⊩t₂ ⊩t₁≡t₂ =
    irrelevanceEq″
      (PE.sym (singleSubstComp _ _ B))
      (PE.sym (singleSubstComp _ _ B))
      (⊩B .unwrap _ (⊩σ₁ , ⊩t₁) .proj₁)
      ⊩B[⇑σ₁][t₁] $
    ⊩B .unwrap _ (⊩σ₁ , ⊩t₁) .proj₂ (⊩σ₂ , ⊩t₂) (⊩σ₁≡σ₂ , ⊩t₁≡t₂)

opaque

  -- An equality preservation lemma.

  ⊩ᵛ≡→≡→≡→⊩[⇑][]₀≡[⇑][]₀ :
    {σ : Subst m n}
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ}
    (⊩B₁ : Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ / ⊩Γ ∙ ⊩A₁) →
    Γ ∙ A₂ ⊩ᵛ⟨ l ⟩ B₂ / ⊩Γ ∙ ⊩A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ / ⊩Γ ∙ ⊩A₁ / ⊩B₁ →
    (⊩B₁[⇑σ][t₁] : Δ ⊩⟨ l ⟩ B₁ [ liftSubst σ ] [ t₁ ]₀)
    (⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ) →
    let ⊩A₁ , _ = ⊩A₁ .unwrap ⊢Δ ⊩σ
        ⊩A₂ , _ = ⊩A₂ .unwrap ⊢Δ ⊩σ
    in
    Δ ⊩⟨ l ⟩ A₁ [ σ ] ≡ A₂ [ σ ] / ⊩A₁ →
    Δ ⊩⟨ l ⟩ t₁ ∷ A₁ [ σ ] / ⊩A₁ →
    Δ ⊩⟨ l ⟩ t₂ ∷ A₂ [ σ ] / ⊩A₂ →
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ [ σ ] / ⊩A₁ →
    Δ ⊩⟨ l ⟩
      B₁ [ liftSubst σ ] [ t₁ ]₀ ≡ B₂ [ liftSubst σ ] [ t₂ ]₀ /
      ⊩B₁[⇑σ][t₁]
  ⊩ᵛ≡→≡→≡→⊩[⇑][]₀≡[⇑][]₀
    {B₁} {B₂} {⊩A₁} {⊩A₂}
    ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[⇑σ][t₁] ⊩σ ⊩A₁≡A₂ ⊩t₁ ⊩t₂ ⊩t₁≡t₂ =
    let ⊩A₁ , _ = ⊩A₁ .unwrap _ ⊩σ
        ⊩A₂ , _ = ⊩A₂ .unwrap _ ⊩σ
    in
    case irrelevance′ (PE.sym (singleSubstComp _ _ B₂))
           (⊩B₂ .unwrap _ (⊩σ , ⊩t₂) .proj₁) of λ {
      ⊩B₂[⇑σ][t₂] →
    case convTerm₂ ⊩A₁ ⊩A₂ ⊩A₁≡A₂ ⊩t₂ of λ {
      ⊩t₂ →
    case irrelevance′ (PE.sym (singleSubstComp _ _ B₁))
           (⊩B₁ .unwrap _ (⊩σ , ⊩t₂) .proj₁) of λ {
      ⊩B₁[⇑σ][t₂] →
    transEq ⊩B₁[⇑σ][t₁] ⊩B₁[⇑σ][t₂] ⊩B₂[⇑σ][t₂]
      (⊩ᵛ→≡→≡→⊩[⇑][]₀≡[⇑][]₀
         ⊩B₁ ⊩B₁[⇑σ][t₁] (reflSubst _ _ ⊩σ) ⊩t₁ ⊩t₂ ⊩t₁≡t₂)
      (irrelevanceEq″
         (PE.sym (singleSubstComp _ _ B₁))
         (PE.sym (singleSubstComp _ _ B₂))
         (⊩B₁ .unwrap _ (⊩σ , ⊩t₂) .proj₁)
         ⊩B₁[⇑σ][t₂]
         (⊩B₁≡B₂ _ (⊩σ , ⊩t₂))) }}}

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→≡→⊢[⇑][]₀≡[⇑][]₀ :
    {σ₁ σ₂ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ}
    {⊩σ₂ : Δ ⊩ˢ σ₂ ∷ Γ / ⊩Γ / ⊢Δ} →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁ →
    let ⊩A₁ , _ = ⊩A .unwrap ⊢Δ ⊩σ₁
        ⊩A₂ , _ = ⊩A .unwrap ⊢Δ ⊩σ₂
    in
    Δ ⊩⟨ l ⟩ t₁ ∷ A [ σ₁ ] / ⊩A₁ →
    Δ ⊩⟨ l ⟩ t₂ ∷ A [ σ₂ ] / ⊩A₂ →
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] / ⊩A₁ →
    Δ ⊢ B [ liftSubst σ₁ ] [ t₁ ]₀ ≡ B [ liftSubst σ₂ ] [ t₂ ]₀
  ⊩ᵛ→≡→≡→⊢[⇑][]₀≡[⇑][]₀ {B} {⊩σ₁} ⊩B ⊩σ₁≡σ₂ ⊩t₁ ⊩t₂ ⊩t₁≡t₂ =
    case irrelevance′ (PE.sym (singleSubstComp _ _ B)) $
         ⊩B .unwrap _ (⊩σ₁ , ⊩t₁) .proj₁ of λ {
      ⊩B[⇑σ₁][t₁] →
    ≅-eq $ escapeEq ⊩B[⇑σ₁][t₁] $
    ⊩ᵛ→≡→≡→⊩[⇑][]₀≡[⇑][]₀ ⊩B ⊩B[⇑σ₁][t₁] ⊩σ₁≡σ₂ ⊩t₁ ⊩t₂ ⊩t₁≡t₂ }

opaque

  -- An equality preservation lemma.

  ⊩ᵛ≡→≡→≡→⊢[⇑][]₀≡[⇑][]₀ :
    {σ : Subst m n}
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ}
    (⊩B₁ : Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ / ⊩Γ ∙ ⊩A₁) →
    Γ ∙ A₂ ⊩ᵛ⟨ l ⟩ B₂ / ⊩Γ ∙ ⊩A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ / ⊩Γ ∙ ⊩A₁ / ⊩B₁ →
    (⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ) →
    let ⊩A₁ , _ = ⊩A₁ .unwrap ⊢Δ ⊩σ
        ⊩A₂ , _ = ⊩A₂ .unwrap ⊢Δ ⊩σ
    in
    Δ ⊩⟨ l ⟩ A₁ [ σ ] ≡ A₂ [ σ ] / ⊩A₁ →
    Δ ⊩⟨ l ⟩ t₁ ∷ A₁ [ σ ] / ⊩A₁ →
    Δ ⊩⟨ l ⟩ t₂ ∷ A₂ [ σ ] / ⊩A₂ →
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ [ σ ] / ⊩A₁ →
    Δ ⊢ B₁ [ liftSubst σ ] [ t₁ ]₀ ≡ B₂ [ liftSubst σ ] [ t₂ ]₀
  ⊩ᵛ≡→≡→≡→⊢[⇑][]₀≡[⇑][]₀
    {B₁} {B₂} {⊩A₁} {⊩A₂}
    ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩σ ⊩A₁≡A₂ ⊩t₁ ⊩t₂ ⊩t₁≡t₂ =
    case irrelevance′ (PE.sym (singleSubstComp _ _ B₁)) $
         ⊩B₁ .unwrap _ (⊩σ , ⊩t₁) .proj₁ of λ {
      ⊩B₁[⇑σ][t₁] →
    ≅-eq $ escapeEq ⊩B₁[⇑σ][t₁] $
    ⊩ᵛ≡→≡→≡→⊩[⇑][]₀≡[⇑][]₀
      ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[⇑σ][t₁] ⊩σ ⊩A₁≡A₂ ⊩t₁ ⊩t₂ ⊩t₁≡t₂ }

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ :
    {σ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ} →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A →
    let ⊩A , _ = ⊩A .unwrap ⊢Δ ⊩σ in
    Δ ⊩⟨ l ⟩ t₁ ∷ A [ σ ] / ⊩A →
    Δ ⊩⟨ l ⟩ t₂ ∷ A [ σ ] / ⊩A →
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A [ σ ] / ⊩A →
    Δ ⊢ B [ liftSubst σ ] [ t₁ ]₀ ≡ B [ liftSubst σ ] [ t₂ ]₀
  ⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ {⊩σ} ⊩B =
    ⊩ᵛ→≡→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B (reflSubst _ _ ⊩σ)

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→≡→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,] :
    {σ : Subst m n} →
    let ⇑⇑σ = liftSubstn σ 2 in
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ}
    {⊩B₁ : Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ / ⊩Γ ∙ ⊩A₁}
    {⊩B₂ : Γ ∙ A₂ ⊩ᵛ⟨ l ⟩ B₂ / ⊩Γ ∙ ⊩A₂}
    {⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ} →
    let ⊩A₁[σ] , _ = ⊩A₁ .unwrap ⊢Δ ⊩σ
        ⊩A₂[σ] , _ = ⊩A₂ .unwrap ⊢Δ ⊩σ
    in
    {⊩t₁ : Δ ⊩⟨ l ⟩ t₁ ∷ A₁ [ σ ] / ⊩A₁[σ]}
    {⊩t₂ : Δ ⊩⟨ l ⟩ t₂ ∷ A₂ [ σ ] / ⊩A₂[σ]}
    (⊩A₁[σ]≡A₂[σ] : Δ ⊩⟨ l ⟩ A₁ [ σ ] ≡ A₂ [ σ ] / ⊩A₁[σ]) →
    let ⊩B₁[σ,t₁] , _ = ⊩B₁ .unwrap ⊢Δ (⊩σ , ⊩t₁)
        ⊩B₂[σ,t₂] , _ = ⊩B₂ .unwrap ⊢Δ (⊩σ , ⊩t₂)
        ⊩B₁[σ,t₂] , _ = ⊩B₁ .unwrap ⊢Δ
          (⊩σ , convTerm₂ ⊩A₁[σ] ⊩A₂[σ] ⊩A₁[σ]≡A₂[σ] ⊩t₂)
    in
    Δ ⊩⟨ l ⟩ B₁ [ consSubst σ t₂ ] ≡ B₂ [ consSubst σ t₂ ] / ⊩B₁[σ,t₂] →
    (⊩C₁ : Γ ∙ A₁ ∙ B₁ ⊩ᵛ⟨ l ⟩ C₁ / ⊩Γ ∙ ⊩A₁ ∙ ⊩B₁) →
    Γ ∙ A₂ ∙ B₂ ⊩ᵛ⟨ l ⟩ C₂ / ⊩Γ ∙ ⊩A₂ ∙ ⊩B₂ →
    Γ ∙ A₁ ∙ B₁ ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ / ⊩Γ ∙ ⊩A₁ ∙ ⊩B₁ / ⊩C₁ →
    (⊩C₁[⇑⇑σ][t₁,u₁] : Δ ⊩⟨ l ⟩ C₁ [ ⇑⇑σ ] [ t₁ , u₁ ]₁₀) →
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ [ σ ] / ⊩A₁[σ] →
    Δ ⊩⟨ l ⟩ u₁ ∷ B₁ [ consSubst σ t₁ ] / ⊩B₁[σ,t₁] →
    Δ ⊩⟨ l ⟩ u₂ ∷ B₂ [ consSubst σ t₂ ] / ⊩B₂[σ,t₂] →
    Δ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ B₁ [ consSubst σ t₁ ] / ⊩B₁[σ,t₁] →
    Δ ⊩⟨ l ⟩ C₁ [ ⇑⇑σ ] [ t₁ , u₁ ]₁₀ ≡ C₂ [ ⇑⇑σ ] [ t₂ , u₂ ]₁₀ /
      ⊩C₁[⇑⇑σ][t₁,u₁]
  ⊩ᵛ→≡→≡→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
    {C₁} {C₂} {⊩A₁} {⊩A₂} {⊩B₁} {⊩B₂} {⊩σ} {⊩t₂}
    ⊩A₁[σ]≡A₂[σ] ⊩B₁[σ,t₁]≡B₂[σ,t₂] ⊩C₁ ⊩C₂ ⊩C₁≡C₂ ⊩C₁[⇑⇑σ][t₁,u₁]
    ⊩t₁≡t₂ ⊩u₁ ⊩u₂ ⊩u₁≡u₂ =
    irrelevanceEq″
      (PE.sym (doubleSubstComp C₁ _ _ _))
      (PE.sym (doubleSubstComp C₂ _ _ _))
      (⊩C₁ .unwrap _ (_ , ⊩u₁) .proj₁)
      ⊩C₁[⇑⇑σ][t₁,u₁] $
    case   ( ⊩σ
           , convTerm₂
               (⊩A₁ .unwrap _ _ .proj₁) (⊩A₂ .unwrap _ _ .proj₁)
               ⊩A₁[σ]≡A₂[σ] ⊩t₂
           )
         , convTerm₂
             (⊩B₁ .unwrap _ _ .proj₁) (⊩B₂ .unwrap _ _ .proj₁)
             ⊩B₁[σ,t₁]≡B₂[σ,t₂] ⊩u₂ of λ {
      ⊩σ,t₂,u₂ →
    transEq
      (⊩C₁ .unwrap _ _ .proj₁)
      (⊩C₁ .unwrap {σ = consSubst (consSubst _ _) _} _ ⊩σ,t₂,u₂ .proj₁)
      (⊩C₂ .unwrap _ ((⊩σ , ⊩t₂) , ⊩u₂) .proj₁)
      (⊩C₁ .unwrap _ _ .proj₂
         ⊩σ,t₂,u₂ ((reflSubst _ _ ⊩σ , ⊩t₁≡t₂) , ⊩u₁≡u₂))
      (⊩C₁≡C₂ _ _) }

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,] :
    {σ₁ σ₂ : Subst m n} →
    let ⇑⇑σ₁ = liftSubstn σ₁ 2
        ⇑⇑σ₂ = liftSubstn σ₂ 2
    in
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A}
    {⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ}
    {⊩σ₂ : Δ ⊩ˢ σ₂ ∷ Γ / ⊩Γ / ⊢Δ} →
    let ⊩A[σ₁] , _ = ⊩A .unwrap ⊢Δ ⊩σ₁
        ⊩A[σ₂] , _ = ⊩A .unwrap ⊢Δ ⊩σ₂
    in
    {⊩t₁ : Δ ⊩⟨ l ⟩ t₁ ∷ A [ σ₁ ] / ⊩A[σ₁]}
    {⊩t₂ : Δ ⊩⟨ l ⟩ t₂ ∷ A [ σ₂ ] / ⊩A[σ₂]} →
    let ⊩B[σ₁,t₁] , _ = ⊩B .unwrap ⊢Δ (⊩σ₁ , ⊩t₁)
        ⊩B[σ₂,t₂] , _ = ⊩B .unwrap ⊢Δ (⊩σ₂ , ⊩t₂)
    in
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A ∙ ⊩B →
    (⊩C[⇑⇑σ₁][t₁,u₁] : Δ ⊩⟨ l ⟩ C [ ⇑⇑σ₁ ] [ t₁ , u₁ ]₁₀) →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁ →
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] / ⊩A[σ₁] →
    Δ ⊩⟨ l ⟩ u₁ ∷ B [ consSubst σ₁ t₁ ] / ⊩B[σ₁,t₁] →
    Δ ⊩⟨ l ⟩ u₂ ∷ B [ consSubst σ₂ t₂ ] / ⊩B[σ₂,t₂] →
    Δ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ B [ consSubst σ₁ t₁ ] / ⊩B[σ₁,t₁] →
    Δ ⊩⟨ l ⟩ C [ ⇑⇑σ₁ ] [ t₁ , u₁ ]₁₀ ≡ C [ ⇑⇑σ₂ ] [ t₂ , u₂ ]₁₀ /
      ⊩C[⇑⇑σ₁][t₁,u₁]
  ⊩ᵛ→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
    {C} ⊩C ⊩C[⇑⇑σ₁][t₁,u₁] ⊩σ₁≡σ₂ ⊩t₁≡t₂ ⊩u₁ ⊩u₂ ⊩u₁≡u₂ =
    irrelevanceEq″
      (PE.sym (doubleSubstComp C _ _ _))
      (PE.sym (doubleSubstComp C _ _ _))
      (⊩C .unwrap _ (_ , ⊩u₁) .proj₁)
      ⊩C[⇑⇑σ₁][t₁,u₁] $
    ⊩C .unwrap _ (_ , ⊩u₁) .proj₂ (_ , ⊩u₂)
      ((⊩σ₁≡σ₂ , ⊩t₁≡t₂) , ⊩u₁≡u₂)

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,] :
    {σ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A}
    {⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ} →
    let ⊩A[σ] , _ = ⊩A .unwrap ⊢Δ ⊩σ in
    {⊩t₁ : Δ ⊩⟨ l ⟩ t₁ ∷ A [ σ ] / ⊩A[σ]}
    {⊩t₂ : Δ ⊩⟨ l ⟩ t₂ ∷ A [ σ ] / ⊩A[σ]} →
    let ⊩B[σ,t₁] , _ = ⊩B .unwrap ⊢Δ (⊩σ , ⊩t₁)
        ⊩B[σ,t₂] , _ = ⊩B .unwrap ⊢Δ (⊩σ , ⊩t₂)
    in
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A ∙ ⊩B →
    let ⇑⇑σ = liftSubstn σ 2 in
    (⊩C[⇑⇑σ][t₁,u₁] : Δ ⊩⟨ l ⟩ C [ ⇑⇑σ ] [ t₁ , u₁ ]₁₀) →
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A [ σ ] / ⊩A[σ] →
    Δ ⊩⟨ l ⟩ u₁ ∷ B [ consSubst σ t₁ ] / ⊩B[σ,t₁] →
    Δ ⊩⟨ l ⟩ u₂ ∷ B [ consSubst σ t₂ ] / ⊩B[σ,t₂] →
    Δ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ B [ consSubst σ t₁ ] / ⊩B[σ,t₁] →
    Δ ⊩⟨ l ⟩ C [ ⇑⇑σ ] [ t₁ , u₁ ]₁₀ ≡ C [ ⇑⇑σ ] [ t₂ , u₂ ]₁₀ /
      ⊩C[⇑⇑σ][t₁,u₁]
  ⊩ᵛ→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,] {⊩σ} ⊩C ⊩C[⇑⇑σ][t₁,u₁] =
    ⊩ᵛ→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,] ⊩C ⊩C[⇑⇑σ][t₁,u₁] (reflSubst _ _ ⊩σ)

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→≡→⊢[⇑⇑][,]≡[⇑⇑][,] :
    {σ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A}
    {⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ} →
    let ⊩A[σ] , _ = ⊩A .unwrap ⊢Δ ⊩σ in
    {⊩t₁ : Δ ⊩⟨ l ⟩ t₁ ∷ A [ σ ] / ⊩A[σ]}
    {⊩t₂ : Δ ⊩⟨ l ⟩ t₂ ∷ A [ σ ] / ⊩A[σ]} →
    let ⊩B[σ,t₁] , _ = ⊩B .unwrap ⊢Δ (⊩σ , ⊩t₁)
        ⊩B[σ,t₂] , _ = ⊩B .unwrap ⊢Δ (⊩σ , ⊩t₂)
    in
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A ∙ ⊩B →
    let ⇑⇑σ = liftSubstn σ 2 in
    Δ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A [ σ ] / ⊩A[σ] →
    Δ ⊩⟨ l ⟩ u₁ ∷ B [ consSubst σ t₁ ] / ⊩B[σ,t₁] →
    Δ ⊩⟨ l ⟩ u₂ ∷ B [ consSubst σ t₂ ] / ⊩B[σ,t₂] →
    Δ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ B [ consSubst σ t₁ ] / ⊩B[σ,t₁] →
    Δ ⊢ C [ ⇑⇑σ ] [ t₁ , u₁ ]₁₀ ≡ C [ ⇑⇑σ ] [ t₂ , u₂ ]₁₀
  ⊩ᵛ→≡→≡→⊢[⇑⇑][,]≡[⇑⇑][,] {C} ⊩C ⊩t₁≡t₂ ⊩u₁ ⊩u₂ ⊩u₁≡u₂ =
    case irrelevance′ (PE.sym (doubleSubstComp C _ _ _)) $
         ⊩C .unwrap _ (_ , ⊩u₁) .proj₁ of λ {
      ⊩C[⇑⇑σ][t₁,u₁] →
    ≅-eq $ escapeEq ⊩C[⇑⇑σ][t₁,u₁] $
    ⊩ᵛ→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,] ⊩C ⊩C[⇑⇑σ][t₁,u₁] ⊩t₁≡t₂ ⊩u₁ ⊩u₂ ⊩u₁≡u₂ }

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→⊩[⇑⇑][,]≡[⇑⇑][,] :
    {σ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A}
    {⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ} →
    let ⊩A[σ] , _ = ⊩A .unwrap ⊢Δ ⊩σ in
    {⊩t : Δ ⊩⟨ l ⟩ t ∷ A [ σ ] / ⊩A[σ]} →
    let ⊩B[σ,t] , _ = ⊩B .unwrap ⊢Δ (⊩σ , ⊩t) in
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A ∙ ⊩B →
    let ⇑⇑σ = liftSubstn σ 2 in
    (⊩C[⇑⇑σ][t,u₁] : Δ ⊩⟨ l ⟩ C [ ⇑⇑σ ] [ t , u₁ ]₁₀) →
    Δ ⊩⟨ l ⟩ u₁ ∷ B [ consSubst σ t ] / ⊩B[σ,t] →
    Δ ⊩⟨ l ⟩ u₂ ∷ B [ consSubst σ t ] / ⊩B[σ,t] →
    Δ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ B [ consSubst σ t ] / ⊩B[σ,t] →
    Δ ⊩⟨ l ⟩ C [ ⇑⇑σ ] [ t , u₁ ]₁₀ ≡ C [ ⇑⇑σ ] [ t , u₂ ]₁₀ /
      ⊩C[⇑⇑σ][t,u₁]
  ⊩ᵛ→≡→⊩[⇑⇑][,]≡[⇑⇑][,] {⊩A} {⊩t} ⊩C ⊩C[⇑⇑σ][t,u₁] =
    ⊩ᵛ→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
      ⊩C ⊩C[⇑⇑σ][t,u₁] (reflEqTerm (⊩A .unwrap _ _ .proj₁) ⊩t)

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→≡→⊢[⇑⇑][,]≡[⇑⇑][,] :
    {σ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A}
    {⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ} →
    let ⊩A[σ] , _ = ⊩A .unwrap ⊢Δ ⊩σ in
    {⊩t : Δ ⊩⟨ l ⟩ t ∷ A [ σ ] / ⊩A[σ]} →
    let ⊩B[σ,t] , _ = ⊩B .unwrap ⊢Δ (⊩σ , ⊩t) in
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A ∙ ⊩B →
    let ⇑⇑σ = liftSubstn σ 2 in
    Δ ⊩⟨ l ⟩ u₁ ∷ B [ consSubst σ t ] / ⊩B[σ,t] →
    Δ ⊩⟨ l ⟩ u₂ ∷ B [ consSubst σ t ] / ⊩B[σ,t] →
    Δ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ B [ consSubst σ t ] / ⊩B[σ,t] →
    Δ ⊢ C [ ⇑⇑σ ] [ t , u₁ ]₁₀ ≡ C [ ⇑⇑σ ] [ t , u₂ ]₁₀
  ⊩ᵛ→≡→⊢[⇑⇑][,]≡[⇑⇑][,] {C} ⊩C ⊩u₁ ⊩u₂ ⊩u₁≡u₂ =
    case irrelevance′ (PE.sym (doubleSubstComp C _ _ _)) $
         ⊩C .unwrap _ (_ , ⊩u₁) .proj₁ of λ {
      ⊩C[⇑⇑σ][t,u₁] →
    ≅-eq $ escapeEq ⊩C[⇑⇑σ][t,u₁] $
    ⊩ᵛ→≡→⊩[⇑⇑][,]≡[⇑⇑][,] ⊩C ⊩C[⇑⇑σ][t,u₁] ⊩u₁ ⊩u₂ ⊩u₁≡u₂ }

opaque

  -- An equality preservation lemma.

  ⊩ᵛ→⊢[⇑⇑][,]≡[⇑⇑][,] :
    {σ : Subst m n}
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩B : Γ ∙ A ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A}
    {⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ} →
    let ⊩A[σ] , _ = ⊩A .unwrap ⊢Δ ⊩σ in
    {⊩t : Δ ⊩⟨ l ⟩ t ∷ A [ σ ] / ⊩A[σ]} →
    let ⊩B[σ,t] , _ = ⊩B .unwrap ⊢Δ (⊩σ , ⊩t) in
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C / ⊩Γ ∙ ⊩A ∙ ⊩B →
    let ⇑⇑σ = liftSubstn σ 2 in
    Δ ⊩⟨ l ⟩ u ∷ B [ consSubst σ t ] / ⊩B[σ,t] →
    Δ ⊢ C [ ⇑⇑σ ] [ t , u ]₁₀ ≡ C [ ⇑⇑σ ] [ t , u ]₁₀
  ⊩ᵛ→⊢[⇑⇑][,]≡[⇑⇑][,] {⊩B} {⊩t} ⊩C ⊩u =
    ⊩ᵛ→≡→⊢[⇑⇑][,]≡[⇑⇑][,]
      ⊩C ⊩u ⊩u (reflEqTerm (⊩B .unwrap _ (_ , ⊩t) .proj₁) ⊩u)
