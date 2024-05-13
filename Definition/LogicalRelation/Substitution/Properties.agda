------------------------------------------------------------------------
-- Lemmata on valid substitutions
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Properties
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
  hiding (_∷_) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
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
    A A₁ A₂ B B₁ B₂ C C₁ C₂ t t₁ t₂ u u₁ u₂ v : Term _
    Γ Δ : Con Term n
    σ σ₁ σ₂ σ′ : Subst m n
    ρ : Wk k n
    l l′ : TypeLevel
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
    case conv (var₀ (escape (⊩A .unwrap _ ⊩σ₁ .proj₁)))
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

opaque

  -- Symmetry for _⊩ᵛ⟨_⟩_≡_/_/_.

  sym-⊩ᵛ≡// :
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ)
    (⊩B : Γ ⊩ᵛ⟨ l ⟩ B / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ B ≡ A / ⊩Γ / ⊩B
  sym-⊩ᵛ≡// ⊩A ⊩B A≡B _ ⊩σ =
    symEq (⊩A .unwrap _ _ .proj₁) (⊩B .unwrap _ _ .proj₁) (A≡B _ ⊩σ)

opaque

  -- Symmetry for _⊩ᵛ⟨_⟩_≡_∷_/_/_.

  sym-⊩ᵛ≡∷// :
    ∀ t u →
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ u ≡ t ∷ A / ⊩Γ / ⊩A
  sym-⊩ᵛ≡∷// _ _ ⊩A t≡u _ ⊩σ =
    symEqTerm (⊩A .unwrap _ _ .proj₁) (t≡u _ ⊩σ)

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

  -- Transitivity for _⊩ᵛ⟨_⟩_≡_/_/_.

  trans-⊩ᵛ≡// :
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ)
    (⊩B : Γ ⊩ᵛ⟨ l ⟩ B / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ C / ⊩Γ →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ B ≡ C / ⊩Γ / ⊩B →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ C / ⊩Γ / ⊩A
  trans-⊩ᵛ≡// ⊩A ⊩B ⊩C A≡B B≡C _ ⊩σ =
    transEq (⊩A .unwrap _ _ .proj₁) (⊩B .unwrap _ _ .proj₁)
      (⊩C .unwrap _ ⊩σ .proj₁) (A≡B _ ⊩σ) (B≡C _ ⊩σ)

opaque

  -- Transitivity for _⊩ᵛ⟨_⟩_≡_∷_/_/_.

  trans-⊩ᵛ≡∷// :
    ∀ t u v →
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ u ≡ v ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ v ∷ A / ⊩Γ / ⊩A
  trans-⊩ᵛ≡∷// _ _ _ ⊩A t≡u u≡v _ ⊩σ =
    transEqTerm (⊩A .unwrap _ _ .proj₁) (t≡u _ ⊩σ) (u≡v _ ⊩σ)

opaque

  -- A validity lemma for sgSubst.

  sgSubstS :
    (⊩ᵛA : Γ ⊩ᵛ⟨ l′ ⟩ A / ⊩Γ)
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
    {⊩ᵛA : Γ ⊩ᵛ⟨ l′ ⟩ A / ⊩Γ}
    {⊩A : Γ ⊩⟨ l ⟩ A}
    {⊩t : Γ ⊩⟨ l ⟩ t ∷ A / ⊩A} →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A /
      ⊩Γ ∙ ⊩ᵛA / soundContext ⊩Γ / sgSubstS ⊩ᵛA ⊩A ⊩t
  sgSubstSEq {⊩ᵛA = ⊩ᵛA} {⊩A = ⊩A} t≡u =
      reflIdSubst _
    , irrelevanceEqTerm′ (PE.sym (subst-id _))
        ⊩A (⊩ᵛA .unwrap _ _ .proj₁) t≡u
