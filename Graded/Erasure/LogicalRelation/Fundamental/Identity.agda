------------------------------------------------------------------------
-- Validity for the identity type
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

import Graded.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed
open import Definition.Typed.Restrictions
import Definition.Untyped hiding (_∷_)

module Graded.Erasure.LogicalRelation.Fundamental.Identity
  {a} {M : Set a}
  (open Graded.Modality M)
  (open Definition.Untyped M renaming (_[_,_] to _[_,_]₁₀))
  {𝕄 : Modality}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Definition.Typed R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄
  {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  ⦃ eqrel : EqRelSet R ⦄
  where

open Has-well-behaved-zero 𝟘-well-behaved
open Type-restrictions R

open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.Inversion R
import Definition.Typed.Consequences.RedSteps R as RS
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Type R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as IE
open import
  Definition.LogicalRelation.Substitution.Introductions.Identity R
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Properties R

open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties.Has-well-behaved-zero 𝕄
open import Graded.Derived.Erased.Untyped 𝕄 as Erased using (Erased)
open import Graded.Erasure.LogicalRelation R is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Conversion R is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Reduction R is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Subsumption R is-𝟘? ⊢Δ
import Graded.Erasure.Target as T
open import Graded.Mode 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  Γ           : Con Term _
  γ δ         : Conₘ _
  A B t u v w : Term _
  m           : Mode
  ⊩Γ          : ⊩ᵛ _
  p q         : M

opaque

  -- Validity of Id.

  Idʳ :
    Γ ⊢ A ∷ U →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ A →
    ∃ λ (⊩Γ : ⊩ᵛ Γ) →
    ∃ λ (⊩U : Γ ⊩ᵛ⟨ ¹ ⟩ U / ⊩Γ) →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ Id A t u ∷[ m ] U / ⊩Γ / ⊩U
  Idʳ ⊢A ⊢t ⊢u =
      valid (wfTerm ⊢A)
    , Uᵛ _
    , λ ⊩σ _ →
        Uᵣ (substitutionTerm (Idⱼ ⊢A ⊢t ⊢u) (wellformedSubst _ _ ⊩σ) ⊢Δ)
          ◀ _

opaque
  unfolding Idᵛ ⊩Id

  -- Validity of rfl.

  rflʳ :
    Γ ⊢ t ∷ A →
    ∃ λ (⊩Γ : ⊩ᵛ Γ) →
    ∃ λ (⊩Id : Γ ⊩ᵛ⟨ ¹ ⟩ Id A t t / ⊩Γ) →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ rfl ∷[ m ] Id A t t / ⊩Γ / ⊩Id
  rflʳ ⊢t =
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
      ⊩Γ
    , Idᵛ ⊩A ⊩t ⊩t
    , λ ⊩σ _ →
        rflᵣ
          (rfl  ∎⟨ rflⱼ (substitutionTerm ⊢t (wellformedSubst _ _ ⊩σ) ⊢Δ) ⟩⇒)
          T.refl
          ◀ _ }

private opaque

  -- Any context of a size that is equal to 0 is equal to (via a
  -- transport) the context ε.

  ≡0→≡ε :
    (k≡0 : k ≡ 0) (Δ : Con Term k) →
    Δ ≡ PE.subst (Con Term) (PE.sym k≡0) ε
  ≡0→≡ε PE.refl ε = PE.refl

opaque
  unfolding Idᵛ ⊩Id

  -- Validity of []-cong for empty "target contexts".

  []-congʳ :
    k ≡ 0 →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ A →
    Γ ⊢ v ∷ Id A t u →
    []-cong-allowed →
    ∃ λ (⊩Γ : ⊩ᵛ Γ) →
    ∃ λ (⊩Id : Γ ⊩ᵛ⟨ ¹ ⟩ Id (Erased A) Erased.[ t ] Erased.[ u ] / ⊩Γ) →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ []-cong A t u v ∷[ m ]
      Id (Erased A) Erased.[ t ] Erased.[ u ] / ⊩Γ / ⊩Id
  []-congʳ {t} {A} {u} {v} PE.refl ⊢t ⊢u ⊢v ok =
    case ≡0→≡ε PE.refl Δ of λ {
      PE.refl →
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
      ⊩Γ
    , Idᵛ (Erasedᵛ ⊩A) ([]ᵛ t ⊩t) ([]ᵛ u (fundamentalTerm′ ⊩A ⊢u))
    , λ {σ = σ} ⊩σ _ →
        case substitutionTerm ⊢v (wellformedSubst _ _ ⊩σ) ⊢Δ of λ {
          ⊢v[σ] →
        case ε⊢∷Id→ε⊢≡∷ ⊢v[σ] of λ {
          t[σ]≡u[σ] →
        rflᵣ
          (([]-cong A t u v) [ σ ]    ⇒*⟨ []-cong-subst* (ε⊢⇒*rfl∷Id ⊢v[σ]) ok ⟩
           ([]-cong A t u rfl) [ σ ]  ⇒⟨ []-cong-β-⇒ t[σ]≡u[σ] ok ⟩∎
           rfl                        ∎)
          T.refl
          ◀ _ }}}}
    where
    open IE ([]-cong→Erased ok)

opaque
  unfolding Idᵛ ⊩Id

  -- Validity of K.

  Kʳ :
    Γ ⊢ t ∷ A →
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v ∷ Id A t t →
    K-allowed →
    (⊩B[rfl] : Γ ⊩ᵛ⟨ ¹ ⟩ B [ rfl ]₀ / ⊩Γ)
    (⊩B[v] : Γ ⊩ᵛ⟨ ¹ ⟩ B [ v ]₀ / ⊩Γ) →
    γ ≤ᶜ δ →
    δ ▸ Γ ⊩ʳ⟨ ¹ ⟩ u ∷[ m ] B [ rfl ]₀ / ⊩Γ / ⊩B[rfl] →
    k ≡ 0 ⊎
    (∃₃ λ η ⊩A (⊩t : Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / ⊩Γ / ⊩A) →
     γ ≤ᶜ η × η ▸ Γ ⊩ʳ⟨ ¹ ⟩ v ∷[ m ] Id A t t / ⊩Γ / Idᵛ ⊩A ⊩t ⊩t) →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ K p A t B u v ∷[ m ] B [ v ]₀ / ⊩Γ / ⊩B[v]
  Kʳ
    {t} {A} {B} {u} {v} {m} {p}
    ⊢t ⊢B ⊢u ⊢v ok ⊩B[rfl] ⊩B[v] γ≤δ ⊩ʳu k≡0⊎⊩ʳv {σ} ⊩σ σ®σ′
    with is-𝟘? ⌜ m ⌝
  … | yes _ = _
  … | no _  =
    let ⊩B[v][σ]   , _ = ⊩B[v]   .unwrap _ ⊩σ
        ⊩B[rfl][σ] , _ = ⊩B[rfl] .unwrap _ ⊩σ
    in
    case wellformedSubst _ _ ⊩σ of λ {
      ⊢ˢσ →
    case (case k≡0⊎⊩ʳv of λ where
            (inj₁ PE.refl) →
              case ≡0→≡ε PE.refl Δ of λ {
                PE.refl →
              ε⊢⇒*rfl∷Id (substitutionTerm ⊢v ⊢ˢσ ⊢Δ) }
            (inj₂ (_ , _ , _ , γ≤η , ⊩ʳv)) →
              case ⊩ʳv ⊩σ
                     (subsumptionSubst {l = ¹} σ®σ′ λ _ →
                      ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤η) of λ {
                (rflᵣ v[σ]⇒*rfl _) → v[σ]⇒*rfl }) of λ {
      v[σ]⇒*rfl →
    case substitution ⊢B
           (liftSubst′ (wfTerm ⊢t) ⊢Δ (Idⱼ ⊢t ⊢t) ⊢ˢσ)
           (⊢Δ ∙ substitution (Idⱼ ⊢t ⊢t) ⊢ˢσ ⊢Δ) of λ {
      ⊢B[⇑σ] →
    case
      B [ liftSubst σ ] [ rfl ]₀      ≡⟨ substTypeEq (refl ⊢B[⇑σ]) (sym (subset*Term v[σ]⇒*rfl)) ⟩⊢∎≡
      B [ liftSubst σ ] [ v [ σ ] ]₀  ≡˘⟨ singleSubstLift B _ ⟩
      B [ v ]₀ [ σ ]                  ∎
      of λ {
      B[⇑σ][rfl]≡B[v][σ] →
    case
      B [ rfl ]₀ [ σ ]            ≡⟨ singleSubstLift B _ ⟩⊢≡
      B [ liftSubst σ ] [ rfl ]₀  ≡⟨ B[⇑σ][rfl]≡B[v][σ] ⟩⊢∎
      B [ v ]₀ [ σ ]              ∎
      of λ {
      B[rfl][σ]≡B[v][σ] →
    case PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
         substitutionTerm ⊢u ⊢ˢσ ⊢Δ of λ {
      ⊢u[σ] →
    redSubstTerm* ⊩B[v][σ]
      (convTermʳ ⊩B[rfl][σ] ⊩B[v][σ] B[rfl][σ]≡B[v][σ] $
       ⊩ʳu ⊩σ (subsumptionSubst {l = ¹} σ®σ′ λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤δ))
      ((K p A t B u v) [ σ ]    ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
                                    RS.K-subst* ⊢B[⇑σ] ⊢u[σ] v[σ]⇒*rfl ok ⟩
       (K p A t B u rfl) [ σ ]  ⇒⟨ conv (K-β-⇒ ⊢B[⇑σ] ⊢u[σ] ok) B[⇑σ][rfl]≡B[v][σ] ⟩∎
       u [ σ ]                  ∎)
      T.refl }}}}}}

opaque
  unfolding Idᵛ ⊩Id

  -- Validity of J.

  Jʳ :
    Γ ⊢ t ∷ A →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ v ∷ A →
    Γ ⊢ w ∷ Id A t v →
    (⊩B[t,rfl] : Γ ⊩ᵛ⟨ ¹ ⟩ B [ t , rfl ]₁₀ / ⊩Γ)
    (⊩B[v,w] : Γ ⊩ᵛ⟨ ¹ ⟩ B [ v , w ]₁₀ / ⊩Γ) →
    γ ≤ᶜ δ →
    δ ▸ Γ ⊩ʳ⟨ ¹ ⟩ u ∷[ m ] B [ t , rfl ]₁₀ / ⊩Γ / ⊩B[t,rfl] →
    k ≡ 0 ⊎
    (∃₂ λ η ⊩A →
     ∃ λ (⊩t : Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / ⊩Γ / ⊩A) →
     ∃ λ (⊩v : Γ ⊩ᵛ⟨ ¹ ⟩ v ∷ A / ⊩Γ / ⊩A) →
     γ ≤ᶜ η × η ▸ Γ ⊩ʳ⟨ ¹ ⟩ w ∷[ m ] Id A t v / ⊩Γ / Idᵛ ⊩A ⊩t ⊩v) →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ J p q A t B u v w ∷[ m ] B [ v , w ]₁₀ / ⊩Γ / ⊩B[v,w]
  Jʳ
    {Γ} {t} {A} {B} {u} {v} {w} {γ} {m} {p} {q}
    ⊢t ⊢B ⊢u ⊢v ⊢w ⊩B[t,rfl] ⊩B[v,w] γ≤δ ⊩ʳu k≡0⊎⊩ʳw {σ} ⊩σ σ®σ′
    with is-𝟘? ⌜ m ⌝
  … | yes _ = _
  … | no _  =
    let ⊩B[v,w][σ]   , _ = ⊩B[v,w]   .unwrap _ ⊩σ
        ⊩B[t,rfl][σ] , _ = ⊩B[t,rfl] .unwrap _ ⊩σ
    in
    case wellformedSubst _ _ ⊩σ of λ {
      ⊢ˢσ →
    case (case k≡0⊎⊩ʳw of λ where
            (inj₁ PE.refl) →
              case ≡0→≡ε PE.refl Δ of λ {
                PE.refl →
              ε⊢⇒*rfl∷Id (substitutionTerm ⊢w ⊢ˢσ ⊢Δ) }
            (inj₂ (_ , _ , _ , _ , γ≤η , ⊩ʳw)) →
              case ⊩ʳw ⊩σ
                     (subsumptionSubst {l = ¹} σ®σ′ λ _ →
                      ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤η) of λ {
                (rflᵣ w[σ]⇒*rfl _) → w[σ]⇒*rfl }) of λ {
      w[σ]⇒*rfl →
    case inversion-rfl-Id
           (syntacticEqTerm (subset*Term w[σ]⇒*rfl)
              .proj₂ .proj₂) of λ {
      t[σ]≡v[σ] →
    case syntacticEqTerm t[σ]≡v[σ] of λ {
      (⊢A[σ] , ⊢t[σ] , _) →
    case J-motive-context ⊢t of λ {
      (⊢Γ∙A ∙ ⊢Id) →
    case substitution ⊢B
           (PE.subst
              (λ u →
                 Δ ∙ A [ σ ] ∙ u ⊢ˢ liftSubst (liftSubst σ) ∷
                 Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0))
              (Id-wk1-wk1-0[⇑]≡ A t) $
            liftSubst′ ⊢Γ∙A (⊢Δ ∙ ⊢A[σ]) ⊢Id $
            liftSubst′ (wfTerm ⊢t) ⊢Δ (syntacticTerm ⊢t) ⊢ˢσ)
           (J-motive-context ⊢t[σ]) of λ {
      ⊢B[⇑⇑σ] →
    case
      B [ liftSubstn σ 2 ] [ t [ σ ] , rfl ]₁₀      ≡⟨ J-result-cong (refl ⊢B[⇑⇑σ]) t[σ]≡v[σ] $
                                                       conv (sym (subset*Term w[σ]⇒*rfl))
                                                         (Id-cong (refl ⊢A[σ]) (refl ⊢t[σ]) (sym t[σ]≡v[σ])) ⟩⊢∎≡
      B [ liftSubstn σ 2 ] [ v [ σ ] , w [ σ ] ]₁₀  ≡˘⟨ [,]-[]-commute B ⟩
      B [ v , w ]₁₀ [ σ ]                           ∎
      of λ {
      B[⇑σ][t[σ],rfl]≡B[v,w][σ] →
    case
      B [ t , rfl ]₁₀ [ σ ]                     ≡⟨ [,]-[]-commute B ⟩⊢≡
      B [ liftSubstn σ 2 ] [ t [ σ ] , rfl ]₁₀  ≡⟨ B[⇑σ][t[σ],rfl]≡B[v,w][σ] ⟩⊢∎
      B [ v , w ]₁₀ [ σ ]                       ∎
      of λ {
      B[t,rfl][σ]≡B[v,w][σ] →
    case PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) $
         substitutionTerm ⊢u ⊢ˢσ ⊢Δ of λ {
      ⊢u[σ] →
    redSubstTerm* ⊩B[v,w][σ]
      (convTermʳ ⊩B[t,rfl][σ] ⊩B[v,w][σ] B[t,rfl][σ]≡B[v,w][σ] $
       ⊩ʳu ⊩σ (subsumptionSubst {l = ¹} σ®σ′ λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 γ≤δ))
      ((J p q A t B u v w) [ σ ]    ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
                                        RS.J-subst* ⊢B[⇑⇑σ] ⊢u[σ] w[σ]⇒*rfl ⟩
       (J p q A t B u v rfl) [ σ ]  ⇒⟨ conv (J-β-⇒ t[σ]≡v[σ] ⊢B[⇑⇑σ] ⊢u[σ])
                                         B[⇑σ][t[σ],rfl]≡B[v,w][σ] ⟩∎
       u [ σ ]                      ∎)
      T.refl }}}}}}}}}
