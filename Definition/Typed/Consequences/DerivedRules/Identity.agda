------------------------------------------------------------------------
-- Derived rules related to the identity type
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Untyped M as U
  hiding (_∷_) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Typed R
open import Definition.Typed.Consequences.DerivedRules.Pi R
open import Definition.Typed.Consequences.DerivedRules.Pi-Sigma R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Term R
import Definition.Typed.RedSteps R as R
open import Definition.Typed.Weakening R
open import Definition.Untyped.Properties M

import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  n                                               : Nat
  Γ Γ₁ Γ₂                                         : Con Term _
  A A₁ A₂ B B₁ B₂
    eq eq₁ eq₂ t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ                                               : Subst _ _
  p q                                             : M
  s                                               : Strength

------------------------------------------------------------------------
-- Lemmas related to rfl

opaque

  -- A variant of the typing rule for rfl.

  rflⱼ′ :
    Γ ⊢ t ≡ u ∷ A →
    Γ ⊢ rfl ∷ Id A t u
  rflⱼ′ t≡u =
    case syntacticEqTerm t≡u of λ {
      (⊢A , ⊢t , _) →
    conv (rflⱼ ⊢t) (Id-cong (refl ⊢A) (refl ⊢t) t≡u) }

------------------------------------------------------------------------
-- Lemmas related to J

opaque

  -- A variant of the typing rule for J.

  Jⱼ′ :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ w ∷ Id A t v →
    Γ ⊢ J p q A t B u v w ∷ B [ v , w ]₁₀
  Jⱼ′ ⊢B ⊢u ⊢w =
    case inversion-Id (syntacticTerm ⊢w) of λ {
      (⊢A , ⊢t , ⊢v) →
    Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w }

opaque

  -- A variant of J-cong.

  J-cong′ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
    Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ≡ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
      B₁ [ v₁ , w₁ ]₁₀
  J-cong′ A₁≡A₂ t₁≡t₂ =
    J-cong (syntacticEq A₁≡A₂ .proj₁) A₁≡A₂
      (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁) t₁≡t₂

opaque

  -- A variant of the equality rule J-β.

  J-β-≡ :
    Γ ⊢ t ∷ A →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ J p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
  J-β-≡ {Γ} {t} {A} ⊢t ⊢B ⊢u =
    case wf ⊢B of λ {
      (_ ∙ ⊢A ∙ _) →
    J-β ⊢A ⊢t ⊢B ⊢u PE.refl }
    where
    -- If a strengthening lemma is proved then one can perhaps drop
    -- the first argument of J-β-≡.

    _ : Γ ∙ A ⊢ wk1 t ∷ wk1 A
    _ =
      case wf ⊢B of λ {
        (_ ∙ _ ∙ ⊢Id) →
      case inversion-Id ⊢Id of λ {
        (_ , ⊢wk1-t , _) →
      ⊢wk1-t }}

opaque

  -- A variant of J-subst.
  --
  -- See also Definition.Typed.Consequences.RedSteps.J-subst*.

  J-subst′ :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ w₁ ⇒ w₂ ∷ Id A t v →
    Γ ⊢ J p q A t B u v w₁ ⇒ J p q A t B u v w₂ ∷ B [ v , w₁ ]₁₀
  J-subst′ ⊢B ⊢u w₁⇒w₂ =
    case inversion-Id (syntacticTerm (redFirstTerm w₁⇒w₂)) of λ {
      (⊢A , ⊢t , ⊢v) →
    J-subst ⊢A ⊢t ⊢B ⊢u ⊢v w₁⇒w₂ }

opaque

  -- A lemma related to the type of an application of J.

  J-result :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ w ∷ Id A t v →
    Γ ⊢ B [ v , w ]₁₀
  J-result ⊢B ⊢w =
    case inversion-Id (syntacticTerm ⊢w) of λ {
      (_ , _ , ⊢v) →
    substType₂ ⊢B ⊢v (PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ ⊢w) }

opaque

  -- A lemma related to the type of an application of J.

  J-result-cong :
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    Γ ⊢ B₁ [ v₁ , w₁ ]₁₀ ≡ B₂ [ v₂ , w₂ ]₁₀
  J-result-cong B₁≡B₂ v₁≡v₂ w₁≡w₂ =
    substTypeEq₂ B₁≡B₂ v₁≡v₂
      (PE.subst (_⊢_≡_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ w₁≡w₂)

opaque

  -- A lemma related to the type of one of the assumptions of J.

  J-motive-rfl-cong :
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ B₁ [ t₁ , rfl ]₁₀ ≡ B₂ [ t₂ , rfl ]₁₀
  J-motive-rfl-cong B₁≡B₂ t₁≡t₂ =
    J-result-cong B₁≡B₂ t₁≡t₂
      (refl (rflⱼ (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁)))

opaque

  -- A variant of the reduction rule J-β.

  J-β-⇒ :
    Γ ⊢ t ≡ t′ ∷ A →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ J p q A t B u t′ rfl ⇒ u ∷ B [ t , rfl ]₁₀
  J-β-⇒ t≡t′ ⊢B =
    case syntacticEqTerm t≡t′ of λ {
      (⊢A , ⊢t , ⊢t′) →
    J-β ⊢A ⊢t ⊢t′ t≡t′ ⊢B (J-motive-rfl-cong (refl ⊢B) t≡t′) }

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context-type :
    Γ ⊢ t ∷ A →
    Γ ∙ A ⊢ Id (wk1 A) (wk1 t) (var x0)
  J-motive-context-type ⊢t =
    case syntacticTerm ⊢t of λ {
      ⊢A →
    Idⱼ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A) }

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context :
    Γ ⊢ t ∷ A →
    ⊢ Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0)
  J-motive-context ⊢t =
    case J-motive-context-type ⊢t of λ {
      ⊢Id →
    wf ⊢Id ∙ ⊢Id }

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context-cong :
    ⊢ Γ₁ ≡ Γ₂ →
    Γ₁ ⊢ A₁ ≡ A₂ →
    Γ₁ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ⊢ Γ₁ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ≡
      Γ₂ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0)
  J-motive-context-cong Γ₁≡Γ₂ A₁≡A₂ t₁≡t₂ =
    case syntacticEq A₁≡A₂ .proj₁ of λ {
      ⊢A₁ →
    Γ₁≡Γ₂ ∙ A₁≡A₂ ∙
    Id-cong (wkEq₁ ⊢A₁ A₁≡A₂) (wkEqTerm₁ ⊢A₁ t₁≡t₂) (refl (var₀ ⊢A₁)) }

opaque

  -- A variant of the previous lemma.

  J-motive-context-cong′ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ⊢ Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ≡
      Γ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0)
  J-motive-context-cong′ A₁≡A₂ =
    J-motive-context-cong (reflConEq (wfEq A₁≡A₂)) A₁≡A₂

------------------------------------------------------------------------
-- Lemmas related to K

opaque

  -- A variant of the typing rule for K.

  Kⱼ′ :
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v ∷ Id A t t →
    K-allowed →
    Γ ⊢ K p A t B u v ∷ B [ v ]₀
  Kⱼ′ ⊢B =
    case wf ⊢B of λ {
      (_ ∙ ⊢Id) →
    case inversion-Id ⊢Id of λ {
      (_ , ⊢t , _) →
    Kⱼ ⊢t ⊢B }}

opaque

  -- A variant of K-cong.

  K-cong′ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀ →
    Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ →
    K-allowed →
    Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ≡ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀
  K-cong′ A₁≡A₂ t₁≡t₂ =
    K-cong A₁≡A₂ (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁) t₁≡t₂

opaque

  -- A variant of the equality rule K-β.

  K-β-≡ :
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    K-allowed →
    Γ ⊢ K p A t B u rfl ≡ u ∷ B [ rfl ]₀
  K-β-≡ ⊢B =
    case wf ⊢B of λ {
      (_ ∙ ⊢Id) →
    case inversion-Id ⊢Id of λ {
      (_ , ⊢t , _) →
    K-β ⊢t ⊢B }}

opaque

  -- A variant of K-subst.
  --
  -- See also Definition.Typed.Consequences.RedSteps.K-subst*.

  K-subst′ :
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v₁ ⇒ v₂ ∷ Id A t t →
    K-allowed →
    Γ ⊢ K p A t B u v₁ ⇒ K p A t B u v₂ ∷ B [ v₁ ]₀
  K-subst′ ⊢B =
    case wf ⊢B of λ {
      (_ ∙ ⊢Id) →
    case inversion-Id ⊢Id of λ {
      (⊢A , ⊢t , _) →
    K-subst ⊢A ⊢t ⊢B }}

opaque

  -- A variant of the reduction rule K-β.

  K-β-⇒ :
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    K-allowed →
    Γ ⊢ K p A t B u rfl ⇒ u ∷ B [ rfl ]₀
  K-β-⇒ ⊢B =
    case wf ⊢B of λ {
      (_ ∙ ⊢Id) →
    case inversion-Id ⊢Id of λ {
      (_ , ⊢t , _) →
    K-β ⊢t ⊢B }}

opaque

  -- A lemma related to the type of one of the assumptions of K.

  K-motive-rfl-cong :
    Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ B₁ [ rfl ]₀ ≡ B₂ [ rfl ]₀
  K-motive-rfl-cong B₁≡B₂ =
    case wfEq B₁≡B₂ of λ {
      (_ ∙ ⊢Id) →
    substTypeEq B₁≡B₂ (refl (rflⱼ (inversion-Id ⊢Id .proj₂ .proj₁))) }

opaque

  -- A lemma related to the context of one of the assumptions of K.

  K-motive-context-type : Γ ⊢ t ∷ A → Γ ⊢ Id A t t
  K-motive-context-type ⊢t = Idⱼ ⊢t ⊢t

opaque

  -- A lemma related to the context of one of the assumptions of K.

  K-motive-context : Γ ⊢ t ∷ A → ⊢ Γ ∙ Id A t t
  K-motive-context ⊢t = wfTerm ⊢t ∙ K-motive-context-type ⊢t

opaque

  -- A lemma related to the context of one of the assumptions of K.

  K-motive-context-cong :
    ⊢ Γ₁ ≡ Γ₂ →
    Γ₁ ⊢ A₁ ≡ A₂ →
    Γ₁ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ⊢ Γ₁ ∙ Id A₁ t₁ t₁ ≡ Γ₂ ∙ Id A₂ t₂ t₂
  K-motive-context-cong Γ₁≡Γ₂ A₁≡A₂ t₁≡t₂ =
    Γ₁≡Γ₂ ∙ Id-cong A₁≡A₂ t₁≡t₂ t₁≡t₂

opaque

  -- A variant of the previous lemma.

  K-motive-context-cong′ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ⊢ Γ ∙ Id A₁ t₁ t₁ ≡ Γ ∙ Id A₂ t₂ t₂
  K-motive-context-cong′ A₁≡A₂ =
    K-motive-context-cong (reflConEq (wfEq A₁≡A₂)) A₁≡A₂

------------------------------------------------------------------------
-- Lemmas related to []-cong

opaque

  -- A variant of the typing rule for []-cong.

  []-congⱼ′ :
    []-cong-allowed s →
    Γ ⊢ v ∷ Id A t u →
    let open Erased s in
      Γ ⊢ []-cong s A t u v ∷ Id (Erased A) ([ t ]) ([ u ])
  []-congⱼ′ ok ⊢v =
    case inversion-Id (syntacticTerm ⊢v) of λ {
      (_ , ⊢t , ⊢u) →
    []-congⱼ ⊢t ⊢u ⊢v ok }

opaque

  -- A variant of []-cong-subst.

  []-cong-subst′ :
    Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
    []-cong-allowed s →
    let open Erased s in
      Γ ⊢ []-cong s A t u v₁ ⇒ []-cong s A t u v₂ ∷
        Id (Erased A) ([ t ]) ([ u ])
  []-cong-subst′ v₁⇒v₂ =
    case inversion-Id (syntacticTerm (redFirstTerm v₁⇒v₂)) of λ {
      (⊢A , ⊢t , ⊢u) →
    []-cong-subst ⊢A ⊢t ⊢u v₁⇒v₂ }

opaque

  -- A variant of Definition.Typed.RedSteps.[]-cong-subst*.

  []-cong-subst* :
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t u →
    []-cong-allowed s →
    let open Erased s in
      Γ ⊢ []-cong s A t u v₁ ⇒* []-cong s A t u v₂ ∷
        Id (Erased A) ([ t ]) ([ u ])
  []-cong-subst* v₁⇒*v₂ =
    case inversion-Id (syntacticTerm (redFirst*Term v₁⇒*v₂)) of λ {
      (⊢A , ⊢t , ⊢u) →
    R.[]-cong-subst* ⊢A ⊢t ⊢u v₁⇒*v₂ }

opaque

  -- A variant of the reduction rule []-cong-β.

  []-cong-β-⇒ :
    Γ ⊢ t ≡ t′ ∷ A →
    []-cong-allowed s →
    let open Erased s in
      Γ ⊢ []-cong s A t t′ rfl ⇒ rfl ∷
        Id (Erased A) ([ t ]) ([ t′ ])
  []-cong-β-⇒ t≡t′ =
    case syntacticEqTerm t≡t′ of λ {
      (⊢A , ⊢t , ⊢t′) →
    []-cong-β ⊢A ⊢t ⊢t′ t≡t′ }

------------------------------------------------------------------------
-- Subst

opaque

  -- Substitutivity.

  subst :
    M →
    Term n → Term (1+ n) → Term n → Term n → Term n → Term n → Term n
  subst p A B t u v w =
    J p 𝟘 A t (wk1 B) w u v

opaque
  unfolding subst

  -- A typing rule for subst.

  ⊢subst :
    Γ ∙ A ⊢ B →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ w ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t u v w ∷ B [ u ]₀
  ⊢subst {B} ⊢B ⊢v ⊢w =
    case inversion-Id (syntacticTerm ⊢v) of λ {
      (_ , ⊢t , _) →
    PE.subst (_⊢_∷_ _ _) (subst-wk B) $
    Jⱼ′ (wk₁ (J-motive-context-type ⊢t) ⊢B)
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-wk B) ⊢w)
      ⊢v }

opaque
  unfolding subst

  -- A reduction rule for subst.

  subst-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t t rfl u ⇒ u ∷ B [ t ]₀
  subst-⇒ {B} ⊢B ⊢t ⊢u =
    PE.subst (_⊢_⇒_∷_ _ _ _) (subst-wk B) $
    J-β-⇒ (refl ⊢t) (wk₁ (J-motive-context-type ⊢t) ⊢B)
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-wk B) ⊢u)

opaque

  -- An equality rule for subst.

  subst-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t t rfl u ≡ u ∷ B [ t ]₀
  subst-≡ ⊢B ⊢t ⊢u =
    subsetTerm (subst-⇒ ⊢B ⊢t ⊢u)

opaque
  unfolding subst

  -- An equality rule for subst.

  subst-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ B₁ [ t₁ ]₀ →
    Γ ⊢ subst p A₁ B₁ t₁ u₁ v₁ w₁ ≡ subst p A₂ B₂ t₂ u₂ v₂ w₂ ∷
      B₁ [ u₁ ]₀
  subst-cong {B₁} A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
    PE.subst (_⊢_≡_∷_ _ _ _) (subst-wk B₁) $
    J-cong′ A₁≡A₂ t₁≡t₂
      (wkEq₁
         (J-motive-context-type (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁))
         B₁≡B₂)
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ subst-wk B₁) w₁≡w₂) u₁≡u₂
      v₁≡v₂

opaque
  unfolding subst

  -- A reduction rule for subst.

  subst-subst :
    Γ ∙ A ⊢ B →
    Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
    Γ ⊢ w ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t u v₁ w ⇒ subst p A B t u v₂ w ∷ B [ u ]₀
  subst-subst {B} ⊢B v₁⇒v₂ ⊢w =
    case inversion-Id (syntacticEqTerm (subsetTerm v₁⇒v₂) .proj₁) of λ {
      (_ , ⊢t , _) →
    PE.subst (_⊢_⇒_∷_ _ _ _) (subst-wk B) $
    J-subst′ (wk₁ (J-motive-context-type ⊢t) ⊢B)
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-wk B) ⊢w) v₁⇒v₂ }

opaque
  unfolding subst

  -- A substitution lemma for subst.

  subst-[] :
    subst p A B t u v w [ σ ] PE.≡
    subst p (A [ σ ]) (B [ liftSubst σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
      (w [ σ ])
  subst-[] {B} =
    PE.cong₄ (J _ _ _ _) (wk1-liftSubst B) PE.refl PE.refl PE.refl

------------------------------------------------------------------------
-- Symmetry

opaque

  -- Symmetry.

  symmetry :
    Term n → Term n → Term n → Term n → Term n
  symmetry A t u eq =
    subst ω A (Id (wk1 A) (var x0) (wk1 t)) t u eq rfl

opaque
  unfolding symmetry

  -- A typing rule for symmetry.

  ⊢symmetry :
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ symmetry A t u eq ∷ Id A u t
  ⊢symmetry ⊢eq =
    case inversion-Id (syntacticTerm ⊢eq) of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _)) $
    ⊢subst
      (Idⱼ (var₀ ⊢A) (wkTerm₁ ⊢A ⊢t))
      ⊢eq
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $
          PE.cong₃ Id (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _)) $
       rflⱼ ⊢t)

opaque
  unfolding symmetry

  -- A reduction rule for symmetry.

  symmetry-⇒ :
    Γ ⊢ t ∷ A →
    Γ ⊢ symmetry A t t rfl ⇒ rfl ∷ Id A t t
  symmetry-⇒ ⊢t =
    case syntacticTerm ⊢t of λ
      ⊢A →
    case PE.cong₃ Id (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _) of λ
      Id≡Id →
    PE.subst (_⊢_⇒_∷_ _ _ _) Id≡Id $
    subst-⇒
      (Idⱼ (var₀ ⊢A) (wkTerm₁ ⊢A ⊢t))
      ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id≡Id) $
       rflⱼ ⊢t)

opaque

  -- An equality rule for symmetry.

  symmetry-≡ :
    Γ ⊢ t ∷ A →
    Γ ⊢ symmetry A t t rfl ≡ rfl ∷ Id A t t
  symmetry-≡ ⊢t =
    subsetTerm (symmetry-⇒ ⊢t)

opaque
  unfolding symmetry

  -- A substitution lemma for symmetry.

  symmetry-[] :
    symmetry A t u eq [ σ ] PE.≡
    symmetry (A [ σ ]) (t [ σ ]) (u [ σ ]) (eq [ σ ])
  symmetry-[] {A} {t} {u} {eq} {σ} =
    subst ω A (Id (wk1 A) (var x0) (wk1 t)) t u eq rfl [ σ ]         ≡⟨ subst-[] ⟩

    subst ω (A [ σ ])
      (Id (wk1 A [ liftSubst σ ]) (var x0) (wk1 t [ liftSubst σ ]))
      (t [ σ ]) (u [ σ ]) (eq [ σ ]) rfl                             ≡⟨ PE.cong₅ (subst _ _)
                                                                          (PE.cong₃ Id (wk1-liftSubst A) PE.refl (wk1-liftSubst t))
                                                                          PE.refl PE.refl PE.refl PE.refl ⟩
    subst ω (A [ σ ])
      (Id (wk1 (A [ σ ])) (var x0) (wk1 (t [ σ ])))
      (t [ σ ]) (u [ σ ]) (eq [ σ ]) rfl                             ∎

------------------------------------------------------------------------
-- Transitivity

opaque

  -- Transitivity.

  transitivity :
    Term n → Term n → Term n → Term n → Term n → Term n → Term n
  transitivity A t u v eq₁ eq₂ =
    subst ω A (Id (wk1 A) (wk1 t) (var x0)) u v eq₂ eq₁

opaque
  unfolding transitivity

  -- A typing rule for transitivity.

  ⊢transitivity :
    Γ ⊢ eq₁ ∷ Id A t u →
    Γ ⊢ eq₂ ∷ Id A u v →
    Γ ⊢ transitivity A t u v eq₁ eq₂ ∷ Id A t v
  ⊢transitivity {A} {t} {u} {eq₂} {v} ⊢eq₁ ⊢eq₂ =
    case inversion-Id (syntacticTerm ⊢eq₁) of λ {
      (_ , ⊢t , _) →
    PE.subst (_⊢_∷_ _ _) (PE.sym ≡Id-wk1-wk1-0[]₀) $
    ⊢subst
      (J-motive-context-type ⊢t)
      ⊢eq₂
      (PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ ⊢eq₁) }

opaque
  unfolding transitivity

  -- A reduction rule for transitivity.

  transitivity-⇒ :
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ transitivity A t u u eq rfl ⇒ eq ∷ Id A t u
  transitivity-⇒ ⊢eq =
    case inversion-Id (syntacticTerm ⊢eq) of λ
      (⊢A , ⊢t , ⊢u) →
    case PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl of λ
      Id≡Id →
    PE.subst (_⊢_⇒_∷_ _ _ _) Id≡Id $
    subst-⇒
      (Idⱼ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A))
      ⊢u
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id≡Id) ⊢eq)

opaque

  -- An equality rule for transitivity.

  transitivity-≡ :
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ transitivity A t u u eq rfl ≡ eq ∷ Id A t u
  transitivity-≡ ⊢eq =
    subsetTerm (transitivity-⇒ ⊢eq)

opaque
  unfolding transitivity

  -- A substitution lemma for transitivity.

  transitivity-[] :
    transitivity A t u v eq₁ eq₂ [ σ ] PE.≡
    transitivity (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ]) (eq₁ [ σ ])
      (eq₂ [ σ ])
  transitivity-[] {A} {t} {u} {v} {eq₁} {eq₂} {σ} =
    subst ω A (Id (wk1 A) (wk1 t) (var x0)) u v eq₂ eq₁ [ σ ]        ≡⟨ subst-[] ⟩

    subst ω (A [ σ ])
      (Id (wk1 A [ liftSubst σ ]) (wk1 t [ liftSubst σ ]) (var x0))
      (u [ σ ]) (v [ σ ]) (eq₂ [ σ ]) (eq₁ [ σ ])                    ≡⟨ PE.cong₅ (subst _ _)
                                                                          (PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl)
                                                                          PE.refl PE.refl PE.refl PE.refl ⟩
    subst ω (A [ σ ]) (Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0))
      (u [ σ ]) (v [ σ ]) (eq₂ [ σ ]) (eq₁ [ σ ])                    ∎

------------------------------------------------------------------------
-- The lemma transitivity-symmetryˡ

opaque

  -- A simplification lemma for transitivity and symmetry.

  transitivity-symmetryˡ :
    Term n → Term n → Term n → Term n → Term n
  transitivity-symmetryˡ A t u eq =
    J ω ω A t
      (Id (Id (wk2 A) (var x1) (var x1))
         (transitivity (wk2 A) (var x1) (wk2 t) (var x1)
            (symmetry (wk2 A) (wk2 t) (var x1) (var x0))
            (var x0))
         rfl)
      rfl u eq

opaque
  unfolding transitivity-symmetryˡ

  -- A typing rule for transitivity-symmetryˡ.

  ⊢transitivity-symmetryˡ :
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ transitivity-symmetryˡ A t u eq ∷
      Id (Id A u u) (transitivity A u t u (symmetry A t u eq) eq) rfl
  ⊢transitivity-symmetryˡ {eq} {A} {t} {u} ⊢eq =
    case inversion-Id (syntacticTerm ⊢eq) of λ
      (⊢A , ⊢t , _) →
    case Idⱼ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A) of λ
      ⊢Id-t′-0 →
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₃ Id
         (PE.cong₃ Id wk2-[,] PE.refl PE.refl)
         (transitivity (wk2 A) (var x1) (wk2 t) (var x1)
            (symmetry (wk2 A) (wk2 t) (var x1) (var x0)) (var x0)
            [ u , eq ]₁₀                                               ≡⟨ transitivity-[] ⟩

          transitivity (wk2 A [ u , eq ]₁₀) u (wk2 t [ u , eq ]₁₀) u
            (symmetry (wk2 A) (wk2 t) (var x1) (var x0) [ u , eq ]₁₀)
            eq                                                         ≡⟨ PE.cong₆ transitivity wk2-[,] PE.refl wk2-[,] PE.refl
                                                                            symmetry-[] PE.refl ⟩
          transitivity A u t u
            (symmetry (wk2 A [ u , eq ]₁₀) (wk2 t [ u , eq ]₁₀) u eq)
            eq                                                         ≡⟨ PE.cong₂ (transitivity _ _ _ _)
                                                                            (PE.cong₄ symmetry wk2-[,] wk2-[,] PE.refl PE.refl)
                                                                            PE.refl ⟩
          transitivity A u t u (symmetry A t u eq) eq                  ∎)
         PE.refl) $
    Jⱼ′
      (Idⱼ
         (⊢transitivity (⊢symmetry (var₀ ⊢Id-t′-0)) (var₀ ⊢Id-t′-0))
         (rflⱼ (var₁ ⊢Id-t′-0)))
      (rflⱼ′
         (transitivity (wk2 A) (var x1) (wk2 t) (var x1)
            (symmetry (wk2 A) (wk2 t) (var x1) (var x0)) (var x0)
            [ t , rfl ]₁₀                                                 ≡⟨ transitivity-[] ⟩⊢≡

          transitivity (wk2 A [ t , rfl ]₁₀) t (wk2 t [ t , rfl ]₁₀) t
            (symmetry (wk2 A) (wk2 t) (var x1) (var x0) [ t , rfl ]₁₀)
            rfl                                                           ≡⟨ PE.cong₆ transitivity wk2-[,] PE.refl wk2-[,] PE.refl
                                                                               symmetry-[] PE.refl ⟩⊢≡
          transitivity A t t t
            (symmetry (wk2 A [ t , rfl ]₁₀) (wk2 t [ t , rfl ]₁₀) t rfl)
            rfl                                                           ≡⟨ PE.cong₂ (transitivity _ _ _ _)
                                                                               (PE.cong₄ symmetry wk2-[,] wk2-[,] PE.refl PE.refl)
                                                                               PE.refl ⟩⊢≡

          transitivity A t t t (symmetry A t t rfl) rfl                   ≡⟨ transitivity-≡ (⊢symmetry (rflⱼ ⊢t)) ⟩⊢
                                                                           ⟨ PE.subst (flip (_⊢_≡_ _) _)
                                                                               (PE.sym $ PE.cong₃ Id wk2-[,] PE.refl PE.refl) $
                                                                             refl (Idⱼ ⊢t ⊢t) ⟩

          symmetry A t t rfl                                              ≡⟨ symmetry-≡ ⊢t ⟩⊢∎

          rfl                                                             ∎))
      ⊢eq

------------------------------------------------------------------------
-- Congruence

opaque

  -- Congruence.

  cong :
    Term n → Term n → Term n → Term n → Term (1+ n) → Term n → Term n
  cong A t u B v w =
    subst ω A (Id (wk1 B) (wk1 (v [ t ]₀)) v) t u w rfl

opaque
  unfolding cong

  -- A typing rule for cong.

  ⊢cong :
    Γ ∙ A ⊢ v ∷ wk1 B →
    Γ ⊢ w ∷ Id A t u →
    Γ ⊢ cong A t u B v w ∷ Id B (v [ t ]₀) (v [ u ]₀)
  ⊢cong ⊢v ⊢w =
    case inversion-Id (syntacticTerm ⊢w) of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl) $
    ⊢subst
      (Idⱼ
         (PE.subst (_⊢_∷_ _ _) (PE.cong wk1 $ wk1-sgSubst _ _) $
          wkTerm₁ ⊢A (substTerm ⊢v ⊢t))
         ⊢v)
      ⊢w
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $ PE.cong₃ Id PE.refl (wk1-sgSubst _ _) PE.refl) $
       rflⱼ (substTerm ⊢v ⊢t))

opaque
  unfolding cong

  -- A reduction rule for cong.

  cong-⇒ :
    Γ ⊢ t ∷ A →
    Γ ∙ A ⊢ u ∷ wk1 B →
    Γ ⊢ cong A t t B u rfl ⇒ rfl ∷ Id B (u [ t ]₀) (u [ t ]₀)
  cong-⇒ ⊢t ⊢u =
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl) $
    subst-⇒
      (Idⱼ
         (PE.subst (_⊢_∷_ _ _)
            (PE.cong wk1 $ wk1-sgSubst _ _) $
          wkTerm₁ (syntacticTerm ⊢t) (substTerm ⊢u ⊢t))
         ⊢u)
      ⊢t
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $ PE.cong₃ Id PE.refl (wk1-sgSubst _ _) PE.refl) $
       rflⱼ (substTerm ⊢u ⊢t))

opaque

  -- An equality rule for cong.

  cong-≡ :
    Γ ⊢ t ∷ A →
    Γ ∙ A ⊢ u ∷ wk1 B →
    Γ ⊢ cong A t t B u rfl ≡ rfl ∷ Id B (u [ t ]₀) (u [ t ]₀)
  cong-≡ ⊢t ⊢u =
    subsetTerm (cong-⇒ ⊢t ⊢u)

opaque
  unfolding cong

  -- A substitution lemma for cong.

  cong-[] :
    cong A t u B v w [ σ ] PE.≡
    cong (A [ σ ]) (t [ σ ]) (u [ σ ]) (B [ σ ]) (v [ liftSubst σ ])
      (w [ σ ])
  cong-[] {A} {t} {u} {B} {v} {w} {σ} =
    subst ω A (Id (wk1 B) (wk1 (v [ t ]₀)) v) t u w rfl [ σ ]        ≡⟨ subst-[] ⟩

    subst ω (A [ σ ])
      (Id (wk1 B [ liftSubst σ ]) (wk1 (v [ t ]₀) [ liftSubst σ ])
         (v [ liftSubst σ ]))
      (t [ σ ]) (u [ σ ]) (w [ σ ]) rfl                              ≡⟨ PE.cong₅ (subst _ _)
                                                                          (PE.cong₃ Id
                                                                             (wk1-liftSubst B)
                                                                             (
      wk1 (v [ t ]₀) [ liftSubst σ ]                                          ≡⟨ wk1-liftSubst (v [ _ ]₀) ⟩
      wk1 (v [ t ]₀ [ σ ])                                                    ≡⟨ PE.cong wk1 $ singleSubstLift v _ ⟩
      wk1 (v [ liftSubst σ ] [ t [ σ ] ]₀)                                    ∎)
                                                                             PE.refl)
                                                                          PE.refl PE.refl PE.refl PE.refl ⟩
    subst ω (A [ σ ])
      (Id (wk1 (B [ σ ])) (wk1 (v [ liftSubst σ ] [ t [ σ ] ]₀))
         (v [ liftSubst σ ]))
      (t [ σ ]) (u [ σ ]) (w [ σ ]) rfl                              ∎

------------------------------------------------------------------------
-- Pointwise equality of functions

opaque

  -- If two functions are equal, then they are pointwise equal.

  pointwise-equality :
    M → M → Term n → Term (1+ n) → Term n → Term n → Term n → Term n →
    Term n
  pointwise-equality p q A B t u v w =
    cong (Π p , q ▷ A ▹ B) t u (B [ w ]₀) (var x0 ∘⟨ p ⟩ wk1 w) v

opaque
  unfolding pointwise-equality

  -- A typing rule for pointwise-equality.

  ⊢pointwise-equality :
    Γ ⊢ v ∷ Id (Π p , q ▷ A ▹ B) t u →
    Γ ⊢ w ∷ A →
    Γ ⊢ pointwise-equality p q A B t u v w ∷
      Id (B [ w ]₀) (t ∘⟨ p ⟩ w) (u ∘⟨ p ⟩ w)
  ⊢pointwise-equality {B} {w} ⊢v ⊢w =
    case inversion-Id (syntacticTerm ⊢v) of λ
      (⊢ΠAB , _ , _) →
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₂ (Id (B [ w ]₀))
         (PE.cong (_ ∘⟨ _ ⟩_) $ wk1-sgSubst _ _)
         (PE.cong (_ ∘⟨ _ ⟩_) $ wk1-sgSubst _ _)) $
    ⊢cong
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B) $
       var₀ ⊢ΠAB ∘ⱼ wkTerm₁ ⊢ΠAB ⊢w)
      ⊢v

opaque
  unfolding pointwise-equality

  -- A reduction rule for pointwise-equality.

  pointwise-equality-⇒ :
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ A →
    Γ ⊢ pointwise-equality p q A B t t rfl u ⇒ rfl ∷
      Id (B [ u ]₀) (t ∘⟨ p ⟩ u) (t ∘⟨ p ⟩ u)
  pointwise-equality-⇒ {B} {u} ⊢t ⊢u =
    case syntacticTerm ⊢t of λ
      ⊢ΠAB →
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.cong₃ Id
         PE.refl
         (PE.cong (_∘⟨_⟩_ _ _) $ wk1-sgSubst _ _)
         (PE.cong (_∘⟨_⟩_ _ _) $ wk1-sgSubst _ _)) $
    cong-⇒ ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-β B) $
       var₀ ⊢ΠAB ∘ⱼ wkTerm₁ ⊢ΠAB ⊢u)

opaque

  -- An equality rule for pointwise-equality.

  pointwise-equality-≡ :
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ A →
    Γ ⊢ pointwise-equality p q A B t t rfl u ≡ rfl ∷
      Id (B [ u ]₀) (t ∘⟨ p ⟩ u) (t ∘⟨ p ⟩ u)
  pointwise-equality-≡ ⊢t ⊢u =
    subsetTerm (pointwise-equality-⇒ ⊢t ⊢u)

opaque
  unfolding pointwise-equality

  -- A substitution lemma for pointwise-equality.

  pointwise-equality-[] :
    pointwise-equality p q A B t u v w [ σ ] PE.≡
    pointwise-equality p q (A [ σ ]) (B [ liftSubst σ ]) (t [ σ ])
      (u [ σ ]) (v [ σ ]) (w [ σ ])
  pointwise-equality-[] {p} {q} {A} {B} {t} {u} {v} {w} {σ} =
    cong (Π p , q ▷ A ▹ B) t u (B [ w ]₀) (var x0 ∘⟨ p ⟩ wk1 w) v [ σ ]  ≡⟨ cong-[] ⟩

    cong (Π p , q ▷ A [ σ ] ▹ (B [ liftSubst σ ])) (t [ σ ]) (u [ σ ])
      (B [ w ]₀ [ σ ]) (var x0 ∘⟨ p ⟩ wk1 w [ liftSubst σ ]) (v [ σ ])   ≡⟨ PE.cong₃ (cong _ _ _)
                                                                              (singleSubstLift B _)
                                                                              (PE.cong (_∘⟨_⟩_ _ _) $ wk1-liftSubst w)
                                                                              PE.refl ⟩
    cong (Π p , q ▷ A [ σ ] ▹ (B [ liftSubst σ ])) (t [ σ ]) (u [ σ ])
      (B [ liftSubst σ ] [ w [ σ ] ]₀) (var x0 ∘⟨ p ⟩ wk1 (w [ σ ]))
      (v [ σ ])                                                          ∎

------------------------------------------------------------------------
-- Uniqueness of identity proofs (UIP)

opaque

  -- UIP.

  uip : M → M → Term n → Term n → Term n → Term n → Term n → Term n
  uip p q A t u eq₁ eq₂ =
    transitivity
      (Id A t u)
      eq₁
      (transitivity A t u u eq₂
         (transitivity A u t u (symmetry A t u eq₁) eq₁))
      eq₂
      (J ω ω A t
         (Id
            (Id (wk2 A) (wk2 t) (var x1))
            (var x0)
            (transitivity (wk2 A) (wk2 t) (wk2 u) (var x1) (wk2 eq₂)
               (transitivity (wk2 A) (wk2 u) (wk2 t) (var x1)
                  (symmetry (wk2 A) (wk2 t) (wk2 u) (wk2 eq₁))
                  (var x0))))
         (K ω A t (Id (Id (wk1 A) (wk1 t) (wk1 t)) rfl (var x0)) rfl
            (transitivity A t u t eq₂
               (transitivity A u t t (symmetry A t u eq₁) rfl)))
         u eq₁)
      (cong (Id A u u) (transitivity A u t u (symmetry A t u eq₁) eq₁)
         rfl (Id A t u)
         (transitivity (wk1 A) (wk1 t) (wk1 u) (wk1 u) (wk1 eq₂)
            (var x0))
         (transitivity-symmetryˡ A t u eq₁))

opaque
  unfolding uip

  -- A typing rule for UIP. Note that this typing rule requires that K
  -- is allowed.

  ⊢uip :
    K-allowed →
    Γ ⊢ eq₁ ∷ Id A t u →
    Γ ⊢ eq₂ ∷ Id A t u →
    Γ ⊢ uip p q A t u eq₁ eq₂ ∷ Id (Id A t u) eq₁ eq₂
  ⊢uip {eq₁} {A} {t} {u} {eq₂} ok ⊢eq₁ ⊢eq₂ =
    case inversion-Id (syntacticTerm ⊢eq₁) of λ
      (⊢A , ⊢t , ⊢u) →
    case Idⱼ ⊢t ⊢t of λ
      ⊢Id-t-t →
    case Idⱼ ⊢u ⊢u of λ
      ⊢Id-u-u →
    ⊢transitivity
      (PE.subst (_⊢_∷_ _ _) lemma₁ $
       Jⱼ′
         (Idⱼ
            (var₀ (J-motive-context-type ⊢t))
            (⊢transitivity
               (wkTerm₁ (J-motive-context-type ⊢t) (wkTerm₁ ⊢A ⊢eq₂)) $
             ⊢transitivity
               (⊢symmetry
                  (wkTerm₁ (J-motive-context-type ⊢t)
                     (wkTerm₁ ⊢A ⊢eq₁))) $
             var₀ (J-motive-context-type ⊢t)))
         (PE.subst (_⊢_∷_ _ _)
            (Id (wk1 (Id A t t)) rfl (var x0)
               [ transitivity A t u t eq₂
                   (transitivity A u t t (symmetry A t u eq₁) rfl) ]₀    ≡⟨ PE.cong₃ Id (wk1-sgSubst _ _) PE.refl PE.refl ⟩

             Id (Id A t t) rfl
               (transitivity A t u t eq₂
                  (transitivity A u t t (symmetry A t u eq₁) rfl))       ≡˘⟨ lemma₁ ⟩

             Id (Id (wk2 A) (wk2 t) (var x1)) (var x0)
               (transitivity (wk2 A) (wk2 t) (wk2 u) (var x1) (wk2 eq₂)
                  (transitivity (wk2 A) (wk2 u) (wk2 t) (var x1)
                     (symmetry (wk2 A) (wk2 t) (wk2 u) (wk2 eq₁))
                     (var x0)))
               [ t , rfl ]₁₀                                             ∎) $
          Kⱼ′
            (Idⱼ (rflⱼ (wkTerm₁ ⊢Id-t-t ⊢t)) (var₀ ⊢Id-t-t))
            (rflⱼ $ rflⱼ $
             PE.subst₂ (_⊢_∷_ _)
               (PE.sym $ wk1-sgSubst _ _)
               (PE.sym $ wk1-sgSubst _ _)
               ⊢t)
            (⊢transitivity ⊢eq₂ $
             ⊢transitivity (⊢symmetry ⊢eq₁) (rflⱼ ⊢t))
            ok)
         ⊢eq₁)
      (conv
         (⊢cong
            (⊢transitivity (wkTerm₁ ⊢Id-u-u ⊢eq₂) (var₀ ⊢Id-u-u))
            (⊢transitivity-symmetryˡ ⊢eq₁))
         (Id-cong
            (refl (Idⱼ ⊢t ⊢u))
            (transitivity (wk1 A) (wk1 t) (wk1 u) (wk1 u) (wk1 eq₂)
               (var x0)
               [ transitivity A u t u (symmetry A t u eq₁) eq₁ ]₀       ≡⟨ lemma₂ ⟩⊢≡

             transitivity A t u u eq₂
               (transitivity A u t u (symmetry A t u eq₁) eq₁)          ∎⟨ ⊢transitivity ⊢eq₂ (⊢transitivity (⊢symmetry ⊢eq₁) ⊢eq₁) ⟩⊢)
            (transitivity (wk1 A) (wk1 t) (wk1 u) (wk1 u) (wk1 eq₂)
               (var x0) [ rfl ]₀                                        ≡⟨ lemma₂ ⟩⊢≡

             transitivity A t u u eq₂ rfl                               ≡⟨ transitivity-≡ ⊢eq₂ ⟩⊢∎

             eq₂                                                        ∎)))
      where
      lemma₁ :
        Id (Id (wk2 A) (wk2 t) (var x1)) (var x0)
          (transitivity (wk2 A) (wk2 t) (wk2 u) (var x1) (wk2 eq₂)
             (transitivity (wk2 A) (wk2 u) (wk2 t) (var x1)
                (symmetry (wk2 A) (wk2 t) (wk2 u) (wk2 eq₁))
                (var x0)))
          [ v , eq ]₁₀ PE.≡
        Id (Id A t v) eq
          (transitivity A t u v eq₂
             (transitivity A u t v (symmetry A t u eq₁) eq))
      lemma₁ {v} {eq} =
        Id (Id (wk2 A) (wk2 t) (var x1)) (var x0)
          (transitivity (wk2 A) (wk2 t) (wk2 u) (var x1) (wk2 eq₂)
             (transitivity (wk2 A) (wk2 u) (wk2 t) (var x1)
                (symmetry (wk2 A) (wk2 t) (wk2 u) (wk2 eq₁))
                (var x0)))
          [ v , eq ]₁₀                                                  ≡⟨ PE.cong (Id _ _) $
                                                                           PE.trans transitivity-[] $
                                                                           PE.cong (transitivity _ _ _ _ _) $
                                                                           PE.trans transitivity-[] $
                                                                           PE.cong (flip (transitivity _ _ _ _) _)
                                                                           symmetry-[] ⟩
        Id (Id (wk2 A [ _ ]) (wk2 t [ _ ]) v) eq
          (transitivity (wk2 A [ _ ]) (wk2 t [ _ ]) (wk2 u [ _ ]) v
             (wk2 eq₂ [ _ ])
             (transitivity (wk2 A [ _ ]) (wk2 u [ _ ]) (wk2 t [ _ ]) v
                (symmetry (wk2 A [ _ ]) (wk2 t [ _ ]) (wk2 u [ _ ])
                   (wk2 eq₁ [ _ ]))
                eq))                                                    ≡⟨ PE.cong₃ Id
                                                                             (PE.cong₃ Id wk2-[,] wk2-[,] PE.refl)
                                                                             PE.refl
                                                                             (PE.cong₆ transitivity wk2-[,] wk2-[,] wk2-[,] PE.refl wk2-[,] $
                                                                              PE.cong₆ transitivity wk2-[,] wk2-[,] wk2-[,] PE.refl
                                                                                (PE.cong₄ symmetry wk2-[,] wk2-[,] wk2-[,] wk2-[,])
                                                                                PE.refl) ⟩
        Id (Id A t v) eq
          (transitivity A t u v eq₂
             (transitivity A u t v (symmetry A t u eq₁) eq))            ∎

      lemma₂ :
        transitivity (wk1 A) (wk1 t) (wk1 u) (wk1 u) (wk1 eq₂) (var x0)
          [ eq ]₀ PE.≡
        transitivity A t u u eq₂ eq
      lemma₂ {eq} =
        transitivity (wk1 A) (wk1 t) (wk1 u) (wk1 u) (wk1 eq₂) (var x0)
          [ eq ]₀                                                        ≡⟨ transitivity-[] ⟩

        transitivity (wk1 A [ _ ]₀) (wk1 t [ _ ]₀) (wk1 u [ _ ]₀)
          (wk1 u [ _ ]₀) (wk1 eq₂ [ _ ]₀) eq                             ≡⟨ PE.cong₆ transitivity (wk1-sgSubst _ _) (wk1-sgSubst _ _)
                                                                              (wk1-sgSubst _ _) (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl ⟩
        transitivity A t u u eq₂ eq                                      ∎
