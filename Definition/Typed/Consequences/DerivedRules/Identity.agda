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

open Type-restrictions R

open import Definition.Untyped M
  hiding (_∷_) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
import Definition.Typed.RedSteps R as R
open import Definition.Typed.Weakening R
open import Definition.Untyped.Properties M

import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ Γ₁ Γ₂                                            : Con Term _
  A A₁ A₂ B B₁ B₂ t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  p q                                                : M
  s                                                  : Strength

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

  J-motive-context :
    Γ ⊢ t ∷ A →
    ⊢ Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0)
  J-motive-context ⊢t =
    case syntacticTerm ⊢t of λ {
      ⊢A →
    wf ⊢A ∙ ⊢A ∙ Idⱼ (wkTerm₁ ⊢A ⊢t) (var (wf ⊢A ∙ ⊢A) here) }

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
    Id-cong (wkEq₁ ⊢A₁ A₁≡A₂) (wkEqTerm₁ ⊢A₁ t₁≡t₂)
      (refl (var (wf ⊢A₁ ∙ ⊢A₁) here)) }

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

  K-motive-context : Γ ⊢ t ∷ A → ⊢ Γ ∙ Id A t t
  K-motive-context ⊢t = wfTerm ⊢t ∙ Idⱼ ⊢t ⊢t

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
