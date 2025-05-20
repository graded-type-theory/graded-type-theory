------------------------------------------------------------------------
-- Admissible rules related to identity types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Untyped M as U
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Equality R
import Definition.Typed.Properties.Admissible.Erased.Primitive R as EP
import Definition.Typed.Properties.Admissible.Identity.Primitive
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+; 2+; 3+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

open Definition.Typed.Properties.Admissible.Identity.Primitive R public

private variable
  n                                               : Nat
  Γ Γ₁ Γ₂                                         : Con Term _
  A A₁ A₂ A′ B B₁ B₂ C
    eq eq₁ eq₂ t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ                                               : Subst _ _
  p p′ q q′                                       : M
  b                                               : BinderMode
  s                                               : Strength
  l l₁ l₂                                         : Universe-level

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
      (_ , ⊢t , ⊢v) →
    Jⱼ ⊢t ⊢B ⊢u ⊢v ⊢w }

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
    J-cong A₁≡A₂ (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁) t₁≡t₂

opaque

  -- A variant of the equality rule J-β.

  J-β-≡ :
    Γ ⊢ t ∷ A →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ J p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
  J-β-≡ {Γ} {t} {A} ⊢t ⊢B ⊢u =
    J-β ⊢t ⊢B ⊢u PE.refl
    where
    -- If a strengthening lemma is proved then one can perhaps drop
    -- the first argument of J-β-≡.

    _ : Γ ∙ A ⊢ wk1 t ∷ wk1 A
    _ =
      case wf ⊢B of λ {
        (∙ ⊢Id) →
      case inversion-Id ⊢Id of λ {
        (_ , ⊢wk1-t , _) →
      ⊢wk1-t }}

opaque

  -- A variant of J-subst.

  J-subst′ :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ w₁ ⇒ w₂ ∷ Id A t v →
    Γ ⊢ J p q A t B u v w₁ ⇒ J p q A t B u v w₂ ∷ B [ v , w₁ ]₁₀
  J-subst′ ⊢B ⊢u w₁⇒w₂ =
    case inversion-Id (syntacticTerm (redFirstTerm w₁⇒w₂)) of λ {
      (_ , ⊢t , ⊢v) →
    J-subst ⊢t ⊢B ⊢u ⊢v w₁⇒w₂ }

opaque

  -- A variant of J-subst for _⊢_⇒*_∷_.

  J-subst* :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ w₁ ⇒* w₂ ∷ Id A t v →
    Γ ⊢ J p q A t B u v w₁ ⇒* J p q A t B u v w₂ ∷ B [ v , w₁ ]₁₀
  J-subst* {A} {t} {B} {u} {w₁} {w₂} {v} {p} {q} ⊢B ⊢u = λ where
    (id ⊢w₁)                     → id (Jⱼ′ ⊢B ⊢u ⊢w₁)
    (_⇨_ {t′ = w₃} w₁⇒w₃ w₃⇒*w₂) →
      let w₁≡w₃      = subsetTerm w₁⇒w₃
          _ , _ , ⊢v = inversion-Id (wf-⊢≡∷ w₁≡w₃ .proj₁)
      in
      J p q A t B u v w₁ ∷ B [ v , w₁ ]₁₀  ⇒⟨ J-subst′ ⊢B ⊢u w₁⇒w₃ ⟩∷
                                           ˘⟨ substTypeEq₂ (refl ⊢B) (refl ⊢v)
                                                (PE.subst (_⊢_≡_∷_ _ _ _)
                                                   (PE.sym $
                                                    PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl) $
                                                 sym′ w₁≡w₃) ⟩⇒
      J p q A t B u v w₃ ∷ B [ v , w₃ ]₁₀  ⇒*⟨ J-subst* ⊢B ⊢u w₃⇒*w₂ ⟩∎∷
      J p q A t B u v w₂                   ∎

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
      (_ , ⊢t , ⊢t′) →
    J-β ⊢t ⊢t′ t≡t′ ⊢B (J-motive-rfl-cong (refl ⊢B) t≡t′) }

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context-type :
    Γ ⊢ t ∷ A →
    Γ ∙ A ⊢ Id (wk1 A) (wk1 t) (var x0)
  J-motive-context-type ⊢t =
    case syntacticTerm ⊢t of λ {
      ⊢A →
    Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A) }

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context :
    Γ ⊢ t ∷ A →
    ⊢ Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0)
  J-motive-context ⊢t = ∙ J-motive-context-type ⊢t

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

  -- A variant of K-subst for _⊢_⇒*_∷_.

  K-subst* :
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t t →
    K-allowed →
    Γ ⊢ K p A t B u v₁ ⇒* K p A t B u v₂ ∷ B [ v₁ ]₀
  K-subst* {A} {t} {B} {u} {v₁} {v₂} {p} ⊢B ⊢u v₁⇒*v₂ ok =
    case v₁⇒*v₂ of λ where
      (id ⊢v₁)                     → id (Kⱼ ⊢B ⊢u ⊢v₁ ok)
      (_⇨_ {t′ = v₃} v₁⇒v₃ v₃⇒*v₂) →
        K p A t B u v₁ ∷ B [ v₁ ]₀  ⇒⟨ K-subst ⊢B ⊢u v₁⇒v₃ ok ⟩∷
                                    ˘⟨ substTypeEq (refl ⊢B) (sym′ (subsetTerm v₁⇒v₃)) ⟩⇒
        K p A t B u v₃ ∷ B [ v₃ ]₀  ⇒*⟨ K-subst* ⊢B ⊢u v₃⇒*v₂ ok ⟩∎∷
        K p A t B u v₂              ∎

opaque

  -- A lemma related to the type of one of the assumptions of K.

  K-motive-rfl-cong :
    Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ B₁ [ rfl ]₀ ≡ B₂ [ rfl ]₀
  K-motive-rfl-cong B₁≡B₂ =
    case wfEq B₁≡B₂ of λ {
      (∙ ⊢Id) →
    substTypeEq B₁≡B₂ (refl (rflⱼ (inversion-Id ⊢Id .proj₂ .proj₁))) }

opaque

  -- A lemma related to the context of one of the assumptions of K.

  K-motive-context-type : Γ ⊢ t ∷ A → Γ ⊢ Id A t t
  K-motive-context-type ⊢t = Idⱼ′ ⊢t ⊢t

opaque

  -- A lemma related to the context of one of the assumptions of K.

  K-motive-context : Γ ⊢ t ∷ A → ⊢ Γ ∙ Id A t t
  K-motive-context ⊢t = ∙ K-motive-context-type ⊢t

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

  -- A variant of []-cong-subst for _⊢_⇒*_∷_.

  []-cong-subst* :
    let open Erased s in
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t u →
    []-cong-allowed s →
    Γ ⊢ []-cong s A t u v₁ ⇒* []-cong s A t u v₂ ∷
      Id (Erased A) [ t ] ([ u ])
  []-cong-subst* {s} v₁⇒*v₂ ok =
    let ⊢A , ⊢t , ⊢u =
          inversion-Id (syntacticTerm (redFirst*Term v₁⇒*v₂))
    in
    case v₁⇒*v₂ of λ where
      (id ⊢v₁)         → id ([]-congⱼ ⊢A ⊢t ⊢u ⊢v₁ ok)
      (v₁⇒v₃ ⇨ v₃⇒*v₂) →
        []-cong-subst ⊢A ⊢t ⊢u v₁⇒v₃ ok ⇨ []-cong-subst* v₃⇒*v₂ ok

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

opaque

  -- A variant of the equality rule []-cong-β.

  []-cong-β-≡ :
    Γ ⊢ t ≡ t′ ∷ A →
    []-cong-allowed s →
    let open Erased s in
      Γ ⊢ []-cong s A t t′ rfl ≡ rfl ∷
        Id (Erased A) ([ t ]) ([ t′ ])
  []-cong-β-≡ t≡t′ ok =
    case syntacticEqTerm t≡t′ of λ {
      (⊢A , ⊢t , ⊢t′) →
    case []-cong-cong (refl ⊢A) (refl ⊢t) (sym′ t≡t′)
           (refl (rflⱼ′ t≡t′)) ok of λ
      []-cong-t≡[]-cong-t′ →
    case ([]-cong-β ⊢t PE.refl ok) of λ
      []-cong-⇒ →
    trans []-cong-t≡[]-cong-t′ (conv []-cong-⇒
      (Id-cong (refl (Erasedⱼ ⊢A)) (refl ([]ⱼ ⊢A ⊢t)) ([]-cong′ ⊢A t≡t′))) }
    where
    open EP ([]-cong→Erased ok)

------------------------------------------------------------------------
-- Lemmas related to subst

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

  subst-⇒′ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ≡ t′ ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t t′ rfl u ⇒ u ∷ B [ t ]₀
  subst-⇒′ {B} ⊢B t≡t′ ⊢u =
    case syntacticEqTerm t≡t′ of λ
      (_ , ⊢t , _) →
    PE.subst (_⊢_⇒_∷_ _ _ _) (subst-wk B) $
    J-β-⇒ t≡t′ (wk₁ (J-motive-context-type ⊢t) ⊢B)
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-wk B) ⊢u)

opaque

  -- Another reduction rule for subst.

  subst-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t t rfl u ⇒ u ∷ B [ t ]₀
  subst-⇒ ⊢B ⊢t = subst-⇒′ ⊢B (refl ⊢t)

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

  -- A reduction rule for subst.

  subst-subst* :
    Γ ∙ A ⊢ B →
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t u →
    Γ ⊢ w ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t u v₁ w ⇒* subst p A B t u v₂ w ∷ B [ u ]₀
  subst-subst* ⊢B = λ where
    (id ⊢v)          ⊢w → id (⊢subst ⊢B ⊢v ⊢w)
    (v₁⇒v₃ ⇨ v₃⇒*v₂) ⊢w →
      subst-subst ⊢B v₁⇒v₃ ⊢w ⇨ subst-subst* ⊢B v₃⇒*v₂ ⊢w

opaque
  unfolding subst

  -- An inversion lemma for subst.
  --
  -- If a suitable form of strengthening is proved, then it should be
  -- easy to add Γ ∙ A ⊢ B to the result.

  inversion-subst :
    Γ ⊢ subst p A B t u v w ∷ C →
    (Γ ⊢ A) ×
    Γ ⊢ t ∷ A ×
    Γ ⊢ u ∷ A ×
    Γ ⊢ v ∷ Id A t u ×
    Γ ⊢ w ∷ B [ t ]₀ ×
    Γ ⊢ C ≡ B [ u ]₀
  inversion-subst {B} ⊢subst =
    case inversion-J ⊢subst of λ
      (⊢A , ⊢t , ⊢Id , ⊢w , ⊢u , ⊢v , C≡) →
    ⊢A , ⊢t , ⊢u , ⊢v , PE.subst (_⊢_∷_ _ _) (subst-wk B) ⊢w ,
    PE.subst (_⊢_≡_ _ _) (subst-wk B) C≡

------------------------------------------------------------------------
-- Lemmas related to cast

opaque
  unfolding cast

  -- A typing rule for cast.

  ⊢cast :
    Γ ⊢ t ∷ Id (U l) A B →
    Γ ⊢ u ∷ A →
    Γ ⊢ cast l A B t u ∷ B
  ⊢cast ⊢t ⊢u =
    ⊢subst (univ (var₀ (Uⱼ (wfTerm ⊢t)))) ⊢t ⊢u

opaque
  unfolding cast

  -- A reduction rule for cast.

  cast-⇒′ :
    Γ ⊢ A ≡ A′ ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ cast l A A′ rfl t ⇒ t ∷ A
  cast-⇒′ A≡A′ ⊢t =
    subst-⇒′ (univ (var₀ (Uⱼ (wfTerm ⊢t)))) A≡A′ ⊢t

opaque

  -- Another reduction rule for cast.

  cast-⇒ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ cast l A A rfl t ⇒ t ∷ A
  cast-⇒ ⊢A ⊢t =
    cast-⇒′ (refl ⊢A) ⊢t

opaque

  -- An equality rule for cast.

  cast-≡ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ cast l A A rfl t ≡ t ∷ A
  cast-≡ ⊢A ⊢t =
    subsetTerm (cast-⇒ ⊢A ⊢t)

opaque
  unfolding cast

  -- An equality rule for cast.

  cast-cong :
    Γ ⊢ A₁ ≡ A₂ ∷ U l →
    Γ ⊢ B₁ ≡ B₂ ∷ U l →
    Γ ⊢ t₁ ≡ t₂ ∷ Id (U l) A₁ B₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ cast l A₁ B₁ t₁ u₁ ≡ cast l A₂ B₂ t₂ u₂ ∷ B₁
  cast-cong A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ =
    case inversion-Id (syntacticEqTerm t₁≡t₂ .proj₁) of λ
      (⊢U , ⊢A₁ , ⊢B₁) →
    subst-cong (refl ⊢U) (refl (univ (var₀ ⊢U))) A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂

opaque
  unfolding cast

  -- A reduction rule for cast.

  cast-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Id (U l) A B →
    Γ ⊢ u ∷ A →
    Γ ⊢ cast l A B t₁ u ⇒ cast l A B t₂ u ∷ B
  cast-subst t₁⇒t₂ ⊢u =
    subst-subst (univ (var₀ (Uⱼ (wfTerm ⊢u)))) t₁⇒t₂ ⊢u

opaque

  -- A reduction rule for cast.

  cast-subst* :
    Γ ⊢ t₁ ⇒* t₂ ∷ Id (U l) A B →
    Γ ⊢ u ∷ A →
    Γ ⊢ cast l A B t₁ u ⇒* cast l A B t₂ u ∷ B
  cast-subst* = λ where
    (id ⊢t)          ⊢u → id (⊢cast ⊢t ⊢u)
    (t₁⇒t₃ ⇨ t₃⇒*t₂) ⊢u →
      cast-subst t₁⇒t₃ ⊢u ⇨ cast-subst* t₃⇒*t₂ ⊢u

opaque
  unfolding cast

  -- An inversion lemma for cast.

  inversion-cast :
    Γ ⊢ cast l A B t u ∷ C →
    Γ ⊢ A ∷ U l ×
    Γ ⊢ B ∷ U l ×
    Γ ⊢ t ∷ Id (U l) A B ×
    Γ ⊢ u ∷ A ×
    Γ ⊢ C ≡ B
  inversion-cast ⊢cast =
    case inversion-subst ⊢cast of λ
      (_ , ⊢A , ⊢B , ⊢t , ⊢u , C≡) →
    ⊢A , ⊢B , ⊢t , ⊢u , C≡

------------------------------------------------------------------------
-- Lemmas related to symmetry

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
      (Idⱼ′ (var₀ ⊢A) (wkTerm₁ ⊢A ⊢t))
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
      (Idⱼ′ (var₀ ⊢A) (wkTerm₁ ⊢A ⊢t))
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

------------------------------------------------------------------------
-- Lemmas related to transitivity

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
      (Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A))
      ⊢u
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id≡Id) ⊢eq)

opaque

  -- An equality rule for transitivity.

  transitivity-≡ :
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ transitivity A t u u eq rfl ≡ eq ∷ Id A t u
  transitivity-≡ ⊢eq =
    subsetTerm (transitivity-⇒ ⊢eq)

------------------------------------------------------------------------
-- Lemmas related to transitivity-symmetryˡ

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
    case Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A) of λ
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
      (Idⱼ′
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

                                                                           ⟨ PE.subst (flip (_⊢_≡_ _) _)
                                                                               (PE.sym $ PE.cong₃ Id wk2-[,] PE.refl PE.refl) $
                                                                             refl (Idⱼ′ ⊢t ⊢t) ⟩≡

          transitivity A t t t (symmetry A t t rfl) rfl                   ≡⟨ transitivity-≡ (⊢symmetry (rflⱼ ⊢t)) ⟩⊢

          symmetry A t t rfl                                              ≡⟨ symmetry-≡ ⊢t ⟩⊢∎

          rfl                                                             ∎))
      ⊢eq

------------------------------------------------------------------------
-- Lemmas related to cong

opaque
  unfolding cong

  -- A typing rule for cong.

  ⊢cong :
    Γ ∙ A ⊢ v ∷ wk1 B →
    Γ ⊢ w ∷ Id A t u →
    Γ ⊢ cong p A t u B v w ∷ Id B (v [ t ]₀) (v [ u ]₀)
  ⊢cong ⊢v ⊢w =
    case inversion-Id (syntacticTerm ⊢w) of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl) $
    ⊢subst
      (Idⱼ′
         (PE.subst (_⊢_∷_ _ _) (PE.cong wk1 $ wk1-sgSubst _ _) $
          wkTerm₁ ⊢A (substTerm ⊢v ⊢t))
         ⊢v)
      ⊢w
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $ PE.cong₃ Id PE.refl (wk1-sgSubst _ _) PE.refl) $
       rflⱼ (substTerm ⊢v ⊢t))

opaque
  unfolding cong

  -- An equality rule for cong.

  cong-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ B₁ ≡ B₂ →
    Γ ∙ A₁ ⊢ v₁ ≡ v₂ ∷ wk1 B₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ cong p A₁ t₁ u₁ B₁ v₁ w₁ ≡ cong p A₂ t₂ u₂ B₂ v₂ w₂ ∷
      Id B₁ (v₁ [ t₁ ]₀) (v₁ [ u₁ ]₀)
  cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ B₁≡B₂ v₁≡v₂ w₁≡w₂ =
    case syntacticEqTerm t₁≡t₂ of λ
      (⊢A₁ , ⊢t₁ , _) →
    case syntacticEqTerm v₁≡v₂ of λ
      (_ , ⊢v₁ , _) →
    PE.subst (_⊢_≡_∷_ _ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl) $
    subst-cong A₁≡A₂
      (Id-cong (wkEq₁ ⊢A₁ B₁≡B₂)
         (wkEqTerm₁ ⊢A₁ $
          PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
          substTermEq v₁≡v₂ t₁≡t₂)
         v₁≡v₂)
      t₁≡t₂ u₁≡u₂ w₁≡w₂
      (_⊢_≡_∷_.refl $
       PE.subst (_⊢_∷_ _ _)
         (PE.cong₂ (Id _) (PE.sym $ wk1-sgSubst _ _) PE.refl) $
       rflⱼ $ substTerm ⊢v₁ ⊢t₁)

opaque
  unfolding cong

  -- A β-rule for cong.

  cong-⇒ :
    Γ ⊢ t ∷ A →
    Γ ∙ A ⊢ u ∷ wk1 B →
    Γ ⊢ cong p A t t B u rfl ⇒ rfl ∷ Id B (u [ t ]₀) (u [ t ]₀)
  cong-⇒ ⊢t ⊢u =
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl) $
    subst-⇒
      (Idⱼ′
         (PE.subst (_⊢_∷_ _ _)
            (PE.cong wk1 $ wk1-sgSubst _ _) $
          wkTerm₁ (syntacticTerm ⊢t) (substTerm ⊢u ⊢t))
         ⊢u)
      ⊢t
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $ PE.cong₃ Id PE.refl (wk1-sgSubst _ _) PE.refl) $
       rflⱼ (substTerm ⊢u ⊢t))

opaque

  -- A β-rule for cong.

  cong-≡ :
    Γ ⊢ t ∷ A →
    Γ ∙ A ⊢ u ∷ wk1 B →
    Γ ⊢ cong p A t t B u rfl ≡ rfl ∷ Id B (u [ t ]₀) (u [ t ]₀)
  cong-≡ ⊢t ⊢u =
    subsetTerm (cong-⇒ ⊢t ⊢u)

opaque
  unfolding cong

  -- A reduction rule for cong.

  cong-subst :
    Γ ∙ A ⊢ v ∷ wk1 B →
    Γ ⊢ w₁ ⇒ w₂ ∷ Id A t u →
    Γ ⊢ cong p A t u B v w₁ ⇒ cong p A t u B v w₂ ∷
      Id B (v [ t ]₀) (v [ u ]₀)
  cong-subst ⊢v w₁⇒w₂ =
    case inversion-Id $ syntacticEqTerm (subsetTerm w₁⇒w₂) .proj₁ of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl) $
    subst-subst
      (Idⱼ′
         (PE.subst (_⊢_∷_ _ _) (PE.cong wk1 $ wk1-sgSubst _ _) $
          wkTerm₁ ⊢A (substTerm ⊢v ⊢t))
         ⊢v)
      w₁⇒w₂
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $ PE.cong₃ Id PE.refl (wk1-sgSubst _ _) PE.refl) $
       rflⱼ (substTerm ⊢v ⊢t))

opaque

  -- A reduction rule for cong.

  cong-subst* :
    Γ ∙ A ⊢ v ∷ wk1 B →
    Γ ⊢ w₁ ⇒* w₂ ∷ Id A t u →
    Γ ⊢ cong p A t u B v w₁ ⇒* cong p A t u B v w₂ ∷
      Id B (v [ t ]₀) (v [ u ]₀)
  cong-subst* ⊢v = λ where
    (id ⊢w)          → id (⊢cong ⊢v ⊢w)
    (w₁⇒w₃ ⇨ w₃⇒*w₂) →
      cong-subst ⊢v w₁⇒w₃ ⇨ cong-subst* ⊢v w₃⇒*w₂

------------------------------------------------------------------------
-- Lemmas related to pointwise-equality

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

------------------------------------------------------------------------
-- Lemmas related to uip

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
    case Idⱼ′ ⊢t ⊢t of λ
      ⊢Id-t-t →
    case Idⱼ′ ⊢u ⊢u of λ
      ⊢Id-u-u →
    ⊢transitivity
      (PE.subst (_⊢_∷_ _ _) lemma₁ $
       Jⱼ′
         (Idⱼ′
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
          Kⱼ
            (Idⱼ′ (rflⱼ (wkTerm₁ ⊢Id-t-t ⊢t)) (var₀ ⊢Id-t-t))
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
            (refl (Idⱼ′ ⊢t ⊢u))
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

------------------------------------------------------------------------
-- Function extensionality

opaque

  -- Has-function-extensionality p q l₁ l₂ Γ means that a certain
  -- formulation of function extensionality holds for the context Γ.

  Has-function-extensionality :
    M → M → Universe-level → Universe-level → Con Term n → Set a
  Has-function-extensionality p q l₁ l₂ Γ =
    ∃ λ t →
    Γ ⊢ t ∷
      Π p , q ▷ U l₁ ▹
      Π p , q ▷ (Π p , q ▷ var x0 ▹ U l₂) ▹
      let Π-type = Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) in
      Π p , q ▷ Π-type ▹
      Π p , q ▷ wk1 Π-type ▹
      Π p , q ▷
        (Π p , q ▷ var x3 ▹
         Id (var x3 ∘⟨ p ⟩ var x0)
           (var x2 ∘⟨ p ⟩ var x0)
           (var x1 ∘⟨ p ⟩ var x0)) ▹
      Id (wk[ 3 ]′ Π-type) (var x2) (var x1)

opaque

  -- Extends the context with the assumption that a certain instance
  -- of function extensionality holds.

  with-function-extensionality-assumption :
    M → M → Universe-level → Universe-level →
    Con Term n → Con Term (1+ n)
  with-function-extensionality-assumption p q l₁ l₂ Γ =
    Γ ∙
    Π p , q ▷ U l₁ ▹
    Π p , q ▷ (Π p , q ▷ var x0 ▹ U l₂) ▹
    let Π-type = Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) in
    Π p , q ▷ Π-type ▹
    Π p , q ▷ wk1 Π-type ▹
    Π p , q ▷
      (Π p , q ▷ var x3 ▹
       Id (var x3 ∘⟨ p ⟩ var x0)
         (var x2 ∘⟨ p ⟩ var x0)
         (var x1 ∘⟨ p ⟩ var x0)) ▹
    Id (wk[ 3 ]′ Π-type) (var x2) (var x1)

private opaque

  -- A lemma used below.

  ⊢Π3Id :
    Π-allowed p q →
    ⊢ Γ →
    Γ ∙ U l₁ ∙ Π p , q ▷ var x0 ▹ U l₂ ∙
    Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) ∙
    Π p , q ▷ var x2 ▹ (var x2 ∘⟨ p ⟩ var x0) ⊢
    Π p , q ▷ var x3 ▹
    Id (var x3 ∘⟨ p ⟩ var x0)
      (var x2 ∘⟨ p ⟩ var x0) (var x1 ∘⟨ p ⟩ var x0)
  ⊢Π3Id {p} {q} {Γ} ok ⊢Γ =
    flip _⊢_.ΠΣⱼ ok $
    Idⱼ′ (var₂ ⊢3 ∘ⱼ var₀ ⊢3) (var₁ ⊢3 ∘ⱼ var₀ ⊢3)
    where
    ⊢1 : Γ ∙ U l₁ ∙ Π p , q ▷ var x0 ▹ U l₂ ⊢ var x1
    ⊢1 =
      _⊢_.univ $ var₁ $ flip _⊢_.ΠΣⱼ ok $
      Uⱼ (∙ univ (var₀ (Uⱼ ⊢Γ)))

    ⊢2 :
      Γ ∙ U l₁ ∙ Π p , q ▷ var x0 ▹ U l₂ ∙
      Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) ⊢
      var x2
    ⊢2 =
      _⊢_.univ $ var₂ $ flip _⊢_.ΠΣⱼ ok $
      univ (var₁ ⊢1 ∘ⱼ var₀ ⊢1)

    ⊢3 :
      Γ ∙ U l₁ ∙ Π p , q ▷ var x0 ▹ U l₂ ∙
      Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) ∙
      Π p , q ▷ var x2 ▹ (var x2 ∘⟨ p ⟩ var x0) ⊢
      var x3
    ⊢3 =
      _⊢_.univ $ var₃ $ flip _⊢_.ΠΣⱼ ok $
      univ (var₂ ⊢2 ∘ⱼ var₀ ⊢2)

opaque
  unfolding
    Has-function-extensionality with-function-extensionality-assumption

  -- If Γ is a well-formed context and certain Π-types are allowed,
  -- then the context
  -- with-function-extensionality-assumption p q l₁ l₂ Γ satisfies
  -- Has-function-extensionality p q l₁ l₂.

  Has-function-extensionality-with-function-extensionality-assumption :
    Π-allowed p q →
    ⊢ Γ →
    Has-function-extensionality p q l₁ l₂
      (with-function-extensionality-assumption p q l₁ l₂ Γ)
  Has-function-extensionality-with-function-extensionality-assumption
    ok ⊢Γ =
    let ⊢Π3Id = ⊢Π3Id ok ⊢Γ in
    var x0 ,
    (var₀ $
     flip _⊢_.ΠΣⱼ ok $ flip _⊢_.ΠΣⱼ ok $ flip _⊢_.ΠΣⱼ ok $
     flip _⊢_.ΠΣⱼ ok $ flip _⊢_.ΠΣⱼ ok $
     Idⱼ′ (var₂ ⊢Π3Id) (var₁ ⊢Π3Id))

------------------------------------------------------------------------
-- Some lemmas related to equality-reflection

opaque

  -- A variant of equality-reflection.

  equality-reflection′ :
    Equality-reflection →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ t ≡ u ∷ A
  equality-reflection′ ok ⊢v =
    equality-reflection ok (wf-⊢∷ ⊢v) ⊢v

opaque

  -- If equality reflection is allowed and the context is inconsistent
  -- (in a certain sense), then any two well-typed terms of the same
  -- type are "definitionally" equal to each other.

  ⊢∷Empty→⊢≡∷ :
    Equality-reflection →
    Γ ⊢ t ∷ Empty →
    Γ ⊢ u ∷ A →
    Γ ⊢ v ∷ A →
    Γ ⊢ u ≡ v ∷ A
  ⊢∷Empty→⊢≡∷ ok ⊢t ⊢u ⊢v =
    equality-reflection′ ok (emptyrecⱼ {p = ω} (Idⱼ′ ⊢u ⊢v) ⊢t)

opaque

  -- In the presence of equality reflection one can prove (one variant
  -- of) function extensionality.

  function-extensionality-∙ :
    Equality-reflection →
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ Π p , q ▷ A ▹ B →
    Γ ∙ A ⊢ v ∷ Id B (wk1 t ∘⟨ p ⟩ var x0) (wk1 u ∘⟨ p ⟩ var x0) →
    Γ ⊢ rfl ∷ Id (Π p , q ▷ A ▹ B) t u
  function-extensionality-∙ ok ⊢t ⊢u ⊢v =
    rflⱼ′ $ η-eq′ ⊢t ⊢u $ equality-reflection′ ok ⊢v

opaque

  -- In the presence of equality reflection one can prove (another
  -- variant of) function extensionality.

  function-extensionality-Π :
    Equality-reflection →
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ v ∷
      Π p , q ▷ A ▹ Id B (wk1 t ∘⟨ p ⟩ var x0) (wk1 u ∘⟨ p ⟩ var x0) →
    Γ ⊢ rfl ∷ Id (Π p , q ▷ A ▹ B) t u
  function-extensionality-Π ok ⊢t ⊢u ⊢v =
    let ⊢A , _ , _ = inversion-ΠΣ (syntacticTerm ⊢t) in
    function-extensionality-∙ ok ⊢t ⊢u $
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₃ Id
         (wkSingleSubstId _)
         (PE.cong₃ _∘⟨_⟩_ (wkSingleSubstId _) PE.refl PE.refl)
         (PE.cong₃ _∘⟨_⟩_ (wkSingleSubstId _) PE.refl PE.refl))
      (wkTerm₁ ⊢A ⊢v ∘ⱼ var₀ ⊢A)

opaque
  unfolding Has-function-extensionality

  -- In the presence of equality reflection
  -- Has-function-extensionality p q holds for every well-formed
  -- context (assuming that Π-allowed p q holds).

  has-function-extensionality :
    Equality-reflection →
    Π-allowed p q →
    ⊢ Γ →
    Has-function-extensionality p q l₁ l₂ Γ
  has-function-extensionality {p} ok Π-ok ⊢Γ =
    let ⊢Π3Id = ⊢Π3Id Π-ok ⊢Γ in
    lam p (lam p (lam p (lam p (lam p rfl)))) ,
    (lamⱼ′ Π-ok $ lamⱼ′ Π-ok $ lamⱼ′ Π-ok $ lamⱼ′ Π-ok $ lamⱼ′ Π-ok $
     function-extensionality-Π ok (var₂ ⊢Π3Id) (var₁ ⊢Π3Id)
       (var₀ ⊢Π3Id))

opaque

  -- In the presence of equality reflection one can prove a
  -- definitional variant of UIP.

  uip-with-equality-reflection-≡ :
    Equality-reflection →
    Γ ⊢ eq₁ ∷ Id A t u →
    Γ ⊢ eq₂ ∷ Id A t u →
    Γ ⊢ eq₁ ≡ eq₂ ∷ Id A t u
  uip-with-equality-reflection-≡ ok ⊢eq₁ ⊢eq₂ =
    trans (lemma ⊢eq₁) (sym′ (lemma ⊢eq₂))
    where
    lemma : Γ ⊢ eq ∷ Id A t u → Γ ⊢ eq ≡ rfl ∷ Id A t u
    lemma ⊢eq =
      let ⊢A , ⊢t , _ = inversion-Id (syntacticTerm ⊢eq)
          ⊢Id         = var₀ $ Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A)
      in
      equality-reflection′ ok $
      PE.subst (_⊢_∷_ _ _)
        (PE.cong₃ Id
           (PE.cong₃ Id wk2-[,] wk2-[,] PE.refl) PE.refl PE.refl) $
      Jⱼ′ {p = ω} {q = ω}
        (Idⱼ′ ⊢Id (rflⱼ′ (equality-reflection′ ok ⊢Id)))
        (rflⱼ $
         PE.subst (_⊢_∷_ _ _)
           (PE.sym $ PE.cong₃ Id wk2-[,] wk2-[,] PE.refl) $
         rflⱼ ⊢t)
        ⊢eq

opaque

  -- In the presence of equality reflection one can prove a variant of
  -- UIP.

  uip-with-equality-reflection-Id :
    Equality-reflection →
    Γ ⊢ eq₁ ∷ Id A t u →
    Γ ⊢ eq₂ ∷ Id A t u →
    Γ ⊢ rfl ∷ Id (Id A t u) eq₁ eq₂
  uip-with-equality-reflection-Id ok ⊢eq₁ ⊢eq₂ =
    rflⱼ′ (uip-with-equality-reflection-≡ ok ⊢eq₁ ⊢eq₂)

opaque

  -- In the presence of equality reflection one can define a variant
  -- of []-cong.

  []-cong-with-equality-reflection :
    let open Erased s in
    Equality-reflection →
    Erased-allowed s →
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ rfl ∷ Id (Erased A) [ t ] ([ u ])
  []-cong-with-equality-reflection ok₁ ok₂ ⊢eq =
    let ⊢A , _ = inversion-Id (syntacticTerm ⊢eq) in
    rflⱼ′ (EP.[]-cong′ ok₂ ⊢A (equality-reflection′ ok₁ ⊢eq))

------------------------------------------------------------------------
-- A preservation lemma

private opaque

  -- A variant of the J rule.

  J′ :
    ∀ {a p} {A : Set a} {x y : A}
    (P : ∀ y → x PE.≡ y → Set p) →
    P x PE.refl →
    (x≡y : x PE.≡ y) →
    P y x≡y
  J′ _ p PE.refl = p

  -- The following code illustrates roughly how ΠΣ-cong-Idˡ below is
  -- defined.

  Π-cong-Idˡ′ :
    ∀ {a b} →
    Function-extensionality a (lsuc b) →
    {A₁ A₂ : Set a} {B₁ : A₁ → Set b} {B₂ : A₂ → Set b} →
    (A₁≡A₂ : A₁ PE.≡ A₂) →
    ((x : A₁) → B₁ x PE.≡ B₂ (PE.subst (λ A → A) A₁≡A₂ x)) →
    ((x : A₁) → B₁ x) PE.≡ ((x : A₂) → B₂ x)
  Π-cong-Idˡ′ {b} fe {A₁} {A₂} {B₁} {B₂} A₁≡A₂ B₁≡B₂ =
    J′ (λ A₂ A₁≡A₂ →
          {B₂ : A₂ → Set b} →
          ((x : A₁) → B₁ x PE.≡ B₂ (PE.subst (λ A → A) A₁≡A₂ x)) →
          ((x : A₁) → B₁ x) PE.≡ ((x : A₂) → B₂ x))
       (λ {B₂} B₁≡B₂ →
          PE.cong (λ B → (x : A₁) → B x) {x = B₁} {y = B₂}
            (ext {A = A₁} {P = λ _ → Set b} {f = B₁} {g = B₂} fe B₁≡B₂))
       A₁≡A₂ B₁≡B₂

opaque
  unfolding Has-function-extensionality

  -- Allowed Π- and Σ-types preserve propositional equality in a
  -- certain sense, assuming that a certain form of function
  -- extensionality can be proved (and that some Π-type is allowed).

  ΠΣ-cong-Idˡ :
    {Γ : Con Term n} →
    ΠΣ-allowed b p q →
    Π-allowed p′ q′ →
    Has-function-extensionality p′ q′ l₁ (1+ l₂) Γ →
    Γ ∙ A₂ ⊢ B₂ ∷ U l₂ →
    Γ ⊢ t ∷ Id (U l₁) A₁ A₂ →
    Γ ∙ A₁ ⊢ u ∷
      Id (U l₂) B₁
        (B₂ [ cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t) (var x0) ]↑) →
    ∃ λ v →
      Γ ⊢ v ∷
        Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
          (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
  ΠΣ-cong-Idˡ
    {n} {b} {p} {q} {p′} {q′} {l₁} {l₂} {A₂} {B₂} {t} {A₁} {u} {B₁} {Γ}
    ok ok′ (ext , ⊢ext) ⊢B₂ ⊢t ⊢u =
    J-app ∘⟨ p′ ⟩ lam p′ B₂ ∘⟨ p′ ⟩ lam p′ u , ⊢J∘∘
    where
    opaque
      ⊢A₁ : Γ ⊢ A₁ ∷ U l₁
      ⊢A₁ = inversion-Id (wf-⊢∷ ⊢t) .proj₂ .proj₁

    opaque
      ⊢A₂ : Γ ⊢ A₂ ∷ U l₁
      ⊢A₂ = inversion-Id (wf-⊢∷ ⊢t) .proj₂ .proj₂

    opaque
      ⊢B₁ : Γ ∙ A₁ ⊢ B₁ ∷ U l₂
      ⊢B₁ = inversion-Id (wf-⊢∷ ⊢u) .proj₂ .proj₁

    opaque
      ∙⊢Id : Γ ∙ U l₁ ⊢ Id (U l₁) (wk1 A₁) (var x0)
      ∙⊢Id = Idⱼ′ (wkTerm₁ (wf-⊢∷ ⊢A₁) ⊢A₁) (var₀ (wf-⊢∷ ⊢A₁))

    opaque
      ∙²⊢ΠU :
        Γ ∙ U l₁ ∙ Id (U l₁) (wk1 A₁) (var x0) ⊢
        Π p′ , q′ ▷ var x1 ▹ U l₂
      ∙²⊢ΠU = ΠΣⱼ (Uⱼ (∙ univ (var₁ ∙⊢Id))) ok′

    opaque
      ∙³⊢A₁ :
        Γ ∙ U l₁ ∙ Id (U l₁) (wk1 A₁) (var x0) ∙
        Π p′ , q′ ▷ var x1 ▹ U l₂ ⊢
        wk[ 3 ] A₁
      ∙³⊢A₁ =
        PE.subst (_⊢_ _) (PE.sym wk[]≡wk[]′) $
        _⊢_.univ $ wkTerm (ʷ⊇-drop (∙ ∙²⊢ΠU)) ⊢A₁

    ΠId : ∀ k → (_ _ _ : Term (1+ (k N.+ n))) → Term (k N.+ n)
    ΠId k C D t =
      Π p′ , q′ ▷ wk[ k ] A₁ ▹
      Id (U l₂) (B₁ [ 1+ k ][ var x0 ]↑)
        (C ∘⟨ p′ ⟩ cast l₁ (wk[ 1+ k ]′ A₁) D t (var x0))

    opaque
      ⊢ΠId :
        {k : Nat} {Δ : Con Term (k N.+ n)}
        {C D t : Term (1+ (k N.+ n))} →
        drop k Δ PE.≡ Γ →
        Δ ∙ wk[ k ] A₁ ⊢ C ∷ Π p′ , q′ ▷ D ▹ U l₂ →
        Δ ∙ wk[ k ] A₁ ⊢ t ∷ Id (U l₁) (wk[ 1+ k ]′ A₁) D →
        Δ ⊢ ΠId k C D t
      ⊢ΠId {k} {Δ} PE.refl ⊢C ⊢t =
        flip _⊢_.ΠΣⱼ ok′ $
        Idⱼ′ (subst-⊢∷ ⊢B₁ (⊢ˢʷ∷-[][]↑ (var₀ (univ ⊢wk[k]A₁∷))))
          (⊢C ∘ⱼ
           ⊢cast ⊢t
             (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
              var₀ (univ ⊢wk[k]A₁∷)))
        where
        ⊢wk[k]A₁∷ : Δ ⊢ wk[ k ] A₁ ∷ U l₁
        ⊢wk[k]A₁∷ =
          PE.subst₂ (_⊢_∷_ _) (PE.sym wk[]≡wk[]′) PE.refl $
          wkTerm (ʷ⊇-drop (wf (⊢∙→⊢ (wf (wf-⊢∷ ⊢C))))) ⊢A₁

    ΠId-lam : Term n
    ΠId-lam = ΠId 0 (wk1 (lam p′ B₂)) (wk1 A₂) (wk1 t)

    opaque
      ⊢ΠId-lam : Γ ⊢ ΠId-lam
      ⊢ΠId-lam =
        ⊢ΠId PE.refl (wkTerm₁ (univ ⊢A₁) (lamⱼ′ ok′ ⊢B₂))
          (wkTerm₁ (univ ⊢A₁) ⊢t)

    opaque
      ΠId-lam⊢A₂ : Γ ∙ ΠId-lam ⊢ wk1 A₂ ∷ U l₁
      ΠId-lam⊢A₂ = wkTerm₁ ⊢ΠId-lam ⊢A₂

    ΠId-1 : Term (3+ n)
    ΠId-1 = ΠId 3 (var x1) (var x3) (var x2)

    opaque
      ⊢ΠId-1 :
        Γ ∙ U l₁ ∙ Id (U l₁) (wk1 A₁) (var x0) ∙
        Π p′ , q′ ▷ var x1 ▹ U l₂ ⊢
        ΠId-1
      ⊢ΠId-1 =
        ⊢ΠId PE.refl (var₁ ∙³⊢A₁)
          (PE.subst (_⊢_∷_ _ _)
             (PE.cong₂ (Id _) wk[]≡wk[]′ PE.refl) $
           var₂ ∙³⊢A₁)

    opaque
      ⊢ΠId-1[] :
        Γ ∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ⊢
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ]
      ⊢ΠId-1[] =
        subst-⊢ ⊢ΠId-1 $
        ⊢ˢʷ∷-⇑′ ∙²⊢ΠU $
        →⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢A₁) $
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₂ (Id _) (PE.sym $ wk1-sgSubst _ _) PE.refl) $
        rflⱼ ⊢A₁

    opaque
      ∙⊢A₁ : Γ ∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ⊢ wk1 A₁ ∷ U l₁
      ∙⊢A₁ = wkTerm₁ (ΠΣⱼ (Uⱼ (∙ univ ⊢A₁)) ok′) ⊢A₁

    opaque
      ∙²⊢A₁ :
        Γ ∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ ∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ⊢
        wk[ 2 ]′ A₁ ∷ U l₁
      ∙²⊢A₁ = wkTerm (stepʷ ⊇-drop ⊢ΠId-1[]) ⊢A₁

    opaque
      ∙³⊢U₂ :
        Γ ∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ ∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ∙ wk[ 2 ]′ A₁ ⊢
        U l₂ ∷ U (1+ l₂)
      ∙³⊢U₂ = Uⱼ (∙ univ ∙²⊢A₁)

    opaque
      ∙³⊢A₁′ :
        Γ ∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ ∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ∙ wk[ 2 ]′ A₁ ⊢
        wk[ 3 ]′ A₁ ∷ U l₁
      ∙³⊢A₁′ = wkTerm (stepʷ ⊇-drop (univ ∙²⊢A₁)) ⊢A₁

    opaque
      ∙³⊢A₁″ :
        Γ ∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ ∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ∙
        ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ wk[ 2 ]′ A₁ ▹ U l₂ ⊢
        wk[ 3 ]′ A₁ ∷ U l₁
      ∙³⊢A₁″ = wkTerm (stepʷ ⊇-drop (univ (ΠΣⱼ ∙²⊢A₁ ∙³⊢U₂ ok′))) ⊢A₁

    Motive : Term (2+ n)
    Motive =
      Π p′ , q′ ▷ (Π p′ , q′ ▷ var x1 ▹ U l₂) ▹
      Π p′ , q′ ▷ ΠId-1 ▹
      Id (U (l₁ ⊔ᵘ l₂)) (wk[ 4 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
        (ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0))

    opaque
      ⊢Π20 :
        Γ ∙ U l₁ ∙ Id (U l₁) (wk1 A₁) (var x0) ∙
        Π p′ , q′ ▷ var x1 ▹ U l₂ ∙ ΠId-1 ⊢
        ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0) ∷
        wk[ 4 ]′ (U (l₁ ⊔ᵘ l₂))
      ⊢Π20 =
        ΠΣⱼ (var₃ ⊢ΠId-1)
          (var₂ (univ (var₃ ⊢ΠId-1)) ∘ⱼ var₀ (univ (var₃ ⊢ΠId-1))) ok

    opaque
      ⊢Π20′ :
        Γ ∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ⊢
        ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₁ ▹ (var x2 ∘⟨ p′ ⟩ var x0) ∷
        U (l₁ ⊔ᵘ l₂)
      ⊢Π20′ =
        ΠΣⱼ ∙²⊢A₁
          (var₂ (univ ∙²⊢A₁) ∘ⱼ
           PE.subst (_⊢_∷_ _ _) (PE.sym $ PE.cong wk1 wk[]≡wk[]′)
             (var₀ (univ ∙²⊢A₁)))
          ok

    opaque
      ⊢Π10 :
        Γ ∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ∙
        wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂) ⊢
        ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0) ∷
        U (l₁ ⊔ᵘ l₂)
      ⊢Π10 =
        ΠΣⱼ ∙³⊢A₁″
          (var₁ (univ ∙³⊢A₁″) ∘ⱼ
           PE.subst (_⊢_∷_ _ _) (PE.sym $ PE.cong wk1 $ wk-comp _ _ _)
             (var₀ (univ ∙³⊢A₁″)))
          ok

    opaque
      ⊢Motive : Γ ∙ U l₁ ∙ Id (U l₁) (wk1 A₁) (var x0) ⊢ Motive
      ⊢Motive =
        flip _⊢_.ΠΣⱼ ok′ $
        flip _⊢_.ΠΣⱼ ok′ $
        Idⱼ′ (wkTerm (ʷ⊇-drop (∙ ⊢ΠId-1)) (ΠΣⱼ ⊢A₁ ⊢B₁ ok)) ⊢Π20

    opaque
      ⊢U≡λU0 : Γ ∙ A₁ ⊢ U l₂ ≡ lam p′ (U l₂) ∘⟨ p′ ⟩ var x0 ∷ U (1+ l₂)
      ⊢U≡λU0 =
        sym′ $
        β-red-≡ (Uⱼ (∙ wk₁ (univ ⊢A₁) (univ ⊢A₁))) (var₀ (univ ⊢A₁)) ok′

    opaque
      ⊢10 :
        Γ ∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ∙ wk1 A₁ ⊢
        var x1 ∘⟨ p′ ⟩ var x0 ∷ U l₂
      ⊢10 = var₁ (univ ∙⊢A₁) ∘ⱼ var₀ (univ ∙⊢A₁)

    opaque
      ⊢ΠId′ :
        Γ ∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ⊢
        Π p′ , q′ ▷ wk1 A₁ ▹
        Id (U l₂) (B₁ [ 2 ][ var x0 ]↑) (var x1 ∘⟨ p′ ⟩ var x0)
      ⊢ΠId′ =
        flip ΠΣⱼ ok′ $
        Idⱼ′ (subst-⊢∷ ⊢B₁ (⊢ˢʷ∷-[][]↑ (var₀ (univ ∙⊢A₁)))) ⊢10

    opaque
      ∙²⊢A₁′ :
        Γ ∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ∙
        Π p′ , q′ ▷ wk1 A₁ ▹
          Id (U l₂) (B₁ [ 2 ][ var x0 ]↑) (var x1 ∘⟨ p′ ⟩ var x0) ⊢
        wk[ 2 ]′ A₁ ∷ U l₁
      ∙²⊢A₁′ = wkTerm (stepʷ ⊇-drop ⊢ΠId′) ⊢A₁

    ext∘³ : Term n
    ext∘³ =
      ext ∘⟨ p′ ⟩ A₁ ∘⟨ p′ ⟩ lam p′ (U l₂) ∘⟨ p′ ⟩ lam p′ B₁

    opaque
      ⊢ext∘³ :
        Γ ⊢
        ext∘³ ∷
        Π p′ , q′ ▷ (Π p′ , q′ ▷ A₁ ▹ U l₂) ▹
        Π p′ , q′ ▷
          (Π p′ , q′ ▷ wk1 A₁ ▹
           Id (U l₂) (B₁ [ 2 ][ var x0 ]↑)
             (var x1 ∘⟨ p′ ⟩ var x0)) ▹
        Id (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂))
          (wk[ 2 ]′ (lam p′ B₁)) (var x1)
      ⊢ext∘³ =
        conv
          (((⊢ext ∘ⱼ ⊢A₁) ∘ⱼ
            lamⱼ′ ok′ (Uⱼ (∙ univ ⊢A₁))) ∘ⱼ
           (_⊢_∷_.conv (lamⱼ′ ok′ ⊢B₁) $ univ
              (Π p′ , q′ ▷ A₁ ▹ U l₂                    ≡⟨ ΠΣ-cong
                                                             (PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) PE.refl $
                                                              refl ⊢A₁)
                                                             ⊢U≡λU0 ok′ ⟩⊢∎
               Π p′ , q′ ▷ wk1 A₁ [ lam p′ (U l₂) ]₀ ▹
               (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)           ∎)))
          (_⊢_≡_.univ $ sym′
             (Π p′ , q′ ▷ (Π p′ , q′ ▷ A₁ ▹ U l₂) ▹
              Π p′ , q′ ▷
                (Π p′ , q′ ▷ wk1 A₁ ▹
                 Id (U l₂) (B₁ [ 2 ][ var x0 ]↑)
                   (var x1 ∘⟨ p′ ⟩ var x0)) ▹
              Id (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂))
                (wk[ 2 ]′ (lam p′ B₁)) (var x1)                        ≡⟨ ΠΣ-cong
                                                                            (ΠΣ-cong (refl ⊢A₁) ⊢U≡λU0 ok′)
                                                                            (ΠΣ-cong
                                                                               (ΠΣ-cong
                                                                                  (refl ∙⊢A₁)
                                                                                  (Id-cong
                                                                                     (wkEqTerm (liftʷ ⊇-drop (univ ∙⊢A₁)) ⊢U≡λU0)
                                                                                     (PE.subst₃ (_⊢_≡_∷_ _) (PE.sym $ [][]↑≡ B₁) PE.refl PE.refl $
                                                                                      sym′ $
                                                                                      β-red-≡
                                                                                        (PE.subst₃ _⊢_∷_
                                                                                           (PE.cong (_∙_ _) (PE.sym wk[]≡wk[]′)) PE.refl PE.refl $
                                                                                         wkTerm
                                                                                           (liftʷ ⊇-drop $
                                                                                            univ (wkTerm (stepʷ ⊇-drop (univ ∙⊢A₁)) ⊢A₁))
                                                                                           ⊢B₁)
                                                                                        (var₀ (univ ∙⊢A₁)) ok′)
                                                                                     (refl ⊢10))
                                                                                  ok′)
                                                                               (Id-cong
                                                                                  (ΠΣ-cong
                                                                                     (refl ∙²⊢A₁′)
                                                                                     (wkEqTerm (liftʷ ⊇-drop (univ ∙²⊢A₁′)) ⊢U≡λU0)
                                                                                     ok′)
                                                                                  (_⊢_≡_∷_.refl $
                                                                                   wkTerm (stepʷ ⊇-drop ⊢ΠId′) (lamⱼ′ ok′ ⊢B₁))
                                                                                  (_⊢_≡_∷_.refl $
                                                                                   PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
                                                                                   var₁ ⊢ΠId′))
                                                                               ok′)
                                                                            ok′ ⟩⊢∎≡
              Π p′ , q′ ▷
                (Π p′ , q′ ▷ A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)) ▹
              Π p′ , q′ ▷
                (Π p′ , q′ ▷ wk1 A₁ ▹
                 Id (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)
                   (wk[ 2 ]′ (lam p′ B₁) ∘⟨ p′ ⟩ var x0)
                   (var x1 ∘⟨ p′ ⟩ var x0)) ▹
              Id
                (wk[ 2 ]′
                   (Π p′ , q′ ▷ A₁ ▹ (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)))
                (wk[ 2 ]′ (lam p′ B₁)) (var x1)                        ≡˘⟨ PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                             (PE.cong₂ (Π p′ , q′ ▷_▹_) wk2-[,] PE.refl)
                                                                             (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                                (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                                   (PE.trans (PE.cong _[ _ ] $ wk[]≡wk[]′ {t = A₁})
                                                                                    wk[2+]′[,⇑]≡)
                                                                                   (PE.cong₂ (Id _)
                                                                                      (PE.cong₃ _∘⟨_⟩_ (wk-comp _ _ _) PE.refl PE.refl)
                                                                                      PE.refl))
                                                                                (PE.cong₃ Id
                                                                                   (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                                      (PE.trans (PE.cong _[ _ ] $ wk[]≡wk[]′ {t = A₁})
                                                                                       wk[2+]′[,⇑]≡)
                                                                                      PE.refl)
                                                                                   (wk-comp _ _ _)
                                                                                   PE.refl)) ⟩
              Π p′ , q′ ▷
                (Π p′ , q′ ▷ wk[ 2 ] A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)) ▹
              Π p′ , q′ ▷
                (Π p′ , q′ ▷ wk[ 3 ] A₁ ▹
                 Id (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)
                   (var x2 ∘⟨ p′ ⟩ var x0) (var x1 ∘⟨ p′ ⟩ var x0)) ▹
              Id
                (Π p′ , q′ ▷ wk[ 4 ] A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0))
                (var x2) (var x1)
              [ lam p′ (U l₂) , lam p′ B₁ ]₁₀                          ≡˘⟨ singleSubstComp _ _
                                                                             (Π _ , _ ▷ (Π _ , _ ▷ wk[ _ ] A₁ ▹ (lam _ (U _) ∘⟨ _ ⟩ var x0)) ▹
                                                                              Π _ , _ ▷
                                                                                (Π _ , _ ▷ wk[ _ ] A₁ ▹
                                                                                 Id (lam _ (U _) ∘⟨ _ ⟩ var x0) (var x2 ∘⟨ _ ⟩ var x0)
                                                                                   (var x1 ∘⟨ _ ⟩ var x0)) ▹
                                                                              Id (Π _ , _ ▷ wk[ 4 ] A₁ ▹ (lam _ (U _) ∘⟨ _ ⟩ var x0)) (var x2)
                                                                                (var x1)) ⟩
              Π p′ , q′ ▷
                (Π p′ , q′ ▷ wk[ 2 ] A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)) ▹
              Π p′ , q′ ▷
                (Π p′ , q′ ▷ wk[ 3 ] A₁ ▹
                 Id (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)
                   (var x2 ∘⟨ p′ ⟩ var x0) (var x1 ∘⟨ p′ ⟩ var x0)) ▹
              Id
                (Π p′ , q′ ▷ wk[ 4 ] A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0))
                (var x2) (var x1)
              [ sgSubst (lam p′ (U l₂)) ⇑ ] [ lam p′ B₁ ]₀             ∎))

    opaque
      ⊢ext∘⁴ :
        Γ ∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ ∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ⊢
        wk[ 2 ]′ ext∘³ ∘⟨ p′ ⟩ var x1 ∷
        Π p′ , q′ ▷
          (Π p′ , q′ ▷ wk[ 2 ]′ A₁ ▹
           Id (U l₂) (B₁ [ 3 ][ var x0 ]↑)
             (var x2 ∘⟨ p′ ⟩ var x0)) ▹
        Id (wk[ 3 ]′ (ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂))
          (wk[ 3 ]′ (lam p′ B₁)) (var x2)
      ⊢ext∘⁴ =
        PE.subst (_⊢_∷_ _ _)
          (Π p′ , q′ ▷
             (U.wk (lift (stepn id 2)) $
              Π p′ , q′ ▷ wk1 A₁ ▹
              Id (U l₂) (B₁ [ 2 ][ var x0 ]↑) (var x1 ∘⟨ p′ ⟩ var x0)) ▹
           Id
             (U.wk (liftn (stepn id 2) 2)
                (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂)))
             (U.wk (liftn (stepn id 2) 2) (wk[ 2 ]′ (lam p′ B₁)))
             (var x1)
           [ var x1 ]₀                                                    ≡⟨ PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                               (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                                  (PE.trans (PE.sym $ [][]↑≡ (wk1 A₁))
                                                                                   wk1-[][]↑′)
                                                                                  (PE.cong₂ (Id _)
                                                                                     (PE.trans (subst-wk (B₁ [ 2 ][ _ ]↑)) $
                                                                                      PE.trans (substCompEq B₁) $
                                                                                      flip substVar-to-subst B₁ λ where
                                                                                        x0     → PE.refl
                                                                                        (_ +1) → PE.refl)
                                                                                     PE.refl))
                                                                               (PE.cong₃ Id
                                                                                  (PE.trans (subst-wk (wk[ 2 ]′ (Π _ , _ ▷ A₁ ▹ U _))) $
                                                                                   PE.trans (subst-wk (Π _ , _ ▷ A₁ ▹ U _)) $
                                                                                   PE.sym $ wk≡subst _ _)
                                                                                  (PE.trans (subst-wk (wk[ 2 ]′ (lam _ B₁))) $
                                                                                   PE.trans (subst-wk (lam _ B₁)) $
                                                                                   PE.sym $ wk≡subst _ _)
                                                                                  PE.refl) ⟩
          Π p′ , q′ ▷
            (Π p′ , q′ ▷ wk[ 2 ]′ A₁ ▹
             Id (U l₂) (B₁ [ 3 ][ var x0 ]↑) (var x2 ∘⟨ p′ ⟩ var x0)) ▹
          Id (wk[ 3 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂)) (wk[ 3 ]′ (lam p′ B₁))
            (var x2)                                                      ∎) $
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₂ (Π p′ , q′ ▷_▹_) (PE.sym wk[]≡wk[]′) PE.refl)
          (wkTerm (stepʷ ⊇-drop ⊢ΠId-1[]) ⊢ext∘³) ∘ⱼ
        var₁ ⊢ΠId-1[]

    opaque
      ⊢ext∘⁵ :
        Γ ∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ ∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ⊢
        wk[ 2 ]′ ext∘³ ∘⟨ p′ ⟩ var x1 ∘⟨ p′ ⟩ var x0 ∷
        Id (wk[ 2 ]′ (ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂))
          (wk[ 2 ]′ (lam p′ B₁)) (var x1)
      ⊢ext∘⁵ =
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₃ Id (step-sgSubst _ _) (step-sgSubst _ _) PE.refl) $
        ⊢ext∘⁴ ∘ⱼ
        (_⊢_∷_.conv (var₀ ⊢ΠId-1[]) $ univ
           (wk1 (ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ])             ≡⟨ PE.trans
                                                                          (PE.cong wk1 $
                                                                           PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                             (PE.trans
                                                                                (PE.cong _[ consSubst (sgSubst _) _ ⇑ ] $
                                                                                 wk[]≡wk[]′ {t = A₁})
                                                                              wk[2+]′[,⇑]≡)
                                                                             (PE.cong₂ (Id _)
                                                                                (PE.trans ([][]↑-[,⇑] 2 B₁) $
                                                                                 [1+][0]↑ {t = B₁})
                                                                                (PE.cong (var x1 ∘⟨ _ ⟩_) $
                                                                                 PE.trans cast-[] $
                                                                                 PE.cong₄ (cast _)
                                                                                   wk[2+]′[,⇑]≡ wk[]≡wk[]′ PE.refl PE.refl))) $
                                                                        PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                          wk[]≡wk[]′
                                                                          (PE.cong₂ (Id _)
                                                                             (PE.trans (wk-comp _ _ _) $
                                                                              PE.sym [1+][0]↑)
                                                                             (PE.cong (_ ∘⟨ _ ⟩_) $
                                                                              PE.trans wk-cast $
                                                                              PE.cong₄ (cast _)
                                                                                (wk-comp _ _ _) (wk-comp _ _ _) PE.refl PE.refl)) ⟩⊢≡
            Π p′ , q′ ▷ wk[ 2 ]′ A₁ ▹
            Id (U l₂) (B₁ [ 3 ][ var x0 ]↑)
              (var x2 ∘⟨ p′ ⟩
               cast l₁ (wk[ 3 ]′ A₁) (wk[ 3 ]′ A₁) rfl (var x0))     ≡⟨ ΠΣ-cong
                                                                          (refl ∙²⊢A₁)
                                                                          (Id-cong
                                                                             (refl ∙³⊢U₂)
                                                                             (_⊢_≡_∷_.refl $ subst-⊢∷ ⊢B₁ $ ⊢ˢʷ∷-[][]↑ $
                                                                              PE.subst₃ _⊢_∷_ (PE.cong (_∙_ _) wk[]≡wk[]′) PE.refl PE.refl $
                                                                              var₀ (PE.subst (_⊢_ _) (PE.sym wk[]≡wk[]′) (univ ∙²⊢A₁)))
                                                                             (app-cong
                                                                                (refl (var₂ (univ ∙²⊢A₁)))
                                                                                (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym wk[]≡wk[]′) $
                                                                                 cast-≡ ∙³⊢A₁′ $
                                                                                 PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
                                                                                 var₀ (univ ∙²⊢A₁))))
                                                                          ok′ ⟩⊢∎≡
            Π p′ , q′ ▷ wk[ 2 ]′ A₁ ▹
            Id (U l₂) (B₁ [ 3 ][ var x0 ]↑) (var x2 ∘⟨ p′ ⟩ var x0)  ∎))

    rfl-case : Term n
    rfl-case =
      lam p′ $ lam p′ $
      cong ω (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂))
        (wk[ 2 ]′ (lam p′ B₁)) (var x1) (U (l₁ ⊔ᵘ l₂))
        (ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0))
        (wk[ 2 ]′ ext∘³ ∘⟨ p′ ⟩ var x1 ∘⟨ p′ ⟩ var x0)

    opaque
      ⊢rfl-case : Γ ⊢ rfl-case ∷ Motive [ A₁ , rfl ]₁₀
      ⊢rfl-case =
        lamⱼ′ ok′ $ lamⱼ′ ok′ $
        _⊢_∷_.conv (⊢cong ⊢Π10 ⊢ext∘⁵) $ univ
          (Id (U (l₁ ⊔ᵘ l₂))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0)
              [ wk[ 2 ]′ (lam p′ B₁) ]₀)
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0)
              [ var x1 ]₀)                                            ≡⟨ PE.cong₂ (Id _)
                                                                           (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                              wk[1+]′-[]₀≡
                                                                              (PE.cong₃ _∘⟨_⟩_ (wk-comp _ _ _) PE.refl PE.refl))
                                                                           (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _) wk[1+]′-[]₀≡ PE.refl) ⟩⊢≡
           Id (U (l₁ ⊔ᵘ l₂))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₁ ▹
              (wk[ 3 ]′ (lam p′ B₁) ∘⟨ p′ ⟩ var x0))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₁ ▹ (var x2 ∘⟨ p′ ⟩ var x0))  ≡⟨ Id-cong (refl (Uⱼ (∙ ⊢ΠId-1[])))
                                                                           (ΠΣ-cong (refl ∙²⊢A₁)
                                                                              (PE.subst₂ (_⊢_≡_∷_ _ _)
                                                                                 (PE.trans (PE.sym $ [][]↑≡ B₁) [1+][0]↑)
                                                                                 PE.refl $
                                                                               β-red-≡
                                                                                 (PE.subst₃ _⊢_∷_
                                                                                    (PE.cong (_∙_ _) $ PE.sym $ wk-comp _ _ _) PE.refl PE.refl $
                                                                                  wkTerm (liftʷ ⊇-drop (univ ∙³⊢A₁′)) ⊢B₁)
                                                                                 (var₀ (univ ∙²⊢A₁)) ok′)
                                                                              ok)
                                                                           (refl ⊢Π20′) ⟩⊢∎≡
           Id (U (l₁ ⊔ᵘ l₂)) (wk[ 2 ]′ (ΠΣ⟨ b ⟩ p , q ▷  A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₁ ▹ (var x2 ∘⟨ p′ ⟩ var x0))  ≡˘⟨ PE.cong₂ (Id _)
                                                                            wk[2+]′[,⇑]≡
                                                                            (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _) wk[]≡wk[]′ PE.refl) ⟩
           (Id (U (l₁ ⊔ᵘ l₂)) (wk[ 4 ]′ (ΠΣ⟨ b ⟩ p , q ▷  A₁ ▹ B₁))
              (ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0))
            [ consSubst (sgSubst A₁) rfl ⇑[ 2 ] ])                    ∎)

    J-app : Term n
    J-app = J ω ω (U l₁) A₁ Motive rfl-case A₂ t

    opaque
      ⊢J :
        Γ ⊢ J-app ∷
        Π p′ , q′ ▷ (Π p′ , q′ ▷ A₂ ▹ U l₂) ▹
        Π p′ , q′ ▷ ΠId 1 (var x1) (wk[ 2 ]′ A₂) (wk[ 2 ]′ t) ▹
        Id (U (l₁ ⊔ᵘ l₂)) (wk[ 2 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
          (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₂ ▹ (var x2 ∘⟨ p′ ⟩ var x0))
      ⊢J =
        PE.subst (_⊢_∷_ _ _)
          (Π p′ , q′ ▷ (Π p′ , q′ ▷ var x1 ▹ U l₂) ▹
           Π p′ , q′ ▷
             (Π p′ , q′ ▷ wk[ 3 ] A₁ ▹
              Id (U l₂) (B₁ [ 4 ][ var x0 ]↑)
                (var x1 ∘⟨ p′ ⟩
                 cast l₁ (wk[ 4 ]′ A₁) (var x3) (var x2) (var x0))) ▹
           Id (U (l₁ ⊔ᵘ l₂)) (wk[ 4 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0))
           [ A₂ , t ]₁₀                                                ≡⟨ PE.cong₂ (Π p′ , q′ ▷_▹_) PE.refl $
                                                                          PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                            (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                               (PE.trans
                                                                                  (PE.cong _[ _ ] $
                                                                                   wk[]≡wk[]′ {t = A₁}) $
                                                                                wk[2+]′[,⇑]≡)
                                                                               (PE.cong₂ (Id _)
                                                                                  ([][]↑-[,⇑] 2 B₁)
                                                                                  (PE.cong (_∘⟨_⟩_ _ _) $
                                                                                   PE.trans cast-[] $
                                                                                   PE.cong₄ (cast _)
                                                                                     wk[2+]′[,⇑]≡ wk[]≡wk[]′ wk[]≡wk[]′ PE.refl)))
                                                                            (PE.cong₂ (Id _)
                                                                               wk[2+]′[,⇑]≡
                                                                               (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _) wk[]≡wk[]′ PE.refl)) ⟩
        Π p′ , q′ ▷ (Π p′ , q′ ▷ A₂ ▹ U l₂) ▹
        Π p′ , q′ ▷
          (Π p′ , q′ ▷ wk1 A₁ ▹
           Id (U l₂) (B₁ [ 2 ][ var x0 ]↑)
             (var x1 ∘⟨ p′ ⟩
              cast l₁ (wk[ 2 ]′ A₁) (wk[ 2 ]′ A₂) (wk[ 2 ]′ t)
                (var x0))) ▹
        Id (U (l₁ ⊔ᵘ l₂)) (wk[ 2 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
          (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₂ ▹ (var x2 ∘⟨ p′ ⟩ var x0))      ∎) $
        Jⱼ′ ⊢Motive ⊢rfl-case ⊢t

    opaque
      ⊢J∘ :
        Γ ⊢ J-app ∘⟨ p′ ⟩ lam p′ B₂ ∷
        Π p′ , q′ ▷
          (Π p′ , q′ ▷ A₁ ▹
           Id (U l₂) (B₁ [ 1 ][ var x0 ]↑)
             (B₂ [ 1 ][ cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t)
                          (var x0) ]↑)) ▹
        Id (U (l₁ ⊔ᵘ l₂)) (wk1 (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
          (ΠΣ⟨ b ⟩ p , q ▷ wk1 A₂ ▹ (B₂ [ 2 ][ var x0 ]↑))
      ⊢J∘ =
        _⊢_∷_.conv (⊢J ∘ⱼ lamⱼ′ ok′ ⊢B₂) $ univ
          (Π p′ , q′ ▷
             (Π p′ , q′ ▷ wk1 A₁ ▹
              Id (U l₂) (B₁ [ 2 ][ var x0 ]↑)
                (var x1 ∘⟨ p′ ⟩
                 cast l₁ (wk[ 2 ]′ A₁) (wk[ 2 ]′ A₂) (wk[ 2 ]′ t)
                   (var x0))) ▹
           Id (U (l₁ ⊔ᵘ l₂)) (wk[ 2 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₂ ▹ (var x2 ∘⟨ p′ ⟩ var x0))
           [ lam p′ B₂ ]₀                                             ≡⟨ PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                           (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                              (wk1-sgSubst _ _)
                                                                              (PE.cong₂ (Id _)
                                                                                 ([][]↑-[₀⇑] 1 B₁)
                                                                                 (PE.cong (_∘⟨_⟩_ _ _) $
                                                                                  PE.trans cast-[] $
                                                                                  PE.cong₄ (cast _)
                                                                                    wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡ PE.refl)))
                                                                           (PE.cong₂ (Id _)
                                                                              wk[+1]′-[₀⇑]≡
                                                                              (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                                 wk[+1]′-[₀⇑]≡
                                                                                 (PE.cong₃ _∘⟨_⟩_ wk[]≡wk[]′ PE.refl PE.refl))) ⟩⊢≡
          (Π p′ , q′ ▷
             (Π p′ , q′ ▷ A₁ ▹
              Id (U l₂) (B₁ [ 1 ][ var x0 ]↑)
                (wk1 (lam p′ B₂) ∘⟨ p′ ⟩
                 cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t) (var x0))) ▹
           Id (U (l₁ ⊔ᵘ l₂)) (wk1 (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk1 A₂ ▹
              (wk[ 2 ]′ (lam p′ B₂) ∘⟨ p′ ⟩ var x0)))                 ≡⟨ ΠΣ-cong
                                                                           (ΠΣ-cong
                                                                              (refl ⊢A₁)
                                                                              (Id-cong (refl (Uⱼ (∙ univ ⊢A₁)))
                                                                                 (refl (subst-⊢∷ ⊢B₁ (⊢ˢʷ∷-[][]↑ (var₀ (univ ⊢A₁)))))
                                                                                 (PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ [][]↑≡ B₂) PE.refl $
                                                                                  β-red-≡
                                                                                    (wkTerm (liftʷ ⊇-drop (wk₁ (univ ⊢A₁) (univ ⊢A₂))) ⊢B₂)
                                                                                    (⊢cast (wkTerm₁ (univ ⊢A₁) ⊢t) (var₀ (univ ⊢A₁))) ok′))
                                                                              ok′)
                                                                           (Id-cong (refl (Uⱼ (∙ ⊢ΠId-lam)))
                                                                              (refl (wkTerm₁ ⊢ΠId-lam (ΠΣⱼ ⊢A₁ ⊢B₁ ok)))
                                                                              (ΠΣ-cong (refl ΠId-lam⊢A₂)
                                                                                 (PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ [][]↑≡ B₂) PE.refl $
                                                                                  β-red-≡
                                                                                    (wkTerm
                                                                                       (liftʷ ⊇-drop $ _⊢_.univ $
                                                                                        wkTerm (ʷ⊇-drop (∙ univ ΠId-lam⊢A₂)) ⊢A₂)
                                                                                       ⊢B₂)
                                                                                    (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
                                                                                     var₀ (univ ΠId-lam⊢A₂)) ok′)
                                                                                 ok))
                                                                           ok′ ⟩⊢∎
           Π p′ , q′ ▷
             (Π p′ , q′ ▷ A₁ ▹
              Id (U l₂) (B₁ [ 1 ][ var x0 ]↑)
                (B₂ [ 1 ][ cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t)
                             (var x0) ]↑)) ▹
           Id (U (l₁ ⊔ᵘ l₂)) (wk1 (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk1 A₂ ▹ (B₂ [ 2 ][ var x0 ]↑))         ∎)

    opaque
      ⊢J∘∘ :
        Γ ⊢ J-app ∘⟨ p′ ⟩ lam p′ B₂ ∘⟨ p′ ⟩ lam p′ u ∷
        Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
          (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
      ⊢J∘∘ =
        PE.subst (_⊢_∷_ _ _)
          (Id (U (l₁ ⊔ᵘ l₂)) (wk1 (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk1 A₂ ▹ (B₂ [ 2 ][ var x0 ]↑))
           [ lam p′ u ]₀                                       ≡⟨ PE.cong₂ (Id _) (wk1-sgSubst _ _) $
                                                                  PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                    (wk1-sgSubst _ _)
                                                                    ([][]↑-[₀⇑] 1 B₂) ⟩
           Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
             (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ (B₂ [ var x0 ]↑))           ≡⟨ PE.cong (Id _ _ ∘→ ΠΣ⟨_⟩_,_▷_▹_ _ _ _ _) [0]↑ ⟩

           Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
             (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)                         ∎)
          (⊢J∘ ∘ⱼ
           PE.subst (_⊢_∷_ _ _)
             (PE.cong (Π p′ , q′ ▷ A₁ ▹_) $
              PE.cong₂ (Id _) (PE.sym [0]↑) PE.refl)
             (lamⱼ′ ok′ ⊢u))

opaque

  -- A variant of ΠΣ-cong-Idˡ.

  ΠΣ-cong-Idʳ :
    ΠΣ-allowed b p q →
    Π-allowed p′ q′ →
    Has-function-extensionality p′ q′ l₁ (1+ l₂) Γ →
    Γ ∙ A₁ ⊢ B₁ ∷ U l₂ →
    Γ ⊢ t ∷ Id (U l₁) A₂ A₁ →
    Γ ∙ A₂ ⊢ u ∷
      Id (U l₂) (B₁ [ cast l₁ (wk1 A₂) (wk1 A₁) (wk1 t) (var x0) ]↑)
        B₂ →
    ∃ λ v →
      Γ ⊢ v ∷
        Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
          (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
  ΠΣ-cong-Idʳ ok ok′ ext ⊢B₁ ⊢t ⊢u =
    _ , ⊢symmetry (ΠΣ-cong-Idˡ ok ok′ ext ⊢B₁ ⊢t (⊢symmetry ⊢u) .proj₂)
