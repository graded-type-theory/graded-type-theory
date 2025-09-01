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
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

open Definition.Typed.Properties.Admissible.Identity.Primitive R public

private variable
  ∇                                               : DCon (Term 0) _
  n                                               : Nat
  Δ Δ₁ Δ₂                                         : Con Term _
  Γ                                               : Cons _ _
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
    Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
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
    Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
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
    Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ J p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
  J-β-≡ {Γ} {t} {A} ⊢t ⊢B ⊢u =
    J-β ⊢t ⊢B ⊢u PE.refl
    where
    -- If a strengthening lemma is proved then one can perhaps drop
    -- the first argument of J-β-≡.

    _ : Γ »∙ A ⊢ wk1 t ∷ wk1 A
    _ =
      case wf ⊢B of λ {
        (∙ ⊢Id) →
      case inversion-Id ⊢Id of λ {
        (_ , ⊢wk1-t , _) →
      ⊢wk1-t }}

opaque

  -- A variant of J-subst.

  J-subst′ :
    Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
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
    Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
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
    Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ w ∷ Id A t v →
    Γ ⊢ B [ v , w ]₁₀
  J-result ⊢B ⊢w =
    case inversion-Id (syntacticTerm ⊢w) of λ {
      (_ , _ , ⊢v) →
    substType₂ ⊢B ⊢v (PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ ⊢w) }

opaque

  -- A lemma related to the type of an application of J.

  J-result-cong :
    Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    Γ ⊢ B₁ [ v₁ , w₁ ]₁₀ ≡ B₂ [ v₂ , w₂ ]₁₀
  J-result-cong B₁≡B₂ v₁≡v₂ w₁≡w₂ =
    substTypeEq₂ B₁≡B₂ v₁≡v₂
      (PE.subst (_⊢_≡_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ w₁≡w₂)

opaque

  -- A lemma related to the type of one of the assumptions of J.

  J-motive-rfl-cong :
    Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ B₁ [ t₁ , rfl ]₁₀ ≡ B₂ [ t₂ , rfl ]₁₀
  J-motive-rfl-cong B₁≡B₂ t₁≡t₂ =
    J-result-cong B₁≡B₂ t₁≡t₂
      (refl (rflⱼ (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁)))

opaque

  -- A variant of the reduction rule J-β.

  J-β-⇒ :
    Γ ⊢ t ≡ t′ ∷ A →
    Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
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
    Γ »∙ A ⊢ Id (wk1 A) (wk1 t) (var x0)
  J-motive-context-type ⊢t =
    case syntacticTerm ⊢t of λ {
      ⊢A →
    Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A) }

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context :
    Γ ⊢ t ∷ A →
    ⊢ Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0)
  J-motive-context ⊢t = ∙ J-motive-context-type ⊢t

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ » Δ₁ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ∇ »⊢ Δ₁ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ≡
      Δ₂ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0)
  J-motive-context-cong Δ₁≡Δ₂ A₁≡A₂ t₁≡t₂ =
    case syntacticEq A₁≡A₂ .proj₁ of λ {
      ⊢A₁ →
    Δ₁≡Δ₂ ∙ A₁≡A₂ ∙
    Id-cong (wkEq₁ ⊢A₁ A₁≡A₂) (wkEqTerm₁ ⊢A₁ t₁≡t₂) (refl (var₀ ⊢A₁)) }

opaque

  -- A variant of the previous lemma.

  J-motive-context-cong′ :
    ∇ » Δ ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ∇ »⊢ Δ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ≡
      Δ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0)
  J-motive-context-cong′ A₁≡A₂ =
    J-motive-context-cong (reflConEq (wfEq A₁≡A₂)) A₁≡A₂

------------------------------------------------------------------------
-- Lemmas related to K

opaque

  -- A variant of K-subst for _⊢_⇒*_∷_.

  K-subst* :
    Γ »∙ Id A t t ⊢ B →
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
    Γ »∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂ →
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

  K-motive-context : Γ ⊢ t ∷ A → ⊢ Γ »∙ Id A t t
  K-motive-context ⊢t = ∙ K-motive-context-type ⊢t

opaque

  -- A lemma related to the context of one of the assumptions of K.

  K-motive-context-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ » Δ₁ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ∇ »⊢ Δ₁ ∙ Id A₁ t₁ t₁ ≡ Δ₂ ∙ Id A₂ t₂ t₂
  K-motive-context-cong Δ₁≡Δ₂ A₁≡A₂ t₁≡t₂ =
    Δ₁≡Δ₂ ∙ Id-cong A₁≡A₂ t₁≡t₂ t₁≡t₂

opaque

  -- A variant of the previous lemma.

  K-motive-context-cong′ :
    ∇ » Δ ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ∇ »⊢ Δ ∙ Id A₁ t₁ t₁ ≡ Δ ∙ Id A₂ t₂ t₂
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
    Γ »∙ A ⊢ B →
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
    Γ »∙ A ⊢ B →
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
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t t rfl u ⇒ u ∷ B [ t ]₀
  subst-⇒ ⊢B ⊢t = subst-⇒′ ⊢B (refl ⊢t)

opaque

  -- An equality rule for subst.

  subst-≡ :
    Γ »∙ A ⊢ B →
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
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
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
    Γ »∙ A ⊢ B →
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
    Γ »∙ A ⊢ B →
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t u →
    Γ ⊢ w ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t u v₁ w ⇒* subst p A B t u v₂ w ∷ B [ u ]₀
  subst-subst* ⊢B = λ where
    (id ⊢v)          ⊢w → id (⊢subst ⊢B ⊢v ⊢w)
    (v₁⇒v₃ ⇨ v₃⇒*v₂) ⊢w →
      subst-subst ⊢B v₁⇒v₃ ⊢w ⇨ subst-subst* ⊢B v₃⇒*v₂ ⊢w

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
    Γ »∙ A ⊢ v ∷ wk1 B →
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
    Γ »∙ A₁ ⊢ v₁ ≡ v₂ ∷ wk1 B₁ →
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
    Γ »∙ A ⊢ u ∷ wk1 B →
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
    Γ »∙ A ⊢ u ∷ wk1 B →
    Γ ⊢ cong p A t t B u rfl ≡ rfl ∷ Id B (u [ t ]₀) (u [ t ]₀)
  cong-≡ ⊢t ⊢u =
    subsetTerm (cong-⇒ ⊢t ⊢u)

opaque
  unfolding cong

  -- A reduction rule for cong.

  cong-subst :
    Γ »∙ A ⊢ v ∷ wk1 B →
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
    Γ »∙ A ⊢ v ∷ wk1 B →
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
    Γ »∙ A ⊢ v ∷ Id B (wk1 t ∘⟨ p ⟩ var x0) (wk1 u ∘⟨ p ⟩ var x0) →
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
        (rflⱼ′ $ _⊢_≡_∷_.refl $
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
