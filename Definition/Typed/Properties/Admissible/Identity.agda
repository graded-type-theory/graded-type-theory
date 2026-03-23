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
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.U R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum

open Definition.Typed.Properties.Admissible.Identity.Primitive R public

private variable
  m n                                                  : Nat
  ∇                                                    : DCon (Term 0) _
  Δ Δ₁ Δ₂                                              : Con Term _
  Γ Η                                                  : Cons _ _
  A A₁ A₁₁ A₁₂ A₂ A₂₁ A₂₂ A′ B B₁ B₂ C
    eq eq₁ eq₁₁ eq₁₂ eq₂ eq₂₁ eq₂₂
    t t₁ t₁₁ t₁₂ t₂ t₂₁ t₂₂ t′ u u₁ u₁₁ u₁₂ u₂ u₂₁ u₂₂
    v v₁ v₂ w w₁ w₁₁ w₁₂ w₂ w₂₁ w₂₂                    : Term _
  l l₁ l₂                                              : Lvl _
  p p′ q q′                                            : M
  s                                                    : Strength

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
          _ , _ , ⊢v = inversion-Id (wf-⊢ w₁≡w₃ .proj₁)
      in
      J p q A t B u v w₁ ∷ B [ v , w₁ ]₁₀  ⇒⟨ J-subst′ ⊢B ⊢u w₁⇒w₃ ⟩∷
                                           ˘⟨ subst-⊢≡₁₀ ⊢B (refl ⊢v)
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
    subst-⊢₁₀ ⊢B ⊢v (PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ ⊢w) }

opaque

  -- A lemma related to the type of an application of J.

  J-result-cong :
    Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂ →
    Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
    Γ ⊢ B₁ [ v₁ , w₁ ]₁₀ ≡ B₂ [ v₂ , w₂ ]₁₀
  J-result-cong B₁≡B₂ v₁≡v₂ w₁≡w₂ =
    subst-⊢≡₁₀ B₁≡B₂ v₁≡v₂
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
    Idⱼ′ (wk₁ ⊢A ⊢t) (var₀ ⊢A) }

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context :
    Γ ⊢ t ∷ A →
    ⊢ Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0)
  J-motive-context ⊢t = ∙ J-motive-context-type ⊢t

opaque

  -- A lemma related to the context of one of the assumptions of J.

  J-motive-context-cong″ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ »∙ A₁ ⊢
      Id (wk1 A₁) (wk1 t₁) (var x0) ≡
      Id (wk1 A₂) (wk1 t₂) (var x0)
  J-motive-context-cong″ A₁≡A₂ t₁≡t₂ =
    let ⊢A₁ , _ = wf-⊢ A₁≡A₂ in
    Id-cong (wk₁ ⊢A₁ A₁≡A₂) (wk₁ ⊢A₁ t₁≡t₂) (refl (var₀ ⊢A₁))

opaque

  -- A variant of the previous lemma.

  J-motive-context-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ » Δ₁ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ∇ »⊢ Δ₁ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ≡
      Δ₂ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0)
  J-motive-context-cong Δ₁≡Δ₂ A₁≡A₂ t₁≡t₂ =
    Δ₁≡Δ₂ ∙ A₁≡A₂ ∙ J-motive-context-cong″ A₁≡A₂ t₁≡t₂

opaque

  -- A variant of the previous lemma.

  J-motive-context-cong′ :
    ∇ » Δ ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ∇ »⊢ Δ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ≡
      Δ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0)
  J-motive-context-cong′ A₁≡A₂ =
    J-motive-context-cong (reflConEq (wf A₁≡A₂)) A₁≡A₂

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
                                    ˘⟨ subst-⊢≡₀ ⊢B (sym′ (subsetTerm v₁⇒v₃)) ⟩⇒
        K p A t B u v₃ ∷ B [ v₃ ]₀  ⇒*⟨ K-subst* ⊢B ⊢u v₃⇒*v₂ ok ⟩∎∷
        K p A t B u v₂              ∎

opaque

  -- A lemma related to the type of one of the assumptions of K.

  K-motive-rfl-cong :
    Γ »∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ B₁ [ rfl ]₀ ≡ B₂ [ rfl ]₀
  K-motive-rfl-cong B₁≡B₂ =
    case wf B₁≡B₂ of λ {
      (∙ ⊢Id) →
    subst-⊢≡₀ B₁≡B₂ (refl (rflⱼ (inversion-Id ⊢Id .proj₂ .proj₁))) }

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

  K-motive-context-cong″ :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ Id A₁ t₁ t₁ ≡ Id A₂ t₂ t₂
  K-motive-context-cong″ A₁≡A₂ t₁≡t₂ =
    Id-cong A₁≡A₂ t₁≡t₂ t₁≡t₂

opaque

  -- A variant of the previous lemma.

  K-motive-context-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ » Δ₁ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ∇ »⊢ Δ₁ ∙ Id A₁ t₁ t₁ ≡ Δ₂ ∙ Id A₂ t₂ t₂
  K-motive-context-cong Δ₁≡Δ₂ A₁≡A₂ t₁≡t₂ =
    Δ₁≡Δ₂ ∙ K-motive-context-cong″ A₁≡A₂ t₁≡t₂

opaque

  -- A variant of the previous lemma.

  K-motive-context-cong′ :
    ∇ » Δ ⊢ A₁ ≡ A₂ →
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ A₁ →
    ∇ »⊢ Δ ∙ Id A₁ t₁ t₁ ≡ Δ ∙ Id A₂ t₂ t₂
  K-motive-context-cong′ A₁≡A₂ =
    K-motive-context-cong (reflConEq (wf A₁≡A₂)) A₁≡A₂

------------------------------------------------------------------------
-- Lemmas related to []-cong

opaque

  -- A variant of []-cong-subst for _⊢_⇒*_∷_.

  []-cong-subst* :
    let open Erased s in
    Γ ⊢ l ∷Level →
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t u →
    []-cong-allowed s →
    Γ ⊢ []-cong s l A t u v₁ ⇒* []-cong s l A t u v₂ ∷
      Id (Erased l A) [ t ] ([ u ])
  []-cong-subst* ⊢l v₁⇒*v₂ ok =
    case v₁⇒*v₂ of λ where
      (id ⊢v₁)         → id ([]-congⱼ′ ok ⊢l ⊢v₁)
      (v₁⇒v₃ ⇨ v₃⇒*v₂) →
        []-cong-subst ⊢l v₁⇒v₃ ok ⇨ []-cong-subst* ⊢l v₃⇒*v₂ ok

opaque

  -- A variant of the equality rule []-cong-β.

  []-cong-β-≡ :
    Γ ⊢ l ∷Level →
    Γ ⊢ t ≡ t′ ∷ A →
    []-cong-allowed s →
    let open Erased s in
      Γ ⊢ []-cong s l A t t′ rfl ≡ rfl ∷
        Id (Erased l A) ([ t ]) ([ t′ ])
  []-cong-β-≡ ⊢l t≡t′ ok =
    let ⊢A , ⊢t , _ = wf-⊢ t≡t′ in
    trans
      ([]-cong-cong (refl-⊢≡∷L ⊢l) (refl ⊢A) (refl ⊢t) (sym′ t≡t′)
         (refl (rflⱼ′ t≡t′)) ok)
      (conv ([]-cong-β ⊢l ⊢t PE.refl ok)
         (Id-cong (refl (Erasedⱼ ⊢l ⊢A)) (refl ([]ⱼ ⊢l ⊢A ⊢t))
            ([]-cong′ ⊢l ⊢A t≡t′)))
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
      (wk₁
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

opaque
  unfolding subst

  -- An inversion lemma for subst.
  --
  -- If a suitable form of strengthening is proved, then it should be
  -- easy to add Γ »∙ A ⊢ B to the result.

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

opaque
  unfolding subst

  -- An inversion lemma for subst.

  inv-⇒-subst :
    Γ ⊢ subst p A B t u v w ⇒ t′ ∷ C →
    (∃ λ v′ → Γ ⊢ v ⇒ v′ ∷ Id A t u × t′ PE.≡ subst p A B t u v′ w) ⊎
    v PE.≡ rfl × t′ PE.≡ w × Γ ⊢ t ≡ u ∷ A
  inv-⇒-subst = inv-⇒-J

------------------------------------------------------------------------
-- Lemmas related to transitivity

opaque
  unfolding transitivity

  -- An equality rule for transitivity.

  transitivity-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
    Γ ⊢ eq₁₁ ≡ eq₁₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ eq₂₁ ≡ eq₂₂ ∷ Id A₁ u₁ v₁ →
    Γ ⊢ transitivity A₁ t₁ u₁ v₁ eq₁₁ eq₂₁ ≡
      transitivity A₂ t₂ u₂ v₂ eq₁₂ eq₂₂ ∷ Id A₁ t₁ v₁
  transitivity-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ eq₁₁≡eq₁₂ eq₂₁≡eq₂₂ =
    PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym ≡Id-wk1-wk1-0[]₀) $
    subst-cong A₁≡A₂ (J-motive-context-cong″ A₁≡A₂ t₁≡t₂) u₁≡u₂ v₁≡v₂
      eq₂₁≡eq₂₂ (PE.subst (_⊢_≡_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ eq₁₁≡eq₁₂)

opaque
  unfolding transitivity

  -- A typing rule for transitivity.

  ⊢transitivity :
    Γ ⊢ eq₁ ∷ Id A t u →
    Γ ⊢ eq₂ ∷ Id A u v →
    Γ ⊢ transitivity A t u v eq₁ eq₂ ∷ Id A t v
  ⊢transitivity ⊢eq₁ ⊢eq₂ =
    let ⊢A , ⊢t , ⊢u = inversion-Id (wf-⊢ ⊢eq₁)
        _  , _  , ⊢v = inversion-Id (wf-⊢ ⊢eq₂)
    in
    wf-⊢
      (transitivity-cong (refl ⊢A) (refl ⊢t) (refl ⊢u) (refl ⊢v)
         (refl ⊢eq₁) (refl ⊢eq₂))
      .proj₂ .proj₁

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
      (Idⱼ′ (wk₁ ⊢A ⊢t) (var₀ ⊢A))
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
          wk₁ ⊢A (subst-⊢₀ ⊢v ⊢t))
         ⊢v)
      ⊢w
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $ PE.cong₃ Id PE.refl (wk1-sgSubst _ _) PE.refl) $
       rflⱼ (subst-⊢₀ ⊢v ⊢t))

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
      (Id-cong (wk₁ ⊢A₁ B₁≡B₂)
         (wk₁ ⊢A₁ $
          PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
          subst-⊢≡₀ v₁≡v₂ t₁≡t₂)
         v₁≡v₂)
      t₁≡t₂ u₁≡u₂ w₁≡w₂
      (_⊢_≡_∷_.refl $
       PE.subst (_⊢_∷_ _ _)
         (PE.cong₂ (Id _) (PE.sym $ wk1-sgSubst _ _) PE.refl) $
       rflⱼ $ subst-⊢₀ ⊢v₁ ⊢t₁)

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
          wk₁ (syntacticTerm ⊢t) (subst-⊢₀ ⊢u ⊢t))
         ⊢u)
      ⊢t
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $ PE.cong₃ Id PE.refl (wk1-sgSubst _ _) PE.refl) $
       rflⱼ (subst-⊢₀ ⊢u ⊢t))

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
          wk₁ ⊢A (subst-⊢₀ ⊢v ⊢t))
         ⊢v)
      w₁⇒w₂
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $ PE.cong₃ Id PE.refl (wk1-sgSubst _ _) PE.refl) $
       rflⱼ (subst-⊢₀ ⊢v ⊢t))

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
-- Lemmas related to cong₂

opaque
  unfolding cong₂

  -- An equality rule for cong₂.

  cong₂-cong :
    Γ ⊢ A₁₁ ≡ A₁₂ →
    Γ ⊢ t₁₁ ≡ t₁₂ ∷ A₁₁ →
    Γ ⊢ u₁₁ ≡ u₁₂ ∷ A₁₁ →
    Γ ⊢ A₂₁ ≡ A₂₂ →
    Γ ⊢ t₂₁ ≡ t₂₂ ∷ A₂₁ →
    Γ ⊢ u₂₁ ≡ u₂₂ ∷ A₂₁ →
    Γ ⊢ B₁ ≡ B₂ →
    Γ »∙ A₁₁ »∙ wk1 A₂₁ ⊢ v₁ ≡ v₂ ∷ wk[ 2 ]′ B₁ →
    Γ ⊢ w₁₁ ≡ w₁₂ ∷ Id A₁₁ t₁₁ u₁₁ →
    Γ ⊢ w₂₁ ≡ w₂₂ ∷ Id A₂₁ t₂₁ u₂₁ →
    Γ ⊢ cong₂ p A₁₁ t₁₁ u₁₁ A₂₁ t₂₁ u₂₁ B₁ v₁ w₁₁ w₂₁ ≡
      cong₂ p A₁₂ t₁₂ u₁₂ A₂₂ t₂₂ u₂₂ B₂ v₂ w₁₂ w₂₂ ∷
      Id B₁ (v₁ [ t₁₁ , t₂₁ ]₁₀) (v₁ [ u₁₁ , u₂₁ ]₁₀)
  cong₂-cong
    {Γ} {A₁₁} {A₂₁} {B₁} {v₁} {v₂}
    A₁₁≡A₁₂ t₁₁≡t₁₂ u₁₁≡u₁₂ A₂₁≡A₂₂ t₂₁≡t₂₂ u₂₁≡u₂₂ B₁≡B₂ v₁≡v₂
    w₁₁≡w₁₂ w₂₁≡w₂₂ =
    let ⊢A₁₁ , _ = wf-⊢ A₁₁≡A₁₂ in
    transitivity-cong B₁≡B₂ (lemma t₁₁≡t₁₂ t₂₁≡t₂₂)
      (lemma u₁₁≡u₁₂ t₂₁≡t₂₂) (lemma u₁₁≡u₁₂ u₂₁≡u₂₂)
      (PE.subst (_⊢_≡_∷_ _ _ _)
         (PE.sym $
          PE.cong₂ (Id _) ([,]≡[wk1]₀[]₀ v₁) ([,]≡[wk1]₀[]₀ v₁)) $
       cong-cong A₁₁≡A₁₂ t₁₁≡t₁₂ u₁₁≡u₁₂ B₁≡B₂
         (PE.subst (_⊢_≡_∷_ _ _ _) wk[1+]′-[]₀≡ $
          subst-⊢≡₀ v₁≡v₂ (wk₁ ⊢A₁₁ t₂₁≡t₂₂))
         w₁₁≡w₁₂)
      (PE.subst (_⊢_≡_∷_ _ _ _)
         (PE.cong₂ (Id _)
            (singleSubstComp _ _ v₁) (singleSubstComp _ _ v₁)) $
       cong-cong A₂₁≡A₂₂ t₂₁≡t₂₂ u₂₁≡u₂₂ B₁≡B₂
         (PE.subst₄ _⊢_≡_∷_
             (PE.cong (_»_ _) (PE.cong (_∙_ _) (wk1-sgSubst _ _)))
             PE.refl PE.refl wk[+1]′-[₀⇑]≡ $
          subst-⊢≡-⇑ v₁≡v₂ (⊢ˢʷ≡∷-sgSubst u₁₁≡u₁₂))
         w₂₁≡w₂₂)
      where
      lemma :
        Γ ⊢ t₁ ≡ t₂ ∷ A₁₁ →
        Γ ⊢ u₁ ≡ u₂ ∷ A₂₁ →
        Γ ⊢ v₁ [ t₁ , u₁ ]₁₀ ≡ v₂ [ t₂ , u₂ ]₁₀ ∷ B₁
      lemma t₁≡t₂ u₁≡u₂ =
        PE.subst (_⊢_≡_∷_ _ _ _) wk₂-[,] $
        subst-⊢≡₁₀ v₁≡v₂ t₁≡t₂ $
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk1-sgSubst _ _) u₁≡u₂

opaque

  -- A typing rule for cong₂.

  ⊢cong₂ :
    Γ »∙ A₁ »∙ wk1 A₂ ⊢ v ∷ wk[ 2 ]′ B →
    Γ ⊢ w₁ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ w₂ ∷ Id A₂ t₂ u₂ →
    Γ ⊢ cong₂ p A₁ t₁ u₁ A₂ t₂ u₂ B v w₁ w₂ ∷
      Id B (v [ t₁ , t₂ ]₁₀) (v [ u₁ , u₂ ]₁₀)
  ⊢cong₂ ⊢v ⊢w₁ ⊢w₂ =
    let ⊢A₁ , ⊢t₁ , ⊢u₁ = inversion-Id (wf-⊢ ⊢w₁)
        ⊢A₂ , ⊢t₂ , ⊢u₂ = inversion-Id (wf-⊢ ⊢w₂)
        ⊢B              = PE.subst (_⊢_ _) wk₂-[,] $
                          subst-⊢₁₀ (wf-⊢ ⊢v) ⊢t₁
                            (PE.subst (_⊢_∷_ _ _)
                               (PE.sym $ wk1-sgSubst _ _)
                             ⊢t₂)
    in
    wf-⊢
      (cong₂-cong (refl ⊢A₁) (refl ⊢t₁) (refl ⊢u₁) (refl ⊢A₂) (refl ⊢t₂)
         (refl ⊢u₂) (refl ⊢B) (refl ⊢v) (refl ⊢w₁) (refl ⊢w₂))
      .proj₂ .proj₁

opaque
  unfolding cong₂

  -- A β-rule for cong₂.

  cong₂-β :
    Γ ⊢ t₁ ∷ A₁ →
    Γ ⊢ t₂ ∷ A₂ →
    Γ »∙ A₁ »∙ wk1 A₂ ⊢ u ∷ wk[ 2 ]′ B →
    Γ ⊢ cong₂ p A₁ t₁ t₁ A₂ t₂ t₂ B u rfl rfl ≡ rfl ∷
      Id B (u [ t₁ , t₂ ]₁₀) (u [ t₁ , t₂ ]₁₀)
  cong₂-β {t₁} {A₁} {t₂} {A₂} {u} {B} {p} ⊢t₁ ⊢t₂ ⊢u =
    let ⊢t₂′      = PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) ⊢t₂
        ⊢B        = PE.subst (_⊢_ _) wk₂-[,] $
                    subst-⊢₁₀ (wf-⊢ ⊢u) ⊢t₁ ⊢t₂′
        ⊢u[,]     = PE.subst (_⊢_∷_ _ _) wk₂-[,] $
                    subst-⊢₁₀ ⊢u ⊢t₁ ⊢t₂′
        u[,]≡u[,] = refl ⊢u[,]
    in
    transitivity B (u [ t₁ , t₂ ]₁₀) (u [ t₁ , t₂ ]₁₀)
      (u [ t₁ , t₂ ]₁₀) (cong p A₁ t₁ t₁ B (u [ sgSubst (wk1 t₂) ]) rfl)
      (cong p A₂ t₂ t₂ B (u [ sgSubst t₁ ⇑ ]) rfl)                        ≡⟨ transitivity-cong (refl ⊢B) u[,]≡u[,] u[,]≡u[,] u[,]≡u[,]
                                                                               (PE.subst (_⊢_≡_∷_ _ _ _)
                                                                                  (PE.sym $
                                                                                   PE.cong₂ (Id _) ([,]≡[wk1]₀[]₀ u) ([,]≡[wk1]₀[]₀ u)) $
                                                                                cong-≡ ⊢t₁
                                                                                  (PE.subst (_⊢_∷_ _ _) wk[1+]′-[]₀≡ $
                                                                                   subst-⊢₀ ⊢u (wk₁ (wf-⊢ ⊢t₁) ⊢t₂)))
                                                                               (PE.subst (_⊢_≡_∷_ _ _ _)
                                                                                  (PE.cong₂ (Id _)
                                                                                     (singleSubstComp _ _ u) (singleSubstComp _ _ u)) $
                                                                                cong-≡ ⊢t₂
                                                                                  (PE.subst₃ _⊢_∷_
                                                                                     (PE.cong (_»_ _) (PE.cong (_∙_ _) (wk1-sgSubst _ _)))
                                                                                     PE.refl wk[+1]′-[₀⇑]≡ $
                                                                                   subst-⊢-⇑ ⊢u (⊢ˢʷ∷-sgSubst ⊢t₁))) ⟩⊢
    transitivity B (u [ t₁ , t₂ ]₁₀) (u [ t₁ , t₂ ]₁₀)
      (u [ t₁ , t₂ ]₁₀) rfl rfl                                           ≡⟨ transitivity-≡ (rflⱼ ⊢u[,]) ⟩⊢∎

    rfl                                                                   ∎

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
       var₀ ⊢ΠAB ∘ⱼ wk₁ ⊢ΠAB ⊢w)
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
       var₀ ⊢ΠAB ∘ⱼ wk₁ ⊢ΠAB ⊢u)

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
-- Lemmas related to symmetry

opaque
  unfolding symmetry

  -- An equality rule for symmetry.

  symmetry-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ eq₁ ≡ eq₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ symmetry A₁ t₁ u₁ eq₁ ≡ symmetry A₂ t₂ u₂ eq₂ ∷ Id A₁ u₁ t₁
  symmetry-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ eq₁≡eq₂ =
    let ⊢A₁ , ⊢t₁ , _ = wf-⊢ t₁≡t₂ in
    PE.subst (_⊢_≡_∷_ _ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _)) $
    subst-cong A₁≡A₂
      (Id-cong (wk₁ ⊢A₁ A₁≡A₂) (refl (var₀ ⊢A₁))
         (wk₁ ⊢A₁ t₁≡t₂))
      t₁≡t₂ u₁≡u₂ eq₁≡eq₂
      (PE.subst (_⊢_≡_∷_ _ _ _)
         (PE.sym $
          PE.cong₃ Id (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _)) $
       refl (rflⱼ ⊢t₁))

opaque

  -- A typing rule for symmetry.

  ⊢symmetry :
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ symmetry A t u eq ∷ Id A u t
  ⊢symmetry ⊢eq =
    let ⊢A , ⊢t , ⊢u = inversion-Id (syntacticTerm ⊢eq) in
    wf-⊢ (symmetry-cong (refl ⊢A) (refl ⊢t) (refl ⊢u) (refl ⊢eq))
      .proj₂ .proj₁

opaque
  unfolding symmetry

  -- A reduction rule for symmetry.

  symmetry-⇒′ :
    Γ ⊢ t ≡ t′ ∷ A →
    Γ ⊢ symmetry A t t′ rfl ⇒ rfl ∷ Id A t t
  symmetry-⇒′ t≡t′ =
    let ⊢A , ⊢t , _ = wf-⊢ t≡t′
        Id≡Id       = PE.cong₃ Id
                        (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _)
    in
    PE.subst (_⊢_⇒_∷_ _ _ _) Id≡Id $
    subst-⇒′
      (Idⱼ′ (var₀ ⊢A) (wk₁ ⊢A ⊢t))
      t≡t′
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id≡Id) $
       rflⱼ ⊢t)

opaque

  -- A reduction rule for symmetry.

  symmetry-⇒ :
    Γ ⊢ t ∷ A →
    Γ ⊢ symmetry A t t rfl ⇒ rfl ∷ Id A t t
  symmetry-⇒ ⊢t =
    symmetry-⇒′ (refl ⊢t)

opaque

  -- An equality rule for symmetry.

  symmetry-≡ :
    Γ ⊢ t ∷ A →
    Γ ⊢ symmetry A t t rfl ≡ rfl ∷ Id A t t
  symmetry-≡ ⊢t =
    subsetTerm (symmetry-⇒ ⊢t)

opaque
  unfolding symmetry

  -- A reduction rule for symmetry.

  symmetry-subst :
    Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
    Γ ⊢ symmetry A t u v₁ ⇒ symmetry A t u v₂ ∷ Id A u t
  symmetry-subst v₁⇒v₂ =
    let ⊢A , ⊢t , ⊢u = inversion-Id (wf-⊢ (subsetTerm v₁⇒v₂) .proj₁)
    in
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _)) $
    subst-subst
      (Idⱼ′ (var₀ ⊢A) (wk₁ ⊢A ⊢t))
      v₁⇒v₂
      (PE.subst (_⊢_∷_ _ _)
         (PE.sym $
          PE.cong₃ Id (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _)) $
       rflⱼ ⊢t)

opaque

  -- A reduction rule for symmetry.

  symmetry-subst* :
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t u →
    Γ ⊢ symmetry A t u v₁ ⇒* symmetry A t u v₂ ∷ Id A u t
  symmetry-subst* (id ⊢v)          = id (⊢symmetry ⊢v)
  symmetry-subst* (v₁⇒v₃ ⇨ v₃⇒*v₂) =
    symmetry-subst v₁⇒v₃ ⇨ symmetry-subst* v₃⇒*v₂

opaque
  unfolding symmetry

  -- An inversion lemma for symmetry.

  inversion-symmetry :
    Γ ⊢ symmetry A t u v ∷ B →
    Γ ⊢ v ∷ Id A t u ×
    Γ ⊢ B ≡ Id A u t
  inversion-symmetry ⊢sym =
    let _ , _ , _ , ⊢v , _ , B≡ = inversion-subst ⊢sym in
    ⊢v ,
    PE.subst (_⊢_≡_ _ _)
      (PE.cong₃ Id (wk1-sgSubst _ _) PE.refl (wk1-sgSubst _ _)) B≡

opaque

  -- A preservation lemma for symmetry.

  symmetry-cong-Id :
    Γ ⊢ w ∷ Id (Id A t u) v₁ v₂ →
    ∃ λ eq →
      Γ ⊢ eq ∷ Id (Id A u t) (symmetry A t u v₁) (symmetry A t u v₂)
  symmetry-cong-Id {w} {A} {t} {u} {v₁} {v₂} ⊢w =
    let ⊢Id , _ = inversion-Id (wf-⊢ ⊢w) in
    cong ω (Id A t u) v₁ v₂ (Id A u t)
      (symmetry (wk1 A) (wk1 t) (wk1 u) (var x0)) w ,
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₂ (Id _) lemma lemma)
      (⊢cong (⊢symmetry (var₀ ⊢Id)) ⊢w)
    where
    lemma :
      symmetry (wk1 A) (wk1 t) (wk1 u) (var x0) [ v ]₀ PE.≡
      symmetry A t u v
    lemma =
      PE.trans symmetry-[] $
      PE.cong₄ symmetry
        (wk1-sgSubst _ _) (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl

opaque
  unfolding symmetry

  -- A simplification lemma for symmetry.

  Id-symmetry-symmetry :
    Γ ⊢ v ∷ Id A t u →
    ∃ λ w → Γ ⊢ w ∷ Id (Id A t u) (symmetry A u t (symmetry A t u v)) v
  Id-symmetry-symmetry {v} {A} {t} {u} ⊢v =
    let ⊢A , ⊢t , _ = inversion-Id (wf-⊢ ⊢v)
        ⊢0          = PE.subst (_⊢_∷_ _ _)
                        (PE.cong₃ Id wk[]≡wk[]′ wk[]≡wk[]′ PE.refl) $
                      var₀ (J-motive-context-type ⊢t)
    in
    J ω ω A t
      (Id (Id (wk[ 2 ]′ A) (wk[ 2 ]′ t) (var x1))
         (symmetry (wk[ 2 ]′ A) (var x1) (wk[ 2 ]′ t)
            (symmetry (wk[ 2 ]′ A) (wk[ 2 ]′ t) (var x1) (var x0)))
         (var x0))
      rfl u v ,
    PE.subst (_⊢_∷_ _ _) lemma
      (Jⱼ′ (Idⱼ′ (⊢symmetry (⊢symmetry ⊢0)) ⊢0)
         (PE.subst (_⊢_∷_ _ _) (PE.sym lemma) $
          rflⱼ′
            (symmetry A t t (symmetry A t t rfl)  ≡⟨ symmetry-cong (refl ⊢A) (refl ⊢t) (refl ⊢t) (symmetry-≡ ⊢t) ⟩⊢
             symmetry A t t rfl                   ≡⟨ symmetry-≡ ⊢t ⟩⊢∎
             rfl                                  ∎))
         ⊢v)
    where
    lemma :
      ∀ {u v} →
      Id (Id (wk[ 2 ]′ A) (wk[ 2 ]′ t) (var x1))
        (symmetry (wk[ 2 ]′ A) (var x1) (wk[ 2 ]′ t)
           (symmetry (wk[ 2 ]′ A) (wk[ 2 ]′ t) (var x1) (var x0)))
        (var x0)
        [ u , v ]₁₀ PE.≡
      Id (Id A t u) (symmetry A u t (symmetry A t u v)) v
    lemma =
      PE.cong₃ Id
        (PE.cong₃ Id wk₂-[,] wk₂-[,] PE.refl)
        (PE.trans symmetry-[] $
         PE.cong₄ symmetry
           wk₂-[,] PE.refl wk₂-[,]
           (PE.trans symmetry-[] $
            PE.cong₄ symmetry
              wk₂-[,] wk₂-[,] PE.refl PE.refl))
        PE.refl

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
    case Idⱼ′ (wk₁ ⊢A ⊢t) (var₀ ⊢A) of λ
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
-- Lemmas related to cast

opaque
  unfolding cast

  -- A typing rule for cast.

  ⊢cast :
    Γ ⊢ t ∷ Id (U l) A B →
    Γ ⊢ u ∷ A →
    Γ ⊢ cast l A B t u ∷ B
  ⊢cast ⊢t ⊢u =
    let ⊢l = inversion-U-Level (inversion-Id (wf-⊢ ⊢t) .proj₁) in
    ⊢subst (univ (var₀ (⊢U ⊢l))) ⊢t ⊢u

opaque
  unfolding cast

  -- A reduction rule for cast.

  cast-⇒′ :
    Γ ⊢ A ≡ A′ ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ cast l A A′ rfl t ⇒ t ∷ A
  cast-⇒′ A≡A′ ⊢t =
    let ⊢l = inversion-U-Level (wf-⊢ A≡A′ .proj₁) in
    subst-⇒′ (univ (var₀ (⊢U ⊢l))) A≡A′ ⊢t

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
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ B₁ ≡ B₂ ∷ U l₁ →
    Γ ⊢ t₁ ≡ t₂ ∷ Id (U l₁) A₁ B₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ cast l₁ A₁ B₁ t₁ u₁ ≡ cast l₂ A₂ B₂ t₂ u₂ ∷ B₁
  cast-cong l₁≡l₂ A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ =
    let ⊢U , ⊢A₁ , ⊢B₁ = inversion-Id (wf-⊢ t₁≡t₂ .proj₁) in
    subst-cong (U-cong-⊢≡ l₁≡l₂) (refl (univ (var₀ ⊢U))) A₁≡A₂ B₁≡B₂
      t₁≡t₂ u₁≡u₂

opaque
  unfolding cast

  -- A reduction rule for cast.

  cast-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Id (U l) A B →
    Γ ⊢ u ∷ A →
    Γ ⊢ cast l A B t₁ u ⇒ cast l A B t₂ u ∷ B
  cast-subst t₁⇒t₂ ⊢u =
    let ⊢l = inversion-U-Level $
             inversion-Id (wf-⊢ (subsetTerm t₁⇒t₂) .proj₁) .proj₁
    in
    subst-subst (univ (var₀ (⊢U ⊢l))) t₁⇒t₂ ⊢u

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

opaque

  -- A preservation lemma for cast.

  cast-cong-Id :
    Γ ⊢ v ∷ Id (Id (U l) A B) t₁ t₂ →
    Γ ⊢ w ∷ Id A u₁ u₂ →
    ∃ λ eq → Γ ⊢ eq ∷ Id B (cast l A B t₁ u₁) (cast l A B t₂ u₂)
  cast-cong-Id {v} {l} {A} {B} {t₁} {t₂} {w} {u₁} {u₂} ⊢v ⊢w =
    let ⊢Id , _    = inversion-Id (wf-⊢ ⊢v)
        _ , ⊢A , _ = inversion-Id ⊢Id
        ⊢A′        = wk₁ ⊢Id (univ ⊢A)
    in
    cong₂ ω (Id (U l) A B) t₁ t₂ A u₁ u₂ B
      (cast (wk[ 2 ]′ l) (wk[ 2 ]′ A) (wk[ 2 ]′ B) (var x1) (var x0)) v
      w ,
    PE.subst (_⊢_∷_ _ _) (PE.cong₂ (Id _) lemma lemma)
      (⊢cong₂
         (⊢cast
            (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $ var₁ ⊢A′)
            (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $ var₀ ⊢A′))
         ⊢v ⊢w)
    where
    lemma :
      cast (wk[ 2 ]′ l) (wk[ 2 ]′ A) (wk[ 2 ]′ B) (var x1) (var x0)
        [ t , u ]₁₀ PE.≡
      cast l A B t u
    lemma =
      PE.trans cast-[] $
      PE.cong₅ cast wk₂-[,] wk₂-[,] wk₂-[,] PE.refl PE.refl

------------------------------------------------------------------------
-- Lemmas related to cast⁻¹

opaque
  unfolding cast⁻¹

  -- An equality rule for cast⁻¹.

  cast⁻¹-cong :
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ B₁ ≡ B₂ ∷ U l₁ →
    Γ ⊢ t₁ ≡ t₂ ∷ Id (U l₁) A₁ B₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ B₁ →
    Γ ⊢ cast⁻¹ l₁ A₁ B₁ t₁ u₁ ≡ cast⁻¹ l₂ A₂ B₂ t₂ u₂ ∷ A₁
  cast⁻¹-cong l₁≡l₂ A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ =
    cast-cong l₁≡l₂ B₁≡B₂ A₁≡A₂
      (symmetry-cong (U-cong-⊢≡ l₁≡l₂) A₁≡A₂ B₁≡B₂ t₁≡t₂) u₁≡u₂

opaque

  -- A typing rule for cast⁻¹.

  ⊢cast⁻¹ :
    Γ ⊢ t ∷ Id (U l) A B →
    Γ ⊢ u ∷ B →
    Γ ⊢ cast⁻¹ l A B t u ∷ A
  ⊢cast⁻¹ ⊢t ⊢u =
    let ⊢U , ⊢A , ⊢B = inversion-Id (wf-⊢ ⊢t)
        ⊢l           = inversion-U-Level ⊢U
    in
    wf-⊢
      (cast⁻¹-cong (refl-⊢≡∷L ⊢l) (refl ⊢A) (refl ⊢B) (refl ⊢t)
         (refl ⊢u))
      .proj₂ .proj₁

opaque
  unfolding cast⁻¹

  -- A reduction rule for cast⁻¹.

  cast⁻¹-⇒′ :
    Γ ⊢ A ≡ A′ ∷ U l →
    Γ ⊢ t ∷ A′ →
    Γ ⊢ cast⁻¹ l A A′ rfl t ⇒* t ∷ A
  cast⁻¹-⇒′ {A} {A′} {l} {t} A≡A′ ⊢t =
    let ⊢U , ⊢A , _ = wf-⊢ A≡A′ in
    cast l A′ A (symmetry (U l) A A′ rfl) t  ⇒⟨ cast-subst (conv (symmetry-⇒′ A≡A′) (Id-cong (refl ⊢U) A≡A′ (refl ⊢A))) ⊢t ⟩
    cast l A′ A rfl t                        ⇒⟨ conv (cast-⇒′ (sym′ A≡A′) ⊢t) (sym (univ A≡A′)) ⟩∎
    t                                        ∎

opaque

  -- Another reduction rule for cast⁻¹.

  cast⁻¹-⇒ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ cast⁻¹ l A A rfl t ⇒* t ∷ A
  cast⁻¹-⇒ ⊢A ⊢t =
    cast⁻¹-⇒′ (refl ⊢A) ⊢t

opaque

  -- An equality rule for cast⁻¹.

  cast⁻¹-≡ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ cast⁻¹ l A A rfl t ≡ t ∷ A
  cast⁻¹-≡ ⊢A ⊢t =
    subset*Term (cast⁻¹-⇒ ⊢A ⊢t)

opaque
  unfolding cast⁻¹

  -- A reduction rule for cast⁻¹.

  cast⁻¹-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Id (U l) A B →
    Γ ⊢ u ∷ B →
    Γ ⊢ cast⁻¹ l A B t₁ u ⇒ cast⁻¹ l A B t₂ u ∷ A
  cast⁻¹-subst t₁⇒t₂ ⊢u =
    cast-subst (symmetry-subst t₁⇒t₂) ⊢u

opaque

  -- A reduction rule for cast⁻¹.

  cast⁻¹-subst* :
    Γ ⊢ t₁ ⇒* t₂ ∷ Id (U l) A B →
    Γ ⊢ u ∷ B →
    Γ ⊢ cast⁻¹ l A B t₁ u ⇒* cast⁻¹ l A B t₂ u ∷ A
  cast⁻¹-subst* = λ where
    (id ⊢t)          ⊢u → id (⊢cast⁻¹ ⊢t ⊢u)
    (t₁⇒t₃ ⇨ t₃⇒*t₂) ⊢u →
      cast⁻¹-subst t₁⇒t₃ ⊢u ⇨ cast⁻¹-subst* t₃⇒*t₂ ⊢u

opaque
  unfolding cast⁻¹

  -- An inversion lemma for cast⁻¹.

  inversion-cast⁻¹ :
    Γ ⊢ cast⁻¹ l A B t u ∷ C →
    Γ ⊢ t ∷ Id (U l) A B ×
    Γ ⊢ u ∷ B ×
    Γ ⊢ C ≡ A
  inversion-cast⁻¹ ⊢cast⁻¹ =
    let _ , _ , ⊢sym , ⊢u , C≡ = inversion-cast ⊢cast⁻¹ in
    inversion-symmetry ⊢sym .proj₁ , ⊢u , C≡

opaque
  unfolding cast⁻¹

  -- A preservation lemma for cast⁻¹.

  cast⁻¹-cong-Id :
    Γ ⊢ v ∷ Id (Id (U l) A B) t₁ t₂ →
    Γ ⊢ w ∷ Id B u₁ u₂ →
    ∃ λ eq → Γ ⊢ eq ∷ Id A (cast⁻¹ l A B t₁ u₁) (cast⁻¹ l A B t₂ u₂)
  cast⁻¹-cong-Id ⊢v ⊢w =
    cast-cong-Id (symmetry-cong-Id ⊢v .proj₂) ⊢w

------------------------------------------------------------------------
-- Some lemmas involving cast and cast⁻¹

opaque

  -- A simplification lemma involving cast⁻¹ and cast.

  Id-cast⁻¹-cast :
    Γ ⊢ t ∷ Id (U l) A B →
    Γ ⊢ u ∷ A →
    ∃ λ v → Γ ⊢ v ∷ Id A (cast⁻¹ l A B t (cast l A B t u)) u
  Id-cast⁻¹-cast {t} {l} {A} {B} {u} ⊢t ⊢u =
    let _ , ⊢A , _ = inversion-Id (wf-⊢ ⊢t)
        ⊢Id        = J-motive-context-type ⊢A
        ⊢0         = PE.subst (_⊢_∷_ _ _)
                       (PE.cong₃ Id wk[]≡wk[]′ wk[]≡wk[]′ PE.refl) $
                     var₀ ⊢Id
        ⊢u′        = W.wk (ʷ⊇-drop (∙ ⊢Id)) ⊢u
    in
    J ω ω (U l) A
      (Id (wk[ 2 ]′ A)
         (cast⁻¹ (wk[ 2 ]′ l) (wk[ 2 ]′ A) (var x1) (var x0)
            (cast (wk[ 2 ]′ l) (wk[ 2 ]′ A) (var x1) (var x0)
               (wk[ 2 ]′ u)))
         (wk[ 2 ]′ u))
      rfl B t ,
    PE.subst (_⊢_∷_ _ _)
      (Id (wk[ 2 ]′ A)
         (cast⁻¹ (wk[ 2 ]′ l) (wk[ 2 ]′ A) (var x1) (var x0)
            (cast (wk[ 2 ]′ l) (wk[ 2 ]′ A) (var x1) (var x0)
               (wk[ 2 ]′ u)))
         (wk[ 2 ]′ u)
       [ B , t ]₁₀                                                 ≡⟨ PE.cong₃ Id
                                                                        wk₂-[,]
                                                                        (PE.trans cast⁻¹-[] $
                                                                         PE.cong₅ cast⁻¹
                                                                           wk₂-[,] wk₂-[,] PE.refl PE.refl
                                                                           (PE.trans cast-[] $
                                                                            PE.cong₅ cast wk₂-[,] wk₂-[,] PE.refl PE.refl wk₂-[,]))
                                                                        wk₂-[,] ⟩
       Id A (cast⁻¹ l A B t (cast l A B t u)) u                    ∎)
      (Jⱼ′ (Idⱼ′ (⊢cast⁻¹ ⊢0 (⊢cast ⊢0 ⊢u′)) ⊢u′)
         (_⊢_∷_.conv (rflⱼ ⊢u) $ univ
            (Id A u u                                                 ≡˘⟨ Id-cong (refl ⊢A) (cast-≡ ⊢A ⊢u) (refl ⊢u) ⟩⊢

             Id A (cast l A A rfl u) u                                ≡˘⟨ Id-cong (refl ⊢A) (cast⁻¹-≡ ⊢A (⊢cast (rflⱼ ⊢A) ⊢u)) (refl ⊢u) ⟩⊢∎≡

             Id A (cast⁻¹ l A A rfl (cast l A A rfl u)) u             ≡˘⟨ PE.cong₃ Id
                                                                            wk₂-[,]
                                                                            (PE.trans cast⁻¹-[] $
                                                                             PE.cong₅ cast⁻¹
                                                                               wk₂-[,] wk₂-[,] PE.refl PE.refl
                                                                               (PE.trans cast-[] $
                                                                                PE.cong₅ cast wk₂-[,] wk₂-[,] PE.refl PE.refl wk₂-[,]))
                                                                            wk₂-[,] ⟩
             Id (wk[ 2 ]′ A)
               (cast⁻¹ (wk[ 2 ]′ l) (wk[ 2 ]′ A) (var x1) (var x0)
                  (cast (wk[ 2 ]′ l) (wk[ 2 ]′ A) (var x1) (var x0)
                     (wk[ 2 ]′ u)))
               (wk[ 2 ]′ u)
             [ A , rfl ]₁₀                                            ∎))
         ⊢t)

opaque
  unfolding cast⁻¹

  -- A simplification lemma involving cast and cast⁻¹.

  Id-cast-cast⁻¹ :
    Γ ⊢ t ∷ Id (U l) A B →
    Γ ⊢ u ∷ B →
    ∃ λ v → Γ ⊢ v ∷ Id B (cast l A B t (cast⁻¹ l A B t u)) u
  Id-cast-cast⁻¹ ⊢t ⊢u =
    _ ,
    ⊢transitivity
      (⊢symmetry $
       cast-cong-Id (Id-symmetry-symmetry ⊢t .proj₂)
         (rflⱼ (⊢cast⁻¹ ⊢t ⊢u)) .proj₂)
      (Id-cast⁻¹-cast (⊢symmetry ⊢t) ⊢u .proj₂)

opaque
  unfolding cast⁻¹

  -- A simplification lemma involving cast⁻¹, symmetry and cast.

  Id-cast⁻¹-symmetry :
    Γ ⊢ t ∷ Id (U l) A B →
    Γ ⊢ u ∷ A →
    ∃ λ v →
      Γ ⊢ v ∷
        Id B (cast⁻¹ l B A (symmetry (U l) A B t) u) (cast l A B t u)
  Id-cast⁻¹-symmetry ⊢t ⊢u =
    cast-cong-Id (Id-symmetry-symmetry ⊢t .proj₂) (rflⱼ ⊢u)

opaque

  -- An equality of the form "t₁ is equal to a cast of t₂" can be
  -- turned into an equality of the form "a cast of t₁ is equal to
  -- t₂".

  cast-right-left :
    Γ ⊢ u ∷ Id (U l) A₁ A₂ →
    Γ ⊢ v ∷ Id A₂ t₁ (cast l A₁ A₂ u t₂) →
    ∃ λ v → Γ ⊢ v ∷ Id A₁ (cast⁻¹ l A₁ A₂ u t₁) t₂
  cast-right-left {u} {l} {A₁} {A₂} {t₁} {t₂} ⊢u ⊢v =
    let ⊢A₂ , _ , ⊢cast-t₂  = inversion-Id (wf-⊢ ⊢v)
        _ , _ , _ , ⊢t₂ , _ = inversion-cast ⊢cast-t₂
    in
    _ ,
    PE.subst (_⊢_∷_ _ _)
      (Id A₁ (cast⁻¹ (wk1 l) (wk1 A₁) (wk1 A₂) (wk1 u) (var x0) [ t₁ ]₀)
         t₂                                                               ≡⟨ PE.cong₂ (Id _)
                                                                               (PE.trans cast⁻¹-[] $
                                                                                PE.cong₅ cast⁻¹ (wk1-sgSubst _ _) (wk1-sgSubst _ _)
                                                                                  (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl)
                                                                               PE.refl ⟩
       Id A₁ (cast⁻¹ l A₁ A₂ u t₁) t₂                                     ∎)
      (⊢transitivity
         (⊢cong {p = ω} (⊢cast⁻¹ (wk₁ ⊢A₂ ⊢u) (var₀ ⊢A₂)) ⊢v)
         (PE.subst (_⊢_∷_ _ _)
            (Id A₁ (cast⁻¹ l A₁ A₂ u (cast l A₁ A₂ u t₂)) t₂       ≡˘⟨ PE.cong₂ (Id _)
                                                                           (PE.trans cast⁻¹-[] $
                                                                            PE.cong₅ cast⁻¹ (wk1-sgSubst _ _) (wk1-sgSubst _ _) (wk1-sgSubst _ _)
                                                                              (wk1-sgSubst _ _) PE.refl)
                                                                           PE.refl ⟩
             Id A₁
               (cast⁻¹ (wk1 l) (wk1 A₁) (wk1 A₂) (wk1 u) (var x0)
                  [ cast l A₁ A₂ u t₂ ]₀)
               t₂                                                  ∎) $
          Id-cast⁻¹-cast ⊢u ⊢t₂ .proj₂))

opaque
  unfolding cast⁻¹

  -- A variant of cast-right-left.

  cast-right-left′ :
    Γ ⊢ u ∷ Id (U l) A₁ A₂ →
    Γ ⊢ v ∷ Id A₁ t₁ (cast⁻¹ l A₁ A₂ u t₂) →
    ∃ λ v → Γ ⊢ v ∷ Id A₂ (cast l A₁ A₂ u t₁) t₂
  cast-right-left′ ⊢u ⊢v =
    let _ , ⊢t₁ , _ = inversion-Id (wf-⊢ ⊢v) in
    _ ,
    ⊢transitivity (⊢symmetry (Id-cast⁻¹-symmetry ⊢u ⊢t₁ .proj₂))
      (cast-right-left (⊢symmetry ⊢u) ⊢v .proj₂)

opaque

  -- An equality of the form "a cast of t₁ is equal to t₂" can be
  -- turned into an equality of the form "t₁ is equal to a cast of
  -- t₂".

  cast-left-right :
    Γ ⊢ u ∷ Id (U l) A₁ A₂ →
    Γ ⊢ v ∷ Id A₂ (cast l A₁ A₂ u t₁) t₂ →
    ∃ λ v → Γ ⊢ v ∷ Id A₁ t₁ (cast⁻¹ l A₁ A₂ u t₂)
  cast-left-right ⊢u ⊢v =
    _ , ⊢symmetry (cast-right-left ⊢u (⊢symmetry ⊢v) .proj₂)

opaque
  unfolding cast⁻¹

  -- A variant of cast-left-right.

  cast-left-right′ :
    Γ ⊢ u ∷ Id (U l) A₁ A₂ →
    Γ ⊢ v ∷ Id A₁ (cast⁻¹ l A₁ A₂ u t₁) t₂ →
    ∃ λ v → Γ ⊢ v ∷ Id A₂ t₁ (cast l A₁ A₂ u t₂)
  cast-left-right′ ⊢u ⊢v =
    let _ , _ , ⊢t₂ = inversion-Id (wf-⊢ ⊢v) in
    _ ,
    ⊢transitivity (cast-left-right (⊢symmetry ⊢u) ⊢v .proj₂)
      (Id-cast⁻¹-symmetry ⊢u ⊢t₂ .proj₂)

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
               (wk₁ (J-motive-context-type ⊢t) (wk₁ ⊢A ⊢eq₂)) $
             ⊢transitivity
               (⊢symmetry
                  (wk₁ (J-motive-context-type ⊢t)
                     (wk₁ ⊢A ⊢eq₁))) $
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
            (Idⱼ′ (rflⱼ (wk₁ ⊢Id-t-t ⊢t)) (var₀ ⊢Id-t-t))
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
            (⊢transitivity (wk₁ ⊢Id-u-u ⊢eq₂) (var₀ ⊢Id-u-u))
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

  -- Is-function-extensionality p q p′ q′ l₁ l₂ Γ t means that t
  -- implements a certain formulation of function extensionality for
  -- the context pair Γ.

  Is-function-extensionality :
    M → M → M → M → Lvl n → Lvl n → Cons m n → Term n → Set a
  Is-function-extensionality p q p′ q′ l₁ l₂ Γ t =
    Γ ⊢ t ∷ Funext p q p′ q′ l₁ l₂

opaque

  -- Has-function-extensionality p q p′ q′ l₁ l₂ Γ means that a
  -- certain formulation of function extensionality holds for the
  -- context pair Γ.

  Has-function-extensionality :
    M → M → M → M → Lvl n → Lvl n → Cons m n → Set a
  Has-function-extensionality p q p′ q′ l₁ l₂ Γ =
    ∃ (Is-function-extensionality p q p′ q′ l₁ l₂ Γ)

opaque

  -- Extends the context pair with the assumption that a certain
  -- instance of function extensionality holds.

  with-function-extensionality-assumption :
    M → M → M → M → Lvl n → Lvl n → Cons m n → Cons m (1+ n)
  with-function-extensionality-assumption p q p′ q′ l₁ l₂ Γ =
    Γ »∙ Funext p q p′ q′ l₁ l₂

private opaque

  -- Some lemmas used below.

  ⊢Π3Id′ :
    Π-allowed p q →
    Η ⊢ l₁ ∷Level →
    Η »∙ U l₁ »∙ var x0 ⊢ wk[ 2 ]′ l₂ ∷Level →
    Η »∙ U l₁ »∙ Π p , q ▷ var x0 ▹ U (wk[ 2 ]′ l₂) »∙
    Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) »∙
    Π p , q ▷ var x2 ▹ (var x2 ∘⟨ p ⟩ var x0) ⊢
    Π p , q ▷ var x3 ▹
    Id (var x3 ∘⟨ p ⟩ var x0)
      (var x2 ∘⟨ p ⟩ var x0) (var x1 ∘⟨ p ⟩ var x0)
  ⊢Π3Id′ {p} {q} {Η} {l₁} {l₂} ok ⊢l₁ ⊢l₂ =
    flip _⊢_.ΠΣⱼ ok $
    Idⱼ′ (var₂ ⊢3 ∘ⱼ var₀ ⊢3) (var₁ ⊢3 ∘ⱼ var₀ ⊢3)
    where
    ⊢1 : Η »∙ U l₁ »∙ Π p , q ▷ var x0 ▹ U (wk[ 2 ]′ l₂) ⊢ var x1
    ⊢1 = univ (var₁ (ΠΣⱼ (⊢U ⊢l₂) ok))

    ⊢2 :
      Η »∙ U l₁ »∙ Π p , q ▷ var x0 ▹ U (wk[ 2 ]′ l₂) »∙
      Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) ⊢
      var x2
    ⊢2 =
      _⊢_.univ $ var₂ $ flip _⊢_.ΠΣⱼ ok $
      univ (var₁ ⊢1 ∘ⱼ var₀ ⊢1)

    ⊢3 :
      Η »∙ U l₁ »∙ Π p , q ▷ var x0 ▹ U (wk[ 2 ]′ l₂) »∙
      Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) »∙
      Π p , q ▷ var x2 ▹ (var x2 ∘⟨ p ⟩ var x0) ⊢
      var x3
    ⊢3 =
      _⊢_.univ $ var₃ $ flip _⊢_.ΠΣⱼ ok $
      univ (var₂ ⊢2 ∘ⱼ var₀ ⊢2)

  ⊢Π3Id :
    Π-allowed p q →
    Η ⊢ l₁ ∷Level →
    Η ⊢ l₂ ∷Level →
    Η »∙ U l₁ »∙ Π p , q ▷ var x0 ▹ U (wk[ 2 ]′ l₂) »∙
    Π p , q ▷ var x1 ▹ (var x1 ∘⟨ p ⟩ var x0) »∙
    Π p , q ▷ var x2 ▹ (var x2 ∘⟨ p ⟩ var x0) ⊢
    Π p , q ▷ var x3 ▹
    Id (var x3 ∘⟨ p ⟩ var x0)
      (var x2 ∘⟨ p ⟩ var x0) (var x1 ∘⟨ p ⟩ var x0)
  ⊢Π3Id ok ⊢l₁ ⊢l₂ =
    ⊢Π3Id′ ok ⊢l₁ (W.wk (ʷ⊇-drop (∙ univ (var₀ (⊢U ⊢l₁)))) ⊢l₂)

opaque
  unfolding
    Funext Has-function-extensionality Is-function-extensionality
    with-function-extensionality-assumption

  -- If l₁ and l₂ are well-typed levels with respect to Η, and certain
  -- Π-types are allowed, then the context
  -- with-function-extensionality-assumption p q p′ q′ l₁ l₂ Η
  -- satisfies
  -- Has-function-extensionality p q p′ q′ (wk1 l₁) (wk1 l₂).

  Has-function-extensionality-with-function-extensionality-assumption :
    Π-allowed p q →
    Π-allowed p′ q′ →
    Η ⊢ l₁ ∷Level →
    Η ⊢ l₂ ∷Level →
    Has-function-extensionality p q p′ q′ (wk1 l₁) (wk1 l₂)
      (with-function-extensionality-assumption p q p′ q′ l₁ l₂ Η)
  Has-function-extensionality-with-function-extensionality-assumption
    ok ok′ ⊢l₁ ⊢l₂ =
    let ⊢Π3Id = ⊢Π3Id ok ⊢l₁ ⊢l₂ in
    var x0 ,
    (PE.subst (_⊢_∷_ _ _) wk-Funext $
     var₀ $
     flip _⊢_.ΠΣⱼ ok $ flip _⊢_.ΠΣⱼ ok′ $ flip _⊢_.ΠΣⱼ ok′ $
     flip _⊢_.ΠΣⱼ ok′ $ flip _⊢_.ΠΣⱼ ok′ $
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
    equality-reflection ok (wf-⊢ ⊢v) ⊢v

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
      (wk₁ ⊢A ⊢v ∘ⱼ var₀ ⊢A)

opaque
  unfolding Funext funext

  -- A typing rule for funext.

  ⊢funext′ :
    Equality-reflection →
    Π-allowed p q →
    Π-allowed p′ q′ →
    Γ ⊢ l₁ ∷Level →
    Γ »∙ U l₁ »∙ var x0 ⊢ wk[ 2 ]′ l₂ ∷Level →
    Γ ⊢ funext p p′ ∷ Funext p q p′ q′ l₁ l₂
  ⊢funext′ ok Π-ok Π-ok′ ⊢l₁ ⊢l₂ =
    let ⊢Π3Id = ⊢Π3Id′ Π-ok ⊢l₁ ⊢l₂ in
    lamⱼ′ Π-ok $ lamⱼ′ Π-ok′ $ lamⱼ′ Π-ok′ $ lamⱼ′ Π-ok′ $ lamⱼ′ Π-ok′ $
    function-extensionality-Π ok (var₂ ⊢Π3Id) (var₁ ⊢Π3Id)
      (var₀ ⊢Π3Id)

opaque

  -- A variant of ⊢funext′.

  ⊢funext :
    Equality-reflection →
    Π-allowed p q →
    Π-allowed p′ q′ →
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ funext p p′ ∷ Funext p q p′ q′ l₁ l₂
  ⊢funext ok Π-ok Π-ok′ ⊢l₁ ⊢l₂ =
    ⊢funext′ ok Π-ok Π-ok′ ⊢l₁
      (W.wk (ʷ⊇-drop (∙ univ (var₀ (⊢U ⊢l₁)))) ⊢l₂)

opaque
  unfolding Has-function-extensionality Is-function-extensionality

  -- In the presence of equality reflection
  -- Has-function-extensionality p q p′ q′ holds for all well-formed
  -- levels (assuming that certain Π-types are allowed).

  has-function-extensionality :
    Equality-reflection →
    Π-allowed p q →
    Π-allowed p′ q′ →
    Η ⊢ l₁ ∷Level →
    Η ⊢ l₂ ∷Level →
    Has-function-extensionality p q p′ q′ l₁ l₂ Η
  has-function-extensionality {p} {p′} ok Π-ok Π-ok′ ⊢l₁ ⊢l₂ =
    funext p p′ ,
    ⊢funext ok Π-ok Π-ok′ ⊢l₁ ⊢l₂

opaque
  unfolding Poly-funext poly-funext

  -- A typing rule for poly-funext.

  ⊢poly-funext :
    Equality-reflection →
    Level-allowed →
    Π-allowed p q →
    Π-allowed p′ q′ →
    ⊢ Γ →
    Γ ⊢ poly-funext p p′ ∷ Poly-funext p q p′ q′
  ⊢poly-funext ok okᴸ Π-ok Π-ok′ ⊢Γ =
    let L⊢L = Levelⱼ′ okᴸ (∙ Levelⱼ′ okᴸ ⊢Γ) in
    lamⱼ′ Π-ok $ lamⱼ′ Π-ok $
    ⊢funext ok Π-ok Π-ok′ (term-⊢∷ (var₁ L⊢L)) (term-⊢∷ (var₀ L⊢L))

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
          ⊢Id         = var₀ $ Idⱼ′ (wk₁ ⊢A ⊢t) (var₀ ⊢A)
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
    Γ ⊢ l ∷Level →
    Γ ⊢ eq ∷ Id A t u →
    Γ ⊢ rfl ∷ Id (Erased l A) [ t ] ([ u ])
  []-cong-with-equality-reflection ok₁ ok₂ ⊢l ⊢eq =
    let ⊢A , _ = inversion-Id (syntacticTerm ⊢eq) in
    rflⱼ′ (EP.[]-cong′ ok₂ ⊢l ⊢A (equality-reflection′ ok₁ ⊢eq))
