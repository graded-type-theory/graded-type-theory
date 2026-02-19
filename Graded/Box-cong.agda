------------------------------------------------------------------------
-- Some discussion of under what circumstances a []-cong combinator or
-- term former can be defined
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Box-cong
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TR : Type-restrictions 𝕄)
  (open Type-restrictions TR)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions UR

open import Definition.Conversion.Consequences.Var TR
open import Definition.Typed TR
open import Definition.Typed.Consequences.Admissible TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Decidable.Internal TR
import Definition.Typed.Decidable.Internal.Context TR as IC
import Definition.Typed.Decidable.Internal.Substitution TR as IS
import Definition.Typed.Decidable.Internal.Term TR as I
import Definition.Typed.Decidable.Internal.Weakening TR as IW
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR as P hiding ([]-cong′)
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Substitution TR
open import Definition.Typed.Syntactic TR
open import Definition.Typed.Weakening TR as W using (_»_∷ʷ_⊇_)
import Definition.Typed.Weakening.Definition TR as WD
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄 as UI
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Whnf M type-variant

open UI.Internal TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
import Graded.Derived.Erased.Usage 𝕄 UR as ErasedU
open import Graded.Derived.Identity UR
open import Graded.Erasure.Extraction 𝕄
import Graded.Erasure.Target as T
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Neutral TR UR
open import Graded.Reduction TR UR
open import Graded.Restrictions 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR

open import Tools.Bool using (Bool; T; true)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
import Tools.List as L
open import Tools.Maybe
open import Tools.Nat using (Nat; 1+; 2+; 3+; 4+; 5+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)
import Tools.Vec as V

private variable
  b                                                : Bool
  n n′ n₁ n₂                                       : Nat
  Δ                                                : Con Term _
  Γ                                                : Cons _ _
  A A₁ A₂ B C l l₁ l₂ t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ w : Term _
  sᵢ                                               : I.Termˢ _
  σ                                                : Subst _ _
  p p₁ p₁′ p₂ p₂′ p₃ p₃′ p₄ p₄′
    q q₁ q₁′ q₂ q₂′ q₃ q₃′ q₄ q₄′ q₅ q₅′           : M
  γ γ₁ γ₂ γ₃ γ₄ γ₅                                 : Conₘ _
  m                                                : Mode
  s                                                : Strength
  sem                                              : Some-erased-matches
  str                                              : T.Strictness
  ok                                               : T _

------------------------------------------------------------------------
-- Some lemmas

private opaque

  -- Some lemmas used below.

  ⊢Id-2-1-0′ :
    Γ ⊢ l ∷Level →
    Γ »∙ U l »∙ var x0 »∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0′ {Γ} {l} ⊢l = Idⱼ′ (var₁ ⊢1) (var₀ ⊢1)
    where
    ⊢1 : Γ »∙ U l »∙ var x0 ⊢ var x1
    ⊢1 = univ (var₁ (univ (var₀ (⊢U ⊢l))))

  ⊢Id-2-1-0 :
    Level-allowed →
    ⊢ Γ →
    Γ »∙ Level »∙ U (var x0) »∙ var x0 »∙ var x1 ⊢
      Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0 ok ⊢Γ = ⊢Id-2-1-0′ (term-⊢∷ (var₀ (Levelⱼ′ ok ⊢Γ)))

  Id-[]₀≡ :
    let open Erased s in
    Id (Erased (wk1 l) (wk1 A)) [ wk1 t ] ([ var x0 ]) [ u ]₀ PE.≡
    Id (Erased l A) [ t ] ([ u ])
  Id-[]₀≡ {s} = PE.cong₃ Id
    (PE.trans Erased-[] $
     PE.cong₂ Erased (wk1-sgSubst _ _) (wk1-sgSubst _ _))
    (PE.trans []-[] $
     PE.cong ([_]) $ wk1-sgSubst _ _)
    []-[]
    where
    open Erased s

  ·ᶜ𝟘ᶜ,≔ :
    (x : Fin n) →
    p ·ᶜ (𝟘ᶜ , x ≔ q) ≈ᶜ 𝟘ᶜ , x ≔ p · q
  ·ᶜ𝟘ᶜ,≔ {p} {q} x = begin
    p ·ᶜ (𝟘ᶜ , x ≔ q)    ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩
    p ·ᶜ 𝟘ᶜ , x ≔ p · q  ≈⟨ update-congˡ (·ᶜ-zeroʳ _) ⟩
    𝟘ᶜ , x ≔ p · q       ∎
    where
    open ≈ᶜ-reasoning

  ·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ :
    ∀ m (x : Fin n) →
    p ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ᵐ· p ⌝) ≈ᶜ 𝟘ᶜ , x ≔ ⌜ m ⌝ · p
  ·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ {p} m x = begin
    p ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ᵐ· p ⌝)  ≈⟨ ·ᶜ𝟘ᶜ,≔ _ ⟩
    𝟘ᶜ , x ≔ p · ⌜ m ᵐ· p ⌝     ≈⟨ update-congʳ (·⌜ᵐ·⌝ m) ⟩
    𝟘ᶜ , x ≔ p · ⌜ m ⌝          ≈˘⟨ update-congʳ (⌜⌝-·-comm m) ⟩
    𝟘ᶜ , x ≔ ⌜ m ⌝ · p          ∎
    where
    open ≈ᶜ-reasoning

------------------------------------------------------------------------
-- []-cong-J

opaque

  -- A variant of []-cong that can be used when erased matches are
  -- available for J and 𝟘ᵐ is allowed, when the mode is 𝟘ᵐ[ ok ], or
  -- when the modality is trivial. Note that the lemmas in this
  -- section do not include assumptions of the form
  -- "[]-cong-allowed s".

  []-cong-J :
    Strength → Term n → Term n → Term n → Term n → Term n → Term n
  []-cong-J s l A t u v =
    subst 𝟘 A (Id (Erased (wk1 l) (wk1 A)) [ wk1 t ] ([ var x0 ])) t u v
      rfl
    where
    open Erased s

opaque
  unfolding []-cong-J

  -- A usage rule for []-cong-J.

  ▸[]-cong-J :
    erased-matches-for-J m PE.≡ not-none sem →
    γ₁ ▸[ 𝟘ᵐ[ ok ] ] l →
    γ₂ ▸[ 𝟘ᵐ[ ok ] ] A →
    γ₃ ▸[ 𝟘ᵐ[ ok ] ] t →
    γ₄ ▸[ 𝟘ᵐ[ ok ] ] u →
    γ₅ ▸[ 𝟘ᵐ[ ok ] ] v →
    𝟘ᶜ ▸[ m ] []-cong-J s l A t u v
  ▸[]-cong-J {m} {ok} {s} ≡not-none ▸l ▸A ▸t ▸u ▸v =
    let ▸l = ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) (▸-𝟘 ▸l)
        ▸A = ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) (▸-𝟘 ▸A)
        ▸t = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t
        ▸u = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸u
        ▸v = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸v
    in
    case PE.singleton $ erased-matches-for-J m of λ where
      (not-none _ , ≡not-none) → sub
        (▸subst-𝟘 ≡not-none ▸A
           (Idₘ-generalised (▸Erased (wkUsage _ ▸l) (wkUsage _ ▸A))
              (▸[] (wkUsage _ ▸t)) (▸[] var)
              (λ _ → ≤ᶜ-refl)
              (λ _ → begin
                 𝟘ᶜ                ≈˘⟨ ≈ᶜ-trans (+ᶜ-congˡ (+ᶜ-identityʳ _)) (+ᶜ-identityʳ _) ⟩
                 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎))
            ▸t ▸u ▸v rflₘ)
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (none , ≡none) →
        case PE.trans (PE.sym ≡not-none) ≡none of λ ()
    where
    open ≤ᶜ-reasoning
    open ErasedU s

opaque
  unfolding []-cong-J

  -- Another usage rule for []-cong-J.

  ▸[]-cong-J-𝟘ᵐ :
    γ₁ ▸[ 𝟘ᵐ[ ok ] ] l →
    γ₂ ▸[ 𝟘ᵐ[ ok ] ] A →
    γ₃ ▸[ 𝟘ᵐ[ ok ] ] t →
    γ₄ ▸[ 𝟘ᵐ[ ok ] ] u →
    γ₅ ▸[ 𝟘ᵐ[ ok ] ] v →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] []-cong-J s l A t u v
  ▸[]-cong-J-𝟘ᵐ {γ₂} {s} ▸l ▸A ▸t ▸u ▸v =
    let ▸A = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A
        ▸l = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸l
    in
    ▸-𝟘 $
    ▸subst ▸A
      (Idₘ-generalised (▸Erased (wkUsage _ ▸l) (wkUsage _ ▸A))
         (▸[] (wkUsage (step id) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t))) (▸[] var)
         (λ _ → begin
            γ₂ ∧ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            γ₂ ∧ᶜ 𝟘ᶜ ∙ 𝟘      ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙ ≤-refl ⟩
            𝟘ᶜ                ∎)
         (λ _ → begin
            γ₂ ∧ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟘      ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            γ₂ ∧ᶜ 𝟘ᶜ ∙ 𝟘          ≤⟨ ∧ᶜ-decreasingˡ _ _ ∙ ≤-refl ⟩
            γ₂ ∙ 𝟘                ≈˘⟨ ≈ᶜ-trans (+ᶜ-congˡ (+ᶜ-identityʳ _)) (+ᶜ-identityʳ _) ⟩
            (γ₂ ∙ 𝟘) +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎))
      ▸t ▸u ▸v rflₘ
    where
    open ErasedU s
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque
  unfolding []-cong-J

  -- A usage rule for []-cong-J that can be used if the modality is
  -- trivial.

  ▸[]-cong-J-trivial :
    Trivial →
    γ₁ ▸[ 𝟘ᵐ? ] l →
    γ₂ ▸[ 𝟘ᵐ? ] A →
    γ₃ ▸[ 𝟘ᵐ? ] t →
    γ₄ ▸[ 𝟘ᵐ? ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    𝟘ᶜ ▸[ m ] []-cong-J s l A t u v
  ▸[]-cong-J-trivial {s} trivial ▸l ▸A ▸t ▸u ▸v =
    flip sub (≈ᶜ-trivial trivial) $
    ▸-trivial trivial $
    ▸subst {γ₂ = 𝟘ᶜ}
      ▸A
      (Idₘ-generalised (▸Erased (wkUsage _ ▸l) (wkUsage _ ▸A))
         (▸[] $ wkUsage (step id) $ ▸-trivial trivial ▸t) (▸[] var)
         (λ _ → ≈ᶜ-trivial trivial)
         (λ _ → ≈ᶜ-trivial trivial))
      ▸t
      ▸u
      ▸v
      rflₘ
    where
    open ErasedU s

opaque
  unfolding []-cong-J

  -- A typing rule for []-cong-J.

  []-cong-Jⱼ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ l ∷Level →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ []-cong-J s l A t u v ∷ Id (Erased l A) [ t ] ([ u ])
  []-cong-Jⱼ ok ⊢l ⊢v =
    let ⊢A , ⊢t , _ = inversion-Id (syntacticTerm ⊢v)
        ⊢wk1-l      = W.wkLevel₁ ⊢A ⊢l
    in
    PE.subst (_⊢_∷_ _ _) Id-[]₀≡ $
    ⊢subst
      (Idⱼ′ ([]ⱼ ok ⊢wk1-l (W.wkTerm₁ ⊢A ⊢t))
         ([]ⱼ ok ⊢wk1-l (var₀ ⊢A)))
      ⊢v
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢l ⊢t))

opaque
  unfolding []-cong-J

  -- A reduction rule for []-cong-J.

  []-cong-J-β-⇒′ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ l ∷Level →
    Γ ⊢ t ≡ t′ ∷ A →
    Γ ⊢ []-cong-J s l A t t′ rfl ⇒ rfl ∷ Id (Erased l A) [ t ] ([ t′ ])
  []-cong-J-β-⇒′ {s} {t} {t′} ok ⊢l t≡t′ =
    let ⊢A , ⊢t , _ = syntacticEqTerm t≡t′
        ⊢wk1-l      = W.wkLevel₁ ⊢A ⊢l
    in
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    conv
      (subst-⇒′
         (Idⱼ′ ([]ⱼ ok ⊢wk1-l (W.wkTerm₁ ⊢A ⊢t))
            ([]ⱼ ok ⊢wk1-l (var₀ ⊢A)))
         t≡t′
         (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
         rflⱼ ([]ⱼ ok ⊢l ⊢t)))
      (Id-cong
         (PE.subst₂ (_⊢_≡_ _)
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased)
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased) $
          refl (Erasedⱼ ok ⊢l ⊢A))
         (PE.subst₃ (_⊢_≡_∷_ _)
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-[])
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-[])
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased) $
          P.[]-cong′ ok ⊢l (refl ⊢t))
         (PE.subst₃ (_⊢_≡_∷_ _) (PE.sym []-[]) (PE.sym []-[])
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased) $
          P.[]-cong′ ok ⊢l t≡t′))
    where
    open Erased s

opaque

  -- Another reduction rule for []-cong-J.

  []-cong-J-β-⇒ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ l ∷Level →
    Γ ⊢ t ∷ A →
    Γ ⊢ []-cong-J s l A t t rfl ⇒ rfl ∷ Id (Erased l A) [ t ] ([ t ])
  []-cong-J-β-⇒ ok ⊢l ⊢t = []-cong-J-β-⇒′ ok ⊢l (refl ⊢t)

opaque

  -- An equality rule for []-cong-J.

  []-cong-J-β-≡ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ l ∷Level →
    Γ ⊢ t ∷ A →
    Γ ⊢ []-cong-J s l A t t rfl ≡ rfl ∷ Id (Erased l A) [ t ] ([ t ])
  []-cong-J-β-≡ ok ⊢l ⊢t = subsetTerm ([]-cong-J-β-⇒ ok ⊢l ⊢t)

opaque
  unfolding []-cong-J

  -- An equality rule for []-cong-J.

  []-cong-J-cong :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ []-cong-J s l₁ A₁ t₁ u₁ v₁ ≡ []-cong-J s l₂ A₂ t₂ u₂ v₂ ∷
      Id (Erased l₁ A₁) [ t₁ ] ([ u₁ ])
  []-cong-J-cong ok l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    let ⊢l₁ , _ = wf-⊢≡∷L l₁≡l₂
        ⊢A₁ , _ = wf-⊢≡ A₁≡A₂
        ⊢wk1-l₁ = W.wkLevel₁ ⊢A₁ ⊢l₁
    in
    PE.subst (_⊢_≡_∷_ _ _ _) Id-[]₀≡ $
    subst-cong A₁≡A₂
      (Id-cong
         (Erased-cong ok (W.wkEqLevel₁ ⊢A₁ l₁≡l₂)
            (W.wkEq₁ ⊢A₁ A₁≡A₂))
         (P.[]-cong′ ok ⊢wk1-l₁ (W.wkEqTerm₁ ⊢A₁ t₁≡t₂))
         (refl ([]ⱼ ok ⊢wk1-l₁ (var₀ ⊢A₁))))
      t₁≡t₂ u₁≡u₂ v₁≡v₂
      (_⊢_≡_∷_.refl $
       PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢l₁ (wf-⊢≡∷ t₁≡t₂ .proj₂ .proj₁)))

opaque
  unfolding []-cong-J

  -- A reduction rule for []-cong-J.

  []-cong-J-subst :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ l ∷Level →
    Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
    Γ ⊢ []-cong-J s l A t u v₁ ⇒ []-cong-J s l A t u v₂ ∷
      Id (Erased l A) [ t ] ([ u ])
  []-cong-J-subst ok ⊢l v₁⇒v₂ =
    let ⊢A , ⊢t , _ = inversion-Id (wf-⊢≡∷ (subsetTerm v₁⇒v₂) .proj₁)
        ⊢wk1-l      = W.wkLevel₁ ⊢A ⊢l
    in
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    subst-subst
      (Idⱼ′ ([]ⱼ ok ⊢wk1-l (W.wkTerm₁ ⊢A ⊢t))
         ([]ⱼ ok ⊢wk1-l (var₀ ⊢A)))
      v₁⇒v₂
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢l ⊢t))

opaque
  unfolding []-cong-J

  -- A substitution lemma for []-cong-J.

  []-cong-J-[] :
    []-cong-J s l A t u v [ σ ] PE.≡
    []-cong-J s (l [ σ ]) (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
  []-cong-J-[] {s} {l} {A} {t} {u} {v} {σ} =
    subst 𝟘 A (Id (Erased (wk1 l) (wk1 A)) [ wk1 t ] ([ var x0 ]))
      t u v rfl U.[ σ ]                                             ≡⟨ subst-[] ⟩

    subst 𝟘 (A U.[ σ ])
      (Id (Erased (wk1 l) (wk1 A) U.[ σ ⇑ ]) ([ wk1 t ] U.[ σ ⇑ ])
         ([ var x0 ] U.[ σ ⇑ ]))
      (t U.[ σ ]) (u U.[ σ ]) (v U.[ σ ]) rfl                       ≡⟨ PE.cong₅ (subst _ _)
                                                                         (PE.cong₃ Id Erased-[] []-[] []-[])
                                                                         PE.refl PE.refl PE.refl PE.refl ⟩
    subst 𝟘 (A U.[ σ ])
      (Id (Erased (wk1 l U.[ σ ⇑ ]) (wk1 A U.[ σ ⇑ ]))
         [ wk1 t U.[ σ ⇑ ] ] ([ var x0 ]))
      (t U.[ σ ]) (u U.[ σ ]) (v U.[ σ ]) rfl                       ≡⟨ PE.cong₅ (subst _ _)
                                                                         (PE.cong₃ Id
                                                                            (PE.cong₂ Erased (wk1-liftSubst l) (wk1-liftSubst A))
                                                                            (PE.cong [_] (wk1-liftSubst t))
                                                                            PE.refl)
                                                                         PE.refl PE.refl PE.refl PE.refl ⟩
    subst 𝟘 (A U.[ σ ])
      (Id (Erased (wk1 (l U.[ σ ])) (wk1 (A U.[ σ ])))
         [ wk1 (t U.[ σ ]) ] ([ var x0 ]))
      (t U.[ σ ]) (u U.[ σ ]) (v U.[ σ ]) rfl                       ∎
    where
    open Erased s
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding []-cong-J subst

  -- The result of "extracting" an application of []-cong-J is an
  -- application of loop?.

  erase-[]-cong-J : erase′ b str ([]-cong-J s l A t u v) PE.≡ loop? str
  erase-[]-cong-J = PE.refl

------------------------------------------------------------------------
-- Has-[]-cong

-- The property of supporting a []-cong combinator for a certain mode,
-- a certain erased variable context, a certain level, a certain type,
-- and certain grades.

Has-[]-cong-for-type :
  Strength → Mode → Con Term n → Term n → Term n → (_ _ _ _ _ : M) →
  Set a
Has-[]-cong-for-type {n} s m Γ l A p₁ q₁ p₂ q₂ q₃ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π p₁ , q₁ ▷ A ▹
    Π p₂ , q₂ ▷ wk1 A ▹
    Π 𝟘  , q₃ ▷ Id (wk[ 2 ]′ A) (var x1) (var x0) ▹
    Id (Erased (wk[ 3 ]′ l) (wk[ 3 ]′ A)) [ var x2 ] ([ var x1 ])

-- The property of supporting a []-cong combinator (with certain
-- grades) for a certain mode, a certain erased variable context, and
-- a certain level.
--
-- Note that, unlike the []-cong primitive, the type argument must be
-- a type in U l.

Has-[]-cong-for-level :
  Strength → Mode → Con Term n → Term n → (_ _ _ _ _ _ _ : M) → Set a
Has-[]-cong-for-level {n} s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π p₁ , q₁ ▷ U l ▹
    Π p₂ , q₂ ▷ var x0 ▹
    Π p₃ , q₃ ▷ var x1 ▹
    Π 𝟘  , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (wk[ 4 ]′ l) (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator (with certain
-- grades) for a certain mode and a certain erased variable context.
--
-- Note that, unlike the []-cong primitive, the type argument must be
-- a type in U l for some l.

Has-[]-cong :
  Strength → Mode → Con Term n → (_ _ _ _ _ _ _ _ _ : M) → Set a
Has-[]-cong {n} s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π p₁ , q₁ ▷ Level ▹
    Π p₂ , q₂ ▷ U (var x0) ▹
    Π p₃ , q₃ ▷ var x0 ▹
    Π p₄ , q₄ ▷ var x1 ▹
    Π 𝟘  , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x4) (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong-for-level :
  Strength → Mode → Con Term n → Term n → (_ _ _ _ _ _ _ : M) → Set a
Has-computing-[]-cong-for-level {n} s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ p₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) :
       Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ p₄) →
  ∀ m n′ (Δ : Cons m n′) (A t : Term n′) (ρ : Wk n′ n) →
  Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
  Δ ⊢ A ∷ U (wk ρ l) →
  Δ ⊢ t ∷ A →
  Δ ⊢ wk ρ []-cong′ ∘⟨ p₁ ⟩ A ∘⟨ p₂ ⟩ t ∘⟨ p₃ ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
    rfl ∷ Id (Erased (wk ρ l) A) [ t ] ([ t ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong :
  Strength → Mode → Con Term n → (_ _ _ _ _ _ _ _ _ : M) → Set a
Has-computing-[]-cong {n} s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅) →
  ∀ m n′ (Δ : Cons m n′) (l A t : Term n′) (ρ : Wk n′ n) →
  Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
  Δ ⊢ A ∷ U l →
  Δ ⊢ t ∷ A →
  Δ ⊢ wk ρ []-cong′ ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ A ∘⟨ p₃ ⟩ t ∘⟨ p₄ ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
    rfl ∷ Id (Erased l A) [ t ] ([ t ])

------------------------------------------------------------------------
-- Some simple lemmas

opaque

  -- If Has-[]-cong holds, then Level is allowed.

  Has-[]-cong→Level-allowed :
    Has-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ → Level-allowed
  Has-[]-cong→Level-allowed (_ , _ , ⊢[]-cong) =
    let ⊢Level , _ = inversion-ΠΣ (wf-⊢∷ ⊢[]-cong) in
    inversion-Level-⊢ ⊢Level

opaque

  -- If Has-[]-cong-for-level holds for l, then l is well-formed.

  Has-[]-cong-for-level→⊢∷L :
    Has-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    ε » Δ ⊢ l ∷Level
  Has-[]-cong-for-level→⊢∷L (_ , _ , ⊢[]-cong) =
    let ⊢U , _ = inversion-ΠΣ (wf-⊢∷ ⊢[]-cong) in
    inversion-U-Level ⊢U

opaque

  -- If Has-[]-cong-for-level holds for s, then Erased s is allowed.

  Has-[]-cong-for-level→Erased-allowed :
    Has-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Erased-allowed s
  Has-[]-cong-for-level→Erased-allowed (_ , _ , ⊢[]-cong) =
    inversion-Erased
      (inversion-Id
         (inversion-ΠΣ
            (inversion-ΠΣ
               (inversion-ΠΣ
                  (inversion-ΠΣ (wf-⊢∷ ⊢[]-cong) .proj₂ .proj₁)
                  .proj₂ .proj₁)
               .proj₂ .proj₁)
            .proj₂ .proj₁)
         .proj₁)
      .proj₁

opaque

  -- Has-[]-cong implies Has-[]-cong-for-level, given certain
  -- assumptions.

  Has-[]-cong→Has-[]-cong-for-level :
    ε » Δ ⊢ l ∷Level →
    𝟘ᶜ ▸[ m ᵐ· p₁ ] l →
    Has-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong-for-level s m Δ l p₂ q₂ p₃ q₃ p₄ q₄ q₅
  Has-[]-cong→Has-[]-cong-for-level
    {l} {p₁} {s} {p₂} {q₂} {p₃} {q₃} {p₄} {q₄} {q₅}
    ⊢l ▸l has-[]-cong@([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    let ok = Has-[]-cong→Level-allowed has-[]-cong in
    []-cong′ ∘⟨ p₁ ⟩ l ,
    (sub
       (▸[]-cong′ ∘ₘ ▸l) $ begin
       𝟘ᶜ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
       𝟘ᶜ +ᶜ p₁ ·ᶜ 𝟘ᶜ  ∎) ,
    (PE.subst (_⊢_∷_ _ _)
       (PE.cong (Π p₂ , q₂ ▷_▹_ _) $
        PE.cong (Π p₃ , q₃ ▷_▹_ _) $
        PE.cong (Π p₄ , q₄ ▷_▹_ _) $
        PE.cong (Π 𝟘  , q₅ ▷_▹_ _) $
        PE.trans (PE.sym Id-Erased-[]) $
        PE.cong₃ Id
          (PE.cong (flip Erased _) wk[]≡wk[]′) PE.refl PE.refl) $
     ⊢[]-cong′ ∘ⱼ ⊢∷Level→⊢∷Level ok ⊢l)
    where
    open ≤ᶜ-reasoning
    open Erased s

opaque

  -- Has-[]-cong-for-level implies Has-[]-cong-for-type, given
  -- certain assumptions.

  Has-[]-cong-for-level→Has-[]-cong-for-type :
    ε » Δ ⊢ A ∷ U l →
    𝟘ᶜ ▸[ m ᵐ· p₁ ] A →
    Has-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-[]-cong-for-type s m Δ l A p₂ q₂ p₃ q₃ q₄
  Has-[]-cong-for-level→Has-[]-cong-for-type
    {A} {l} {p₁} {s} {p₂} {q₂} {p₃} {q₃} {q₄}
    ⊢A ▸A has-[]-cong@([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    []-cong′ ∘⟨ p₁ ⟩ A ,
    (sub
       (▸[]-cong′ ∘ₘ ▸A) $ begin
       𝟘ᶜ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
       𝟘ᶜ +ᶜ p₁ ·ᶜ 𝟘ᶜ  ∎) ,
    (PE.subst (_⊢_∷_ _ _)
       (PE.cong  (Π p₂ , q₂ ▷_▹_ _) $
        PE.cong  (Π p₃ , q₃ ▷_▹_ _) $
        PE.cong₂ (Π 𝟘  , q₄ ▷_▹_)
          (PE.cong₃ Id wk[]≡wk[]′ PE.refl PE.refl) $
        PE.trans (PE.sym Id-Erased-[]) $
        PE.cong₃ Id
          (PE.cong₂ Erased
             (PE.trans (subst-wk l) $
              PE.sym (wk≡subst _ _))
             wk[]≡wk[]′)
          PE.refl PE.refl) $
     ⊢[]-cong′ ∘ⱼ ⊢A)
    where
    open ≤ᶜ-reasoning
    open Erased s

opaque

  -- Has-[]-cong implies Has-[]-cong-for-type, given certain
  -- assumptions.

  Has-[]-cong→Has-[]-cong-for-type :
    𝟘ᶜ ▸[ m ᵐ· p₁ ] l →
    𝟘ᶜ ▸[ m ᵐ· p₂ ] A →
    ε » Δ ⊢ A ∷ U l →
    Has-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong-for-type s m Δ l A p₃ q₃ p₄ q₄ q₅
  Has-[]-cong→Has-[]-cong-for-type ▸l ▸A ⊢A =
    Has-[]-cong-for-level→Has-[]-cong-for-type ⊢A ▸A ∘→
    Has-[]-cong→Has-[]-cong-for-level (inversion-U-Level (wf-⊢∷ ⊢A)) ▸l

------------------------------------------------------------------------
-- Some instances of
-- Has-[]-cong-for-level/Has-computing-[]-cong-for-level are logically
-- equivalent

-- Some definitions/lemmas used below.

private
  module Has-[]-cong-for-level-weaker
    {Γ : Con Term n}
    (hyp₁ : Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′)
    (hyp₂ : Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′)
    (hyp₃ : Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′)
    (hyp₄ : Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄)
    where

    open Erased s

    []-cong″ : Term (4+ n)
    []-cong″ =
       wk (stepn id 4) []-cong′ ∘⟨ p₁ ⟩ var x3 ∘⟨ p₂ ⟩ var x2
         ∘⟨ p₃ ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        ε » Γ ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢
          []-cong″ ∷
          Id (Erased (wk[ 4 ]′ l) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₃ Id
             (PE.cong (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷_▹_ _ ∘→ flip Lift _) $
              PE.trans
                (substCompEq
                   (wk _ (wk1 (wk[ 4 ]′ l)) U.[ _ ] U.[ _ ])) $
              PE.trans (substCompEq (wk _ (wk1 (wk[ 4 ]′ l)) U.[ _ ])) $
              PE.trans (substCompEq (wk _ (wk1 (wk[ 4 ]′ l)))) $
              PE.trans (subst-wk (wk1 (wk[ 4 ]′ l))) $
              PE.trans
                (flip substVar-to-subst (wk1 (wk[ 4 ]′ l)) λ where
                   x0                  → PE.refl
                   (x0 +1)             → PE.refl
                   (x0 +1 +1)          → PE.refl
                   (x0 +1 +1 +1)       → PE.refl
                   (x0 +1 +1 +1 +1)    → PE.refl
                   (_  +1 +1 +1 +1 +1) → PE.refl) $
              subst-id _)
             PE.refl PE.refl) $
        flip _∘ⱼ_ (var₀ ⊢Id) $
        flip _∘ⱼ_ (var₁ ⊢Id) $
        flip _∘ⱼ_ (var₂ ⊢Id) $
        flip _∘ⱼ_ (var₃ ⊢Id) $
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₂ (Π p₁ , q₁ ▷_▹_)
             (PE.cong U (PE.sym wk[]≡wk[]′)) PE.refl) $
        WD.defn-wkTerm (WD.»⊇ε ε) $
        W.wkTerm (W.ʷ⊇-drop (∙ ⊢Id)) ⊢[]-cong′
        where
        ⊢Id :
          ε » Γ ∙ U l ∙ var x0 ∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
        ⊢Id = ⊢Id-2-1-0′ (Has-[]-cong-for-level→⊢∷L has-[]-cong)

    oks :
      Π-allowed p₁′ q₁′ × Π-allowed p₂′ q₂′ × Π-allowed p₃′ q₃′ ×
      Π-allowed 𝟘 q₄′
    oks =
      let _ , ⊢Π , ok₁ = inversion-ΠΣ $ syntacticTerm ⊢[]-cong′
          _ , ⊢Π , ok₂ = inversion-ΠΣ ⊢Π
          _ , ⊢Π , ok₃ = inversion-ΠΣ ⊢Π
          _ , _  , ok₄ = inversion-ΠΣ ⊢Π
      in
      hyp₁ ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄

opaque

  -- One can make the "p" grades of Has-[]-cong-for-level "smaller"
  -- (given certain assumptions).

  Has-[]-cong-for-level-weaker :
    {Γ : Con Term n} →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · p₁ →
    ⌜ m ⌝ · p₂′ ≤ ⌜ m ⌝ · p₂ →
    ⌜ m ⌝ · p₃′ ≤ ⌜ m ⌝ · p₃ →
    Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-[]-cong-for-level s m Γ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
  Has-[]-cong-for-level-weaker
    {n} {p₁} {p₁′} {q₁′} {p₂} {p₂′} {q₂′} {p₃} {p₃′} {q₃′} {q₄′} {m} {s}
    {l} {Γ}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′
    has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open Has-[]-cong-for-level-weaker hyp₁ hyp₂ hyp₃ hyp₄ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ = lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 []-cong″

    ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
    ▸[]-cong‴ =
      lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub
        ((((wkUsage (stepn id 4) ▸[]-cong′ ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ
         var) $
      (begin
         𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · 𝟘  ≤⟨ ≤ᶜ-refl ∙ hyp₁′ ∙ hyp₂′ ∙ hyp₃′ ∙ ≤-reflexive (·-zeroʳ _) ⟩

         𝟘ᶜ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · p₃ ∙ 𝟘             ≈˘⟨ (≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-zeroˡ _)) $
                                                                       ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                       ≈ᶜ-trans
                                                                         (+ᶜ-cong
                                                                            (+ᶜ-cong
                                                                               (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x3))
                                                                               (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x2))
                                                                            (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x1))
                                                                         ((≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                           +ᶜ-identityʳ _) ∙
                                                                          (PE.trans (+-identityʳ _) $
                                                                           +-identityʳ _) ∙
                                                                          (PE.trans (+-identityʳ _) $
                                                                           +-identityˡ _) ∙
                                                                          (PE.trans (+-congʳ (+-identityʳ _)) $
                                                                           +-identityˡ _) ∙
                                                                          (PE.trans (+-identityʳ _) $
                                                                           +-identityʳ _))) ⟩
         (((𝟘ᶜ +ᶜ p₁ ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ m ᵐ· p₁ ⌝)) +ᶜ
           p₂ ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· p₂ ⌝)) +ᶜ
          p₃ ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· p₃ ⌝)) +ᶜ
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝)                               ∎)
      where
      open ≤ᶜ-reasoning

    ⊢[]-cong‴ :
      ε » Γ ⊢ []-cong‴ ∷
        Π p₁′ , q₁′ ▷ U l ▹
        Π p₂′ , q₂′ ▷ var x0 ▹
        Π p₃′ , q₃′ ▷ var x1 ▹
        Π 𝟘   , q₄′ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (wk[ 4 ]′ l) (var x3)) ([ var x2 ]) ([ var x1 ])
    ⊢[]-cong‴ =
      let ok₁ , ok₂ , ok₃ , ok₄ = oks in
      lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ ⊢[]-cong″

opaque
  unfolding Has-[]-cong-for-level-weaker Erased.Erased Erased.[_]

  -- One can make the "p" grades of Has-computing-[]-cong-for-level
  -- "smaller" (given certain assumptions).

  Has-computing-[]-cong-for-level-weaker :
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · p₁ →
    ⌜ m ⌝ · p₂′ ≤ ⌜ m ⌝ · p₂ →
    ⌜ m ⌝ · p₃′ ≤ ⌜ m ⌝ · p₃ →
    Has-computing-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-computing-[]-cong-for-level s m Δ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
  Has-computing-[]-cong-for-level-weaker
    {p₁} {p₁′} {p₂} {p₂′} {p₃} {p₃′} {s} {l}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    let ⊢l                    = Has-[]-cong-for-level→⊢∷L has-[]-cong
        ok₁ , ok₂ , ok₃ , ok₄ = oks
    in
      Has-[]-cong-for-level-weaker hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′
        has-[]-cong
    , λ _ _ _ A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) in
        wk ρ
          (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
           wk (stepn id 4) []-cong′ ∘⟨ p₁ ⟩ var x3 ∘⟨ p₂ ⟩ var x2
             ∘⟨ p₃ ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0)
          ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl                     ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _)
                                                                                (PE.cong₃ Id
                                                                                   (PE.cong (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷_▹_ _ ∘→ flip Lift _) $
                                                                                    PE.trans (subst-wk (wk1 (wk[ 4 ]′ l))) $
                                                                                    PE.trans (subst-wk (wk[ 4 ]′ l)) $
                                                                                    PE.trans (subst-wk l) $
                                                                                    PE.sym $
                                                                                    PE.trans (wk-comp _ _ _) $
                                                                                    wk≡subst _ _)
                                                                                   PE.refl PE.refl) $
                                                                              β-red-⇒₄′ ok₁ ok₂ ok₃ ok₄
                                                                                (W.wkTerm (W.liftnʷ Δ⊇Γ (∙ (⊢Id-2-1-0′ (WD.defn-wkLevel ⊇ε ⊢l)))) $
                                                                                 WD.defn-wkTerm ⊇ε ⊢[]-cong″)
                                                                                ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        (wk (liftn ρ 4) (wk (stepn id 4) []-cong′)
           [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ])
          ∘⟨ p₁ ⟩ A ∘⟨ p₂ ⟩ t ∘⟨ p₃ ⟩ t ∘⟨ 𝟘 ⟩ rfl                        ≡⟨ PE.cong (λ []-cong → []-cong ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _) $
                                                                             PE.trans (subst-wk (wk[ 4 ]′ []-cong′)) $
                                                                             PE.trans (subst-wk []-cong′) $
                                                                             PE.sym (wk≡subst _ _) ⟩⊢≡

        wk ρ []-cong′ ∘⟨ p₁ ⟩ A ∘⟨ p₂ ⟩ t ∘⟨ p₃ ⟩ t ∘⟨ 𝟘 ⟩ rfl            ≡⟨ []-cong′≡ _ _ _ _ _ _ Δ⊇Γ ⊢A ⊢t ⟩⊢∎

        rfl                                                               ∎
    where
    open Has-[]-cong-for-level-weaker hyp₁ hyp₂ hyp₃ hyp₄ has-[]-cong

-- Some definitions/lemmas used below.

private
  module Has-[]-cong-for-level-stronger
    {Γ : Con Term n}
    (hyp₁ : Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′)
    (hyp₂ : Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′)
    (hyp₃ : Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′)
    (hyp₄ : Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄)
    where

    open Erased s
    open Erased.Internal s TR

    []-cong″ : Term n
    []-cong″ =
      lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
      cong 𝟘 (Erased (wk[ 4 ]′ l) (Erased (wk[ 4 ]′ l) (var x3)))
        [ [ var x2 ] ] [ [ var x1 ] ] (Erased (wk[ 4 ]′ l) (var x3))
        (mapᴱ (Erased (wk[ 5 ]′ l) (var x4))
           (erased (var x5) (var x0)) (var x0))
        (wk[ 4 ]′ []-cong′ ∘⟨ p₁ ⟩ Erased (wk[ 4 ]′ l) (var x3)
           ∘⟨ p₂ ⟩ [ var x2 ] ∘⟨ p₃ ⟩ [ var x1 ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                    (Erased (wk[ 4 ]′ l) (var x3)) [ var x0 ] (var x0))

    opaque

      Erased-ok : Erased-allowed s
      Erased-ok = Has-[]-cong-for-level→Erased-allowed has-[]-cong

    module Box-cong-internal
      (Δ : Cons n₁ n₂)
      (l []-cong′ A t : Term n₂)
      (⊢l : Δ ⊢ l ∷Level)
      (⊢[]-cong′ :
         Δ ⊢ []-cong′ ∷
         Π p₁ , q₁ ▷ U l ▹
         Π p₂ , q₂ ▷ var x0 ▹
         Π p₃ , q₃ ▷ var x1 ▹
         Π 𝟘  , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
         Id (Erased (wk[ 4 ]′ l) (var x3)) ([ var x2 ]) ([ var x1 ]))
      (⊢A : Δ ⊢ A ∷ U l)
      (⊢t : Δ ⊢ t ∷ A)
      where

      c : I.Constants
      c .I.gs               = 14
      c .I.ss               = 0
      c .I.bms              = 0
      c .I.ms               = 4
      c .I.base-dcon-size   = n₁
      c .I.base-con-size    = n₂
      c .I.base-con-allowed = true
      c .I.meta-con-size    = V.replicate 4 n₂

      xp₁ xp₁′ xp₂ xp₂′ xp₃ xp₃′ xq₁ xq₁′ xq₂ xq₂′ xq₃ xq₃′ xq₄ xq₄′ :
        I.Termᵍ 14
      xp₁  = I.var x0
      xp₁′ = I.var x1
      xp₂  = I.var x2
      xp₂′ = I.var x3
      xp₃  = I.var x4
      xp₃′ = I.var x5
      xq₁  = I.var x6
      xq₁′ = I.var x7
      xq₂  = I.var x8
      xq₂′ = I.var x9
      xq₃  = I.var x10
      xq₃′ = I.var x11
      xq₄  = I.var (x11 +1)
      xq₄′ = I.var (x11 +1 +1)

      xl : I.Term c n₂
      xl       = I.varᵐ x0
      x[]-cong = I.varᵐ {c = c} x1
      xA       = I.varᵐ {c = c} x2
      xt       = I.varᵐ {c = c} x3

      γ′ : I.Termˢ 0 → I.Contexts c
      γ′ _ .I.grades =
        p₁ V.∷ p₁′ V.∷ p₂ V.∷ p₂′ V.∷ p₃ V.∷ p₃′ V.∷ q₁ V.∷ q₁′ V.∷
        q₂ V.∷ q₂′ V.∷ q₃ V.∷ q₃′ V.∷ q₄ V.∷ q₄′ V.∷ V.ε
      γ′ _ .I.strengths    = V.ε
      γ′ _ .I.binder-modes = V.ε
      γ′ _ .I.⌜base⌝       = Δ
      γ′ _ .I.constraints⁰ = I.emptyᶜ⁰
      γ′ s .I.constraints⁺ =
        I.unit-allowed s      L.∷
        I.σ-allowed s I.𝟘 I.𝟘 L.∷
        I.π-allowed xp₁′ xq₁′ L.∷
        I.π-allowed xp₂′ xq₂′ L.∷
        I.π-allowed xp₃′ xq₃′ L.∷
        I.π-allowed I.𝟘  xq₄′ L.∷
        L.[]
      γ′ _ .I.metas .I.equalities = L.[]
      γ′ s .I.metas .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l
        (I.var! x1) →
          I.base ,
          I.term
            []-cong′
            (I.Π xp₁ , xq₁ ▷ I.U xl ▹
             I.Π xp₂ , xq₂ ▷ I.var x0 ▹
             I.Π xp₃ , xq₃ ▷ I.var x1 ▹
             I.Π I.𝟘 , xq₄ ▷ I.Id (I.var x2) (I.var x1) (I.var x0) ▹
             I.Id (I.Erased s (IW.wk[ 4 ] xl) (I.var x3))
               (I.box s (IW.wk[ 4 ] xl) (I.var x2))
               (I.box s (IW.wk[ 4 ] xl) (I.var x1)))
        (I.var! x2)      → I.base , I.term A (I.U xl)
        (I.var! x3)      → I.base , I.term t xA
        (I.var not-x4 _)

      []-cong″ᵢ : I.Termˢ 0 → I.Term c n₂
      []-cong″ᵢ s =
        I.lam xp₁′ (just (xq₁′ , I.U xl)) $
        I.lam xp₂′ (just (xq₂′ , I.var x0)) $
        I.lam xp₃′ (just (xq₃′ , I.var x1)) $
        I.lam I.𝟘
          (just (xq₄′ , I.Id (I.var x2) (I.var x1) (I.var x0))) $
        congᵢ I.𝟘
          (I.Erased s (IW.wk[ 4 ] xl)
             (I.Erased s (IW.wk[ 4 ] xl) (I.var x3)))
          (I.box s (IW.wk[ 4 ] xl) (I.box s (IW.wk[ 4 ] xl) (I.var x2)))
          (I.box s (IW.wk[ 4 ] xl) (I.box s (IW.wk[ 4 ] xl) (I.var x1)))
          (I.Erased s (IW.wk[ 4 ] xl) (I.var x3))
          (mapᴱᵢ (IW.wk[ 5 ] xl) (I.Erased s (IW.wk[ 5 ] xl) (I.var x4))
             (erasedᵢ (I.var x5) (I.var x0)) (I.var x0))
          (IW.wk[ 4 ] x[]-cong I.∘⟨ xp₁ ⟩
           I.Erased s (IW.wk[ 4 ] xl) (I.var x3) I.∘⟨ xp₂ ⟩
           I.box s (IW.wk[ 4 ] xl) (I.var x2) I.∘⟨ xp₃ ⟩
           I.box s (IW.wk[ 4 ] xl) (I.var x1) I.∘⟨ I.𝟘 ⟩
           congᵢ I.𝟘 (I.var x3) (I.var x2) (I.var x1)
             (I.Erased s (IW.wk[ 4 ] xl) (I.var x3))
             (I.box s (IW.wk[ 5 ] xl) (I.var x0))
             (I.var x0))

      opaque
        unfolding Erased [_]

        γ-wf :
          I.⟦ sᵢ ⟧ˢ (γ′ sᵢ) PE.≡ s →
          IC.Contexts-wf (I.base nothing) (γ′ sᵢ)
        γ-wf eq = λ where
          .IC.constraints-wf →
            let Unit-ok , Σ-ok = PE.subst Erased-allowed (PE.sym eq)
                                   Erased-ok
                _ , ⊢Π , ok₁   = inversion-ΠΣ $ syntacticTerm ⊢[]-cong′
                _ , ⊢Π , ok₂   = inversion-ΠΣ ⊢Π
                _ , ⊢Π , ok₃   = inversion-ΠΣ ⊢Π
                _ , _  , ok₄   = inversion-ΠΣ ⊢Π
            in
            Unit-ok  L.∷
            Σ-ok     L.∷
            hyp₁ ok₁ L.∷
            hyp₂ ok₂ L.∷
            hyp₃ ok₃ L.∷
            hyp₄ ok₄ L.∷
            L.[]
          .IC.metas-wf .IC.equalities-wf → L.[]
          .IC.metas-wf .IC.bindings-wf   → λ where
            (I.var! x0) → ⊢l
            (I.var! x1) →
              PE.subst (_⊢_∷_ _ _)
                (PE.cong (Π p₁ , q₁ ▷_▹_ _) $
                 PE.cong (Π p₂ , q₂ ▷_▹_ _) $
                 PE.cong (Π p₃ , q₃ ▷_▹_ _) $
                 PE.cong (Π 𝟘  , q₄ ▷_▹_ _) $
                 PE.cong
                   (λ s →
                      Id (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ var x3 ▹ Lift _ (Unit s))
                        (prod s 𝟘 (var x2) (lift (star s)))
                        (prod s 𝟘 (var x1) (lift (star s))))
                   (PE.sym eq)) $
              ⊢[]-cong′
            (I.var! x2)       → ⊢A
            (I.var! x3)       → ⊢t
            (I.var  not-x4 _)

    opaque

      ⊢l : ε » Γ ⊢ l ∷Level
      ⊢l = Has-[]-cong-for-level→⊢∷L has-[]-cong

    open Box-cong-internal (ε » Γ) l []-cong′ (Lift l ℕ) (lift zero)
           ⊢l ⊢[]-cong′
           (conv (Liftⱼ′ ⊢l (ℕⱼ (wfLevel ⊢l)))
              (U-cong-⊢≡ (supᵘₗ-zeroˡ ⊢l)))
           (liftⱼ′ ⊢l (zeroⱼ (wfLevel ⊢l)))

    private

      Goalᵢ : I.Termˢ 0 → I.Term c n
      Goalᵢ s =
        I.Π xp₁′ , xq₁′ ▷ I.U xl ▹
        I.Π xp₂′ , xq₂′ ▷ I.var x0 ▹
        I.Π xp₃′ , xq₃′ ▷ I.var x1 ▹
        I.Π I.𝟘  , xq₄′ ▷ I.Id (I.var x2) (I.var x1) (I.var x0) ▹
        I.Id (I.Erased s (IW.wk[ 4 ] xl) (I.var x3))
          (I.box s (IW.wk[ 4 ] xl) (I.var x2))
          (I.box s (IW.wk[ 4 ] xl) (I.var x1))

    opaque
      unfolding Erased cong erased fst⟨_⟩ mapᴱ subst [_]

      ⊢[]-cong″ :
        ε » Γ ⊢ []-cong″ ∷
        Π p₁′ , q₁′ ▷ U l ▹
        Π p₂′ , q₂′ ▷ var x0 ▹
        Π p₃′ , q₃′ ▷ var x1 ▹
        Π 𝟘   , q₄′ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (wk[ 4 ]′ l) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ = case PE.singleton s of λ where
        (𝕤 , PE.refl) →
          check-type-and-term-sound (γ′ I.𝕤) (I.base nothing I.» I.base)
            ([]-cong″ᵢ I.𝕤) (Goalᵢ I.𝕤) 22 PE.refl (γ-wf PE.refl)
            (wfLevel ⊢l)
        (𝕨 , PE.refl) →
          check-type-and-term-sound (γ′ I.𝕨) (I.base nothing I.» I.base)
            ([]-cong″ᵢ I.𝕨) (Goalᵢ I.𝕨) 21 PE.refl (γ-wf PE.refl)
            (wfLevel ⊢l)

opaque

  -- One can replace some of the "p" grades in Has-[]-cong-for-level
  -- with grades that satisfy certain assumptions (given certain
  -- assumptions).
  --
  -- Note that, if all Π-types are allowed and l is a level literal,
  -- then all of the assumptions are satisfied for the erasure
  -- modality with 𝟘ᵐ.

  Has-[]-cong-for-level-stronger :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′) →
    ⌜ m ⌝ · p₁′ ≤ 𝟘 →
    ⌜ m ⌝ · p₂′ ≤ 𝟘 →
    ⌜ m ⌝ · p₃′ ≤ 𝟘 →
    γ ▸[ 𝟘ᵐ? ] l →
    Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-[]-cong-for-level s m Γ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
  Has-[]-cong-for-level-stronger
    {s} {p₁} {p₁′} {p₂} {p₂′} {p₃} {p₃′} {m}
    trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′ ▸l
    has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong″ , ▸[]-cong″ , ⊢[]-cong″
    where
    open ErasedU s
    open Has-[]-cong-for-level-stronger hyp₁ hyp₂ hyp₃ hyp₄ has-[]-cong

    ▸[]-cong″ : 𝟘ᶜ ▸[ m ] []-cong″
    ▸[]-cong″ =
      let ▸l′ = wkUsage _ ▸l in
      lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub
        (▸cong (▸Erased ▸l′ (▸Erased ▸l′ var)) (▸[] (▸[] var))
           (▸[] (▸[] var)) (sub (▸Erased ▸l′ var) lemma)
           (sub
              (▸mapᴱ′ trivial 𝟘≤𝟙
                 (λ _ → _ , ▸Erased (wkUsage _ ▸l) var)
                 (sub
                    (▸erased′ trivial 𝟘≤𝟙 var (λ _ → _ , var))
                    (begin
                       𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                       𝟘ᶜ                ∎))
                 var)
              (begin
                 𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                 𝟘ᶜ              ∎))
           (flip _∘ₘ_
              (▸cong var var var (sub (▸Erased ▸l′ var) lemma)
                 (sub (▸[] var) $ begin
                    𝟘ᶜ ∙ ⌜ m ᵐ· 𝟘 ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                    𝟘ᶜ                   ∎)
                 var
                 (λ _ → begin
                    𝟘ᶜ ∙ ⌜ m ᵐ· 𝟘 ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                    𝟘ᶜ                   ∎)
                 (λ _ → begin
                    𝟘ᶜ                                             ≈˘⟨ ≈ᶜ-trans
                                                                         (+ᶜ-cong
                                                                            (≈ᶜ-trans (·ᶜ-congʳ $ ·-zeroʳ _) $
                                                                             ·ᶜ-zeroˡ _)
                                                                            (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _))) $
                                                                       +ᶜ-identityʳ _ ⟩
                    (⌜ m ᵐ· 𝟘 ⌝ · 𝟘) ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
                    𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ                            ∎)) $
            flip _∘ₘ_ (▸[] var) $
            flip _∘ₘ_ (▸[] var) $
            flip _∘ₘ_ (sub (▸Erased ▸l′ var) lemma) $
            wkUsage _ ▸[]-cong′)
           (λ _ → begin
              𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ              ∎)
           (λ _ → begin
              𝟘ᶜ                                        ≈˘⟨ ≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _))) $
                                                            +ᶜ-identityʳ _ ⟩
              (⌜ m ⌝ · 𝟘) ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ  ∎)) $
      (begin
         𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

         𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ 𝟘          ≤⟨ ≤ᶜ-refl ∙ hyp₁′ ∙ hyp₂′ ∙ hyp₃′ ∙ ≤-refl ⟩

         𝟘ᶜ                                                        ≈˘⟨ ≈ᶜ-trans
                                                                         (·ᶜ-congˡ $
                                                                          ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                          ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                          ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                          ≈ᶜ-trans
                                                                            (+ᶜ-cong
                                                                               (≈ᶜ-trans
                                                                                  (+ᶜ-cong
                                                                                     (≈ᶜ-trans
                                                                                        (+ᶜ-cong
                                                                                           (≈ᶜ-trans
                                                                                              (+ᶜ-identityˡ _) $
                                                                                            ·ᶜ-zeroʳ _)
                                                                                           (·ᶜ-zeroʳ _)) $
                                                                                      +ᶜ-identityʳ _)
                                                                                     (·ᶜ-zeroʳ _)) $
                                                                                +ᶜ-identityʳ _)
                                                                               (·ᶜ-zeroˡ _)) $
                                                                          +ᶜ-identityʳ _) $
                                                                       ·ᶜ-zeroʳ _ ⟩
         ω ·ᶜ
         (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ
          ((((𝟘ᶜ +ᶜ p₁ ·ᶜ 𝟘ᶜ) +ᶜ p₂ ·ᶜ 𝟘ᶜ) +ᶜ p₃ ·ᶜ 𝟘ᶜ) +ᶜ
           𝟘 ·ᶜ ω ·ᶜ
           ((𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
            (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ 𝟘ᶜ)) +ᶜ
          𝟘ᶜ)                                                      ∎)
      where
      open ≤ᶜ-reasoning

      𝟘≤⌜𝟘ᵐ?⌝ : 𝟘 ≤ ⌜ 𝟘ᵐ? ⌝
      𝟘≤⌜𝟘ᵐ?⌝ = 𝟘ᵐ?-elim (λ m → 𝟘 ≤ ⌜ m ⌝) ≤-refl
        (case PE.singleton s of λ where
           (𝕨 , PE.refl) → ≡-trivial ∘→ proj₁ ∘→ trivial PE.refl
           (𝕤 , PE.refl) → 𝟘≤𝟙 PE.refl)

      lemma : 𝟘ᶜ {n = 4+ n} ≤ᶜ 𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝
      lemma = begin
        𝟘ᶜ                 ≡⟨⟩
        𝟘ᶜ , x3 ≔ 𝟘        ≤⟨ update-monotoneʳ {γ = 𝟘ᶜ} x3 𝟘≤⌜𝟘ᵐ?⌝ ⟩
        𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝  ∎

opaque
  unfolding Has-[]-cong-for-level-stronger

  -- One can replace some of the "p" grades in
  -- Has-computing-[]-cong-for-level with grades that satisfy certain
  -- assumptions (given certain assumptions).
  --
  -- Note that, if all Π-types are allowed and l is a level literal,
  -- then all the assumptions are satisfied for the erasure modality
  -- with 𝟘ᵐ.

  Has-computing-[]-cong-for-level-stronger :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed 𝟘  q₄ → Π-allowed 𝟘   q₄′) →
    ⌜ m ⌝ · p₁′ ≤ 𝟘 →
    ⌜ m ⌝ · p₂′ ≤ 𝟘 →
    ⌜ m ⌝ · p₃′ ≤ 𝟘 →
    γ ▸[ 𝟘ᵐ? ] l →
    Has-computing-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-computing-[]-cong-for-level s m Γ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
  Has-computing-[]-cong-for-level-stronger
    {n} {s} {p₁} {q₁} {p₁′} {q₁′} {p₂} {q₂} {p₂′} {q₂′} {p₃} {q₃}
    {p₃′} {q₃′} {q₄} {q₄′} {m} {l} {Γ}
    trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′ ▸l
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    has-[]-cong′ , []-cong″-computes
    where
    open Erased s
    open Erased.Internal s TR
    open Has-[]-cong-for-level-stronger
           hyp₁ hyp₂ hyp₃ hyp₄ has-[]-cong

    has-[]-cong′ :
      Has-[]-cong-for-level s m Γ l p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ q₄′
    has-[]-cong′ =
      Has-[]-cong-for-level-stronger
        trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₁′ hyp₂′ hyp₃′ ▸l has-[]-cong

    opaque

      []-cong″-computes :
        ∀ m n′ (Δ : Cons m n′) (A t : Term n′) (ρ : Wk n′ n) →
        Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
        Δ ⊢ A ∷ U (wk ρ l) →
        Δ ⊢ t ∷ A →
        Δ ⊢
          wk ρ []-cong″ ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
          rfl ∷ Id (Erased (wk ρ l) A) [ t ] ([ t ])
      []-cong″-computes m n′ Δ A t ρ Δ⊇Γ ⊢A ⊢t =
        wk ρ
          (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
           cong 𝟘 (Erased (wk[ 4 ]′ l) (Erased (wk[ 4 ]′ l) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ]
             (Erased (wk[ 4 ]′ l) (var x3))
             (mapᴱ (Erased (wk[ 5 ]′ l) (var x4))
                (erased (var x5) (var x0)) (var x0))
             (wk[ 4 ]′ []-cong′ ∘⟨ p₁ ⟩ Erased (wk[ 4 ]′ l) (var x3)
                ∘⟨ p₂ ⟩ [ var x2 ] ∘⟨ p₃ ⟩ [ var x1 ]
                ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                         (Erased (wk[ 4 ]′ l) (var x3)) [ var x0 ]
                         (var x0)))
          ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl                     ≡⟨ PE.cong (flip _∘⟨ 𝟘   ⟩_ _) $
                                                                             PE.cong (flip _∘⟨ p₃′ ⟩_ _) $
                                                                             PE.cong (flip _∘⟨ p₂′ ⟩_ _) $
                                                                             PE.cong (flip _∘⟨ p₁′ ⟩_ _) $
                                                                             PE.cong (lam _ ∘→ lam _ ∘→ lam _ ∘→ lam _) $
                                                                             PE.trans wk-cong $
                                                                             PE.cong₆ (cong _)
                                                                               (PE.trans wk-Erased $
                                                                                PE.cong₂ Erased (wk⇑[]-wk[]≡ 4) $
                                                                                PE.trans wk-Erased $
                                                                                PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4))
                                                                               (PE.trans wk-[] $
                                                                                PE.cong [_] wk-[])
                                                                               (PE.trans wk-[] $
                                                                                PE.cong [_] wk-[])
                                                                               (PE.trans wk-Erased $
                                                                                PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4))
                                                                               (PE.trans wk-mapᴱ $
                                                                                PE.cong₃ mapᴱ
                                                                                  (PE.trans wk-Erased $
                                                                                   PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 5))
                                                                                  wk-erased PE.refl)
                                                                               (PE.cong₂ _∘⟨ 𝟘 ⟩_
                                                                                  (PE.cong₂ _∘⟨ p₃ ⟩_
                                                                                     (PE.cong₂ _∘⟨ p₂ ⟩_
                                                                                        (PE.cong₂ _∘⟨ p₁ ⟩_
                                                                                           (wk⇑[]-wk[]≡ 4)
                                                                                           (PE.trans wk-Erased $
                                                                                            PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4)))
                                                                                        wk-[])
                                                                                     wk-[]) $
                                                                                PE.trans wk-cong $
                                                                                PE.cong₃ (cong _ _ _ _)
                                                                                  (PE.trans wk-Erased $
                                                                                   PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4))
                                                                                  wk-[]
                                                                                  PE.refl) ⟩⊢≡
        (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
         cong 𝟘
           (Erased (wk[ 4 ]′ (wk ρ l))
              (Erased (wk[ 4 ]′ (wk ρ l)) (var x3)))
           [ [ var x2 ] ] [ [ var x1 ] ]
           (Erased (wk[ 4 ]′ (wk ρ l)) (var x3))
           (mapᴱ (Erased (wk[ 5 ]′ (wk ρ l)) (var x4))
              (erased (var x5) (var x0)) (var x0))
           (wk[ 4 ]′ (wk ρ []-cong′)
              ∘⟨ p₁ ⟩ Erased (wk[ 4 ]′ (wk ρ l)) (var x3)
              ∘⟨ p₂ ⟩ [ var x2 ] ∘⟨ p₃ ⟩ [ var x1 ]
              ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                       (Erased (wk[ 4 ]′ (wk ρ l)) (var x3))
                       [ var x0 ] (var x0)))
          ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl ∷
          Id (Erased (wk ρ l) A) [ t ] ([ t ])                            ≡⟨ lemma₁ ⟩⊢∷
                                                                           ⟨ lemma₂ ⟩≡
        cong 𝟘 (Erased (wk ρ l) (Erased (wk ρ l) A)) [ [ t ] ] [ [ t ] ]
          (Erased (wk ρ l) A)
          (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
             (erased (wk₂ A) (var x0)) (var x0))
          (wk ρ []-cong′ ∘⟨ p₁ ⟩ Erased (wk ρ l) A ∘⟨ p₂ ⟩ [ t ]
             ∘⟨ p₃ ⟩ [ t ] ∘⟨ 𝟘 ⟩ rfl) ∷
          Id (Erased (wk ρ l) A)
            (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
               (erased (wk₂ A) (var x0)) (var x0) [ [ [ t ] ] ]₀)
            (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
               (erased (wk₂ A) (var x0)) (var x0) [ [ [ t ] ] ]₀)         ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                               (refl (univ ⊢Erased-A)) (refl ⊢mapᴱ-0) $
                                                                             []-cong′≡ _ _ _ _ _ _ Δ⊇Γ ⊢Erased-A ⊢[t] ⟩⊢∷
        cong 𝟘 (Erased (wk ρ l) (Erased (wk ρ l) A)) [ [ t ] ] [ [ t ] ]
          (Erased (wk ρ l) A)
          (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
             (erased (wk₂ A) (var x0)) (var x0))
          rfl                                                             ⇒⟨ cong-⇒ ⊢[[t]] ⊢mapᴱ-0 ⟩⊢∎

        rfl                                                               ∎
        where
        opaque

          Δ⊇ε : WD.» Δ .defs ⊇ ε
          Δ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A))

        opaque

          ⊢wk-l : Δ ⊢ wk ρ l ∷Level
          ⊢wk-l = W.wkLevel Δ⊇Γ (WD.defn-wkLevel Δ⊇ε ⊢l)

        open Box-cong-internal Δ (wk ρ l) (wk ρ []-cong′) A t
               ⊢wk-l
               (PE.subst (_⊢_∷_ _ _)
                  (PE.cong (Π p₁ , q₁ ▷_▹_ _) $
                   PE.cong (Π p₂ , q₂ ▷_▹_ _) $
                   PE.cong (Π p₃ , q₃ ▷_▹_ _) $
                   PE.cong (Π 𝟘  , q₄ ▷_▹_ _) $
                   PE.cong₃ Id
                     (PE.trans wk-Erased $
                      PE.cong (flip Erased _) (wk⇑[]-wk[]≡ 4))
                     wk-[] wk-[]) $
                W.wkTerm Δ⊇Γ (WD.defn-wkTerm Δ⊇ε ⊢[]-cong′))
               ⊢A ⊢t

        opaque

          ⊢Erased-A : Δ ⊢ Erased (wk ρ l) A ∷ U (wk ρ l)
          ⊢Erased-A = Erasedⱼ-U Erased-ok ⊢A

        opaque

          ⊢Erased-Erased-A : Δ ⊢ Erased (wk ρ l) (Erased (wk ρ l) A)
          ⊢Erased-Erased-A = Erasedⱼ Erased-ok ⊢wk-l (univ ⊢Erased-A)

        opaque

          ⊢[t] : Δ ⊢ [ t ] ∷ Erased (wk ρ l) A
          ⊢[t] = []ⱼ Erased-ok ⊢wk-l ⊢t

        opaque

          ⊢[[t]] : Δ ⊢ [ [ t ] ] ∷ Erased (wk ρ l) (Erased (wk ρ l) A)
          ⊢[[t]] = []ⱼ Erased-ok ⊢wk-l ⊢[t]

        opaque

          ⊢mapᴱ-0 :
            Δ »∙ Erased (wk ρ l) (Erased (wk ρ l) A) ⊢
            mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
              (erased (wk₂ A) (var x0)) (var x0) ∷
            wk1 (Erased (wk ρ l) A)
          ⊢mapᴱ-0 =
            PE.subst (_⊢_∷_ _ _) (PE.sym wk-Erased) $
            ⊢mapᴱ (W.wkLevel₁ ⊢Erased-Erased-A ⊢wk-l)
              (PE.subst (flip (_⊢_∷_ _) _)
                 (PE.cong (flip erased _) wk[]≡wk[]′) $
               erasedⱼ $ PE.subst (_⊢_∷_ _ _) wk-Erased $
               var₀ $ PE.subst (_⊢_ _) wk-Erased $
               W.wk₁ ⊢Erased-Erased-A (univ ⊢Erased-A))
              (PE.subst (_⊢_∷_ _ _)
                 (PE.trans wk-Erased $ PE.cong (Erased _) wk-Erased) $
               var₀ ⊢Erased-Erased-A)

        lhsᵢ : I.Termˢ 0 → I.Term c n′
        lhsᵢ s =
          []-cong″ᵢ s I.∘⟨ xp₁′ ⟩ xA I.∘⟨ xp₂′ ⟩ xt I.∘⟨ xp₃′ ⟩ xt
            I.∘⟨ I.𝟘 ⟩ I.rfl nothing

        rhsᵢ : I.Termˢ 0 → I.Term c n′
        rhsᵢ s =
          congᵢ I.𝟘 (I.Erased s xl (I.Erased s xl xA))
            (I.box s xl (I.box s xl xt)) (I.box s xl (I.box s xl xt))
            (I.Erased s xl xA)
            (mapᴱᵢ (IW.wk[ 1 ] xl)
               (I.Erased s (IW.wk[ 1 ] xl) (IW.wk[ 1 ] xA))
               (erasedᵢ (IW.wk[ 2 ] xA) (I.var x0)) (I.var x0))
            (x[]-cong I.∘⟨ xp₁ ⟩ I.Erased s xl xA
               I.∘⟨ xp₂ ⟩ I.box s xl xt I.∘⟨ xp₃ ⟩ I.box s xl xt
               I.∘⟨ I.𝟘 ⟩ I.rfl nothing)

        Lhsᵢ : I.Termˢ 0 → I.Term c n′
        Lhsᵢ s =
          I.Id (I.Erased s xl xA) (I.box s xl xt) (I.box s xl xt)

        Rhsᵢ : I.Termˢ 0 → I.Term c n′
        Rhsᵢ s =
          let tm =
                I.subst
                  (mapᴱᵢ (IW.wk[ 1 ] xl)
                     (I.Erased s (IW.wk[ 1 ] xl) (IW.wk[ 1 ] xA))
                     (erasedᵢ (IW.wk[ 2 ] xA) (I.var x0)) (I.var x0))
                  (IS.sgSubst (I.box s xl (I.box s xl xt)))
          in
          I.Id (I.Erased s xl xA) tm tm

        opaque
          unfolding Erased cong erased fst⟨_⟩ mapᴱ subst [_]

          lemma₁ :
            Δ ⊢
              (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam 𝟘 $
               cong 𝟘
                 (Erased (wk[ 4 ]′ (wk ρ l))
                    (Erased (wk[ 4 ]′ (wk ρ l)) (var x3)))
                 [ [ var x2 ] ] [ [ var x1 ] ]
                 (Erased (wk[ 4 ]′ (wk ρ l)) (var x3))
                 (mapᴱ (Erased (wk[ 5 ]′ (wk ρ l)) (var x4))
                    (erased (var x5) (var x0)) (var x0))
                 (wk[ 4 ]′ (wk ρ []-cong′)
                    ∘⟨ p₁ ⟩ Erased (wk[ 4 ]′ (wk ρ l)) (var x3)
                    ∘⟨ p₂ ⟩ [ var x2 ] ∘⟨ p₃ ⟩ [ var x1 ]
                    ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                             (Erased (wk[ 4 ]′ (wk ρ l)) (var x3))
                             [ var x0 ] (var x0)))
                ∘⟨ p₁′ ⟩ A ∘⟨ p₂′ ⟩ t ∘⟨ p₃′ ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
              cong 𝟘 (Erased (wk ρ l) (Erased (wk ρ l) A)) [ [ t ] ]
                [ [ t ] ] (Erased (wk ρ l) A)
                (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
                   (erased (wk₂ A) (var x0)) (var x0))
                (wk ρ []-cong′ ∘⟨ p₁ ⟩ Erased (wk ρ l) A ∘⟨ p₂ ⟩ [ t ]
                   ∘⟨ p₃ ⟩ [ t ] ∘⟨ 𝟘 ⟩ rfl) ∷
              Id (Erased (wk ρ l) A) [ t ] ([ t ])
          lemma₁ = case PE.singleton s of λ where
            (𝕤 , PE.refl) →
              check-and-equal-type-and-terms-sound (γ′ I.𝕤)
                (I.base nothing I.» I.base) (lhsᵢ I.𝕤) (rhsᵢ I.𝕤)
                (Lhsᵢ I.𝕤) 29 PE.refl (γ-wf PE.refl) (wfTerm ⊢A)
            (𝕨 , PE.refl) →
              check-and-equal-type-and-terms-sound (γ′ I.𝕨)
                (I.base nothing I.» I.base) (lhsᵢ I.𝕨) (rhsᵢ I.𝕨)
                (Lhsᵢ I.𝕨) 28 PE.refl (γ-wf PE.refl) (wfTerm ⊢A)

        opaque
          unfolding Erased erased fst⟨_⟩ mapᴱ [_]

          lemma₂ :
            Δ ⊢ Id (Erased (wk ρ l) A) [ t ] ([ t ]) ≡
              Id (Erased (wk ρ l) A)
                (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
                   (erased (wk₂ A) (var x0)) (var x0) [ [ [ t ] ] ]₀)
                (mapᴱ (Erased (wk1 (wk ρ l)) (wk1 A))
                   (erased (wk₂ A) (var x0)) (var x0) [ [ [ t ] ] ]₀)
          lemma₂ = case PE.singleton s of λ where
            (𝕤 , PE.refl) →
              check-and-equal-ty-sound (γ′ I.𝕤)
                (I.base nothing I.» I.base) (Lhsᵢ I.𝕤) (Rhsᵢ I.𝕤) 15
                PE.refl (γ-wf PE.refl) (wfTerm ⊢A)
            (𝕨 , PE.refl) →
              check-and-equal-ty-sound (γ′ I.𝕨)
                (I.base nothing I.» I.base) (Lhsᵢ I.𝕨) (Rhsᵢ I.𝕨) 14
                PE.refl (γ-wf PE.refl) (wfTerm ⊢A)

------------------------------------------------------------------------
-- Some instances of Has-[]-cong/Has-computing-[]-cong are logically
-- equivalent

-- Some definitions/lemmas used below.

private
  module Has-[]-cong-weaker
    {Γ : Con Term n}
    (hyp₁ : Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′)
    (hyp₂ : Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′)
    (hyp₃ : Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′)
    (hyp₄ : Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′)
    (hyp₅ : Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅)
    where

    open Erased s

    []-cong″ : Term (5+ n)
    []-cong″ =
       wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4 ∘⟨ p₂ ⟩ var x3
         ∘⟨ p₃ ⟩ var x2 ∘⟨ p₄ ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        ε » Γ ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
          Id (var x2) (var x1) (var x0) ⊢
          []-cong″ ∷
          Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        flip _∘ⱼ_ (var₀ ⊢Id) $
        flip _∘ⱼ_ (var₁ ⊢Id) $
        flip _∘ⱼ_ (var₂ ⊢Id) $
        flip _∘ⱼ_ (var₃ ⊢Id) $
        flip _∘ⱼ_ (var₄ ⊢Id) $
        WD.defn-wkTerm (WD.»⊇ε ε) $
        W.wkTerm (W.ʷ⊇-drop (∙ ⊢Id)) ⊢[]-cong′
        where
        ⊢Id :
          ε » Γ ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ⊢
          Id (var x2) (var x1) (var x0)
        ⊢Id =
          ⊢Id-2-1-0 (Has-[]-cong→Level-allowed has-[]-cong)
            (wfTerm ⊢[]-cong′)

    oks :
      Π-allowed p₁′ q₁′ × Π-allowed p₂′ q₂′ × Π-allowed p₃′ q₃′ ×
      Π-allowed p₄′ q₄′ × Π-allowed 𝟘 q₅′
    oks =
      let _ , ⊢Π , ok₁ = inversion-ΠΣ $ syntacticTerm ⊢[]-cong′
          _ , ⊢Π , ok₂ = inversion-ΠΣ ⊢Π
          _ , ⊢Π , ok₃ = inversion-ΠΣ ⊢Π
          _ , ⊢Π , ok₄ = inversion-ΠΣ ⊢Π
          _ , _  , ok₅ = inversion-ΠΣ ⊢Π
      in
      hyp₁ ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄ , hyp₅ ok₅

opaque

  -- One can make the "p" grades of Has-[]-cong "smaller" (given
  -- certain assumptions).

  Has-[]-cong-weaker :
    {Γ : Con Term n} →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′) →
    (Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · p₁ →
    ⌜ m ⌝ · p₂′ ≤ ⌜ m ⌝ · p₂ →
    ⌜ m ⌝ · p₃′ ≤ ⌜ m ⌝ · p₃ →
    ⌜ m ⌝ · p₄′ ≤ ⌜ m ⌝ · p₄ →
    Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong s m Γ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
  Has-[]-cong-weaker
    {n} {p₁} {p₁′} {q₁′} {p₂} {p₂′} {q₂′} {p₃} {p₃′} {q₃′}
    {p₄} {p₄′} {q₄′} {q₅′} {m} {s} {Γ}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
    has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open Has-[]-cong-weaker hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ = lam p₁′ $ lam p₂′ $ lam p₃′ $ lam p₄′ $ lam 𝟘 []-cong″

    ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
    ▸[]-cong‴ =
      lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub
        (((((wkUsage (stepn id 5) ▸[]-cong′ ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ
          var) ∘ₘ
         var) $
      (begin
         𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · p₄′ ∙
         ⌜ m ⌝ · 𝟘                                                     ≤⟨ ≤ᶜ-refl ∙ hyp₁′ ∙ hyp₂′ ∙ hyp₃′ ∙ hyp₄′ ∙ ≤-reflexive (·-zeroʳ _) ⟩

         𝟘ᶜ ∙ ⌜ m ⌝ · p₁ ∙ ⌜ m ⌝ · p₂ ∙ ⌜ m ⌝ · p₃ ∙ ⌜ m ⌝ · p₄ ∙ 𝟘    ≈˘⟨ ≈ᶜ-trans (+ᶜ-congˡ (·ᶜ-zeroˡ _)) $
                                                                           ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                           ≈ᶜ-trans
                                                                             (+ᶜ-cong
                                                                                (+ᶜ-cong
                                                                                   (+ᶜ-cong (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x4))
                                                                                      (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x3))
                                                                                   (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x2))
                                                                                (·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x1))
                                                                             ((≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                               ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                               +ᶜ-identityʳ _) ∙
                                                                              (PE.trans (+-identityʳ _) $
                                                                               PE.trans (+-identityʳ _) $
                                                                               +-identityˡ _) ∙
                                                                              (PE.trans (+-identityʳ _) $
                                                                               PE.trans (+-congʳ (+-identityʳ _)) $
                                                                               +-identityˡ _) ∙
                                                                              (PE.trans
                                                                                 (+-congʳ $
                                                                                  (PE.trans (+-identityʳ _) $
                                                                                   +-identityʳ _)) $
                                                                               +-identityˡ _ ) ∙
                                                                              (PE.trans (+-identityʳ _) $
                                                                               PE.trans (+-identityʳ _) $
                                                                               +-identityʳ _)) ⟩
         ((((𝟘ᶜ +ᶜ p₁ ·ᶜ (𝟘ᶜ , x4 ≔ ⌜ m ᵐ· p₁ ⌝)) +ᶜ
            p₂ ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ m ᵐ· p₂ ⌝)) +ᶜ
           p₃ ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· p₃ ⌝)) +ᶜ
          p₄ ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· p₄ ⌝)) +ᶜ
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝)                                   ∎)
      where
      open ≤ᶜ-reasoning

    ⊢[]-cong‴ :
      ε » Γ ⊢ []-cong‴ ∷
        Π p₁′ , q₁′ ▷ Level ▹
        Π p₂′ , q₂′ ▷ U (var x0) ▹
        Π p₃′ , q₃′ ▷ var x0 ▹
        Π p₄′ , q₄′ ▷ var x1 ▹
        Π 𝟘   , q₅′ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (var x4) (var x3)) ([ var x2 ]) ([ var x1 ])
    ⊢[]-cong‴ =
      let ok₁ , ok₂ , ok₃ , ok₄ , ok₅ = oks in
      lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
      lamⱼ′ ok₅ ⊢[]-cong″

opaque
  unfolding Has-[]-cong-weaker Erased.Erased Erased.[_]

  -- One can make the "p" grades of Has-computing-[]-cong "smaller"
  -- (given certain assumptions).

  Has-computing-[]-cong-weaker :
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′) →
    (Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · p₁ →
    ⌜ m ⌝ · p₂′ ≤ ⌜ m ⌝ · p₂ →
    ⌜ m ⌝ · p₃′ ≤ ⌜ m ⌝ · p₃ →
    ⌜ m ⌝ · p₄′ ≤ ⌜ m ⌝ · p₄ →
    Has-computing-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-computing-[]-cong s m Δ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
  Has-computing-[]-cong-weaker
    {p₁} {p₁′} {p₂} {p₂′} {p₃} {p₃′} {p₄} {p₄′}
    hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    let open Has-[]-cong-weaker hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ has-[]-cong

        ok = Has-[]-cong→Level-allowed has-[]-cong

        ok₁ , ok₂ , ok₃ , ok₄ , ok₅ = oks
    in
      Has-[]-cong-weaker hyp₁ hyp₂ hyp₃ hyp₄ hyp₅
        hyp₁′ hyp₂′ hyp₃′ hyp₄′ has-[]-cong
    , λ _ _ _ l A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) in
        wk ρ
          (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam p₄′ $ lam 𝟘 $
           wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4 ∘⟨ p₂ ⟩ var x3
             ∘⟨ p₃ ⟩ var x2 ∘⟨ p₄ ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0)
          ∘⟨ p₁′ ⟩ l ∘⟨ p₂′ ⟩ A ∘⟨ p₃′ ⟩ t ∘⟨ p₄′ ⟩ t ∘⟨ 𝟘 ⟩ rfl          ⇒*⟨ β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                                (W.wkTerm
                                                                                  (W.liftnʷ Δ⊇Γ $ ∙_ $ ⊢Id-2-1-0 ok $ wfTerm $
                                                                                   WD.defn-wkTerm ⊇ε ⊢[]-cong′) $
                                                                                  WD.defn-wkTerm ⊇ε ⊢[]-cong″)
                                                                                (⊢∷Level→⊢∷Level ok (inversion-U-Level (wf-⊢∷ ⊢A)))
                                                                                ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        (wk (liftn ρ 5) (wk (stepn id 5) []-cong′)
           [ consSubst
               (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
               rfl ])
          ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ A ∘⟨ p₃ ⟩ t ∘⟨ p₄ ⟩ t ∘⟨ 𝟘 ⟩ rfl              ≡⟨ PE.cong
                                                                               (λ []-cong → []-cong ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _) $
                                                                             PE.trans
                                                                               (PE.cong _[ _ ] $
                                                                                PE.trans (wk-comp _ _ []-cong′) $
                                                                                PE.cong (flip wk _) $
                                                                                PE.sym $ liftn-stepn-comp 5) $
                                                                             PE.trans (subst-wk []-cong′) $
                                                                             PE.sym $ wk≡subst _ _ ⟩⊢≡

        wk ρ []-cong′ ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ A ∘⟨ p₃ ⟩ t ∘⟨ p₄ ⟩ t ∘⟨ 𝟘 ⟩ rfl  ≡⟨ []-cong′≡ _ _ _ _ _ _ _ Δ⊇Γ ⊢A ⊢t ⟩⊢∎

        rfl                                                               ∎

-- Some definitions/lemmas used below.

private
  module Has-[]-cong-stronger
    {Γ : Con Term n}
    (hyp₁ : Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′)
    (hyp₂ : Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′)
    (hyp₃ : Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′)
    (hyp₄ : Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′)
    (hyp₅ : Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅)
    where

    open Erased s

    []-cong″ : Term (5+ n)
    []-cong″ =
      cong 𝟘 (Erased (var x4) (Erased (var x4) (var x3))) [ [ var x2 ] ]
        [ [ var x1 ] ] (Erased (var x4) (var x3))
        (mapᴱ (Erased (var x5) (var x4))
           (erased (var x5) (var x0)) (var x0))
        (wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4
           ∘⟨ p₂ ⟩ Erased (var x4) (var x3) ∘⟨ p₃ ⟩ [ var x2 ]
           ∘⟨ p₄ ⟩ [ var x1 ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                    (Erased (var x4) (var x3)) [ var x0 ] (var x0))

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        Π-allowed p₁′ q₁′ × Π-allowed p₂′ q₂′ ×
        Π-allowed p₃′ q₃′ × Π-allowed p₄′ q₄′ ×
        Π-allowed 𝟘 q₅′ ×
        ε »
        Γ ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
          Id (var x2) (var x1) (var x0) ⊢
        []-cong″ ∷
        Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        let ok               = Has-[]-cong→Level-allowed has-[]-cong
            _ , ⊢Π  , ok₁    = inversion-ΠΣ $ syntacticTerm ⊢[]-cong′
            _ , ⊢Π  , ok₂    = inversion-ΠΣ ⊢Π
            _ , ⊢Π  , ok₃    = inversion-ΠΣ ⊢Π
            _ , ⊢Π  , ok₄    = inversion-ΠΣ ⊢Π
            _ , ⊢Id , ok₅    = inversion-ΠΣ ⊢Π
            Erased-ok , _    = inversion-Erased $
                               inversion-Id ⊢Id .proj₁
            ⊢Id              = ⊢Id-2-1-0 ok (wfTerm ⊢[]-cong′)
            ⊢3               = var₃ ⊢Id
            ⊢4               = term ok (var₄ ⊢Id)
            ⊢Erased-3        = Erasedⱼ-U Erased-ok ⊢3
            ⊢Erased-Erased-3 = univ (Erasedⱼ-U Erased-ok ⊢Erased-3)
            ⊢5               = term ok (var₅ ⊢Erased-Erased-3)

            lemma :
              ∀ t →
              ε »
                Γ ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
                  Id (var x2) (var x1) (var x0) ⊢
                t ∷ var x3 →
              ε »
                Γ ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
                  Id (var x2) (var x1) (var x0) ⊢
                mapᴱ (Erased (var x5) (var x4))
                  (erased (var x5) (var x0)) (var x0) [ [ [ t ] ] ]₀ ≡
                [ t ] ∷ Erased (var x4) (var x3)
            lemma t ⊢t =
              mapᴱ (Erased (var x5) (var x4)) (erased (var x5) (var x0))
                (var x0) [ [ [ t ] ] ]₀                                   ≡⟨ PE.trans mapᴱ-[] $
                                                                             PE.cong₂ (mapᴱ _) erased-[] PE.refl ⟩⊢≡
              mapᴱ (Erased (var x4) (var x3)) (erased (var x4) (var x0))
                ([ [ t ] ])                                               ≡⟨ mapᴱ-β Erased-ok ⊢4 (erasedⱼ (var₀ (univ ⊢Erased-3)))
                                                                               ([]ⱼ Erased-ok ⊢4 ⊢t) ⟩⊢

              [ erased (var x4) (var x0) [ [ t ] ]₀ ]                     ≡⟨ PE.cong [_] erased-[] ⟩⊢≡

              [ erased (var x3) ([ t ]) ]                                 ≡⟨ P.[]-cong′ Erased-ok ⊢4 $
                                                                             Erased-β Erased-ok ⊢t ⟩⊢∎
              [ t ]                                                       ∎
        in
        hyp₁ ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄ , hyp₅ ok₅ ,
        _⊢_∷_.conv
          (⊢cong
             (⊢mapᴱ ⊢5
                (erasedⱼ $ var₀ $ Erasedⱼ Erased-ok ⊢5 $
                 univ (var₄ ⊢Erased-Erased-3))
                (var₀ ⊢Erased-Erased-3)) $
           flip _∘ⱼ_
             (⊢cong
                ([]ⱼ Erased-ok (term ok (var₅ (univ ⊢3))) $
                 var₀ (univ ⊢3)) $
              var₀ ⊢Id) $
           flip _∘ⱼ_ ([]ⱼ Erased-ok ⊢4 $ var₁ ⊢Id) $
           flip _∘ⱼ_ ([]ⱼ Erased-ok ⊢4 $ var₂ ⊢Id) $
           flip _∘ⱼ_ (Erasedⱼ-U Erased-ok $ var₃ ⊢Id) $
           flip _∘ⱼ_ (var₄ ⊢Id) $
            W.wkTerm (W.ʷ⊇-drop (∙ ⊢Id)) ⊢[]-cong′)
          (Id-cong (refl (univ ⊢Erased-3)) (lemma _ (var₂ ⊢Id))
             (lemma _ (var₁ ⊢Id)))

opaque

  -- One can replace some of the "p" grades in Has-[]-cong with grades
  -- that satisfy certain assumptions (given certain assumptions).
  --
  -- Note that, if all Π-types are allowed, then all but one of the
  -- assumptions (⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · ω · p₁) are satisfied for the
  -- erasure modality with 𝟘ᵐ.

  Has-[]-cong-stronger :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′) →
    (Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · ω · p₁ →
    ⌜ m ⌝ · p₂′ ≤ 𝟘 →
    ⌜ m ⌝ · p₃′ ≤ 𝟘 →
    ⌜ m ⌝ · p₄′ ≤ 𝟘 →
    Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong s m Γ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
  Has-[]-cong-stronger
    {n} {s} {p₁} {p₁′} {q₁′} {p₂} {p₂′} {q₂′} {p₃} {p₃′} {q₃′}
    {p₄} {p₄′} {q₄′} {q₅′} {m} {Γ}
    trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
    has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open ErasedU s
    open Has-[]-cong-stronger hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ =
      lam p₁′ $ lam p₂′ $ lam p₃′ $ lam p₄′ $ lam 𝟘 []-cong″

    opaque

      ⊢[]-cong‴ :
        ε » Γ ⊢ []-cong‴ ∷
        Π p₁′ , q₁′ ▷ Level ▹
        Π p₂′ , q₂′ ▷ U (var x0) ▹
        Π p₃′ , q₃′ ▷ var x0 ▹
        Π p₄′ , q₄′ ▷ var x1 ▹
        Π 𝟘   , q₅′ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong‴ =
        let ok₁ , ok₂ , ok₃ , ok₄ , ok₅ , ⊢[]-cong″ = ⊢[]-cong″ in
        lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
        lamⱼ′ ok₅ ⊢[]-cong″

      ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
      ▸[]-cong‴ =
        lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
        sub
          (▸cong (▸Erased var (▸Erased var var)) (▸[] (▸[] var))
             (▸[] (▸[] var)) (sub (▸Erased var var) lemma)
             (sub
                (▸mapᴱ′ trivial 𝟘≤𝟙 (λ _ → _ , ▸Erased var var)
                   (sub
                      (▸erased′ trivial 𝟘≤𝟙 var (λ _ → _ , var))
                      (begin
                         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                         𝟘ᶜ                ∎))
                   var)
                (begin
                   𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                   𝟘ᶜ              ∎))
             (flip _∘ₘ_
                (▸cong var var var (sub (▸Erased var var) lemma)
                   (sub (▸[] var) $ begin
                      𝟘ᶜ ∙ ⌜ m ᵐ· 𝟘 ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                      𝟘ᶜ                   ∎)
                   var
                   (λ _ → begin
                      𝟘ᶜ ∙ ⌜ m ᵐ· 𝟘 ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                      𝟘ᶜ                   ∎)
                   (λ _ → begin
                      𝟘ᶜ                                             ≈˘⟨ ≈ᶜ-trans
                                                                           (+ᶜ-cong
                                                                              (≈ᶜ-trans (·ᶜ-congʳ $ ·-zeroʳ _) $
                                                                               ·ᶜ-zeroˡ _)
                                                                              (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _))) $
                                                                         +ᶜ-identityʳ _ ⟩
                      (⌜ m ᵐ· 𝟘 ⌝ · 𝟘) ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
                      𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ                            ∎)) $
              flip _∘ₘ_ (▸[] var) $
              flip _∘ₘ_ (▸[] var) $
              flip _∘ₘ_ (sub (▸Erased var var) lemma) $
              flip _∘ₘ_ var $
              wkUsage _ ▸[]-cong′)
             (λ _ → begin
                𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                𝟘ᶜ              ∎)
             (λ _ → begin
                𝟘ᶜ                                        ≈˘⟨ ≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _))) $
                                                              +ᶜ-identityʳ _ ⟩
                (⌜ m ⌝ · 𝟘) ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ  ∎)) $
        (begin
           𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · p₄′ ∙
           ⌜ m ⌝ · 𝟘                                                     ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

           𝟘ᶜ ∙ ⌜ m ⌝ · p₁′ ∙ ⌜ m ⌝ · p₂′ ∙ ⌜ m ⌝ · p₃′ ∙ ⌜ m ⌝ · p₄′ ∙
           𝟘                                                             ≤⟨ ≤ᶜ-refl ∙ hyp₁′ ∙ hyp₂′ ∙ hyp₃′ ∙ hyp₄′ ∙ ≤-refl ⟩

           𝟘ᶜ , x4 ≔ ⌜ m ⌝ · ω · p₁                                      ≈⟨ update-congʳ {γ = 𝟘ᶜ} {x = x4} $
                                                                            PE.trans (⌜⌝-·-comm m) $
                                                                            PE.trans (·-assoc _ _ _) $
                                                                            ·-congˡ (PE.sym (⌜⌝-·-comm m)) ⟩

           𝟘ᶜ , x4 ≔ ω · ⌜ m ⌝ · p₁                                      ≈˘⟨ ≈ᶜ-trans
                                                                               (·ᶜ-congˡ $
                                                                                ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                                ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                                ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                                ≈ᶜ-trans
                                                                                  (+ᶜ-cong
                                                                                     (≈ᶜ-trans
                                                                                        (+ᶜ-cong
                                                                                           (≈ᶜ-trans
                                                                                              (+ᶜ-cong
                                                                                                 (≈ᶜ-trans
                                                                                                    (+ᶜ-cong
                                                                                                       (≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                                                        ·ᶜ𝟘ᶜ,≔⌜ᵐ·⌝ m x4)
                                                                                                       (·ᶜ-zeroʳ _)) $
                                                                                                  +ᶜ-identityʳ _)
                                                                                                 (·ᶜ-zeroʳ _)) $
                                                                                            +ᶜ-identityʳ _)
                                                                                           (·ᶜ-zeroʳ _)) $
                                                                                      +ᶜ-identityʳ _)
                                                                                     (·ᶜ-zeroˡ _)) $
                                                                                +ᶜ-identityʳ _) $
                                                                             ·ᶜ𝟘ᶜ,≔ x4 ⟩
           ω ·ᶜ
           (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ
            (((((𝟘ᶜ +ᶜ p₁ ·ᶜ (𝟘ᶜ , x4 ≔ ⌜ m ᵐ· p₁ ⌝)) +ᶜ
                p₂ ·ᶜ 𝟘ᶜ) +ᶜ
               p₃ ·ᶜ 𝟘ᶜ) +ᶜ
              p₄ ·ᶜ 𝟘ᶜ) +ᶜ
             𝟘 ·ᶜ ω ·ᶜ
             ((𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
              (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ 𝟘ᶜ)) +ᶜ
            𝟘ᶜ)                                                          ∎)
        where
        open ≤ᶜ-reasoning

        𝟘≤⌜𝟘ᵐ?⌝ : 𝟘 ≤ ⌜ 𝟘ᵐ? ⌝
        𝟘≤⌜𝟘ᵐ?⌝ = 𝟘ᵐ?-elim (λ m → 𝟘 ≤ ⌜ m ⌝) ≤-refl
          (case PE.singleton s of λ where
             (𝕨 , PE.refl) → ≡-trivial ∘→ proj₁ ∘→ trivial PE.refl
             (𝕤 , PE.refl) → 𝟘≤𝟙 PE.refl)

        lemma : 𝟘ᶜ {n = 5+ n} ≤ᶜ 𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝
        lemma = begin
          𝟘ᶜ                 ≡⟨⟩
          𝟘ᶜ , x3 ≔ 𝟘        ≤⟨ update-monotoneʳ {γ = 𝟘ᶜ} x3 𝟘≤⌜𝟘ᵐ?⌝ ⟩
          𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝  ∎

private opaque

  -- Some lemmas used below.

  wk2-[]₁ : wk2 t [ sgSubst u ⇑ ] PE.≡ wk1 t
  wk2-[]₁ {t} {u} =
    wk2 t [ sgSubst u ⇑ ]        ≡⟨⟩
    wk1 (wk1 t) [ sgSubst u ⇑ ]  ≡⟨ wk1-liftSubst (wk1 t) ⟩
    wk1 (wk1 t [ u ]₀)           ≡⟨ PE.cong wk1 $ wk1-sgSubst _ _ ⟩
    wk1 t                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

  wk2-[]₁[]₀ : wk2 t [ sgSubst u ⇑ ] [ v ]₀ PE.≡ t
  wk2-[]₁[]₀ {t} {u} {v} =
    wk2 t [ sgSubst u ⇑ ] [ v ]₀  ≡⟨ PE.cong _[ _ ] $ wk2-[]₁ {t = t} ⟩
    wk1 t [ v ]₀                  ≡⟨ wk1-sgSubst _ _ ⟩
    t                             ∎
    where
    open Tools.Reasoning.PropositionalEquality

  wk3-[]₂[]₁[]₀ :
    wk[ 3 ] t [ sgSubst u ⇑ ⇑ ] [ sgSubst v ⇑ ] [ w ]₀ PE.≡ t
  wk3-[]₂[]₁[]₀ {t} {u} {v} {w} =
    wk[ 3 ] t [ sgSubst u ⇑ ⇑ ] [ sgSubst v ⇑ ] [ w ]₀    ≡⟨⟩
    wk1 (wk2 t) [ sgSubst u ⇑ ⇑ ] [ sgSubst v ⇑ ] [ w ]₀  ≡⟨ PE.cong _[ _ ] $ PE.cong _[ _ ] $ wk1-liftSubst (wk2 t) ⟩
    wk1 (wk2 t [ sgSubst u ⇑ ]) [ sgSubst v ⇑ ] [ w ]₀    ≡⟨ PE.cong _[ _ ] $ wk1-liftSubst (wk2 t [ _ ]) ⟩
    wk1 (wk2 t [ sgSubst u ⇑ ] [ sgSubst v ]) [ w ]₀      ≡⟨ wk1-sgSubst _ _ ⟩
    wk2 t [ sgSubst u ⇑ ] [ sgSubst v ]                   ≡⟨ wk2-[]₁[]₀ ⟩
    t                                                     ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding Has-[]-cong-stronger

  -- One can replace some of the "p" grades in Has-computing-[]-cong
  -- with grades that satisfy certain assumptions (given certain
  -- assumptions).
  --
  -- Note that, if all Π-types are allowed, then all but one of the
  -- assumptions (⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · ω · p₁) are satisfied for the
  -- erasure modality with 𝟘ᵐ.

  Has-computing-[]-cong-stronger :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₁ q₁ → Π-allowed p₁′ q₁′) →
    (Π-allowed p₂ q₂ → Π-allowed p₂′ q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed p₃′ q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed p₄′ q₄′) →
    (Π-allowed 𝟘  q₅ → Π-allowed 𝟘   q₅′) →
    ⌜ m ⌝ · p₁′ ≤ ⌜ m ⌝ · ω · p₁ →
    ⌜ m ⌝ · p₂′ ≤ 𝟘 →
    ⌜ m ⌝ · p₃′ ≤ 𝟘 →
    ⌜ m ⌝ · p₄′ ≤ 𝟘 →
    Has-computing-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-computing-[]-cong s m Γ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
  Has-computing-[]-cong-stronger
    {n} {s} {p₁} {p₁′} {q₁′} {p₂} {p₂′} {q₂′} {p₃} {p₃′} {q₃′}
    {p₄} {q₄} {p₄′} {q₄′} {q₅} {q₅′} {m} {Γ}
    trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    has-[]-cong′ , []-cong″-computes
    where
    open Erased s

    has-[]-cong′ : Has-[]-cong s m Γ p₁′ q₁′ p₂′ q₂′ p₃′ q₃′ p₄′ q₄′ q₅′
    has-[]-cong′ =
      Has-[]-cong-stronger
        trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ hyp₁′ hyp₂′ hyp₃′ hyp₄′
        has-[]-cong

    []-cong″ : Term n
    []-cong″ = has-[]-cong′ .proj₁

    opaque

      lemma :
        (ρ : Wk n′ n) (l A t : Term n′) (u : Term n) →
        wk (stepn id 5) u
          U.[ consSubst
                (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                rfl ₛ•
              liftn ρ 5 ] PE.≡
        wk ρ u
      lemma ρ l A t u =
        wk (stepn id 5) u
          U.[ consSubst
                (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                rfl ₛ•
              liftn ρ 5 ]                                               ≡⟨ subst-wk u ⟩

        u U.[ (consSubst
                 (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                 rfl ₛ•
               liftn ρ 5) ₛ•
              stepn id 5 ]                                              ≡˘⟨ wk≡subst _ _ ⟩

        wk ρ u                                                          ∎
        where
        open Tools.Reasoning.PropositionalEquality

    opaque
      unfolding Erased [_]

      []-cong″-computes :
        ∀ m n′ (Δ : Cons m n′) (l A t : Term n′) (ρ : Wk n′ n) →
        Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
        Δ ⊢ A ∷ U l →
        Δ ⊢ t ∷ A →
        Δ ⊢
          wk ρ []-cong″ ∘⟨ p₁′ ⟩ l ∘⟨ p₂′ ⟩ A ∘⟨ p₃′ ⟩ t ∘⟨ p₄′ ⟩ t
            ∘⟨ 𝟘 ⟩ rfl ≡
          rfl ∷ Id (Erased l A) [ t ] ([ t ])
      []-cong″-computes _ _ Δ l A t ρ Δ⊇Γ ⊢A ⊢t =
        let open Has-[]-cong-stronger
                   hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ has-[]-cong

            ok₁ , ok₂ , ok₃ , ok₄ , ok₅ , ⊢[]-cong″ = ⊢[]-cong″

            ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A))
        in
        wk ρ
          (lam p₁′ $ lam p₂′ $ lam p₃′ $ lam p₄′ $ lam 𝟘 $
           cong 𝟘 (Erased (var x4) (Erased (var x4) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ] (Erased (var x4) (var x3))
             (mapᴱ (Erased (var x5) (var x4)) (erased (var x5) (var x0))
                (var x0))
             (wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4
                ∘⟨ p₂ ⟩ Erased (var x4) (var x3) ∘⟨ p₃ ⟩ [ var x2 ]
                ∘⟨ p₄ ⟩ [ var x1 ]
                ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                         (Erased (var x4) (var x3)) [ var x0 ]
                         (var x0)))
          ∘⟨ p₁′ ⟩ l ∘⟨ p₂′ ⟩ A ∘⟨ p₃′ ⟩ t ∘⟨ p₄′ ⟩ t ∘⟨ 𝟘 ⟩ rfl ∷
          Id (Erased l A) [ t ] ([ t ])                                   ⇒*⟨ β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                                (W.wkTerm
                                                                                   (W.liftnʷ Δ⊇Γ $
                                                                                    ∙ ⊢Id-2-1-0 Level-ok (WD.defn-wk′ ⊇ε (wfTerm ⊢[]-cong′))) $
                                                                                 WD.defn-wkTerm ⊇ε ⊢[]-cong″)
                                                                                ⊢l ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢∷
                                                                           ˘⟨ Id-cong (refl (univ ⊢Erased-A)) mapᴱ-lemma mapᴱ-lemma ⟩≡
        wk (liftn ρ 5)
          (cong 𝟘 (Erased (var x4) (Erased (var x4) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ] (Erased (var x4) (var x3))
             (mapᴱ (Erased (var x5) (var x4)) (erased (var x5) (var x0))
                (var x0))
             (wk (stepn id 5) []-cong′ ∘⟨ p₁ ⟩ var x4
                ∘⟨ p₂ ⟩ Erased (var x4) (var x3) ∘⟨ p₃ ⟩ [ var x2 ]
                ∘⟨ p₄ ⟩ [ var x1 ]
                ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                         (Erased (var x4) (var x3)) [ var x0 ]
                         (var x0)))
          U.[ consSubst
                (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                rfl ] ∷
          Id (Erased l A)
            (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
               (var x0) [ [ [ t ] ] ]₀)
            (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
               (var x0) [ [ [ t ] ] ]₀)                                   ≡⟨ PE.trans (subst-wk (cong _ _ _ _ _ _ _)) $
                                                                             PE.trans cong-[] $
                                                                             PE.cong₂ (cong _ _ _ _ _)
                                                                               (PE.trans mapᴱ-[] $
                                                                                PE.cong₂ (mapᴱ _) erased-[] PE.refl)
                                                                               (PE.cong₂ _∘⟨ 𝟘 ⟩_
                                                                                  (PE.cong (_∘⟨ p₄ ⟩ [ t ]) $
                                                                                   PE.cong (_∘⟨ p₃ ⟩ [ t ]) $
                                                                                   PE.cong (_∘⟨ p₂ ⟩ Erased l A) $
                                                                                   PE.cong (_∘⟨ _ ⟩ _) $
                                                                                   lemma _ _ _ _ _)
                                                                                  cong-[]) ⟩⊢∷≡
        cong 𝟘 (Erased l (Erased l A)) [ [ t ] ] [ [ t ] ] (Erased l A)
          (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
             (var x0))
          (wk ρ []-cong′ ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ Erased l A ∘⟨ p₃ ⟩ [ t ]
             ∘⟨ p₄ ⟩ [ t ]
             ∘⟨ 𝟘 ⟩ cong 𝟘 A t t (Erased l A) [ var x0 ] rfl)             ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                               (refl (univ ⊢Erased-A)) (refl ⊢mapᴱ-0) $
                                                                             PE.subst (_⊢_≡_∷_ _ _ _)
                                                                               (PE.cong₃ Id ≡Erased-Erased wk2-[]₁[]₀ (wk1-sgSubst _ _)) $
                                                                             _⊢_≡_∷_.app-cong
                                                                               (_⊢_≡_∷_.refl $
                                                                                PE.subst (_⊢_∷_ _ _)
                                                                                  (PE.cong₂ (Π_,_▷_▹_ 𝟘 q₅)
                                                                                     (PE.cong₃ Id wk2-[]₁[]₀ (wk1-sgSubst _ _) PE.refl) $
                                                                                   PE.refl) $
                                                                                flip _∘ⱼ_ ⊢[t] $
                                                                                PE.subst (_⊢_∷_ _ _)
                                                                                  (PE.cong₂ (Π_,_▷_▹_ p₄ q₄) (wk1-sgSubst _ _) PE.refl) $
                                                                                flip _∘ⱼ_ ⊢[t] $
                                                                                flip _∘ⱼ_ ⊢Erased-A∷U $
                                                                                flip _∘ⱼ_ ⊢l $
                                                                                W.wkTerm Δ⊇Γ $
                                                                                WD.defn-wkTerm ⊇ε ⊢[]-cong′) $
                                                                             cong-≡ ⊢t $
                                                                             PE.subst (_⊢_∷_ _ _) (PE.sym wk-Erased) $
                                                                             []ⱼ Erased-ok (W.wkLevel₁ (univ ⊢A) ⊢l∷L) (var₀ (univ ⊢A)) ⟩⊢
        cong 𝟘 (Erased l (Erased l A)) [ [ t ] ] [ [ t ] ] (Erased l A)
          (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
             (var x0))
          (wk ρ []-cong′ ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ Erased l A ∘⟨ p₃ ⟩ [ t ]
             ∘⟨ p₄ ⟩ [ t ] ∘⟨ 𝟘 ⟩ rfl)                                    ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                               (refl (univ ⊢Erased-A)) (refl ⊢mapᴱ-0) $
                                                                             []-cong′≡ _ _ _ _ _ _ _ Δ⊇Γ ⊢Erased-A∷U ⊢[t] ⟩⊢
        cong 𝟘 (Erased l (Erased l A)) [ [ t ] ] [ [ t ] ] (Erased l A)
          (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
             (var x0))
          rfl                                                             ⇒⟨ cong-⇒ ⊢[[t]] ⊢mapᴱ-0 ⟩⊢∎

        rfl                                                               ∎
        where
        Level-ok : Level-allowed
        Level-ok = Has-[]-cong→Level-allowed has-[]-cong

        Erased-ok : Erased-allowed s
        Erased-ok =
          proj₁ $ inversion-Erased $
          proj₁ $ inversion-Id $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          proj₁ $ proj₂ $ inversion-ΠΣ $
          syntacticTerm $ has-[]-cong′ .proj₂ .proj₂

        ⊢l∷L : Δ ⊢ l ∷Level
        ⊢l∷L = inversion-U-Level (wf-⊢∷ ⊢A)

        ⊢l : Δ ⊢ l ∷ Level
        ⊢l = ⊢∷Level→⊢∷Level Level-ok ⊢l∷L

        ⊢[t] : Δ ⊢ [ t ] ∷ Erased l A
        ⊢[t] = []ⱼ Erased-ok ⊢l∷L ⊢t

        ⊢Erased-A : Δ ⊢ Erased l A ∷ U l
        ⊢Erased-A = Erasedⱼ-U Erased-ok ⊢A

        ⊢[[t]] : Δ ⊢ [ [ t ] ] ∷ Erased l (Erased l A)
        ⊢[[t]] = []ⱼ Erased-ok ⊢l∷L ⊢[t]

        ⊢Erased-Erased-A : Δ ⊢ Erased l (Erased l A)
        ⊢Erased-Erased-A = syntacticTerm ⊢[[t]]

        ⊢Erased-A∷U : Δ ⊢ Erased l A ∷ U l
        ⊢Erased-A∷U = Erasedⱼ-U Erased-ok ⊢A

        ⊢mapᴱ-0 :
          Δ »∙ Erased l (Erased l A) ⊢
            mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
              (var x0) ∷
            wk1 (Erased l A)
        ⊢mapᴱ-0 =
          PE.subst (_⊢_∷_ _ _) (PE.sym wk-Erased) $
          ⊢mapᴱ (W.wkLevel₁ ⊢Erased-Erased-A ⊢l∷L)
            (erasedⱼ $ PE.subst (_⊢_∷_ _ _) wk-Erased $
             var₀ $ PE.subst (_⊢_ _) wk-Erased $
             W.wk₁ ⊢Erased-Erased-A (univ ⊢Erased-A))
            (PE.subst (_⊢_∷_ _ _)
               (PE.trans wk-Erased $ PE.cong (Erased _) wk-Erased) $
             var₀ ⊢Erased-Erased-A)

        mapᴱ-lemma :
          Δ ⊢
            mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
              (var x0) [ [ [ t ] ] ]₀ ≡
            [ t ] ∷
            Erased l A
        mapᴱ-lemma =
          mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
            (var x0) [ [ [ t ] ] ]₀                                 ≡⟨ PE.trans mapᴱ-[] $
                                                                       PE.cong₃ mapᴱ
                                                                         (PE.trans
                                                                            (PE.cong _[ [ [ t ] ] ]₀ $ PE.sym $
                                                                             wk-Erased {l = l} {A = A}) $
                                                                          wk1-sgSubst _ _)
                                                                         (PE.trans erased-[] $
                                                                          PE.cong₂ erased wk2-[]₁ PE.refl)
                                                                         PE.refl ⟩⊢≡

          mapᴱ (Erased l A) (erased (wk1 A) (var x0)) ([ [ t ] ])   ≡⟨ mapᴱ-β Erased-ok ⊢l∷L
                                                                         (erasedⱼ $
                                                                          PE.subst (_⊢_∷_ _ _) wk-Erased $
                                                                          var₀ (univ ⊢Erased-A))
                                                                         ([]ⱼ Erased-ok ⊢l∷L ⊢t) ⟩⊢

          [ erased (wk1 A) (var x0) [ [ t ] ]₀ ]                    ≡⟨ PE.cong ([_]) $
                                                                       PE.trans erased-[] $
                                                                       PE.cong₂ erased (wk1-sgSubst _ _) PE.refl ⟩⊢≡

          [ erased A ([ t ]) ]                                      ≡⟨ P.[]-cong′ Erased-ok ⊢l∷L $
                                                                       Erased-β Erased-ok ⊢t ⟩⊢∎
          [ t ]                                                     ∎

        ≡Erased-Erased :
          (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷
           wk[ 3 ] (Erased l A) ▹
           Lift (wk[ 5 ] l U.[ sgSubst (Erased l A) ⇑[ 4 ] ]) (Unit s))
            U.[ sgSubst ([ t ]) ⇑[ 2 ] ] [ sgSubst ([ t ]) ⇑ ]
            [ cong 𝟘 A t t (Erased l A) [ var x0 ] rfl ]₀ PE.≡
          Erased l (Erased l A)
        ≡Erased-Erased =
          let u = cong 𝟘 A t t (Erased l A) [ var x0 ] rfl

              lemma =
                wk[ 5 ] l U.[ sgSubst (Erased l A) ⇑[ 4 ] ]   ≡⟨ PE.cong _[ sgSubst (Erased l A) ⇑[ 4 ] ] $ wk[]≡wk[]′ {t = l} ⟩
                wk[ 5 ]′ l U.[ sgSubst (Erased l A) ⇑[ 4 ] ]  ≡⟨ wk[+1]′-[₀⇑]≡ ⟩
                wk[ 4 ]′ l                                    ≡˘⟨ wk[]≡wk[]′ ⟩
                wk[ 4 ] l                                     ∎
          in

          (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷
           wk[ 3 ] (Erased l A) ▹
           Lift (wk[ 5 ] l U.[ sgSubst (Erased l A) ⇑[ 4 ] ]) (Unit s))
            U.[ sgSubst ([ t ]) ⇑[ 2 ] ] [ sgSubst ([ t ]) ⇑ ] [ u ]₀    ≡⟨ PE.cong
                                                                              (_[ u ]₀ ∘→ _[ sgSubst ([ t ]) ⇑ ] ∘→
                                                                               _[ sgSubst ([ t ]) ⇑[ 2 ] ] ∘→
                                                                               Σ⟨ s ⟩ 𝟘 , 𝟘 ▷ wk[ 3 ] (Erased l A) ▹_ ∘→
                                                                               flip Lift (Unit s))
                                                                              lemma ⟩
          Erased (wk[ 3 ] l) (wk[ 3 ] (Erased l A))
            U.[ sgSubst ([ t ]) ⇑[ 2 ] ] [ sgSubst ([ t ]) ⇑ ] [ u ]₀    ≡˘⟨ PE.cong (_[ u ]₀ ∘→ _[ sgSubst ([ t ]) ⇑ ]) $
                                                                             PE.cong _[ sgSubst ([ t ]) ⇑[ 2 ] ] $
                                                                             PE.trans wk[]≡wk[]′ $
                                                                             PE.trans (wk-Erased {l = l} {A = Erased l A}) $
                                                                             PE.sym $ PE.cong₂ Erased wk[]≡wk[]′ wk[]≡wk[]′ ⟩
          wk[ 3 ] (Erased l (Erased l A))
            U.[ sgSubst ([ t ]) ⇑[ 2 ] ] [ sgSubst ([ t ]) ⇑ ] [ u ]₀    ≡⟨ wk3-[]₂[]₁[]₀ ⟩

          Erased l (Erased l A)                                          ∎
          where
          open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- []-cong can sometimes be defined

-- Some definitions used in
-- []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong-for-level and
-- []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong.

private
  module []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
    (ok : ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
          Erased-allowed s ×
          (erased-matches-for-J m ≢ none × T 𝟘ᵐ-allowed ⊎
           (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
           Trivial ⊎
           Equality-reflection))
    (ok₂ : Π-allowed 𝟘 q₂)
    (ok₃ : Π-allowed 𝟘 q₃)
    (ok₄ : Π-allowed 𝟘 q₄)
    (ok₅ : Π-allowed 𝟘 q₅)
    where

    opaque

      Erased-ok : Erased-allowed s
      Erased-ok = case ok of λ where
        (inj₁ (ok , _)) → []-cong→Erased ok
        (inj₂ (ok , _)) → ok

    OK : Set a
    OK =
      ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
      Equality-reflection ⊎
      (∃ λ sem → erased-matches-for-J m PE.≡ not-none sem) ×
        T 𝟘ᵐ-allowed ⊎
      (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
      Trivial

    opaque

      ok′ : OK
      ok′ = case ok of λ where
        (inj₁ ok) →
          inj₁ ok
        (inj₂ (_ , inj₂ (inj₂ (inj₂ ok)))) →
          inj₂ (inj₁ ok)
        (inj₂ (_ , inj₂ (inj₂ (inj₁ trivial)))) →
          inj₂ (inj₂ (inj₂ (inj₂ trivial)))
        (inj₂ (_ , inj₂ (inj₁ ok))) →
          inj₂ (inj₂ (inj₂ (inj₁ ok)))
        (inj₂ (_ , inj₁ (≢none , ok))) →
          inj₂ $ inj₂ $ inj₁ $
          case PE.singleton $ erased-matches-for-J m of λ where
            (not-none _ , ≡not-none) → (_ , ≡not-none) , ok
            (none       , ≡none)     → ⊥-elim $ ≢none ≡none

    []-cong′ :
      OK → Term n′ → Term n′ → Term n′ → Term n′ → Term n′ → Term n′
    []-cong′ (inj₁ _)        = []-cong s
    []-cong′ (inj₂ (inj₁ _)) = λ _ _ _ _ _ → rfl
    []-cong′ (inj₂ (inj₂ _)) = []-cong-J s

    opaque

      ▸[]-cong′ :
        ∀ ok →
        γ₁ ▸[ 𝟘ᵐ? ] l →
        γ₂ ▸[ 𝟘ᵐ? ] A →
        γ₃ ▸[ 𝟘ᵐ? ] t →
        γ₄ ▸[ 𝟘ᵐ? ] u →
        γ₅ ▸[ 𝟘ᵐ? ] v →
        𝟘ᶜ ▸[ m ] []-cong′ ok l A t u v
      ▸[]-cong′ (inj₁ (_ , ok)) ▸l ▸A ▸t ▸u ▸v =
        []-congₘ ▸l ▸A ▸t ▸u ▸v ok
      ▸[]-cong′ (inj₂ (inj₁ ok)) _ _ _ _ _ =
        rflₘ
      ▸[]-cong′
        (inj₂ (inj₂ (inj₁ ((_ , ≡not-none) , ok)))) ▸l ▸A ▸t ▸u ▸v =
        ▸[]-cong-J {ok = ok} ≡not-none (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸l)
          (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u)
          (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
      ▸[]-cong′
        (inj₂ (inj₂ (inj₂ (inj₁ (_ , PE.refl))))) ▸l ▸A ▸t ▸u ▸v =
        ▸[]-cong-J-𝟘ᵐ (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸l) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A)
          (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
      ▸[]-cong′ (inj₂ (inj₂ (inj₂ (inj₂ trivial)))) =
        ▸[]-cong-J-trivial trivial

    opaque

      ⊢[]-cong′ :
        let open Erased s in
        ∀ ok →
        Γ ⊢ l ∷Level →
        Γ ⊢ v ∷ Id A t u →
        Γ ⊢ []-cong′ ok l A t u v ∷ Id (Erased l A) [ t ] ([ u ])
      ⊢[]-cong′ (inj₁ (ok , _))  = []-congⱼ′ ok
      ⊢[]-cong′ (inj₂ (inj₂ _))  = []-cong-Jⱼ Erased-ok
      ⊢[]-cong′ (inj₂ (inj₁ ok)) =
        []-cong-with-equality-reflection ok Erased-ok

    opaque

      ⊢[]-cong′-3-2-1-0 :
        let open Erased s in
        Γ ⊢ l ∷Level →
        Γ »∙ U l »∙ var x0 »∙ var x1 »∙ Id (var x2) (var x1) (var x0) ⊢
          []-cong′ ok′ (wk[ 4 ]′ l) (var x3) (var x2) (var x1)
            (var x0) ∷
          Id (Erased (wk[ 4 ]′ l) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong′-3-2-1-0 ⊢l =
        let ⊢Id = ⊢Id-2-1-0′ ⊢l in
        ⊢[]-cong′ ok′ (W.wkLevel (W.ʷ⊇-drop (∙ ⊢Id)) ⊢l) (var₀ ⊢Id)

    opaque

      ⊢[]-cong′-4-3-2-1-0 :
        let open Erased s in
        Level-allowed →
        ⊢ Γ →
        Γ »∙ Level »∙ U (var x0) »∙ var x0 »∙ var x1 »∙
          Id (var x2) (var x1) (var x0) ⊢
          []-cong′ ok′ (var x4) (var x3) (var x2) (var x1) (var x0) ∷
          Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong′-4-3-2-1-0 Level-ok ⊢Γ =
        ⊢[]-cong′-3-2-1-0 (term-⊢∷ (var₀ (Levelⱼ′ Level-ok ⊢Γ)))

    opaque

      []-cong′-[] :
        ∀ ok →
        []-cong′ ok l A t u v [ σ ] PE.≡
        []-cong′ ok (l [ σ ]) (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
      []-cong′-[] (inj₁ _)         = PE.refl
      []-cong′-[] (inj₂ (inj₁ ok)) = PE.refl
      []-cong′-[] (inj₂ (inj₂ _))  = []-cong-J-[]

    opaque

      []-cong′-β-⇒* :
        let open Erased s in
        ∀ ok →
        Γ ⊢ l ∷Level →
        Γ ⊢ t ∷ A →
        Γ ⊢ []-cong′ ok l A t t rfl ⇒* rfl ∷
          Id (Erased l A) [ t ] ([ t ])
      []-cong′-β-⇒* (inj₁ (ok , _)) ⊢l ⊢t =
        redMany ([]-cong-β ⊢l (refl ⊢t) ok)
      []-cong′-β-⇒* (inj₂ (inj₂ _)) ⊢l ⊢t =
        redMany ([]-cong-J-β-⇒ Erased-ok ⊢l ⊢t)
      []-cong′-β-⇒* (inj₂ (inj₁ ok)) ⊢l ⊢t =
        id ([]-cong-with-equality-reflection ok Erased-ok ⊢l (rflⱼ ⊢t))

    []-cong₁ : Term n → Term n
    []-cong₁ l =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong′ ok′ (wk[ 4 ]′ l) (var x3) (var x2) (var x1) (var x0)

    opaque

      ▸[]-cong₁ : γ ▸[ 𝟘ᵐ? ] l → 𝟘ᶜ ▸[ m ] []-cong₁ l
      ▸[]-cong₁ ▸l =
        lamₘ $ lamₘ $ lamₘ $ lamₘ $
        sub (▸[]-cong′ ok′ (wkUsage _ ▸l) var var var var) $ begin
          𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩

          𝟘ᶜ                                                  ∎
        where
        open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    opaque

      ⊢[]-cong₁ :
        let open Erased s in
        Γ ⊢ l ∷Level →
        Γ ⊢ []-cong₁ l ∷
        Π 𝟘 , q₂ ▷ U l ▹
        Π 𝟘 , q₃ ▷ var x0 ▹
        Π 𝟘 , q₄ ▷ var (x0 +1) ▹
        Π 𝟘 , q₅ ▷ Id (var ((x0 +1) +1)) (var (x0 +1)) (var x0) ▹
        Id (Erased (wk[ 4 ]′ l) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong₁ ⊢l =
        lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $ lamⱼ′ ok₅ $
        ⊢[]-cong′-3-2-1-0 ⊢l

    []-cong₂ : Term n
    []-cong₂ = lam 𝟘 ([]-cong₁ (var x0))

    opaque

      ▸[]-cong₂ : 𝟘ᶜ ▸[ m ] []-cong₂ {n = n}
      ▸[]-cong₂ =
        lamₘ $ sub (▸[]-cong₁ var) $ begin
          𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩

          𝟘ᶜ              ∎
        where
        open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    opaque

      ⊢[]-cong₂ :
        let open Erased s in
        Level-allowed →
        Π-allowed 𝟘 q₁ →
        ⊢ Γ →
        Γ ⊢ []-cong₂ ∷
        Π 𝟘 , q₁ ▷ Level ▹
        Π 𝟘 , q₂ ▷ U (var x0) ▹
        Π 𝟘 , q₃ ▷ var x0 ▹
        Π 𝟘 , q₄ ▷ var (x0 +1) ▹
        Π 𝟘 , q₅ ▷ Id (var ((x0 +1) +1)) (var (x0 +1)) (var x0) ▹
        Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong₂ Level-ok ok₁ ⊢Γ =
        lamⱼ′ ok₁ (⊢[]-cong₁ (term-⊢∷ (var₀ (Levelⱼ′ Level-ok ⊢Γ))))

opaque

  -- []-cong is supported for the strength s, the mode m, the variable
  -- context Γ, and the (in a certain sense well-formed) level l, for
  -- certain grades that satisfy certain assumptions, if
  --
  -- * []-cong is allowed for s, or
  -- * Erased is allowed for s and
  --   * erased matches are available for J and 𝟘ᵐ is allowed, or
  --   * m is 𝟘ᵐ, or
  --   * the modality is trivial, or
  --   * equality reflection is allowed.

  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong-for-level :
    {Γ : Con Term n} →
    ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
    Erased-allowed s ×
    (erased-matches-for-J m ≢ none × T 𝟘ᵐ-allowed ⊎
     (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
     Trivial ⊎
     Equality-reflection) →
    ε » Γ ⊢ l ∷Level →
    γ ▸[ 𝟘ᵐ? ] l →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Has-computing-[]-cong-for-level s m Γ l 𝟘 q₁ 𝟘 q₂ 𝟘 q₃ q₄
  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong-for-level
    {l} ok ⊢l ▸l ok₁ ok₂ ok₃ ok₄ =
      ([]-cong₁ l , ▸[]-cong₁ ▸l , ⊢[]-cong₁ ⊢l)
    , λ _ _ _ A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) in
        wk ρ ([]-cong₁ l) ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl      ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _)
                                                                           (PE.trans (PE.sym $ Erased.wk-Id-Erased-[]-[] _) $
                                                                            PE.cong₃ Id
                                                                              (PE.cong (flip (Erased.Erased _) _) $
                                                                               PE.trans (subst-wk (wk[ 4 ]′ l)) $
                                                                               PE.trans (subst-wk l) $
                                                                               PE.sym (wk≡subst _ _))
                                                                              PE.refl PE.refl) $
                                                                         β-red-⇒₄′ ok₁ ok₂ ok₃ ok₄
                                                                           (W.wkTerm (W.liftnʷ Δ⊇Γ (∙ ⊢Id-2-1-0′ (WD.defn-wkLevel ⊇ε ⊢l))) $
                                                                            WD.defn-wkTerm ⊇ε (⊢[]-cong′-3-2-1-0 ⊢l))
                                                                           ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        wk (liftn ρ 4)
          ([]-cong′ ok′ (wk[ 4 ]′ l) (var x3) (var x2) (var x1)
             (var x0))
          [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ]  ≡⟨ PE.trans (subst-wk ([]-cong′ ok′ _ _ _ _ _)) $
                                                                        PE.trans ([]-cong′-[] ok′) $
                                                                        PE.cong (λ l → []-cong′ ok′ l _ _ _ _) $
                                                                        PE.trans (subst-wk l) $
                                                                        PE.sym (wk≡subst _ _) ⟩⊢≡

        []-cong′ ok′ (wk ρ l) A t t rfl                              ⇒*⟨ []-cong′-β-⇒* ok′ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢t ⟩⊢∎

        rfl                                                          ∎
    where
    open []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
           ok ok₁ ok₂ ok₃ ok₄

opaque

  -- []-cong is supported for the strength s, the mode m, and a
  -- well-formed variable context, for certain grades that satisfy
  -- certain assumptions, if Level is allowed and
  --
  -- * []-cong is allowed for s, or
  -- * Erased is allowed for s and
  --   * erased matches are available for J and 𝟘ᵐ is allowed, or
  --   * m is 𝟘ᵐ, or
  --   * the modality is trivial, or
  --   * equality reflection is allowed.

  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong :
    {Γ : Con Term n} →
    Level-allowed →
    ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
    Erased-allowed s ×
    (erased-matches-for-J m ≢ none × T 𝟘ᵐ-allowed ⊎
     (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
     Trivial ⊎
     Equality-reflection) →
    ε »⊢ Γ →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Π-allowed 𝟘 q₅ →
    Has-computing-[]-cong s m Γ 𝟘 q₁ 𝟘 q₂ 𝟘 q₃ 𝟘 q₄ q₅
  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
    Level-ok ok ⊢Γ ok₁ ok₂ ok₃ ok₄ ok₅ =
      ([]-cong₂ , ▸[]-cong₂ , ⊢[]-cong₂ Level-ok ok₁ ⊢Γ)
    , λ _ _ _ l A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) in
        wk ρ []-cong₂ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl   ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _)
                                                                             (PE.sym $
                                                                              PE.trans (Erased.Id-Erased-[] _) $
                                                                              PE.cong
                                                                                _[ consSubst (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                                                                                     rfl ] $
                                                                              Erased.wk-Id-Erased _) $
                                                                           β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                             (W.wkTerm (W.liftnʷ Δ⊇Γ (∙ ⊢Id-2-1-0 Level-ok (WD.defn-wk′ ⊇ε ⊢Γ))) $
                                                                              WD.defn-wkTerm ⊇ε (⊢[]-cong′-4-3-2-1-0 Level-ok ⊢Γ))
                                                                             (⊢∷Level→⊢∷Level Level-ok (inversion-U-Level (wf-⊢∷ ⊢A)))
                                                                             ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        wk (liftn ρ 5)
          ([]-cong′ ok′ (var x4) (var x3) (var x2) (var x1) (var x0))
          [ consSubst
              (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
              rfl ]                                                    ≡⟨ PE.trans (subst-wk ([]-cong′ ok′ _ _ _ _ _)) $
                                                                          []-cong′-[] ok′ ⟩⊢≡

        []-cong′ ok′ l A t t rfl                                       ⇒*⟨ []-cong′-β-⇒* ok′ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢t ⟩⊢∎

        rfl                                                            ∎
    where
    open []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
           ok ok₂ ok₃ ok₄ ok₅

------------------------------------------------------------------------
-- Sometimes []-cong cannot be defined

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ and a "consistent" well-formed type A
  -- (in an empty definition context) without η-equality that is
  -- distinct from Level, if the "p" grades are 𝟘.

  ¬-[]-cong-for-type :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    No-η-equality ε A →
    A ≢ Level →
    ε » Γ ⊢ A →
    Consistent (ε » Γ ∙ A) →
    ¬ Has-[]-cong-for-type s 𝟙ᵐ Γ l A 𝟘 q₁ 𝟘 q₂ q₃
  ¬-[]-cong-for-type
    {n} {A} {Γ} nem Unitʷ-η→ no-η A≢Level ⊢A consistent (_ , hyp) =
    let ▸[]-cong′ , ⊢[]-cong′ = lemma (lemma (lemma hyp)) in
    case red-Id ⦃ ok = included ⦄ ⊢[]-cong′ of λ where
      (_ , rflₙ , ⇒*rfl) →
        case var-only-equal-to-itself (wk-No-η-equality no-η)
               (A≢Level ∘→ wk-Level) (ne (var _ _)) $
             []-cong′⁻¹ ⦃ ok = included ⦄
               (inversion-rfl-Id ⦃ ok = included ⦄ $
                wf-⊢≡∷ (subset*Term ⇒*rfl) .proj₂ .proj₂)
        of λ ()
      (_ , ne u-ne , []-cong′⇒*u) →
        neutral-not-well-resourced nem
          (λ _ → subst-Consistent ⊢σ consistent)
          PE.refl (ne→ _ u-ne)
          (wf-⊢≡∷ (subset*Term []-cong′⇒*u) .proj₂ .proj₂)
          (usagePres*Term Unitʷ-η→ (λ ()) ▸[]-cong′ []-cong′⇒*u)
    where
    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wfTerm (hyp .proj₂)

    σ′ : Subst (1+ n) (3+ n)
    σ′ = consSubst (sgSubst (var x0)) rfl

    ⊢σ :
      ε » Γ ∙ A ⊢ˢʷ σ′ ∷
        Γ ∙ A ∙ wk1 A ∙ Id (wk[ 2 ]′ A) (var x1) (var x0)
    ⊢σ =
      let ⊢0 = PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-id _) (var₀ ⊢A) in
      →⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-idSubst (∙ ⊢A)) ⊢0)
        (rflⱼ $
         PE.subst (_⊢_∷_ _ _)
           (wk1 A [ idSubst ]       ≡⟨ subst-id _ ⟩
            wk1 A                   ≡˘⟨ wk[1+]′-[]₀≡ ⟩
            wk[ 2 ]′ A [ var x0 ]₀  ∎)
           ⊢0)
      where
      open Tools.Reasoning.PropositionalEquality

    opaque

      lemma :
        𝟘ᶜ ▸[ 𝟙ᵐ ] t × ε » Δ ⊢ t ∷ Π 𝟘 , p ▷ B ▹ C →
        let t0 = wk1 t ∘⟨ 𝟘 ⟩ var x0 in
        𝟘ᶜ ▸[ 𝟙ᵐ ] t0 × ε » Δ ∙ B ⊢ t0 ∷ C
      lemma (▸t , ⊢t) =
        let ⊢B , _ = inversion-ΠΣ (wf-⊢∷ ⊢t) in
        sub (wkUsage (step id) ▸t ∘ₘ var)
          (begin
             𝟘ᶜ                           ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
             𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ 𝟘 ⌟ ⌝)        ≈˘⟨ +ᶜ-identityˡ _ ⟩
             𝟘ᶜ +ᶜ 𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ 𝟘 ⌟ ⌝)  ∎) ,
        PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _)
          (W.wkTerm₁ ⊢B ⊢t ∘ⱼ var₀ ⊢B)
        where
        open ≤ᶜ-reasoning

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ, the consistent variable context Γ, the
  -- well-resourced level l, and certain grades.

  ¬-[]-cong-for-level :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    γ ▸[ 𝟘ᵐ? ] l →
    Consistent (ε » Γ) →
    ¬ Has-[]-cong-for-level s 𝟙ᵐ Γ l p₁ q₁ 𝟘 q₂ 𝟘 q₃ q₄
  ¬-[]-cong-for-level
    {n} {l} {s} {p₁} {q₁} {q₂} {q₃} {q₄} {Γ}
    nem Unitʷ-η→ ▸l consistent has-[]-cong =
                                                       $⟨ has-[]-cong ⟩
    Has-[]-cong-for-level s 𝟙ᵐ Γ l p₁ q₁ 𝟘 q₂ 𝟘 q₃ q₄  →⟨ Has-[]-cong-for-level→Has-[]-cong-for-type ⊢A ▸A ⟩
    Has-[]-cong-for-type s 𝟙ᵐ Γ l A′ 𝟘 q₂ 𝟘 q₃ q₄      →⟨ ¬-[]-cong-for-type nem Unitʷ-η→ No-η-equality-A A≢Level (univ ⊢A)
                                                            (subst-Consistent (⊢ˢʷ∷-sgSubst ⊢t) consistent) ⟩
    ⊥                                                  □
    where
    ⊢l : ε » Γ ⊢ l ∷Level
    ⊢l = Has-[]-cong-for-level→⊢∷L has-[]-cong

    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wfLevel ⊢l

    u′ : Term n
    u′ = lift zero

    A′ : Term n
    A′ = Id (Lift l ℕ) u′ u′

    t″ : Term n
    t″ = rfl

    ⊢u : ε » Γ ⊢ u′ ∷ Lift l ℕ
    ⊢u = liftⱼ′ ⊢l (zeroⱼ ⊢Γ)

    ⊢A : ε » Γ ⊢ A′ ∷ U l
    ⊢A =
      Idⱼ (conv (Liftⱼ′ ⊢l (ℕⱼ ⊢Γ)) (U-cong-⊢≡ (supᵘₗ-zeroˡ ⊢l))) ⊢u ⊢u

    ⊢t : ε » Γ ⊢ t″ ∷ A′
    ⊢t = rflⱼ ⊢u

    ▸u : 𝟘ᶜ ▸[ m ] u′
    ▸u = liftₘ zeroₘ

    ▸A : 𝟘ᶜ ▸[ m ] A′
    ▸A =
      Idₘ-generalised (Liftₘ ▸l ℕₘ) ▸u ▸u (λ _ → ≤ᶜ-refl)
        (λ _ → begin
           𝟘ᶜ              ≈˘⟨ ≈ᶜ-trans (+ᶜ-congˡ (+ᶜ-identityˡ _)) $
                               +ᶜ-identityˡ _ ⟩
           𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
      where
      open ≤ᶜ-reasoning

    No-η-equality-A : No-η-equality ε A′
    No-η-equality-A = Idₙ

    A≢Level : A′ ≢ Level
    A≢Level ()

opaque

  -- A variant of ¬-[]-cong-for-level.
  --
  -- Note that, if all Π-types are allowed and l is a level literal,
  -- then the seven assumptions after No-erased-matches TR UR and
  -- before Consistent (ε » Δ) are satisfied for the erasure modality
  -- with 𝟘ᵐ (along with 𝟘-well-behaved). If Δ is empty then
  -- Consistent (ε » Δ) also holds.

  ¬-[]-cong-for-level′ :
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₂ q₂ → Π-allowed 𝟘 q₂′) →
    (Π-allowed p₃ q₃ → Π-allowed 𝟘 q₃′) →
    p₁ ≤ 𝟘 →
    γ ▸[ 𝟘ᵐ? ] l →
    Consistent (ε » Δ) →
    ¬ Has-[]-cong-for-level s 𝟙ᵐ Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄
  ¬-[]-cong-for-level′
    {s} {p₂} {q₂} {q₂′} {p₃} {q₃} {q₃′} {p₁} {l} {Δ} {q₁} {q₄}
    nem Unitʷ-η→ trivial 𝟘≤𝟙 hyp₂ hyp₃ hyp₁ ▸l consistent =
    Has-[]-cong-for-level s 𝟙ᵐ Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄  →⟨ Has-[]-cong-for-level-stronger trivial 𝟘≤𝟙 idᶠ hyp₂ hyp₃ idᶠ
                                                              (≤-trans (≤-reflexive (·-identityˡ _)) hyp₁) (≤-reflexive (·-identityˡ _))
                                                              (≤-reflexive (·-identityˡ _)) ▸l ⟩
    Has-[]-cong-for-level s 𝟙ᵐ Δ l p₁ q₁ 𝟘 q₂′ 𝟘 q₃′ q₄  →⟨ ¬-[]-cong-for-level nem Unitʷ-η→ ▸l consistent ⟩
    ⊥                                                    □

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ, a consistent variable context Γ, and
  -- certain grades.

  ¬-[]-cong :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    Consistent (ε » Γ) →
    ¬ Has-[]-cong s 𝟙ᵐ Γ p₁ q₁ p₂ q₂ 𝟘 q₃ 𝟘 q₄ q₅
  ¬-[]-cong
    {n} {s} {p₁} {q₁} {p₂} {q₂} {q₃} {q₄} {q₅} {Γ}
    nem Unitʷ-η→ consistent has-[]-cong@(_ , hyp) =
                                                        $⟨ has-[]-cong ⟩
    Has-[]-cong s 𝟙ᵐ Γ p₁ q₁ p₂ q₂ 𝟘 q₃ 𝟘 q₄ q₅         →⟨ Has-[]-cong→Has-[]-cong-for-level ⊢l ▸l ⟩
    Has-[]-cong-for-level s 𝟙ᵐ Γ l′ p₂ q₂ 𝟘 q₃ 𝟘 q₄ q₅  →⟨ ¬-[]-cong-for-level nem Unitʷ-η→ ▸l consistent ⟩
    ⊥                                                   □
    where
    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wfTerm (hyp .proj₂)

    l′ : Term n
    l′ = zeroᵘ

    ⊢l : ε » Γ ⊢ l′ ∷Level
    ⊢l = ⊢zeroᵘ ⊢Γ

    ▸l : 𝟘ᶜ ▸[ m ] l′
    ▸l = zeroᵘₘ

opaque

  -- A variant of ¬-[]-cong.
  --
  -- Note that, if all Π-types are allowed, then the seven assumptions
  -- after No-erased-matches TR UR and before Consistent (ε » Δ) are
  -- satisfied for the erasure modality with 𝟘ᵐ (along with
  -- 𝟘-well-behaved). If Δ is empty then Consistent (ε » Δ) also
  -- holds.

  ¬-[]-cong′ :
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed p₃ q₃ → Π-allowed 𝟘 q₃′) →
    (Π-allowed p₄ q₄ → Π-allowed 𝟘 q₄′) →
    p₁ ≤ ω · p₁ →
    p₂ ≤ 𝟘 →
    Consistent (ε » Δ) →
    ¬ Has-[]-cong s 𝟙ᵐ Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅
  ¬-[]-cong′
    {s} {p₃} {q₃} {q₃′} {p₄} {q₄} {q₄′} {p₁} {p₂} {Δ} {q₁} {q₂} {q₅}
    nem Unitʷ-η→ trivial 𝟘≤𝟙 hyp₃ hyp₄ hyp₁ hyp₂ consistent =
    Has-[]-cong s 𝟙ᵐ Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅  →⟨ Has-[]-cong-stronger trivial 𝟘≤𝟙 idᶠ idᶠ hyp₃ hyp₄ idᶠ (·-monotoneʳ hyp₁)
                                                        (≤-trans (≤-reflexive (·-identityˡ _)) hyp₂) (≤-reflexive (·-identityˡ _))
                                                        (≤-reflexive (·-identityˡ _)) ⟩
    Has-[]-cong s 𝟙ᵐ Δ p₁ q₁ p₂ q₂ 𝟘 q₃′ 𝟘 q₄′ q₅  →⟨ ¬-[]-cong nem Unitʷ-η→ consistent ⟩
    ⊥                                              □
