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
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

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

open import Tools.Bool using (Bool; T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; 3+; 5+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  b                                                : Bool
  n n′                                             : Nat
  Δ                                                : Con Term _
  Γ                                                : Cons _ _
  A A₁ A₂ B C l l₁ l₂ t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ w : Term _
  σ                                                : Subst _ _
  p q q₁ q₁′ q₂ q₂′ q₃ q₃′ q₄ q₄′ q₅               : M
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

  ⊢Id-2-1-0 :
    Level-allowed →
    ⊢ Γ →
    Γ »∙ Level »∙ U (var x0) »∙ var x0 »∙ var x1 ⊢
      Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0 {Γ} ok ⊢Γ = Idⱼ′ (var₁ ⊢1) (var₀ ⊢1)
    where
    ⊢1 : Γ »∙ Level »∙ U (var x0) »∙ var x0 ⊢ var x1
    ⊢1 = univ (var₁ (univ (var₀ (⊢U′ (var₀ (Levelⱼ′ ok ⊢Γ))))))

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

Has-[]-cong-for :
  Strength → Mode → Con Term n → Term n → Term n → M → M → M → Set a
Has-[]-cong-for {n} s m Γ l A q₁ q₂ q₃ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ A ▹
    Π 𝟘 , q₂ ▷ wk1 A ▹
    Π 𝟘 , q₃ ▷ Id (wk[ 2 ]′ A) (var x1) (var x0) ▹
    Id (Erased (wk[ 3 ]′ l) (wk[ 3 ]′ A)) [ var x2 ] ([ var x1 ])

-- The property of supporting a []-cong combinator (with certain
-- grades) for a certain mode and a certain erased variable context.
--
-- Note that, unlike the []-cong primitive, the type argument must be
-- a type in U l for some l.

Has-[]-cong : Strength → Mode → Con Term n → M → M → M → M → M → Set a
Has-[]-cong {n} s m Γ q₁ q₂ q₃ q₄ q₅ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ Level ▹
    Π 𝟘 , q₂ ▷ U (var x0) ▹
    Π 𝟘 , q₃ ▷ var x0 ▹
    Π 𝟘 , q₄ ▷ var x1 ▹
    Π 𝟘 , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x4) (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong :
  Strength → Mode → Con Term n → M → M → M → M → M → Set a
Has-computing-[]-cong {n} s m Γ q₁ q₂ q₃ q₄ q₅ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s m Γ q₁ q₂ q₃ q₄ q₅) →
  ∀ m n′ (Δ : Cons m n′) (l A t : Term n′) (ρ : Wk n′ n) →
  Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
  Δ ⊢ A ∷ U l →
  Δ ⊢ t ∷ A →
  Δ ⊢ wk ρ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
    rfl ∷ Id (Erased l A) [ t ] ([ t ])

opaque

  -- If Has-[]-cong holds, then Level is allowed.

  Has-[]-cong→Level-allowed :
    Has-[]-cong s m Δ q₁ q₂ q₃ q₄ q₅ → Level-allowed
  Has-[]-cong→Level-allowed (_ , _ , ⊢[]-cong) =
    let ⊢Level , _ = inversion-ΠΣ (wf-⊢∷ ⊢[]-cong) in
    inversion-Level-⊢ ⊢Level

opaque

  -- []-cong is supported for the strength s, the mode m, and a
  -- well-formed variable context, for grades for which "Π 𝟘" are
  -- allowed, if Level is allowed and
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
    Has-computing-[]-cong s m Γ q₁ q₂ q₃ q₄ q₅
  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
    {n} {s} {m} Level-ok ok ⊢Γ ok₁ ok₂ ok₃ ok₄ ok₅ =
    let ⊢Id       = ⊢Id-2-1-0 Level-ok ⊢Γ
        ⊢[]-cong″ = ⊢[]-cong″ ok′ (term Level-ok (var₄ ⊢Id)) (var₀ ⊢Id)
    in
      ( []-cong′
      , (lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub (▸[]-cong″ ok′ var var var var var) $ begin
           𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙
             ⌜ m ⌝ · 𝟘                                           ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩

           𝟘ᶜ                                                    ∎)
      , (lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
         lamⱼ′ ok₅ ⊢[]-cong″)
      )
    , λ _ _ _ l A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) in
        wk ρ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl   ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _)
                                                                             (PE.sym $
                                                                              PE.trans (Erased.Id-Erased-[] _) $
                                                                              PE.cong
                                                                                _[ consSubst (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                                                                                     rfl ] $
                                                                              Erased.wk-Id-Erased _) $
                                                                           β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                             (W.wkTerm (W.liftnʷ Δ⊇Γ (∙ ⊢Id-2-1-0 Level-ok (WD.defn-wk′ ⊇ε ⊢Γ))) $
                                                                              WD.defn-wkTerm ⊇ε ⊢[]-cong″)
                                                                             (⊢∷Level→⊢∷Level Level-ok (inversion-U-Level (wf-⊢∷ ⊢A)))
                                                                             ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        wk (liftn ρ 5)
          ([]-cong″ ok′ (var x4) (var x3) (var x2) (var x1) (var x0))
          [ consSubst
              (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
              rfl ]                                                    ≡⟨ PE.trans (subst-wk ([]-cong″ ok′ _ _ _ _ _)) $
                                                                          []-cong″-[] ok′ ⟩⊢≡

        []-cong″ ok′ l A t t rfl                                       ⇒*⟨ []-cong″-β-⇒* ok′ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢t ⟩⊢∎

        rfl                                                            ∎
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

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

    []-cong″ :
      OK → Term n′ → Term n′ → Term n′ → Term n′ → Term n′ → Term n′
    []-cong″ (inj₁ _)        = []-cong s
    []-cong″ (inj₂ (inj₁ _)) = λ _ _ _ _ _ → rfl
    []-cong″ (inj₂ (inj₂ _)) = []-cong-J s

    ▸[]-cong″ :
      ∀ ok →
      γ₁ ▸[ 𝟘ᵐ? ] l →
      γ₂ ▸[ 𝟘ᵐ? ] A →
      γ₃ ▸[ 𝟘ᵐ? ] t →
      γ₄ ▸[ 𝟘ᵐ? ] u →
      γ₅ ▸[ 𝟘ᵐ? ] v →
      𝟘ᶜ ▸[ m ] []-cong″ ok l A t u v
    ▸[]-cong″ (inj₁ (_ , ok)) ▸l ▸A ▸t ▸u ▸v =
      []-congₘ ▸l ▸A ▸t ▸u ▸v ok
    ▸[]-cong″ (inj₂ (inj₁ ok)) _ _ _ _ _ =
      rflₘ
    ▸[]-cong″
      (inj₂ (inj₂ (inj₁ ((_ , ≡not-none) , ok)))) ▸l ▸A ▸t ▸u ▸v =
      ▸[]-cong-J {ok = ok} ≡not-none (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸l)
        (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u)
        (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸[]-cong″ (inj₂ (inj₂ (inj₂ (inj₁ (_ , PE.refl))))) ▸l ▸A ▸t ▸u ▸v =
      ▸[]-cong-J-𝟘ᵐ (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸l) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A)
        (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸[]-cong″ (inj₂ (inj₂ (inj₂ (inj₂ trivial)))) =
      ▸[]-cong-J-trivial trivial

    ⊢[]-cong″ :
      let open Erased s in
      ∀ ok →
      Γ ⊢ l ∷Level →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ []-cong″ ok l A t u v ∷ Id (Erased l A) [ t ] ([ u ])
    ⊢[]-cong″ (inj₁ (ok , _))  = []-congⱼ′ ok
    ⊢[]-cong″ (inj₂ (inj₂ _))  = []-cong-Jⱼ Erased-ok
    ⊢[]-cong″ (inj₂ (inj₁ ok)) = λ ⊢v →
      []-cong-with-equality-reflection ok Erased-ok ⊢v

    []-cong″-[] :
      ∀ ok →
      []-cong″ ok l A t u v [ σ ] PE.≡
      []-cong″ ok (l [ σ ]) (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
    []-cong″-[] (inj₁ _)         = PE.refl
    []-cong″-[] (inj₂ (inj₁ ok)) = PE.refl
    []-cong″-[] (inj₂ (inj₂ _))  = []-cong-J-[]

    []-cong″-β-⇒* :
      let open Erased s in
      ∀ ok →
      Γ ⊢ l ∷Level →
      Γ ⊢ t ∷ A →
      Γ ⊢ []-cong″ ok l A t t rfl ⇒* rfl ∷ Id (Erased l A) [ t ] ([ t ])
    []-cong″-β-⇒* (inj₁ (ok , _)) ⊢l ⊢t =
      redMany ([]-cong-β ⊢l (refl ⊢t) ok)
    []-cong″-β-⇒* (inj₂ (inj₂ _)) ⊢l ⊢t =
      redMany ([]-cong-J-β-⇒ Erased-ok ⊢l ⊢t)
    []-cong″-β-⇒* (inj₂ (inj₁ ok)) ⊢l ⊢t =
      id ([]-cong-with-equality-reflection ok Erased-ok ⊢l (rflⱼ ⊢t))

    []-cong′ : Term n
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong″ ok′ (var x4) (var x3) (var x2) (var x1) (var x0)

opaque

  -- Has-[]-cong implies Has-[]-cong-for, given certain assumptions.

  Has-[]-cong→Has-[]-cong-for :
    γ₁ ▸[ 𝟘ᵐ? ] l →
    γ₂ ▸[ 𝟘ᵐ? ] A →
    ε » Δ ⊢ A ∷ U l →
    Has-[]-cong s m Δ q₁ q₂ q₃ q₄ q₅ →
    Has-[]-cong-for s m Δ l A q₃ q₄ q₅
  Has-[]-cong→Has-[]-cong-for
    {γ₁} {l} {γ₂} {A} {s} {m} {q₃} {q₄} {q₅}
    ▸l ▸A ⊢A has-[]-cong@([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    let ok = Has-[]-cong→Level-allowed has-[]-cong
        ⊢l = ⊢∷Level→⊢∷Level ok (inversion-U-Level (wf-⊢∷ ⊢A))
    in
    []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ,
    (sub
       ((▸[]-cong′ ∘ₘ ▸-cong (PE.sym $ ᵐ·-zeroʳ m) ▸l) ∘ₘ
        ▸-cong (PE.sym $ ᵐ·-zeroʳ m) ▸A) $ begin
       𝟘ᶜ                          ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityʳ _) (+ᶜ-identityʳ _) ⟩
       (𝟘ᶜ +ᶜ 𝟘ᶜ) +ᶜ 𝟘ᶜ            ≈˘⟨ +ᶜ-cong (+ᶜ-congˡ (·ᶜ-zeroˡ _)) (·ᶜ-zeroˡ _) ⟩
       (𝟘ᶜ +ᶜ 𝟘 ·ᶜ γ₁) +ᶜ 𝟘 ·ᶜ γ₂  ∎) ,
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₂ (Π 𝟘 , q₃ ▷_▹_) PE.refl $
       PE.cong₂ (Π 𝟘 , q₄ ▷_▹_) PE.refl $
       PE.cong₂ (Π 𝟘 , q₅ ▷_▹_)
         (PE.cong₃ Id wk[]≡wk[]′ PE.refl PE.refl)
         (PE.cong₃ Id
            (PE.cong₂ Erased wk[]≡wk[]′ wk[]≡wk[]′) PE.refl PE.refl))
      (PE.subst (_⊢_∷_ _ _)
         (PE.cong (Π 𝟘 , q₃ ▷_▹_ _) $
          PE.cong (Π 𝟘 , q₄ ▷_▹_ _) $
          PE.cong (Π 𝟘 , q₅ ▷_▹_ _) $
          PE.trans (substCompEq (Id (Erased _ _) [ _ ] ([ _ ]))) $
          PE.trans (PE.sym Id-Erased-[]) $
          PE.cong₃ Id
            (PE.cong (flip Erased _) $
             PE.trans (PE.cong _[ _ ] $ wk[]≡wk[]′ {t = l}) $
             PE.trans wk[+1]′-[₀⇑]≡ $
             PE.sym $ wk[]≡wk[]′ {t = l})
            PE.refl PE.refl) $
       (⊢[]-cong′ ∘ⱼ ⊢l) ∘ⱼ ⊢A)
    where
    open ≤ᶜ-reasoning
    open Erased s

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ and a "consistent" well-formed type A
  -- (in an empty definition context) without η-equality that is
  -- distinct from Level.

  ¬-[]-cong-for :
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
    ¬ Has-[]-cong-for s 𝟙ᵐ Γ l A q₁ q₂ q₃
  ¬-[]-cong-for
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
  -- supported for the mode 𝟙ᵐ and a consistent variable context Γ.

  ¬-[]-cong :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    Consistent (ε » Γ) →
    ¬ Has-[]-cong s 𝟙ᵐ Γ q₁ q₂ q₃ q₄ q₅
  ¬-[]-cong
    {n} {s} {q₁} {q₂} {q₃} {q₄} {q₅} {Γ}
    nem Unitʷ-η→ consistent has-[]-cong@(_ , hyp) =
                                           $⟨ has-[]-cong ⟩
    Has-[]-cong s 𝟙ᵐ Γ q₁ q₂ q₃ q₄ q₅      →⟨ Has-[]-cong→Has-[]-cong-for ▸l ▸A ⊢A ⟩
    Has-[]-cong-for s 𝟙ᵐ Γ l′ A′ q₃ q₄ q₅  →⟨ ¬-[]-cong-for nem Unitʷ-η→ No-η-equality-A A≢Level (univ ⊢A)
                                                (subst-Consistent (⊢ˢʷ∷-sgSubst ⊢t) consistent) ⟩
    ⊥                                      □
    where
    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wfTerm (hyp .proj₂)

    l′ : Term n
    l′ = zeroᵘ

    A′ : Term n
    A′ = ℕ

    t″ : Term n
    t″ = zero

    ⊢l : ε » Γ ⊢ l′ ∷ Level
    ⊢l = zeroᵘⱼ (Has-[]-cong→Level-allowed has-[]-cong) ⊢Γ

    ⊢A : ε » Γ ⊢ A′ ∷ U l′
    ⊢A = ℕⱼ ⊢Γ

    ⊢t : ε » Γ ⊢ t″ ∷ A′
    ⊢t = zeroⱼ ⊢Γ

    ▸l : 𝟘ᶜ ▸[ 𝟘ᵐ? ] l′
    ▸l = ▸-cong (ᵐ·-zeroʳ 𝟙ᵐ) zeroᵘₘ

    ▸A : 𝟘ᶜ ▸[ 𝟘ᵐ? ] A′
    ▸A = ▸-cong (ᵐ·-zeroʳ 𝟙ᵐ) ℕₘ

    No-η-equality-A : No-η-equality ε A′
    No-η-equality-A = ℕₙ

    A≢Level : A′ ≢ Level
    A≢Level ()

------------------------------------------------------------------------
-- Has-weaker-[]-cong

-- A "weaker" variant of Has-[]-cong.

Has-weaker-[]-cong :
  Strength → Mode → Con Term n → M → M → M → M → M → Set a
Has-weaker-[]-cong {n} s m Γ q₁ q₂ q₃ q₄ q₅ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ Level ▹
    Π ω , q₂ ▷ U (var x0) ▹
    Π ω , q₃ ▷ var x0 ▹
    Π ω , q₄ ▷ var x1 ▹
    Π 𝟘 , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])

-- A "weaker" variant of Has-computing-[]-cong.

Has-weaker-computing-[]-cong :
  Strength → Mode → Con Term n → M → M → M → M → M → Set a
Has-weaker-computing-[]-cong {n} s m Γ q₁ q₂ q₃ q₄ q₅ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-weaker-[]-cong s m Γ q₁ q₂ q₃ q₄ q₅) →
  ∀ m n′ (Δ : Cons m n′) (l A t : Term n′) (ρ : Wk n′ n) →
  Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
  Δ ⊢ A ∷ U l →
  Δ ⊢ t ∷ A →
  Δ ⊢ wk ρ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∘⟨ ω ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
    rfl ∷ Id (Erased l A) [ t ] ([ t ])

opaque

  -- If Has-weaker-[]-cong holds, then Level is allowed.

  Has-weaker-[]-cong→Level-allowed :
    Has-weaker-[]-cong s m Δ q₁ q₂ q₃ q₄ q₅ → Level-allowed
  Has-weaker-[]-cong→Level-allowed (_ , _ , ⊢[]-cong) =
    let ⊢Level , _ = inversion-ΠΣ (wf-⊢∷ ⊢[]-cong) in
    inversion-Level-⊢ ⊢Level

-- Some definitions/lemmas used below.

private
  module Has-[]-cong→Has-weaker-[]-cong
    {Γ : Con Term n}
    (hyp₂ : Π-allowed 𝟘 q₂ → Π-allowed ω q₂′)
    (hyp₃ : Π-allowed 𝟘 q₃ → Π-allowed ω q₃′)
    (hyp₄ : Π-allowed 𝟘 q₄ → Π-allowed ω q₄′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-[]-cong s m Γ q₁ q₂ q₃ q₄ q₅)
    where

    open Erased s

    []-cong″ : Term (5+ n)
    []-cong″ =
       wk (stepn id 5) []-cong′ ∘⟨ 𝟘 ⟩ var x4 ∘⟨ 𝟘 ⟩ var x3
         ∘⟨ 𝟘 ⟩ var x2 ∘⟨ 𝟘 ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0

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
      Π-allowed 𝟘 q₁ × Π-allowed ω q₂′ × Π-allowed ω q₃′ ×
      Π-allowed ω q₄′ × Π-allowed 𝟘 q₅
    oks =
      let _ , ⊢Π , ok₁ = inversion-ΠΣ $ syntacticTerm ⊢[]-cong′
          _ , ⊢Π , ok₂ = inversion-ΠΣ ⊢Π
          _ , ⊢Π , ok₃ = inversion-ΠΣ ⊢Π
          _ , ⊢Π , ok₄ = inversion-ΠΣ ⊢Π
          _ , _  , ok₅ = inversion-ΠΣ ⊢Π
      in
      ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄ , ok₅

opaque

  -- Has-weaker-[]-cong is no stronger than Has-[]-cong (given certain
  -- assumptions).

  Has-[]-cong→Has-weaker-[]-cong :
    {Γ : Con Term n} →
    (Π-allowed 𝟘 q₂ → Π-allowed ω q₂′) →
    (Π-allowed 𝟘 q₃ → Π-allowed ω q₃′) →
    (Π-allowed 𝟘 q₄ → Π-allowed ω q₄′) →
    Has-[]-cong s m Γ q₁ q₂ q₃ q₄ q₅ →
    Has-weaker-[]-cong s m Γ q₁ q₂′ q₃′ q₄′ q₅
  Has-[]-cong→Has-weaker-[]-cong
    {n} {q₂′} {q₃′} {q₄′} {s} {m} {q₁} {q₅} {Γ}
    hyp₂ hyp₃ hyp₄ has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open Has-[]-cong→Has-weaker-[]-cong hyp₂ hyp₃ hyp₄ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ = lam 𝟘 $ lam ω $ lam ω $ lam ω $ lam 𝟘 []-cong″

    ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
    ▸[]-cong‴ =
      lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub
        (((((wkUsage (stepn id 5) ▸[]-cong′ ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ
          var) ∘ₘ
         var) $
      (begin
         𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · 𝟘  ≤⟨ ≤ᶜ-refl ∙ ≤-reflexive (·-zeroʳ _) ∙ lemma ∙ lemma ∙ lemma ∙
                                                                            ≤-reflexive (·-zeroʳ _) ⟩

         𝟘ᶜ                                                              ≈˘⟨ ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                             ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                             ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                             ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                             ≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _ ⟩
         ((((𝟘ᶜ +ᶜ 𝟘 ·ᶜ (𝟘ᶜ , x4 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
            𝟘 ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
           𝟘 ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
          𝟘 ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝)                                     ∎)
      where
      lemma : ⌜ m ⌝ · ω ≤ 𝟘
      lemma =
        case PE.singleton m of λ where
          (𝟘ᵐ , PE.refl) → begin
            𝟘 · ω  ≡⟨ ·-zeroˡ _ ⟩
            𝟘      ∎
          (𝟙ᵐ , PE.refl) → begin
            𝟙 · ω  ≡⟨ ·-identityˡ _ ⟩
            ω      ≤⟨ ω≤𝟘 ⟩
            𝟘      ∎
        where
        open Tools.Reasoning.PartialOrder ≤-poset

      open ≤ᶜ-reasoning

    ⊢[]-cong‴ :
      ε » Γ ⊢ []-cong‴ ∷
        Π 𝟘 , q₁ ▷ Level ▹
        Π ω , q₂′ ▷ U (var x0) ▹
        Π ω , q₃′ ▷ var x0 ▹
        Π ω , q₄′ ▷ var x1 ▹
        Π 𝟘 , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (var x4) (var x3)) ([ var x2 ]) ([ var x1 ])
    ⊢[]-cong‴ =
      let ok₁ , ok₂ , ok₃ , ok₄ , ok₅ = oks in
      lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
      lamⱼ′ ok₅ ⊢[]-cong″

opaque
  unfolding Has-[]-cong→Has-weaker-[]-cong Erased.Erased Erased.[_]

  -- Has-weaker-computing-[]-cong is no stronger than
  -- Has-computing-[]-cong (given certain assumptions).

  Has-computing-[]-cong→Has-weaker-computing-[]-cong :
    (Π-allowed 𝟘 q₂ → Π-allowed ω q₂′) →
    (Π-allowed 𝟘 q₃ → Π-allowed ω q₃′) →
    (Π-allowed 𝟘 q₄ → Π-allowed ω q₄′) →
    Has-computing-[]-cong s m Δ q₁ q₂ q₃ q₄ q₅ →
    Has-weaker-computing-[]-cong s m Δ q₁ q₂′ q₃′ q₄′ q₅
  Has-computing-[]-cong→Has-weaker-computing-[]-cong
    hyp₂ hyp₃ hyp₄
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    let open Has-[]-cong→Has-weaker-[]-cong hyp₂ hyp₃ hyp₄ has-[]-cong

        ok = Has-[]-cong→Level-allowed has-[]-cong

        ok₁ , ok₂ , ok₃ , ok₄ , ok₅ = oks
    in
      Has-[]-cong→Has-weaker-[]-cong hyp₂ hyp₃ hyp₄ has-[]-cong
    , λ _ _ _ l A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) in
        wk ρ
          (lam 𝟘 $ lam ω $ lam ω $ lam ω $ lam 𝟘 $
           wk (stepn id 5) []-cong′ ∘⟨ 𝟘 ⟩ var x4 ∘⟨ 𝟘 ⟩ var x3
             ∘⟨ 𝟘 ⟩ var x2 ∘⟨ 𝟘 ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0)
          ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∘⟨ ω ⟩ t ∘⟨ 𝟘 ⟩ rfl               ⇒*⟨ β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
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
          ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl               ≡⟨ PE.cong
                                                                            (λ []-cong → []-cong ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _) $
                                                                          PE.trans
                                                                            (PE.cong _[ _ ] $
                                                                             PE.trans (wk-comp _ _ []-cong′) $
                                                                             PE.cong (flip wk _) $
                                                                             PE.sym $ liftn-stepn-comp 5) $
                                                                          PE.trans (subst-wk []-cong′) $
                                                                          PE.sym $ wk≡subst _ _ ⟩⊢≡

        wk ρ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl   ≡⟨ []-cong′≡ _ _ _ _ _ _ _ Δ⊇Γ ⊢A ⊢t ⟩⊢∎

        rfl                                                            ∎

-- Some definitions/lemmas used below.

private
  module Has-weaker-[]-cong→Has-[]-cong
    {Γ : Con Term n}
    (hyp₂ : Π-allowed ω q₂ → Π-allowed 𝟘 q₂′)
    (hyp₃ : Π-allowed ω q₃ → Π-allowed 𝟘 q₃′)
    (hyp₄ : Π-allowed ω q₄ → Π-allowed 𝟘 q₄′)
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) :
     Has-weaker-[]-cong s m Γ q₁ q₂ q₃ q₄ q₅)
    where

    open Erased s

    []-cong″ : Term (5+ n)
    []-cong″ =
      cong 𝟘 (Erased (var x4) (Erased (var x4) (var x3))) [ [ var x2 ] ]
        [ [ var x1 ] ] (Erased (var x4) (var x3))
        (mapᴱ (Erased (var x5) (var x4))
           (erased (var x5) (var x0)) (var x0))
        (wk (stepn id 5) []-cong′ ∘⟨ 𝟘 ⟩ var x4
           ∘⟨ ω ⟩ Erased (var x4) (var x3) ∘⟨ ω ⟩ [ var x2 ]
           ∘⟨ ω ⟩ [ var x1 ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                    (Erased (var x4) (var x3)) [ var x0 ] (var x0))

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        Π-allowed 𝟘 q₁ × Π-allowed 𝟘 q₂′ ×
        Π-allowed 𝟘 q₃′ × Π-allowed 𝟘 q₄′ ×
        Π-allowed 𝟘 q₅ ×
        ε »
        Γ ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
          Id (var x2) (var x1) (var x0) ⊢
        []-cong″ ∷
        Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        let ok               = Has-weaker-[]-cong→Level-allowed
                                 has-[]-cong
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
        ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄ , ok₅ ,
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

  -- Has-weaker-[]-cong is at least as strong as Has-[]-cong (given
  -- certain assumptions).

  Has-weaker-[]-cong→Has-[]-cong :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂′) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃′) →
    (Π-allowed ω q₄ → Π-allowed 𝟘 q₄′) →
    Has-weaker-[]-cong s m Γ q₁ q₂ q₃ q₄ q₅ →
    Has-[]-cong s m Γ q₁ q₂′ q₃′ q₄′ q₅
  Has-weaker-[]-cong→Has-[]-cong
    {n} {s} {q₂′} {q₃′} {q₄′} {m} {q₁} {q₅} {Γ}
    trivial 𝟘≤𝟙 hyp₂ hyp₃ hyp₄ has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open ErasedU s
    open Has-weaker-[]-cong→Has-[]-cong hyp₂ hyp₃ hyp₄ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 []-cong″

    opaque

      ⊢[]-cong‴ :
        ε » Γ ⊢ []-cong‴ ∷
        Π 𝟘 , q₁ ▷ Level ▹
        Π 𝟘 , q₂′ ▷ U (var x0) ▹
        Π 𝟘 , q₃′ ▷ var x0 ▹
        Π 𝟘 , q₄′ ▷ var x1 ▹
        Π 𝟘 , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
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
           𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙
           ⌜ m ⌝ · 𝟘                                               ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩

           𝟘ᶜ                                                      ≈˘⟨ ≈ᶜ-trans
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
                                                                                                  ·ᶜ-zeroˡ _)
                                                                                                 (·ᶜ-zeroʳ _)) $
                                                                                            +ᶜ-identityʳ _)
                                                                                           (·ᶜ-zeroʳ _)) $
                                                                                      +ᶜ-identityʳ _)
                                                                                     (·ᶜ-zeroʳ _)) $
                                                                                +ᶜ-identityʳ _)
                                                                               (·ᶜ-zeroˡ _)) $
                                                                          +ᶜ-identityʳ _) $
                                                                       ·ᶜ-zeroʳ _ ⟩
           ω ·ᶜ
           (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ
            (((((𝟘ᶜ +ᶜ 𝟘 ·ᶜ (𝟘ᶜ , x4 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
                ω ·ᶜ 𝟘ᶜ) +ᶜ
               ω ·ᶜ 𝟘ᶜ) +ᶜ
              ω ·ᶜ 𝟘ᶜ) +ᶜ
             𝟘 ·ᶜ ω ·ᶜ
             ((𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
              (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ 𝟘ᶜ)) +ᶜ
            𝟘ᶜ)                                                    ∎)
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
  unfolding Has-weaker-[]-cong→Has-[]-cong

  -- Has-weaker-computing-[]-cong is at least as strong as
  -- Has-computing-[]-cong (given certain assumptions).

  Has-weaker-computing-[]-cong→Has-computing-[]-cong :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂′) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃′) →
    (Π-allowed ω q₄ → Π-allowed 𝟘 q₄′) →
    Has-weaker-computing-[]-cong s m Γ q₁ q₂ q₃ q₄ q₅ →
    Has-computing-[]-cong s m Γ q₁ q₂′ q₃′ q₄′ q₅
  Has-weaker-computing-[]-cong→Has-computing-[]-cong
    {n} {s} {q₂′} {q₃′} {q₄} {q₄′} {m} {q₁} {q₅} {Γ}
    trivial 𝟘≤𝟙 hyp₂ hyp₃ hyp₄
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    has-[]-cong′ , []-cong″-computes
    where
    open Erased s

    has-[]-cong′ : Has-[]-cong s m Γ q₁ q₂′ q₃′ q₄′ q₅
    has-[]-cong′ =
      Has-weaker-[]-cong→Has-[]-cong
        trivial 𝟘≤𝟙 hyp₂ hyp₃ hyp₄ has-[]-cong

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
          wk ρ []-cong″ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
          rfl ∷ Id (Erased l A) [ t ] ([ t ])
      []-cong″-computes _ _ Δ l A t ρ Δ⊇Γ ⊢A ⊢t =
        let open Has-weaker-[]-cong→Has-[]-cong
                   hyp₂ hyp₃ hyp₄ has-[]-cong

            ok₁ , ok₂ , ok₃ , ok₄ , ok₅ , ⊢[]-cong″ = ⊢[]-cong″

            ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A))
        in
        wk ρ
          (lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
           cong 𝟘 (Erased (var x4) (Erased (var x4) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ] (Erased (var x4) (var x3))
             (mapᴱ (Erased (var x5) (var x4)) (erased (var x5) (var x0))
                (var x0))
             (wk (stepn id 5) []-cong′ ∘⟨ 𝟘 ⟩ var x4
                ∘⟨ ω ⟩ Erased (var x4) (var x3) ∘⟨ ω ⟩ [ var x2 ]
                ∘⟨ ω ⟩ [ var x1 ]
                ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                         (Erased (var x4) (var x3)) [ var x0 ]
                         (var x0)))
          ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ∷
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
             (wk (stepn id 5) []-cong′ ∘⟨ 𝟘 ⟩ var x4
                ∘⟨ ω ⟩ Erased (var x4) (var x3) ∘⟨ ω ⟩ [ var x2 ]
                ∘⟨ ω ⟩ [ var x1 ]
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
                                                                                  (PE.cong (_∘⟨ ω ⟩ [ t ]) $
                                                                                   PE.cong (_∘⟨ ω ⟩ [ t ]) $
                                                                                   PE.cong (_∘⟨ ω ⟩ Erased l A) $
                                                                                   PE.cong (_∘⟨ _ ⟩ _) $
                                                                                   lemma _ _ _ _ _)
                                                                                  cong-[]) ⟩⊢∷≡
        cong 𝟘 (Erased l (Erased l A)) [ [ t ] ] [ [ t ] ] (Erased l A)
          (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
             (var x0))
          (wk ρ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ Erased l A ∘⟨ ω ⟩ [ t ]
             ∘⟨ ω ⟩ [ t ]
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
                                                                                  (PE.cong₂ (Π_,_▷_▹_ ω q₄) (wk1-sgSubst _ _) PE.refl) $
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
          (wk ρ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ Erased l A ∘⟨ ω ⟩ [ t ]
             ∘⟨ ω ⟩ [ t ] ∘⟨ 𝟘 ⟩ rfl)                                     ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                               (refl (univ ⊢Erased-A)) (refl ⊢mapᴱ-0) $
                                                                             []-cong′≡ _ _ _ _ _ _ _ Δ⊇Γ ⊢Erased-A∷U ⊢[t] ⟩⊢
        cong 𝟘 (Erased l (Erased l A)) [ [ t ] ] [ [ t ] ] (Erased l A)
          (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
             (var x0))
          rfl                                                             ⇒⟨ cong-⇒ ⊢[[t]] ⊢mapᴱ-0 ⟩⊢∎

        rfl                                                               ∎
        where
        Level-ok : Level-allowed
        Level-ok = Has-weaker-[]-cong→Level-allowed has-[]-cong

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

opaque

  -- A variant of ¬-[]-cong for Has-weaker-[]-cong.

  ¬-Has-weaker-[]-cong :
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂′) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃′) →
    (Π-allowed ω q₄ → Π-allowed 𝟘 q₄′) →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    Consistent (ε » Δ) →
    ¬ Has-weaker-[]-cong s 𝟙ᵐ Δ q₁ q₂ q₃ q₄ q₅
  ¬-Has-weaker-[]-cong
    {s} {q₂} {q₂′} {q₃} {q₃′} {q₄} {q₄′} {Δ} {q₁} {q₅}
    trivial 𝟘≤𝟙 hyp₂ hyp₃ hyp₄ nem Unitʷ-η→ consistent =
    Has-weaker-[]-cong s 𝟙ᵐ Δ q₁ q₂ q₃ q₄ q₅  →⟨ Has-weaker-[]-cong→Has-[]-cong trivial 𝟘≤𝟙 hyp₂ hyp₃ hyp₄ ⟩
    Has-[]-cong s 𝟙ᵐ Δ q₁ q₂′ q₃′ q₄′ q₅      →⟨ ¬-[]-cong nem Unitʷ-η→ consistent ⟩
    ⊥                                         □
