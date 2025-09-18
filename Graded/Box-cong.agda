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
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR
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
import Definition.Typed.Weakening TR as W
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
import Graded.Derived.Erased.Usage 𝕄 UR as ErasedU
open import Graded.Derived.Identity UR
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

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n                                              : Nat
  Γ                                              : Con Term _
  A A₁ A₂ B l l₁ l₂ t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ w : Term _
  σ                                              : Subst _ _
  p q q₁ q₂ q₃ q₄ q₅                             : M
  γ₁ γ₂ γ₃ γ₄ γ₅                                 : Conₘ _
  m                                              : Mode
  s                                              : Strength
  sem                                            : Some-erased-matches
  ok                                             : T _

------------------------------------------------------------------------
-- Some lemmas

private opaque

  -- Some lemmas used below.

  ⊢Id-2-1-0 :
    ⊢ Γ →
    Γ ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ⊢
      Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0 {Γ} ⊢Γ = Idⱼ′ (var₁ ⊢1) (var₀ ⊢1)
    where
    ⊢1 : Γ ∙ Level ∙ U (var x0) ∙ var x0 ⊢ var x1
    ⊢1 = univ (var₁ (univ (var₀ (Uⱼ (var₀ (Levelⱼ ⊢Γ))))))

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
  -- available for J, when the mode is 𝟘ᵐ[ ok ], or when the modality
  -- is trivial. Note that the lemmas in this section do not include
  -- assumptions of the form "[]-cong-allowed s".

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
    γ₁ ▸[ 𝟘ᵐ? ] l →
    γ₂ ▸[ 𝟘ᵐ? ] A →
    γ₃ ▸[ 𝟘ᵐ? ] t →
    γ₄ ▸[ 𝟘ᵐ? ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    𝟘ᶜ ▸[ m ] []-cong-J s l A t u v
  ▸[]-cong-J {m} {s} ≡not-none ▸l ▸A ▸t ▸u ▸v =
    case PE.singleton $ erased-matches-for-J m of λ where
      (not-none _ , ≡not-none) → sub
        (▸subst-𝟘 ≡not-none ▸A
           (Idₘ-generalised (▸Erased (wkUsage _ ▸l) (wkUsage _ ▸A))
              (▸[] (wkUsage _ ▸t)) (▸[] var)
              (λ _ → ≤ᶜ-refl)
              (λ _ →
                 let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
                   𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
                   𝟘ᶜ +ᶜ 𝟘ᶜ  ∎))
            ▸t ▸u ▸v rflₘ)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (none , ≡none) →
        case PE.trans (PE.sym ≡not-none) ≡none of λ ()
    where
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
  ▸[]-cong-J-𝟘ᵐ {s} ▸l ▸A ▸t ▸u ▸v =
    let ▸A = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A
        ▸l = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸l
    in
    ▸-𝟘 $
    ▸subst ▸A
      (Idₘ-generalised (▸Erased (wkUsage _ ▸l) (wkUsage _ ▸A))
         (▸[] (wkUsage (step id) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t))) (▸[] var)
         (λ _ → begin
            𝟘ᶜ ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ          ∎)
         (λ _ → begin
            𝟘ᶜ ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ          ≈˘⟨ +ᶜ-identityʳ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ    ∎))
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
    Γ ⊢ A ∷ U l →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ []-cong-J s l A t u v ∷ Id (Erased l A) [ t ] ([ u ])
  []-cong-Jⱼ ok ⊢A ⊢v =
    let ⊢A′ , ⊢t , _ = inversion-Id (syntacticTerm ⊢v)
        ⊢wk1-A       = W.wkTerm₁ ⊢A′ ⊢A
    in
    PE.subst (_⊢_∷_ _ _) Id-[]₀≡ $
    ⊢subst
      (Idⱼ′ ([]ⱼ ok ⊢wk1-A (W.wkTerm₁ ⊢A′ ⊢t))
         ([]ⱼ ok ⊢wk1-A (var₀ ⊢A′)))
      ⊢v
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢A ⊢t))

opaque
  unfolding []-cong-J

  -- A reduction rule for []-cong-J.

  []-cong-J-β-⇒′ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ≡ t′ ∷ A →
    Γ ⊢ []-cong-J s l A t t′ rfl ⇒ rfl ∷ Id (Erased l A) [ t ] ([ t′ ])
  []-cong-J-β-⇒′ {s} {t} {t′} ok ⊢A t≡t′ =
    let ⊢A′ , ⊢t , _ = syntacticEqTerm t≡t′
        ⊢wk1-A       = W.wkTerm₁ ⊢A′ ⊢A
    in
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    conv
      (subst-⇒′
         (Idⱼ′ ([]ⱼ ok ⊢wk1-A (W.wkTerm₁ ⊢A′ ⊢t))
            ([]ⱼ ok ⊢wk1-A (var₀ ⊢A′)))
         t≡t′
         (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
         rflⱼ ([]ⱼ ok ⊢A ⊢t)))
      (Id-cong
         (PE.subst₂ (_⊢_≡_ _)
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased)
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased) $
          refl (Erasedⱼ ok ⊢A))
         (PE.subst₃ (_⊢_≡_∷_ _)
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-[])
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-[])
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased) $
          P.[]-cong′ ok ⊢A (refl ⊢t))
         (PE.subst₃ (_⊢_≡_∷_ _) (PE.sym []-[]) (PE.sym []-[])
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased) $
          P.[]-cong′ ok ⊢A t≡t′))
    where
    open Erased s

opaque

  -- Another reduction rule for []-cong-J.

  []-cong-J-β-⇒ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ []-cong-J s l A t t rfl ⇒ rfl ∷ Id (Erased l A) [ t ] ([ t ])
  []-cong-J-β-⇒ ok ⊢A ⊢t = []-cong-J-β-⇒′ ok ⊢A (refl ⊢t)

opaque

  -- An equality rule for []-cong-J.

  []-cong-J-β-≡ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ []-cong-J s l A t t rfl ≡ rfl ∷ Id (Erased l A) [ t ] ([ t ])
  []-cong-J-β-≡ ok ⊢A ⊢t = subsetTerm ([]-cong-J-β-⇒ ok ⊢A ⊢t)

opaque
  unfolding []-cong-J

  -- An equality rule for []-cong-J.

  []-cong-J-cong :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ l₁ ≡ l₂ ∷ Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ []-cong-J s l₁ A₁ t₁ u₁ v₁ ≡ []-cong-J s l₂ A₂ t₂ u₂ v₂ ∷
      Id (Erased l₁ A₁) [ t₁ ] ([ u₁ ])
  []-cong-J-cong ok l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    let _ , ⊢A₁ , _ = wf-⊢≡∷ A₁≡A₂
        ⊢A₁′        = univ ⊢A₁
        ⊢wk1-A₁     = W.wkTerm₁ ⊢A₁′ ⊢A₁
    in
    PE.subst (_⊢_≡_∷_ _ _ _) Id-[]₀≡ $
    subst-cong (univ A₁≡A₂)
      (Id-cong
         (Erased-cong ok (W.wkEqTerm₁ ⊢A₁′ l₁≡l₂)
            (W.wkEqTerm₁ ⊢A₁′ A₁≡A₂))
         (P.[]-cong′ ok ⊢wk1-A₁ (W.wkEqTerm₁ ⊢A₁′ t₁≡t₂))
         (refl ([]ⱼ ok ⊢wk1-A₁ (var₀ ⊢A₁′))))
      t₁≡t₂ u₁≡u₂ v₁≡v₂
      (_⊢_≡_∷_.refl $
       PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢A₁ (wf-⊢≡∷ t₁≡t₂ .proj₂ .proj₁)))

opaque
  unfolding []-cong-J

  -- A reduction rule for []-cong-J.

  []-cong-J-subst :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A ∷ U l →
    Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
    Γ ⊢ []-cong-J s l A t u v₁ ⇒ []-cong-J s l A t u v₂ ∷
      Id (Erased l A) [ t ] ([ u ])
  []-cong-J-subst ok ⊢A v₁⇒v₂ =
    let ⊢A′ , ⊢t , _ = inversion-Id (wf-⊢≡∷ (subsetTerm v₁⇒v₂) .proj₁)
        ⊢wk1-A       = W.wkTerm₁ ⊢A′ ⊢A
    in
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    subst-subst
      (Idⱼ′ ([]ⱼ ok ⊢wk1-A (W.wkTerm₁ ⊢A′ ⊢t))
         ([]ⱼ ok ⊢wk1-A (var₀ ⊢A′)))
      v₁⇒v₂
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢A ⊢t))

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

------------------------------------------------------------------------
-- Has-[]-cong

-- The property of supporting a []-cong combinator (with certain
-- grades) for a certain mode.
--
-- Note that, unlike the []-cong primitive, the first argument must be
-- a type in U l for some l.

Has-[]-cong : Strength → Mode → M → M → M → M → M → Set a
Has-[]-cong s m q₁ q₂ q₃ q₄ q₅ =
  let open Erased s in
  ∃ λ ([]-cong : Term 0) →
  ε ▸[ m ] []-cong ×
  ε ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ Level ▹
    Π 𝟘 , q₂ ▷ U (var x0) ▹
    Π 𝟘 , q₃ ▷ var x0 ▹
    Π 𝟘 , q₄ ▷ var x1 ▹
    Π 𝟘 , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x4) (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong :
  Strength → Mode → M → M → M → M → M → Set a
Has-computing-[]-cong s m q₁ q₂ q₃ q₄ q₅ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s m q₁ q₂ q₃ q₄ q₅) →
  ∀ n (Γ : Con Term n) (l A t : Term n) →
  Γ ⊢ A ∷ U l →
  Γ ⊢ t ∷ A →
  Γ ⊢ wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
    rfl ∷ Id (Erased l A) [ t ] ([ t ])

opaque

  -- []-cong is supported for the strength s and the mode m, for
  -- grades for which "Π 𝟘" are allowed, if
  --
  -- * []-cong is allowed for s, or
  -- * Erased is allowed for s and
  --   * erased matches are available for J, or
  --   * m is 𝟘ᵐ, or
  --   * the modality is trivial.

  []-cong⊎J⊎𝟘ᵐ⊎Trivial→[]-cong :
    ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
    Erased-allowed s ×
    (erased-matches-for-J m ≢ none ⊎
     (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
     Trivial) →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Π-allowed 𝟘 q₅ →
    Has-computing-[]-cong s m q₁ q₂ q₃ q₄ q₅
  []-cong⊎J⊎𝟘ᵐ⊎Trivial→[]-cong {s} {m} ok ok₁ ok₂ ok₃ ok₄ ok₅ =
    let ⊢[]-cong″ =
          ⊢[]-cong″ ok′ (var₃ (⊢Id-2-1-0 ε)) (var₀ (⊢Id-2-1-0 ε))
    in
      ( []-cong′
      , (lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub (▸[]-cong″ ok′ var var var var var) $ begin
           ⌜ m ⌝ ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
           𝟘ᶜ           ∎)
      , lamⱼ′ ok₁ (lamⱼ′ ok₂ (lamⱼ′ ok₃ (lamⱼ′ ok₄ (lamⱼ′ ok₅ ⊢[]-cong″))))
      )
    , λ _ _ l A t ⊢A ⊢t →
        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl
                                                                        ⇒*⟨ PE.subst (_⊢_⇒*_∷_ _ _ _)
                                                                              (PE.sym $
                                                                               PE.trans (Erased.Id-Erased-[] _) $
                                                                               PE.cong
                                                                                 _[ consSubst (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                                                                                      rfl ] $
                                                                               Erased.wk-Id-Erased _) $
                                                                            β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                              (W.wkTerm
                                                                                 (W.liftʷ (W.lift (W.lift (W.lift (W.lift W.wk₀∷⊇)))) $
                                                                                  ⊢Id-2-1-0 (wfTerm ⊢A))
                                                                                 ⊢[]-cong″)
                                                                              (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        wk (liftn wk₀ 5)
          ([]-cong″ ok′ (var x4) (var x3) (var x2) (var x1) (var x0))
          [ consSubst
              (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
              rfl ]                                                     ≡⟨ PE.trans (subst-wk ([]-cong″ ok′ _ _ _ _ _)) $
                                                                           []-cong″-[] ok′ ⟩⊢≡

        []-cong″ ok′ l A t t rfl                                        ⇒⟨ []-cong″-β-⇒ ok′ ⊢A ⊢t ⟩⊢∎

        rfl                                                             ∎
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    Erased-ok : Erased-allowed s
    Erased-ok = case ok of λ where
      (inj₁ (ok , _)) → []-cong→Erased ok
      (inj₂ (ok , _)) → ok

    OK : Set a
    OK =
      ([]-cong-allowed s × []-cong-allowed-mode s m) ⊎
      (∃ λ sem → erased-matches-for-J m PE.≡ not-none sem) ⊎
      (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]) ⊎
      Trivial

    ok′ : OK
    ok′ = case ok of λ where
      (inj₁ ok)                        → inj₁ ok
      (inj₂ (_ , inj₂ (inj₂ trivial))) → inj₂ (inj₂ (inj₂ trivial))
      (inj₂ (_ , inj₂ (inj₁ ok)))      → inj₂ (inj₂ (inj₁ ok))
      (inj₂ (_ , inj₁ ≢none))          →
        inj₂ $ inj₁ $
        case PE.singleton $ erased-matches-for-J m of λ where
          (not-none _ , ≡not-none) → _ , ≡not-none
          (none       , ≡none)     → ⊥-elim $ ≢none ≡none

    []-cong″ : OK → Term n → Term n → Term n → Term n → Term n → Term n
    []-cong″ (inj₁ _) = []-cong s
    []-cong″ (inj₂ _) = []-cong-J s

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
    ▸[]-cong″ (inj₂ (inj₁ (_ , ≡not-none))) =
      ▸[]-cong-J ≡not-none
    ▸[]-cong″ (inj₂ (inj₂ (inj₁ (_ , PE.refl)))) ▸l ▸A ▸t ▸u ▸v =
      ▸[]-cong-J-𝟘ᵐ (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸l) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A)
        (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸[]-cong″ (inj₂ (inj₂ (inj₂ trivial))) =
      ▸[]-cong-J-trivial trivial

    ⊢[]-cong″ :
      let open Erased s in
      ∀ ok →
      Γ ⊢ A ∷ U l →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ []-cong″ ok l A t u v ∷ Id (Erased l A) [ t ] ([ u ])
    ⊢[]-cong″ (inj₁ (ok , _)) = []-congⱼ′ ok
    ⊢[]-cong″ (inj₂ _)        = []-cong-Jⱼ Erased-ok

    []-cong″-[] :
      ∀ ok →
      []-cong″ ok l A t u v [ σ ] PE.≡
      []-cong″ ok (l [ σ ]) (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
    []-cong″-[] (inj₁ _) = PE.refl
    []-cong″-[] (inj₂ _) = []-cong-J-[]

    []-cong″-β-⇒ :
      let open Erased s in
      ∀ ok →
      Γ ⊢ A ∷ U l →
      Γ ⊢ t ∷ A →
      Γ ⊢ []-cong″ ok l A t t rfl ⇒ rfl ∷ Id (Erased l A) [ t ] ([ t ])
    []-cong″-β-⇒ (inj₁ (ok , _)) ⊢A ⊢t = []-cong-β-⇒ ⊢A (refl ⊢t) ok
    []-cong″-β-⇒ (inj₂ _)        ⊢A ⊢t = []-cong-J-β-⇒ Erased-ok ⊢A ⊢t

    []-cong′ : Term 0
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong″ ok′ (var x4) (var x3) (var x2) (var x1) (var x0)

opaque
  unfolding Erased.Erased Erased.[_]

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ.

  ¬-[]-cong :
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    ¬ Has-[]-cong s 𝟙ᵐ q₁ q₂ q₃ q₄ q₅
  ¬-[]-cong nem Unitʷ-η→ (_ , ▸[]-cong , ⊢[]-cong) =
    case lemma
           (lemma
              (lemma
                 (lemma
                    (lemma
                       (idSubst , ⊢ˢʷ∷-idSubst ε , _ , ▸[]-cong ,
                        ⊢[]-cong)
                       ⊢l)
                    ⊢A)
                 ⊢t)
              ⊢t)
           (rflⱼ ⊢t) of λ {
      (_ , ⊢σ , _ , ▸t , ⊢t) →
    case red-Id ⦃ ok = included ⦄ ⊢t of λ where
      (_ , rflₙ , ⇒*rfl) →
        case var-only-equal-to-itself
               (neₙ (var _)) (λ ()) (ne! (var _)) $
             prod-cong⁻¹ ⦃ ok = included ⦄
               (inversion-rfl-Id ⦃ ok = included ⦄ $
                wf-⊢≡∷ (subset*Term ⇒*rfl) .proj₂ .proj₂)
               .proj₂ .proj₁ of λ ()
      (_ , ne u-ne , t⇒*u) →
        neutral-not-well-resourced nem (λ _ → inhabited-consistent ⊢σ)
          u-ne (wf-⊢≡∷ (subset*Term t⇒*u) .proj₂ .proj₂)
          (usagePres*Term Unitʷ-η→ ▸t t⇒*u) }
    where
    l′ : Term 0
    l′ = zeroᵘ

    A′ : Term 0
    A′ = ℕ

    t″ : Term 0
    t″ = zero

    ⊢l : ε ⊢ l′ ∷ Level
    ⊢l = zeroᵘⱼ ε

    ⊢A : ε ⊢ A′ ∷ U l′
    ⊢A = ℕⱼ ε

    ⊢t : ε ⊢ t″ ∷ A′
    ⊢t = zeroⱼ ε

    lemma :
      ((σ , _) :
       ∃ λ σ → ε ⊢ˢʷ σ ∷ Γ ×
       ∃ λ t → 𝟘ᶜ ▸[ 𝟙ᵐ ] t × Γ ⊢ t ∷ Π 𝟘 , p ▷ A ▹ B) →
      ε ⊢ u ∷ A [ σ ] →
      (∃ λ σ → ε ⊢ˢʷ σ ∷ Γ ∙ A ×
       ∃ λ t → 𝟘ᶜ ▸[ 𝟙ᵐ ] t × Γ ∙ A ⊢ t ∷ B)
    lemma (_ , ⊢σ , _ , ▸t , ⊢t) ⊢u =
        consSubst _ _
      , →⊢ˢʷ∷∙ ⊢σ ⊢u
      , (case red-Π ⦃ ok = included ⦄ ⊢t of λ where
           (_ , ne v-n , t⇒*v) →
             ⊥-elim $
             neutral-not-well-resourced nem
               (λ _ → inhabited-consistent ⊢σ) v-n
               (wf-⊢≡∷ (subset*Term t⇒*v) .proj₂ .proj₂)
               (usagePres*Term Unitʷ-η→ ▸t t⇒*v)
           (lam _ v , lamₙ , t⇒*lam) →
             case inv-usage-lam
                    (usagePres*Term Unitʷ-η→ ▸t t⇒*lam) of λ {
               (invUsageLam ▸v 𝟘≤) →
             case inversion-lam-Π-no-equality-reflection
                    (wf-⊢≡∷ (subset*Term t⇒*lam) .proj₂ .proj₂) of λ {
               (⊢v , PE.refl , _) →
               _
             , sub ▸v (𝟘≤ ∙ ≤-reflexive (PE.sym (·-zeroʳ _)))
             , ⊢v }})

------------------------------------------------------------------------
-- Has-weaker-[]-cong

-- A "weaker" variant of Has-[]-cong.

Has-weaker-[]-cong :
  Strength → Mode → M → M → M → M → M → Set a
Has-weaker-[]-cong s m q₁ q₂ q₃ q₄ q₅ =
  let open Erased s in
  ∃ λ ([]-cong : Term 0) →
  ε ▸[ m ] []-cong ×
  ε ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ Level ▹
    Π ω , q₂ ▷ U (var x0) ▹
    Π ω , q₃ ▷ var x0 ▹
    Π ω , q₄ ▷ var x1 ▹
    Π 𝟘 , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])

-- A "weaker" variant of Has-computing-[]-cong.

Has-weaker-computing-[]-cong :
  Strength → Mode → M → M → M → M → M → Set a
Has-weaker-computing-[]-cong s m q₁ q₂ q₃ q₄ q₅ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-weaker-[]-cong s m q₁ q₂ q₃ q₄ q₅) →
  ∀ n (Γ : Con Term n) (l A t : Term n) →
  Γ ⊢ A ∷ U l →
  Γ ⊢ t ∷ A →
  Γ ⊢ wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∘⟨ ω ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
    rfl ∷ Id (Erased l A) [ t ] ([ t ])

-- Some definitions/lemmas used below.

private
  module Has-[]-cong→Has-weaker-[]-cong
    (hyp₂ : Π-allowed 𝟘 q₂ → Π-allowed ω q₂)
    (hyp₃ : Π-allowed 𝟘 q₃ → Π-allowed ω q₃)
    (hyp₄ : Π-allowed 𝟘 q₄ → Π-allowed ω q₄)
    (([]-cong′ , _ , ⊢[]-cong′) : Has-[]-cong s m q₁ q₂ q₃ q₄ q₅)
    where

    open Erased s

    []-cong″ : Term 5
    []-cong″ =
       wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ var x4 ∘⟨ 𝟘 ⟩ var x3 ∘⟨ 𝟘 ⟩ var x2
         ∘⟨ 𝟘 ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        ε ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
          Id (var x2) (var x1) (var x0) ⊢
          []-cong″ ∷
          Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        flip _∘ⱼ_ (var₀ ⊢Id) $
        flip _∘ⱼ_ (var₁ ⊢Id) $
        flip _∘ⱼ_ (var₂ ⊢Id) $
        flip _∘ⱼ_ (var₃ ⊢Id) $
        flip _∘ⱼ_ (var₄ ⊢Id) $
        W.wkTerm (W.wk₀∷ʷ⊇ (∙ ⊢Id)) ⊢[]-cong′
        where
        ⊢Id :
          ε ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ⊢
          Id (var x2) (var x1) (var x0)
        ⊢Id = ⊢Id-2-1-0 ε

    oks :
      Π-allowed 𝟘 q₁ × Π-allowed ω q₂ × Π-allowed ω q₃ ×
      Π-allowed ω q₄ × Π-allowed 𝟘 q₅
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
    (Π-allowed 𝟘 q₂ → Π-allowed ω q₂) →
    (Π-allowed 𝟘 q₃ → Π-allowed ω q₃) →
    (Π-allowed 𝟘 q₄ → Π-allowed ω q₄) →
    Has-[]-cong s m q₁ q₂ q₃ q₄ q₅ →
    Has-weaker-[]-cong s m q₁ q₂ q₃ q₄ q₅
  Has-[]-cong→Has-weaker-[]-cong
    {q₂} {q₃} {q₄} {s} {m} {q₁} {q₅}
    hyp₂ hyp₃ hyp₄ has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open Has-[]-cong→Has-weaker-[]-cong hyp₂ hyp₃ hyp₄ has-[]-cong

    []-cong‴ : Term 0
    []-cong‴ =
       lam 𝟘 $ lam ω $ lam ω $ lam ω $ lam 𝟘 []-cong″

    ▸[]-cong‴ : ε ▸[ m ] []-cong‴
    ▸[]-cong‴ =
      lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub (((((wkUsage wk₀ ▸[]-cong′ ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ
           var) $
      (begin
         ε ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · 𝟘  ≤⟨ ε ∙ ≤-reflexive (·-zeroʳ _) ∙ lemma ∙ lemma ∙ lemma ∙
                                                                           ≤-reflexive (·-zeroʳ _) ⟩

         𝟘ᶜ                                                             ≈˘⟨ ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                            ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                            ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                            ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                            ≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _ ⟩
         ((((𝟘ᶜ +ᶜ 𝟘 ·ᶜ (𝟘ᶜ , x4 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
            𝟘 ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
           𝟘 ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
          𝟘 ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝)                                    ∎)
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
      ε ⊢ []-cong‴ ∷
        Π 𝟘 , q₁ ▷ Level ▹
        Π ω , q₂ ▷ U (var x0) ▹
        Π ω , q₃ ▷ var x0 ▹
        Π ω , q₄ ▷ var x1 ▹
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
    (Π-allowed 𝟘 q₂ → Π-allowed ω q₂) →
    (Π-allowed 𝟘 q₃ → Π-allowed ω q₃) →
    (Π-allowed 𝟘 q₄ → Π-allowed ω q₄) →
    Has-computing-[]-cong s m q₁ q₂ q₃ q₄ q₅ →
    Has-weaker-computing-[]-cong s m q₁ q₂ q₃ q₄ q₅
  Has-computing-[]-cong→Has-weaker-computing-[]-cong
    hyp₂ hyp₃ hyp₄ (has-[]-cong@([]-cong′ , _ , _) , []-cong′≡) =
    let open Has-[]-cong→Has-weaker-[]-cong hyp₂ hyp₃ hyp₄ has-[]-cong

        ok₁ , ok₂ , ok₃ , ok₄ , ok₅ = oks
    in
      Has-[]-cong→Has-weaker-[]-cong hyp₂ hyp₃ hyp₄ has-[]-cong
    , λ _ _ l A t ⊢A ⊢t →
        wk wk₀
          (lam 𝟘 $ lam ω $ lam ω $ lam ω $ lam 𝟘 $
           wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ var x4 ∘⟨ 𝟘 ⟩ var x3 ∘⟨ 𝟘 ⟩ var x2
             ∘⟨ 𝟘 ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0)
          ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∘⟨ ω ⟩ t ∘⟨ 𝟘 ⟩ rfl                ⇒*⟨ β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                              (W.wkTerm
                                                                                 (W.liftʷ (W.lift (W.lift (W.lift (W.lift W.wk₀∷⊇)))) $
                                                                                  ⊢Id-2-1-0 (wfTerm ⊢A))
                                                                                 ⊢[]-cong″)
                                                                              (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        (wk (liftn wk₀ 5) (wk wk₀ []-cong′)
           [ consSubst
               (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
               rfl ])
          ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl                ≡⟨ PE.cong
                                                                             (λ []-cong → []-cong ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _) $
                                                                           PE.trans
                                                                             (PE.cong _[ _ ] $
                                                                              PE.trans (wk-comp _ _ []-cong′) $
                                                                              PE.cong (flip wk _) $
                                                                              liftn-wk₀-•-wk₀ 5) $
                                                                           PE.trans (subst-wk []-cong′) $
                                                                           PE.sym $ wk≡subst _ _ ⟩⊢≡

        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl  ≡⟨ []-cong′≡ _ _ _ _ _ ⊢A ⊢t ⟩⊢∎

        rfl                                                             ∎

-- Some definitions/lemmas used below.

private
  module Has-weaker-[]-cong→Has-[]-cong
    (hyp₂ : Π-allowed ω q₂ → Π-allowed 𝟘 q₂)
    (hyp₃ : Π-allowed ω q₃ → Π-allowed 𝟘 q₃)
    (hyp₄ : Π-allowed ω q₄ → Π-allowed 𝟘 q₄)
    (([]-cong′ , _ , ⊢[]-cong′) : Has-weaker-[]-cong s m q₁ q₂ q₃ q₄ q₅)
    where

    open Erased s

    []-cong″ : Term 5
    []-cong″ =
      cong 𝟘 (Erased (var x4) (Erased (var x4) (var x3))) [ [ var x2 ] ]
        [ [ var x1 ] ] (Erased (var x4) (var x3))
        (mapᴱ (Erased (var x5) (var x4))
           (erased (var x5) (var x0)) (var x0))
        (wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ var x4
           ∘⟨ ω ⟩ Erased (var x4) (var x3) ∘⟨ ω ⟩ [ var x2 ]
           ∘⟨ ω ⟩ [ var x1 ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                    (Erased (var x4) (var x3)) [ var x0 ] (var x0))

    opaque
      unfolding Erased [_]

      ⊢[]-cong″ :
        Π-allowed 𝟘 q₁ × Π-allowed 𝟘 q₂ ×
        Π-allowed 𝟘 q₃ × Π-allowed 𝟘 q₄ ×
        Π-allowed 𝟘 q₅ ×
        ε ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
          Id (var x2) (var x1) (var x0) ⊢
          []-cong″ ∷
          Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        let _ , ⊢Π  , ok₁    = inversion-ΠΣ $ syntacticTerm ⊢[]-cong′
            _ , ⊢Π  , ok₂    = inversion-ΠΣ ⊢Π
            _ , ⊢Π  , ok₃    = inversion-ΠΣ ⊢Π
            _ , ⊢Π  , ok₄    = inversion-ΠΣ ⊢Π
            _ , ⊢Id , ok₅    = inversion-ΠΣ ⊢Π
            Erased-ok , _    = inversion-Erased $
                               inversion-Id ⊢Id .proj₁
            ⊢Id              = ⊢Id-2-1-0 ε
            ⊢3               = var₃ ⊢Id
            ⊢Erased-3        = Erasedⱼ-U Erased-ok ⊢3
            ⊢Erased-Erased-3 = univ (Erasedⱼ-U Erased-ok ⊢Erased-3)

            lemma :
              ∀ t →
              ε ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
                Id (var x2) (var x1) (var x0) ⊢
                t ∷ var x3 →
              ε ∙ Level ∙ U (var x0) ∙ var x0 ∙ var x1 ∙
                Id (var x2) (var x1) (var x0) ⊢
                mapᴱ (Erased (var x5) (var x4))
                  (erased (var x5) (var x0)) (var x0) [ [ [ t ] ] ]₀ ≡
                [ t ] ∷ Erased (var x4) (var x3)
            lemma t ⊢t =
              mapᴱ (Erased (var x5) (var x4)) (erased (var x5) (var x0))
                (var x0) [ [ [ t ] ] ]₀                                   ≡⟨ PE.trans mapᴱ-[] $
                                                                             PE.cong₂ (mapᴱ _) erased-[] PE.refl ⟩⊢≡
              mapᴱ (Erased (var x4) (var x3)) (erased (var x4) (var x0))
                ([ [ t ] ])                                               ≡⟨ mapᴱ-β Erased-ok ⊢3 (erasedⱼ (var₀ (univ ⊢Erased-3)))
                                                                               ([]ⱼ Erased-ok ⊢3 ⊢t) ⟩⊢

              [ erased (var x4) (var x0) [ [ t ] ]₀ ]                     ≡⟨ PE.cong [_] erased-[] ⟩⊢≡

              [ erased (var x3) ([ t ]) ]                                 ≡⟨ P.[]-cong′ Erased-ok ⊢3 $
                                                                             Erased-β Erased-ok ⊢t ⟩⊢∎
              [ t ]                                                       ∎
        in
        ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , hyp₄ ok₄ , ok₅ ,
        _⊢_∷_.conv
          (⊢cong
             (⊢mapᴱ (Erasedⱼ-U Erased-ok (var₄ ⊢Erased-Erased-3))
                (var₄ ⊢Erased-Erased-3)
                (erasedⱼ $ var₀ $ Erasedⱼ Erased-ok $
                 var₄ ⊢Erased-Erased-3)
                (var₀ ⊢Erased-Erased-3)) $
           flip _∘ⱼ_
             (⊢cong ([]ⱼ Erased-ok (var₄ (univ ⊢3)) $ var₀ (univ ⊢3)) $
              var₀ ⊢Id) $
           flip _∘ⱼ_ ([]ⱼ Erased-ok ⊢3 $ var₁ ⊢Id) $
           flip _∘ⱼ_ ([]ⱼ Erased-ok ⊢3 $ var₂ ⊢Id) $
           flip _∘ⱼ_ (Erasedⱼ-U Erased-ok $ var₃ ⊢Id) $
           flip _∘ⱼ_ (var₄ ⊢Id) $
            W.wkTerm (W.wk₀∷ʷ⊇ (wf ⊢Erased-Erased-3)) ⊢[]-cong′)
          (Id-cong (refl (univ ⊢Erased-3)) (lemma _ (var₂ ⊢Id))
             (lemma _ (var₁ ⊢Id)))

opaque

  -- Has-weaker-[]-cong is at least as strong as Has-[]-cong (given
  -- certain assumptions).

  Has-weaker-[]-cong→Has-[]-cong :
    (¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃) →
    (Π-allowed ω q₄ → Π-allowed 𝟘 q₄) →
    Has-weaker-[]-cong s m q₁ q₂ q₃ q₄ q₅ →
    Has-[]-cong s m q₁ q₂ q₃ q₄ q₅
  Has-weaker-[]-cong→Has-[]-cong
    {s} {q₂} {q₃} {q₄} {m} {q₁} {q₅}
    trivial prodrec-ok hyp₂ hyp₃ hyp₄ has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open ErasedU s
    open Has-weaker-[]-cong→Has-[]-cong hyp₂ hyp₃ hyp₄ has-[]-cong

    []-cong‴ : Term 0
    []-cong‴ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 []-cong″

    opaque

      ⊢[]-cong‴ :
        ε ⊢ []-cong‴ ∷
        Π 𝟘 , q₁ ▷ Level ▹
        Π 𝟘 , q₂ ▷ U (var x0) ▹
        Π 𝟘 , q₃ ▷ var x0 ▹
        Π 𝟘 , q₄ ▷ var x1 ▹
        Π 𝟘 , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (var x4) (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong‴ =
        let ok₁ , ok₂ , ok₃ , ok₄ , ok₅ , ⊢[]-cong″ = ⊢[]-cong″ in
        lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
        lamⱼ′ ok₅ ⊢[]-cong″

      ▸[]-cong‴ : ε ▸[ m ] []-cong‴
      ▸[]-cong‴ =
        lamₘ $ lamₘ $ lamₘ $ lamₘ $ lamₘ $
        sub
          (▸cong (▸Erased var (▸Erased var var)) (▸[] (▸[] var))
             (▸[] (▸[] var)) (▸Erased var var)
             (sub
                (▸mapᴱ′ (λ _ → trivial) (λ _ → trivial′) prodrec-ok
                   (λ _ → _ , ▸Erased var var)
                   (sub
                      (▸erased′ (λ _ → trivial) (λ _ → trivial′) var
                         (λ _ → _ , var) prodrec-ok)
                      (begin
                         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                         𝟘ᶜ                ∎))
                   var)
                (begin
                   𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                   𝟘ᶜ              ∎))
             (flip _∘ₘ_
                (▸cong var var var (▸Erased var var)
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
                                                                              (·ᶜ-zeroʳ _)) $
                                                                         +ᶜ-identityʳ _ ⟩
                      (⌜ m ᵐ· 𝟘 ⌝ · 𝟘) ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
                      (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ                                  ∎)) $
              flip _∘ₘ_ (▸[] var) $
              flip _∘ₘ_ (▸[] var) $
              flip _∘ₘ_ (▸Erased var var) $
              flip _∘ₘ_ var $
              wkUsage wk₀ ▸[]-cong′)
             (λ _ → begin
                𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                𝟘ᶜ              ∎)
             (λ _ → begin
                𝟘ᶜ                                  ≈˘⟨ ≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _)) $
                                                        +ᶜ-identityʳ _ ⟩
                (⌜ m ⌝ · 𝟘) ·ᶜ 𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ  ∎)) $
        (begin
           ε ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ε ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩

           𝟘ᶜ                                                             ≤⟨ ε ∙ lemma₁ ∙ lemma₂ ∙ lemma₁ ∙ lemma₁ ∙ lemma₁ ⟩

           ω ·ᶜ ω ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝)                                  ≈˘⟨ ·ᶜ-congˡ $
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
                                                                                                  (+ᶜ-congʳ $
                                                                                                   ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                                                   ·ᶜ-zeroˡ _) $
                                                                                                +ᶜ-identityˡ _)
                                                                                               (·ᶜ-zeroʳ _)) $
                                                                                          +ᶜ-identityʳ _)
                                                                                         (·ᶜ-zeroʳ _)) $
                                                                                    +ᶜ-identityʳ _)
                                                                                   (·ᶜ-zeroˡ _)) $
                                                                              +ᶜ-identityʳ _ ⟩
           ω ·ᶜ
           (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ
            (((((𝟘ᶜ +ᶜ 𝟘 ·ᶜ (𝟘ᶜ , x4 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
                ω ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝)) +ᶜ
               ω ·ᶜ 𝟘ᶜ) +ᶜ
              ω ·ᶜ 𝟘ᶜ) +ᶜ
             𝟘 ·ᶜ ω ·ᶜ
             ((𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
              (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ 𝟘ᶜ)) +ᶜ
            𝟘ᶜ)                                                           ∎)
        where
        trivial′ : ¬ T 𝟘ᵐ-allowed → p ≤ q
        trivial′ = ≡-trivial ∘→ trivial

        lemma₁ : 𝟘 ≤ ω · ω · 𝟘
        lemma₁ = begin
          𝟘            ≡˘⟨ ·-zeroʳ _ ⟩
          (ω · ω) · 𝟘  ≡⟨ ·-assoc _ _ _ ⟩
          ω · ω · 𝟘    ∎
          where
          open Tools.Reasoning.PartialOrder ≤-poset

        lemma₂ : 𝟘 ≤ ω · ω · ⌜ 𝟘ᵐ? ⌝
        lemma₂ = 𝟘ᵐ?-elim (λ m → 𝟘 ≤ ω · ω · ⌜ m ⌝) lemma₁ trivial′

        open ≤ᶜ-reasoning

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
    (¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃) →
    (Π-allowed ω q₄ → Π-allowed 𝟘 q₄) →
    Has-weaker-computing-[]-cong s m q₁ q₂ q₃ q₄ q₅ →
    Has-computing-[]-cong s m q₁ q₂ q₃ q₄ q₅
  Has-weaker-computing-[]-cong→Has-computing-[]-cong
    {s} {q₂} {q₃} {q₄} {m} {q₁} {q₅}
    trivial prodrec-ok hyp₂ hyp₃ hyp₄
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    has-[]-cong′ , []-cong″-computes
    where
    open Erased s

    has-[]-cong′ : Has-[]-cong s m q₁ q₂ q₃ q₄ q₅
    has-[]-cong′ =
      Has-weaker-[]-cong→Has-[]-cong
        trivial prodrec-ok hyp₂ hyp₃ hyp₄ has-[]-cong

    []-cong″ : Term 0
    []-cong″ = has-[]-cong′ .proj₁

    opaque

      lemma :
        (l A t : Term n) (u : Term 0) →
        wk wk₀ u
          U.[ consSubst
                (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                rfl ₛ•
              liftn wk₀ 5 ] PE.≡
        wk wk₀ u
      lemma l A t u =
        wk wk₀ u
          U.[ consSubst
                (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                rfl ₛ•
              liftn wk₀ 5 ]                                             ≡⟨ subst-wk u ⟩

        u U.[ (consSubst
                 (consSubst (consSubst (consSubst (sgSubst l) A) t) t)
                 rfl ₛ•
               liftn wk₀ 5) ₛ•
              wk₀ ]                                                     ≡˘⟨ wk≡subst _ _ ⟩

        wk wk₀ u                                                        ∎
        where
        open Tools.Reasoning.PropositionalEquality

    opaque
      unfolding Erased [_]

      []-cong″-computes :
        ∀ n (Γ : Con Term n) (l A t : Term n) →
        Γ ⊢ A ∷ U l →
        Γ ⊢ t ∷ A →
        Γ ⊢
          wk wk₀ []-cong″ ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t
            ∘⟨ 𝟘 ⟩ rfl ≡
          rfl ∷ Id (Erased l A) [ t ] ([ t ])
      []-cong″-computes _ Γ l A t ⊢A ⊢t =
        let open Has-weaker-[]-cong→Has-[]-cong
              hyp₂ hyp₃ hyp₄ has-[]-cong

            ok₁ , ok₂ , ok₃ , ok₄ , ok₅ , ⊢[]-cong″ = ⊢[]-cong″
        in
        wk wk₀
          (lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
           cong 𝟘 (Erased (var x4) (Erased (var x4) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ] (Erased (var x4) (var x3))
             (mapᴱ (Erased (var x5) (var x4)) (erased (var x5) (var x0))
                (var x0))
             (wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ var x4
                ∘⟨ ω ⟩ Erased (var x4) (var x3) ∘⟨ ω ⟩ [ var x2 ]
                ∘⟨ ω ⟩ [ var x1 ]
                ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                         (Erased (var x4) (var x3)) [ var x0 ]
                         (var x0)))
          ∘⟨ 𝟘 ⟩ l ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ∷
          Id (Erased l A) [ t ] ([ t ])                                   ⇒*⟨ β-red-⇒₅′ ok₁ ok₂ ok₃ ok₄ ok₅
                                                                                (W.wkTerm
                                                                                   (W.liftʷ (W.lift (W.lift (W.lift (W.lift W.wk₀∷⊇)))) $
                                                                                    ⊢Id-2-1-0 (wfTerm ⊢A))
                                                                                   ⊢[]-cong″)
                                                                                ⊢l ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢∷
                                                                           ˘⟨ Id-cong (refl (univ ⊢Erased-A)) mapᴱ-lemma mapᴱ-lemma ⟩≡
        wk (liftn wk₀ 5)
          (cong 𝟘 (Erased (var x4) (Erased (var x4) (var x3)))
             [ [ var x2 ] ] [ [ var x1 ] ] (Erased (var x4) (var x3))
             (mapᴱ (Erased (var x5) (var x4)) (erased (var x5) (var x0))
                (var x0))
             (wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ var x4
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
                                                                                   lemma _ _ _ _)
                                                                                  cong-[]) ⟩⊢∷≡
        cong 𝟘 (Erased l (Erased l A)) [ [ t ] ] [ [ t ] ] (Erased l A)
          (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
             (var x0))
          (wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ Erased l A ∘⟨ ω ⟩ [ t ]
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
                                                                                W.wkTerm (W.wk₀∷ʷ⊇ (wfTerm ⊢A)) ⊢[]-cong′) $
                                                                             cong-≡ ⊢t $
                                                                             PE.subst (_⊢_∷_ _ _) (PE.sym wk-Erased) $
                                                                             []ⱼ Erased-ok (W.wkTerm₁ (univ ⊢A) ⊢A) (var₀ (univ ⊢A)) ⟩⊢
        cong 𝟘 (Erased l (Erased l A)) [ [ t ] ] [ [ t ] ] (Erased l A)
          (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
             (var x0))
          (wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ l ∘⟨ ω ⟩ Erased l A ∘⟨ ω ⟩ [ t ]
             ∘⟨ ω ⟩ [ t ] ∘⟨ 𝟘 ⟩ rfl)                                     ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                               (refl (univ ⊢Erased-A)) (refl ⊢mapᴱ-0) $
                                                                             []-cong′≡ _ _ _ _ _ ⊢Erased-A∷U ⊢[t] ⟩⊢
        cong 𝟘 (Erased l (Erased l A)) [ [ t ] ] [ [ t ] ] (Erased l A)
          (mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
             (var x0))
          rfl                                                             ⇒⟨ cong-⇒ ⊢[[t]] ⊢mapᴱ-0 ⟩⊢∎

        rfl                                                               ∎
        where
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

        ⊢l : Γ ⊢ l ∷ Level
        ⊢l = inversion-U-Level (wf-⊢∷ ⊢A)

        ⊢[t] : Γ ⊢ [ t ] ∷ Erased l A
        ⊢[t] = []ⱼ Erased-ok ⊢A ⊢t

        ⊢Erased-A : Γ ⊢ Erased l A ∷ U l
        ⊢Erased-A = Erasedⱼ-U Erased-ok ⊢A

        ⊢[[t]] : Γ ⊢ [ [ t ] ] ∷ Erased l (Erased l A)
        ⊢[[t]] = []ⱼ Erased-ok ⊢Erased-A ⊢[t]

        ⊢Erased-Erased-A : Γ ⊢ Erased l (Erased l A)
        ⊢Erased-Erased-A = syntacticTerm ⊢[[t]]

        ⊢Erased-A∷U : Γ ⊢ Erased l A ∷ U l
        ⊢Erased-A∷U = Erasedⱼ-U Erased-ok ⊢A

        ⊢mapᴱ-0 :
          Γ ∙ Erased l (Erased l A) ⊢
            mapᴱ (Erased (wk1 l) (wk1 A)) (erased (wk2 A) (var x0))
              (var x0) ∷
            wk1 (Erased l A)
        ⊢mapᴱ-0 =
          PE.subst (_⊢_∷_ _ _) (PE.sym wk-Erased) $
          ⊢mapᴱ
            (Erasedⱼ-U Erased-ok (W.wkTerm₁ ⊢Erased-Erased-A ⊢A))
            (W.wkTerm₁ ⊢Erased-Erased-A ⊢A)
            (erasedⱼ $ PE.subst (_⊢_∷_ _ _) wk-Erased $
             var₀ $ PE.subst (_⊢_ _) wk-Erased $
             W.wk₁ ⊢Erased-Erased-A (univ ⊢Erased-A))
            (PE.subst (_⊢_∷_ _ _)
               (PE.trans wk-Erased $ PE.cong (Erased _) wk-Erased) $
             var₀ ⊢Erased-Erased-A)

        mapᴱ-lemma :
          Γ ⊢
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

          mapᴱ (Erased l A) (erased (wk1 A) (var x0)) ([ [ t ] ])   ≡⟨ mapᴱ-β Erased-ok ⊢A
                                                                         (erasedⱼ $
                                                                          PE.subst (_⊢_∷_ _ _) wk-Erased $
                                                                          var₀ (univ ⊢Erased-A))
                                                                         ([]ⱼ Erased-ok ⊢A ⊢t) ⟩⊢

          [ erased (wk1 A) (var x0) [ [ t ] ]₀ ]                    ≡⟨ PE.cong ([_]) $
                                                                       PE.trans erased-[] $
                                                                       PE.cong₂ erased (wk1-sgSubst _ _) PE.refl ⟩⊢≡

          [ erased A ([ t ]) ]                                      ≡⟨ P.[]-cong′ Erased-ok ⊢A $
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
    ⦃ not-ok : No-equality-reflection ⦄ →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ[ ok ] (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃) →
    (Π-allowed ω q₄ → Π-allowed 𝟘 q₄) →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    ¬ Has-weaker-[]-cong s 𝟙ᵐ q₁ q₂ q₃ q₄ q₅
  ¬-Has-weaker-[]-cong
    {s} {ok} {q₂} {q₃} {q₄} {q₁} {q₅}
    prodrec-ok hyp₂ hyp₃ hyp₄ nem Unitʷ-η→ =
    Has-weaker-[]-cong s 𝟙ᵐ q₁ q₂ q₃ q₄ q₅  →⟨ Has-weaker-[]-cong→Has-[]-cong (⊥-elim ∘→ (_$ ok))
                                                 (PE.subst (λ m → Prodrec-allowed m _ _ _) (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ∘→ prodrec-ok)
                                                 hyp₂ hyp₃ hyp₄ ⟩
    Has-[]-cong s 𝟙ᵐ q₁ q₂ q₃ q₄ q₅         →⟨ ¬-[]-cong ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄ nem Unitʷ-η→ ⟩
    ⊥                                       □
