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
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
import Definition.Typed.Weakening TR as W
open import Definition.Untyped M as U
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Erased.Typed TR as ET hiding ([]-cong′)
import Graded.Derived.Erased.Untyped 𝕄 as Erased
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

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n                                    : Nat
  Γ                                    : Con Term _
  A A₁ A₂ B t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ : Term _
  σ                                    : Subst _ _
  p q₁ q₂ q₃ q₄                        : M
  γ₁ γ₂ γ₃ γ₄                          : Conₘ _
  m                                    : Mode
  s                                    : Strength
  sem                                  : Some-erased-matches
  ok                                   : T _

------------------------------------------------------------------------
-- Some lemmas

private opaque

  -- Some lemmas used below.

  ⊢Id-2-1-0 : ε ∙ U ∙ var x0 ∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0 = Idⱼ (var₁ ⊢1) (var₀ ⊢1)
    where
    ⊢1 : ε ∙ U ∙ var x0 ⊢ var x1
    ⊢1 = univ (var₁ (univ (var₀ (Uⱼ ε))))

  ⊢Id-4-3-0 :
    ε ∙ U ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ∙ var x3 ⊢
    Id (var x4) (var x3) (var x0)
  ⊢Id-4-3-0 = Idⱼ (var₃ ⊢3) (var₀ ⊢3)
    where
    ⊢3 :
      ε ∙ U ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢ var x3
    ⊢3 = univ (var₃ ⊢Id-2-1-0)

  Id-[]₀≡ :
    let open Erased s in
    Id (Erased (wk1 A)) [ wk1 t ] ([ var x0 ]) [ u ]₀ PE.≡
    Id (Erased A) [ t ] ([ u ])
  Id-[]₀≡ {s} = PE.cong₃ Id
    (PE.cong Erased $ wk1-sgSubst _ _)
    (PE.cong ([_]) $ wk1-sgSubst _ _)
    PE.refl
    where
    open Erased s

------------------------------------------------------------------------
-- []-cong-J

opaque

  -- A variant of []-cong which can be used when erased matches are
  -- available for J, or when the mode is 𝟘ᵐ[ ok ]. Note that the
  -- lemmas in this section do not include assumptions of the form
  -- "[]-cong-allowed s".

  []-cong-J : Strength → Term n → Term n → Term n → Term n → Term n
  []-cong-J s A t u v =
    subst 𝟘 A (Id (Erased (wk1 A)) [ wk1 t ] ([ var x0 ])) t u v rfl
    where
    open Erased s

opaque
  unfolding []-cong-J

  -- A usage rule for []-cong-J.

  ▸[]-cong-J :
    erased-matches-for-J m PE.≡ not-none sem →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ▸[ 𝟘ᵐ? ] u →
    γ₄ ▸[ 𝟘ᵐ? ] v →
    𝟘ᶜ ▸[ m ] []-cong-J s A t u v
  ▸[]-cong-J {m} {s} ≡not-none ▸A ▸t ▸u ▸v =
    case PE.singleton $ erased-matches-for-J m of λ where
      (not-none _ , ≡not-none) → sub
        (▸subst-𝟘 ≡not-none ▸A
           (Idₘ-generalised (▸Erased (wkUsage _ ▸A))
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
    γ₁ ▸[ 𝟘ᵐ[ ok ] ] A →
    γ₂ ▸[ 𝟘ᵐ[ ok ] ] t →
    γ₃ ▸[ 𝟘ᵐ[ ok ] ] u →
    γ₄ ▸[ 𝟘ᵐ[ ok ] ] v →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] []-cong-J s A t u v
  ▸[]-cong-J-𝟘ᵐ {s} ▸A ▸t ▸u ▸v =
    case ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A of λ
      ▸A →
    ▸-𝟘 $
    ▸subst ▸A
      (Idₘ-generalised (▸Erased (wkUsage (step id) ▸A))
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

  -- A typing rule for []-cong-J.

  []-cong-Jⱼ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ []-cong-J s A t u v ∷ Id (Erased A) [ t ] ([ u ])
  []-cong-Jⱼ ok ⊢v =
    case inversion-Id (syntacticTerm ⊢v) of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_∷_ _ _) Id-[]₀≡ $
    ⊢subst (Idⱼ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A))) ⊢v
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢t))

opaque
  unfolding []-cong-J

  -- A reduction rule for []-cong-J.

  []-cong-J-β-⇒′ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ t ≡ t′ ∷ A →
    Γ ⊢ []-cong-J s A t t′ rfl ⇒ rfl ∷ Id (Erased A) [ t ] ([ t′ ])
  []-cong-J-β-⇒′ ok t≡t′ =
    case syntacticEqTerm t≡t′ of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    conv
      (subst-⇒′ (Idⱼ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A))) t≡t′
         (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
         rflⱼ ([]ⱼ ok ⊢t)))
      (Id-cong
         (PE.subst₂ (_⊢_≡_ _)
            (PE.sym $ wk1-sgSubst _ _)
            (PE.sym $ wk1-sgSubst _ _) $
          Erased-cong ok $ refl ⊢A)
         (PE.subst₃ (_⊢_≡_∷_ _)
            (PE.sym $ wk1-sgSubst _ _)
            (PE.sym $ wk1-sgSubst _ _)
            (PE.sym $ wk1-sgSubst _ _) $
          ET.[]-cong′ ok $ refl ⊢t)
         (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk1-sgSubst _ _) $
          ET.[]-cong′ ok t≡t′))

opaque

  -- Another reduction rule for []-cong-J.

  []-cong-J-β-⇒ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ t ∷ A →
    Γ ⊢ []-cong-J s A t t rfl ⇒ rfl ∷ Id (Erased A) [ t ] ([ t ])
  []-cong-J-β-⇒ ok ⊢t = []-cong-J-β-⇒′ ok (refl ⊢t)

opaque

  -- An equality rule for []-cong-J.

  []-cong-J-β-≡ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ t ∷ A →
    Γ ⊢ []-cong-J s A t t rfl ≡ rfl ∷ Id (Erased A) [ t ] ([ t ])
  []-cong-J-β-≡ ok ⊢t = subsetTerm ([]-cong-J-β-⇒ ok ⊢t)

opaque
  unfolding []-cong-J

  -- An equality rule for []-cong-J.

  []-cong-J-cong :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ []-cong-J s A₁ t₁ u₁ v₁ ≡ []-cong-J s A₂ t₂ u₂ v₂ ∷
      Id (Erased A₁) [ t₁ ] ([ u₁ ])
  []-cong-J-cong ok A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case syntacticEq A₁≡A₂ of λ
      (⊢A₁ , _) →
    PE.subst (_⊢_≡_∷_ _ _ _) Id-[]₀≡ $
    subst-cong A₁≡A₂
      (Id-cong (W.wkEq₁ ⊢A₁ (Erased-cong ok A₁≡A₂))
         (ET.[]-cong′ ok (W.wkEqTerm₁ ⊢A₁ t₁≡t₂))
         (refl ([]ⱼ ok (var₀ ⊢A₁))))
      t₁≡t₂ u₁≡u₂ v₁≡v₂
      (refl $
       PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok (syntacticEqTerm t₁≡t₂ .proj₂ .proj₁)))

opaque
  unfolding []-cong-J

  -- A reduction rule for []-cong-J.

  []-cong-J-subst :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
    Γ ⊢ []-cong-J s A t u v₁ ⇒ []-cong-J s A t u v₂ ∷
      Id (Erased A) [ t ] ([ u ])
  []-cong-J-subst ok v₁⇒v₂ =
    case inversion-Id (syntacticEqTerm (subsetTerm v₁⇒v₂) .proj₁) of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    subst-subst (Idⱼ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A)))
      v₁⇒v₂
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢t))

opaque
  unfolding []-cong-J

  -- A substitution lemma for []-cong-J.

  []-cong-J-[] :
    []-cong-J s A t u v [ σ ] PE.≡
    []-cong-J s (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
  []-cong-J-[] {s} {A} {t} {u} {v} {σ} =
    subst 𝟘 A (Id (Erased (wk1 A)) [ wk1 t ] ([ var x0 ])) t u v rfl
      U.[ σ ]                                                             ≡⟨ subst-[] ⟩

    subst 𝟘 (A U.[ σ ])
      (Id (Erased (wk1 A U.[ liftSubst σ ])) [ wk1 t U.[ liftSubst σ ] ]
         ([ var x0 ]))
      (t U.[ σ ]) (u U.[ σ ]) (v U.[ σ ]) rfl                             ≡⟨ PE.cong₅ (subst _ _)
                                                                               (PE.cong₃ Id
                                                                                  (PE.cong Erased (wk1-liftSubst A))
                                                                                  (PE.cong [_] (wk1-liftSubst t))
                                                                                  PE.refl)
                                                                               PE.refl PE.refl PE.refl PE.refl ⟩
    subst 𝟘 (A U.[ σ ])
      (Id (Erased (wk1 (A U.[ σ ]))) [ wk1 (t U.[ σ ]) ] ([ var x0 ]))
      (t U.[ σ ]) (u U.[ σ ]) (v U.[ σ ]) rfl                             ∎
    where
    open Erased s
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Has-[]-cong

-- The property of supporting a []-cong combinator (with certain
-- grades) for a certain mode.
--
-- Note that, unlike the []-cong primitive, the first argument must be
-- a type in U.

Has-[]-cong : Strength → Mode → M → M → M → M → Set a
Has-[]-cong s m q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ ([]-cong : Term 0) →
  ε ▸[ m ] []-cong ×
  ε ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ U ▹
    Π 𝟘 , q₂ ▷ var x0 ▹
    Π 𝟘 , q₃ ▷ var x1 ▹
    Π 𝟘 , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong : Strength → Mode → M → M → M → M → Set a
Has-computing-[]-cong s m q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s m q₁ q₂ q₃ q₄) →
  ∀ n (Γ : Con Term n) (A t : Term n) →
  Γ ⊢ A ∷ U →
  Γ ⊢ t ∷ A →
  Γ ⊢ wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡ rfl ∷
    Id (Erased A) ([ t ]) ([ t ])

opaque

  -- []-cong is supported for the strength s and the mode m, for
  -- grades for which "Π 𝟘" are allowed, if
  --
  -- * []-cong is allowed for s, or
  -- * Erased is allowed for s and
  --   * erased matches are available for J, or
  --   * m is 𝟘ᵐ.

  []-cong⊎J⊎𝟘ᵐ→[]-cong :
    []-cong-allowed s ⊎
    Erased-allowed s ×
    (erased-matches-for-J m ≢ none ⊎
     (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ])) →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Has-computing-[]-cong s m q₁ q₂ q₃ q₄
  []-cong⊎J⊎𝟘ᵐ→[]-cong {s} {m} ok ok₁ ok₂ ok₃ ok₄ =
    case lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
         ⊢[]-cong″ ok′ (var₀ ⊢Id-2-1-0) of λ {
      ⊢[]-cong →
      ( []-cong′
      , (lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub (▸[]-cong″ ok′ var var var var) $ begin
           ⌜ m ⌝ ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
           𝟘ᶜ           ∎)
      , ⊢[]-cong
      )
    , λ _ _ A t ⊢A ⊢t →
        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl        ⇒*⟨ β-red-⇒₄ (W.wkTerm W.wk₀∷⊇ (wfTerm ⊢A) ⊢[]-cong) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢

        wk (liftn wk₀ 4)
          ([]-cong″ ok′ (var x3) (var x2) (var x1) (var x0))
          [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ]  ≡⟨ PE.trans (subst-wk ([]-cong″ ok′ _ _ _ _)) $
                                                                        []-cong″-[] ok′ ⟩⊢≡

        []-cong″ ok′ A t t rfl                                       ⇒⟨ []-cong″-β-⇒ ok′ ⊢t ⟩⊢∎

        rfl                                                          ∎ }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    Erased-ok : Erased-allowed s
    Erased-ok = case ok of λ where
      (inj₁ ok)       → []-cong→Erased ok
      (inj₂ (ok , _)) → ok

    OK : Set a
    OK =
      []-cong-allowed s ⊎
      ((∃ λ sem → erased-matches-for-J m PE.≡ not-none sem) ⊎
       (∃ λ ok → m PE.≡ 𝟘ᵐ[ ok ]))

    ok′ : OK
    ok′ = case ok of λ where
      (inj₁ ok)               → inj₁ ok
      (inj₂ (_ , inj₂ ok))    → inj₂ (inj₂ ok)
      (inj₂ (_ , inj₁ ≢none)) →
        inj₂ $ inj₁ $
        case PE.singleton $ erased-matches-for-J m of λ where
          (not-none _ , ≡not-none) → _ , ≡not-none
          (none       , ≡none)     → ⊥-elim $ ≢none ≡none

    []-cong″ : OK → Term n → Term n → Term n → Term n → Term n
    []-cong″ (inj₁ _) = []-cong s
    []-cong″ (inj₂ _) = []-cong-J s

    ▸[]-cong″ :
      ∀ ok →
      γ₁ ▸[ 𝟘ᵐ? ] A →
      γ₂ ▸[ 𝟘ᵐ? ] t →
      γ₃ ▸[ 𝟘ᵐ? ] u →
      γ₄ ▸[ 𝟘ᵐ? ] v →
      𝟘ᶜ ▸[ m ] []-cong″ ok A t u v
    ▸[]-cong″ (inj₁ _)                      = []-congₘ
    ▸[]-cong″ (inj₂ (inj₁ (_ , ≡not-none))) = ▸[]-cong-J ≡not-none
    ▸[]-cong″ (inj₂ (inj₂ (_ , PE.refl)))   = λ ▸A ▸t ▸u ▸v →
      ▸[]-cong-J-𝟘ᵐ (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t)
        (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)

    ⊢[]-cong″ :
      let open Erased s in
      ∀ ok →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ []-cong″ ok A t u v ∷ Id (Erased A) [ t ] ([ u ])
    ⊢[]-cong″ (inj₁ ok) = []-congⱼ′ ok
    ⊢[]-cong″ (inj₂ _)  = []-cong-Jⱼ Erased-ok

    []-cong″-[] :
      ∀ ok →
      []-cong″ ok A t u v [ σ ] PE.≡
      []-cong″ ok (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
    []-cong″-[] (inj₁ _) = PE.refl
    []-cong″-[] (inj₂ _) = []-cong-J-[]

    []-cong″-β-⇒ :
      let open Erased s in
      ∀ ok →
      Γ ⊢ t ∷ A →
      Γ ⊢ []-cong″ ok A t t rfl ⇒ rfl ∷ Id (Erased A) [ t ] ([ t ])
    []-cong″-β-⇒ (inj₁ ok) ⊢t = []-cong-β-⇒ (refl ⊢t) ok
    []-cong″-β-⇒ (inj₂ _)  ⊢t = []-cong-J-β-⇒ Erased-ok ⊢t

    []-cong′ : Term 0
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong″ ok′ (var x3) (var x2) (var x1) (var x0)

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, and η-equality is not
  -- allowed for the weak unit type unless a certain condition is
  -- satisfied, then []-cong is not supported (with any grades) for
  -- the mode 𝟙ᵐ.

  ¬-[]-cong :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    ¬ Has-[]-cong s 𝟙ᵐ q₁ q₂ q₃ q₄
  ¬-[]-cong nem Unitʷ-η→ (_ , ▸[]-cong , ⊢[]-cong) =
    case lemma
           (lemma
              (lemma
                 (lemma (idSubst , id , _ , ▸[]-cong , ⊢[]-cong) (ℕⱼ ε))
                 (zeroⱼ ε))
              (zeroⱼ ε))
           (rflⱼ (zeroⱼ ε)) of λ {
      (_ , ⊢σ , _ , ▸t , ⊢t) →
    case red-Id ⊢t of λ where
      (_ , rflₙ , ⇒*rfl) →
        case var-only-equal-to-itself (neₙ (var _)) (ne (var _)) $
             prod-cong⁻¹ (inversion-rfl-Id (⊢u-redₜ ⇒*rfl))
               .proj₂ .proj₁ of λ ()
      (_ , ne u-ne , t⇒*u) →
        neutral-not-well-resourced nem (λ _ → inhabited-consistent ⊢σ)
          u-ne (⊢u-redₜ t⇒*u)
          (usagePres*Term Unitʷ-η→ ▸t (redₜ t⇒*u)) }
    where
    lemma :
      ((σ , _) :
       ∃ λ σ → ε ⊢ˢ σ ∷ Γ ×
       ∃ λ t → 𝟘ᶜ ▸[ 𝟙ᵐ ] t × Γ ⊢ t ∷ Π 𝟘 , p ▷ A ▹ B) →
      ε ⊢ u ∷ A [ σ ] →
      (∃ λ σ → ε ⊢ˢ σ ∷ Γ ∙ A ×
       ∃ λ t → 𝟘ᶜ ▸[ 𝟙ᵐ ] t × Γ ∙ A ⊢ t ∷ B)
    lemma (_ , ⊢σ , _ , ▸t , ⊢t) ⊢u =
        consSubst _ _
      , (⊢σ , ⊢u)
      , (case red-Π ⊢t of λ where
           (_ , ne v-n , t⇒*v) →
             ⊥-elim $
             neutral-not-well-resourced nem
               (λ _ → inhabited-consistent ⊢σ) v-n (⊢u-redₜ t⇒*v)
               (usagePres*Term Unitʷ-η→ ▸t (redₜ t⇒*v))
           (lam _ v , lamₙ , t⇒*lam) →
             case inv-usage-lam
                    (usagePres*Term Unitʷ-η→ ▸t (redₜ t⇒*lam)) of λ {
               (invUsageLam ▸v 𝟘≤) →
             case inversion-lam-Π (⊢u-redₜ t⇒*lam) of λ {
               (⊢v , PE.refl , _) →
               _
             , sub ▸v (𝟘≤ ∙ ≤-reflexive (PE.sym (·-zeroʳ _)))
             , ⊢v }})
