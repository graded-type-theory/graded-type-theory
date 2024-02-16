------------------------------------------------------------------------
-- Some discussion of under what circumstances a []-cong combinator or
-- term former can be defined
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

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
open import Definition.Typed.Reasoning.Reduction TR
import Definition.Typed.Weakening TR as W
open import Definition.Untyped M as U hiding (_∷_)
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Erased.Typed TR as ET hiding ([]-cong′)
import Graded.Derived.Erased.Untyped 𝕄 as Erased
import Graded.Derived.Erased.Usage 𝕄 UR as ErasedU
open import Graded.Derived.Identity TR UR
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

private variable
  n                                 : Nat
  Γ                                 : Con Term _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ                                 : Subst _ _
  p q₁ q₂ q₃ q₄                     : M
  γ₁ γ₂ γ₃ γ₄                       : Conₘ _
  s                                 : Strength
  ok                                : T _

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
-- []-cong₀

opaque

  -- A variant of []-cong which can be used when the mode is 𝟘ᵐ[ ok ].
  -- Note that the lemmas in this section do not include assumptions
  -- of the form "[]-cong-allowed s".

  []-cong₀ : Strength → Term n → Term n → Term n → Term n → Term n
  []-cong₀ s A t u v =
    subst A (Id (Erased (wk1 A)) [ wk1 t ] ([ var x0 ])) t u v rfl
    where
    open Erased s

opaque
  unfolding []-cong₀

  -- A usage rule for []-cong₀.

  ▸[]-cong₀ :
    γ₁ ▸[ 𝟘ᵐ[ ok ] ] A →
    γ₂ ▸[ 𝟘ᵐ[ ok ] ] t →
    γ₃ ▸[ 𝟘ᵐ[ ok ] ] u →
    γ₄ ▸[ 𝟘ᵐ[ ok ] ] v →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] []-cong₀ s A t u v
  ▸[]-cong₀ {s} ▸A ▸t ▸u ▸v =
    case ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A of λ
      ▸A →
    ▸-𝟘 $
    ▸subst ▸A
      (Idₘ′ (▸Erased (wkUsage (step id) ▸A))
         (▸[] (wkUsage (step id) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t))) (▸[] var)
         (begin
            𝟘ᶜ ∙ 𝟘 · ω  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ          ∎)
         (begin
            𝟘ᶜ ∙ 𝟘 · ω  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ          ≈˘⟨ +ᶜ-identityʳ _ ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ    ∎))
      ▸t ▸u ▸v rflₘ
    where
    open ErasedU s
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque
  unfolding []-cong₀

  -- A typing rule for []-cong₀.

  []-cong₀ⱼ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ []-cong₀ s A t u v ∷ Id (Erased A) [ t ] ([ u ])
  []-cong₀ⱼ ok ⊢v =
    case inversion-Id (syntacticTerm ⊢v) of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_∷_ _ _) Id-[]₀≡ $
    ⊢subst (Idⱼ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A))) ⊢v
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢t))

opaque
  unfolding []-cong₀

  -- A reduction rule for []-cong₀.

  []-cong₀-β-⇒ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ t ∷ A →
    Γ ⊢ []-cong₀ s A t t rfl ⇒ rfl ∷ Id (Erased A) [ t ] ([ t ])
  []-cong₀-β-⇒ ok ⊢t =
    case syntacticTerm ⊢t of λ
      ⊢A →
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    subst-⇒ (Idⱼ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A))) ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢t))

opaque

  -- An equality rule for []-cong₀.

  []-cong₀-β-≡ :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ t ∷ A →
    Γ ⊢ []-cong₀ s A t t rfl ≡ rfl ∷ Id (Erased A) [ t ] ([ t ])
  []-cong₀-β-≡ ok ⊢t = subsetTerm ([]-cong₀-β-⇒ ok ⊢t)

opaque
  unfolding []-cong₀

  -- An equality rule for []-cong₀.

  []-cong₀-cong :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ []-cong₀ s A₁ t₁ u₁ v₁ ≡ []-cong₀ s A₂ t₂ u₂ v₂ ∷
      Id (Erased A₁) [ t₁ ] ([ u₁ ])
  []-cong₀-cong ok A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
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
  unfolding []-cong₀

  -- A reduction rule for []-cong₀.

  []-cong₀-subst :
    let open Erased s in
    Erased-allowed s →
    Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u →
    Γ ⊢ []-cong₀ s A t u v₁ ⇒ []-cong₀ s A t u v₂ ∷
      Id (Erased A) [ t ] ([ u ])
  []-cong₀-subst ok v₁⇒v₂ =
    case inversion-Id (syntacticEqTerm (subsetTerm v₁⇒v₂) .proj₁) of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    subst-subst (Idⱼ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A)))
      v₁⇒v₂
      (PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢t))

opaque
  unfolding []-cong₀

  -- A substitution lemma for []-cong₀.

  []-cong₀-[] :
    []-cong₀ s A t u v [ σ ] PE.≡
    []-cong₀ s (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
  []-cong₀-[] {s} {A} {t} {u} {v} {σ} =
    subst A (Id (Erased (wk1 A)) [ wk1 t ] ([ var x0 ])) t u v rfl
      U.[ σ ]                                                             ≡⟨ subst-[] ⟩

    subst (A U.[ σ ])
      (Id (Erased (wk1 A U.[ liftSubst σ ])) [ wk1 t U.[ liftSubst σ ] ]
         ([ var x0 ]))
      (t U.[ σ ]) (u U.[ σ ]) (v U.[ σ ]) rfl                             ≡⟨ PE.cong₅ (subst _)
                                                                               (PE.cong₃ Id
                                                                                  (PE.cong Erased (wk1-liftSubst A))
                                                                                  (PE.cong [_] (wk1-liftSubst t))
                                                                                  PE.refl)
                                                                               PE.refl PE.refl PE.refl PE.refl ⟩
    subst (A U.[ σ ])
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

-- The property of supporting a []-cong combinator that computes
-- correctly.

Has-computing-[]-cong : Strength → Mode → M → M → M → M → Set a
Has-computing-[]-cong s m q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s m q₁ q₂ q₃ q₄) →
  ∀ n (Γ : Con Term n) (A t : Term n) →
  Γ ⊢ A ∷ U →
  Γ ⊢ t ∷ A →
  Γ ⊢ wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ⇒* rfl ∷
    Id (Erased A) ([ t ]) ([ t ])

opaque

  -- []-cong is supported for the strength s and the mode 𝟘ᵐ[ ok ],
  -- for grades for which "Π 𝟘" are allowed, if Erased is allowed
  -- for s.

  []-cong-𝟘ᵐ :
    Erased-allowed s →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Has-computing-[]-cong s 𝟘ᵐ[ ok ] q₁ q₂ q₃ q₄
  []-cong-𝟘ᵐ {s} ok ok₁ ok₂ ok₃ ok₄ =
    case lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
         []-cong₀ⱼ ok (var₀ ⊢Id-2-1-0) of λ
      ⊢[]-cong₀′ →
      ( []-cong₀′
      , (lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub (▸[]-cong₀ var var var var) $ begin
           ε ∙ 𝟘 · 𝟘 ∙ 𝟘 · 𝟘 ∙ 𝟘 · 𝟘 ∙ 𝟘 · 𝟘  ≈⟨ ε ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                                 ∎)
      , ⊢[]-cong₀′
      )
    , λ _ _ A t ⊢A ⊢t →
        wk wk₀ []-cong₀′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl        ⇒*⟨ β-red-⇒₄ (W.wkTerm W.wk₀∷⊇ (wfTerm ⊢A) ⊢[]-cong₀′) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩

        wk (liftn wk₀ 4)
          ([]-cong₀ s (var x3) (var x2) (var x1) (var x0))
          [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ]   ≡⟨ PE.trans (subst-wk ([]-cong₀ _ _ _ _ _))
                                                                         []-cong₀-[] ⟩⇒

        []-cong₀ s A t t rfl                                          ⇒⟨ []-cong₀-β-⇒ ok ⊢t ⟩∎

        rfl                                                           ∎
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    []-cong₀′ : Term 0
    []-cong₀′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong₀ s (var x3) (var x2) (var x1) (var x0)

opaque

  -- If the []-cong primitive is allowed, then []-cong is supported
  -- for 𝟙ᵐ and grades for which "Π 𝟘" are allowed.

  []-cong→[]-cong :
    []-cong-allowed s →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Has-computing-[]-cong s 𝟙ᵐ q₁ q₂ q₃ q₄
  []-cong→[]-cong {s} ok ok₁ ok₂ ok₃ ok₄ =
    case lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
         []-congⱼ′ ok (var₀ ⊢Id-2-1-0) of λ {
      ⊢[]-cong →
      ( []-cong′
      , (lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub ([]-congₘ var var var var) $ begin
           ε ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ε ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                                 ∎)
      , ⊢[]-cong
      )
    , λ _ _ A t ⊢A ⊢t →
        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl  ⇒*⟨ β-red-⇒₄ (W.wkTerm W.wk₀∷⊇ (wfTerm ⊢A) ⊢[]-cong) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩
        []-cong s A t t rfl                                    ⇒⟨ []-cong-β-⇒ (refl ⊢t) ok ⟩∎
        rfl                                                    ∎ }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

    []-cong′ : Term 0
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong s (var x3) (var x2) (var x1) (var x0)

opaque

  -- If erased matches are allowed for J (when the mode is 𝟙ᵐ) and the
  -- type Erased is allowed, then []-cong is supported for 𝟙ᵐ and
  -- grades for which "Π 𝟘" are allowed.

  J₀→[]-cong :
    erased-matches-for-J 𝟙ᵐ ≢ none →
    Erased-allowed s →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟘 q₃ →
    Π-allowed 𝟘 q₄ →
    Has-computing-[]-cong s 𝟙ᵐ q₁ q₂ q₃ q₄
  J₀→[]-cong {s} J₀-ok Erased-ok ok₁ ok₂ ok₃ ok₄ =
    case lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ $
         Jⱼ′
           (Idⱼ ([]ⱼ Erased-ok (var₄ ⊢Id-4-3-0))
              ([]ⱼ Erased-ok (var₁ ⊢Id-4-3-0)))
           (rflⱼ ([]ⱼ Erased-ok (var₂ ⊢Id-2-1-0)))
           (var₀ ⊢Id-2-1-0) of λ {
      ⊢[]-cong →
      ( []-cong′
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub (J₀ₘ (≢none→≡all J₀-ok) var var ▸Id rflₘ var var) $ begin
           ε ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ε ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                                 ∎)
      , ⊢[]-cong
      )
    , λ _ _ A t ⊢A ⊢t →
        case Idⱼ (W.wkTerm₁ (univ ⊢A) ⊢t) (var₀ (univ ⊢A)) of λ {
          ⊢Id →
        case PE.cong₂
               (λ A′ t′ → Id (Erased A′) ([ t′ ]) ([ t ]))
               (PE.trans (wk2-tail A) (subst-id A))
               (PE.trans (wk2-tail t) (subst-id t)) of λ {
          lemma →
        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl  ⇒*⟨ β-red-⇒₄ (W.wkTerm W.wk₀∷⊇ (wfTerm ⊢A) ⊢[]-cong) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩

        J 𝟘 𝟘 A t
          (Id (Erased (wk1 (wk1 A))) ([ wk1 (wk1 t) ])
             ([ var x1 ]))
          rfl t rfl                                            ⇒⟨ PE.subst (_⊢_⇒_∷_ _ _ _) lemma $
                                                                  J-β-⇒ (refl ⊢t)
                                                                    (Idⱼ
                                                                       ([]ⱼ Erased-ok $
                                                                        W.wkTerm₁ ⊢Id (W.wkTerm₁ (univ ⊢A) ⊢t))
                                                                       ([]ⱼ Erased-ok (var₁ ⊢Id)))
                                                                    (PE.subst (_⊢_∷_ _ _) (PE.sym lemma) $
                                                                     rflⱼ ([]ⱼ Erased-ok ⊢t)) ⟩∎
        rfl                                                    ∎ }}}
    where
    open Erased s
    open ErasedU s

    []-cong′ : Term 0
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      J 𝟘 𝟘 (var x3) (var x2)
        (Id (Erased (var x5)) ([ var x4 ]) ([ var x1 ]))
        rfl (var x1) (var x0)

    lemma : 𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ≈ᶜ 𝟘ᶜ {n = 6}
    lemma = ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _

    ▸Id :
      𝟘ᶜ {n = 4} ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ▸[ 𝟘ᵐ? ]
        Id (Erased (var x5)) ([ var x4 ]) ([ var x1 ])
    ▸Id = Idₘ′ (▸Erased var) (▸[] var) (▸[] var)
      (begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ lemma ⟩
         𝟘ᶜ                              ∎)
      (begin
         𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ lemma ⟩
         𝟘ᶜ                              ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ                        ∎)
      where
      open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- If the modality's zero is well-behaved and erased matches
  -- (including the []-cong primitive) are not allowed, then []-cong
  -- is not supported (with any grades) for the mode 𝟙ᵐ.

  ¬-[]-cong :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    ¬ Has-[]-cong s 𝟙ᵐ q₁ q₂ q₃ q₄
  ¬-[]-cong nem (_ , ▸[]-cong , ⊢[]-cong) =
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
        neutral-not-well-resourced nem (inhabited-consistent ⊢σ) u-ne
          (⊢u-redₜ t⇒*u) (usagePres*Term ▸t (redₜ t⇒*u)) }
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
             neutral-not-well-resourced nem (inhabited-consistent ⊢σ)
               v-n (⊢u-redₜ t⇒*v) (usagePres*Term ▸t (redₜ t⇒*v))
           (lam _ v , lamₙ , t⇒*lam) →
             case inv-usage-lam (usagePres*Term ▸t (redₜ t⇒*lam)) of λ {
               (invUsageLam ▸v 𝟘≤) →
             case inversion-lam-Π (⊢u-redₜ t⇒*lam) of λ {
               (⊢v , PE.refl , _) →
               _
             , sub ▸v (𝟘≤ ∙ ≤-reflexive (PE.sym (·-zeroʳ _)))
             , ⊢v }})
