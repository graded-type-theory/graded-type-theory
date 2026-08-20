------------------------------------------------------------------------
-- []-cong-J
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Has-box-cong.Definable.J
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
import Definition.Typed.Weakening TR as W
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
import Graded.Derived.Erased.Usage UR as ErasedU
open import Graded.Derived.Identity UR
open import Graded.Erasure.Extraction 𝕄
import Graded.Erasure.Target as T
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties UR
open import Graded.Usage.Properties.Zero-one variant UR
open import Graded.Usage.Weakening UR

open import Tools.Bool using (Bool; T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private variable
  b                                  : Bool
  n                                  : Nat
  Γ                                  : Cons _ _
  A A₁ A₂ t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ : Term _
  l l₁ l₂                            : Lvl _
  σ                                  : Subst _ _
  γ₁ γ₂ γ₃ γ₄ γ₅                     : Conₘ _
  m                                  : Mode
  s                                  : Strength
  sem                                : Some-erased-matches
  str                                : T.Strictness
  ok                                 : T _

------------------------------------------------------------------------
-- A lemma

private opaque

  -- A lemma used below.

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
    Strength → Lvl n → Term n → Term n → Term n → Term n → Term n
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
    let ▸l = ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) (▸-𝟘₀₁ ▸l)
        ▸A = ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) (▸-𝟘₀₁ ▸A)
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
    ▸-𝟘₀₁ $
    ▸subst ▸A
      (Idₘ-generalised (▸Erased (wkUsage _ ▸l) (wkUsage _ ▸A))
         (▸[] (wkUsage (step id) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t))) (▸[] var)
         (λ _ → begin
            γ₂ ∧ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            γ₂ ∧ᶜ 𝟘ᶜ ∙ 𝟘      ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙ ≤-refl ⟩
            𝟘ᶜ                ∎)
         (λ _ → begin
            γ₂ ∧ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            γ₂ ∧ᶜ 𝟘ᶜ ∙ 𝟘      ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙ ≤-refl ⟩
            𝟘ᶜ                ≈˘⟨ ≈ᶜ-trans (+ᶜ-congˡ (+ᶜ-identityʳ _)) (+ᶜ-identityʳ _) ⟩
            𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ    ∎))
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
    let ⊢A , ⊢t , _ = inversion-Id (wf-⊢ ⊢v)
        ⊢wk1-l      = W.wk₁ ⊢A ⊢l
    in
    PE.subst (_⊢_∷_ _ _) Id-[]₀≡ $
    ⊢subst
      (Idⱼ′ ([]ⱼ ok ⊢wk1-l (W.wk₁ ⊢A ⊢t))
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
    let ⊢A , ⊢t , _ = wf-⊢ t≡t′
        ⊢wk1-l      = W.wk₁ ⊢A ⊢l
    in
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    conv
      (subst-⇒′
         (Idⱼ′ ([]ⱼ ok ⊢wk1-l (W.wk₁ ⊢A ⊢t))
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
          []-cong′ ok ⊢l (refl ⊢t))
         (PE.subst₃ (_⊢_≡_∷_ _) (PE.sym []-[]) (PE.sym []-[])
            (PE.trans (PE.sym $ wk1-sgSubst _ _) $
             PE.cong _[ _ ]₀ wk-Erased) $
          []-cong′ ok ⊢l t≡t′))
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
    let ⊢l₁ , _ = wf-⊢ l₁≡l₂
        ⊢A₁ , _ = wf-⊢ A₁≡A₂
        ⊢wk1-l₁ = W.wk₁ ⊢A₁ ⊢l₁
    in
    PE.subst (_⊢_≡_∷_ _ _ _) Id-[]₀≡ $
    subst-cong A₁≡A₂
      (Id-cong
         (Erased-cong ok (W.wk₁ ⊢A₁ l₁≡l₂)
            (W.wk₁ ⊢A₁ A₁≡A₂))
         ([]-cong′ ok ⊢wk1-l₁ (W.wk₁ ⊢A₁ t₁≡t₂))
         (refl ([]ⱼ ok ⊢wk1-l₁ (var₀ ⊢A₁))))
      t₁≡t₂ u₁≡u₂ v₁≡v₂
      (_⊢_≡_∷_.refl $
       PE.subst (_⊢_∷_ _ _) (PE.sym Id-[]₀≡) $
       rflⱼ ([]ⱼ ok ⊢l₁ (wf-⊢ t₁≡t₂ .proj₂ .proj₁)))

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
    let ⊢A , ⊢t , _ = inversion-Id (wf-⊢ (subsetTerm v₁⇒v₂) .proj₁)
        ⊢wk1-l      = W.wk₁ ⊢A ⊢l
    in
    PE.subst (_⊢_⇒_∷_ _ _ _) Id-[]₀≡ $
    subst-subst
      (Idⱼ′ ([]ⱼ ok ⊢wk1-l (W.wk₁ ⊢A ⊢t))
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
