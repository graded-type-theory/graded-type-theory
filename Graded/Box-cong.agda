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
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Syntactic TR
import Definition.Typed.Weakening TR as W
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M as U
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Erased.Typed TR as ET hiding ([]-cong′)
open import Graded.Derived.Erased.Typed.Inversion TR
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
  n                                      : Nat
  Γ                                      : Con Term _
  A A₁ A₂ B t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ w : Term _
  σ                                      : Subst _ _
  p q q₁ q₂ q₃ q₄                        : M
  γ₁ γ₂ γ₃ γ₄                            : Conₘ _
  m                                      : Mode
  s                                      : Strength
  l                                      : Universe-level
  sem                                    : Some-erased-matches
  ok                                     : T _

------------------------------------------------------------------------
-- Some lemmas

private opaque

  -- Some lemmas used below.

  ⊢Id-2-1-0 : ε ∙ U l ∙ var x0 ∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0 = Idⱼ′ (var₁ ⊢1) (var₀ ⊢1)
    where
    ⊢1 : ε ∙ U l ∙ var x0 ⊢ var x1
    ⊢1 = univ (var₁ (univ (var₀ (Uⱼ ε))))

  ⊢Id-4-3-0 :
    ε ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ∙ var x3 ⊢
    Id (var x4) (var x3) (var x0)
  ⊢Id-4-3-0 = Idⱼ′ (var₃ ⊢3) (var₀ ⊢3)
    where
    ⊢3 :
      ε ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢ var x3
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

  -- A variant of []-cong that can be used when erased matches are
  -- available for J, when the mode is 𝟘ᵐ[ ok ], or when the modality
  -- is trivial. Note that the lemmas in this section do not include
  -- assumptions of the form "[]-cong-allowed s".

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

  -- A usage rule for []-cong-J that can be used if the modality is
  -- trivial.

  ▸[]-cong-J-trivial :
    Trivial →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ▸[ 𝟘ᵐ? ] u →
    γ₄ ▸[ 𝟘ᵐ? ] v →
    𝟘ᶜ ▸[ m ] []-cong-J s A t u v
  ▸[]-cong-J-trivial {s} trivial ▸A ▸t ▸u ▸v =
    flip sub (≈ᶜ-trivial trivial) $
    ▸-trivial trivial $
    ▸subst {γ₂ = 𝟘ᶜ}
      ▸A
      (Idₘ-generalised (▸Erased (wkUsage (step id) ▸A))
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
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ []-cong-J s A t u v ∷ Id (Erased A) [ t ] ([ u ])
  []-cong-Jⱼ ok ⊢v =
    case inversion-Id (syntacticTerm ⊢v) of λ
      (⊢A , ⊢t , _) →
    PE.subst (_⊢_∷_ _ _) Id-[]₀≡ $
    ⊢subst (Idⱼ′ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A))) ⊢v
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
      (subst-⇒′ (Idⱼ′ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A)))
         t≡t′
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
    subst-subst (Idⱼ′ ([]ⱼ ok (W.wkTerm₁ ⊢A ⊢t)) ([]ⱼ ok (var₀ ⊢A)))
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
-- grades) for a certain mode and universe level.
--
-- Note that, unlike the []-cong primitive, the first argument must be
-- a type in U l for some l.

Has-[]-cong : Strength → Mode → Universe-level → M → M → M → M → Set a
Has-[]-cong s m l q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ ([]-cong : Term 0) →
  ε ▸[ m ] []-cong ×
  ε ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ U l ▹
    Π 𝟘 , q₂ ▷ var x0 ▹
    Π 𝟘 , q₃ ▷ var x1 ▹
    Π 𝟘 , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong :
  Strength → Mode → Universe-level → M → M → M → M → Set a
Has-computing-[]-cong s m l q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s m l q₁ q₂ q₃ q₄) →
  ∀ n (Γ : Con Term n) (A t : Term n) →
  Γ ⊢ A ∷ U l →
  Γ ⊢ t ∷ A →
  Γ ⊢ wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡ rfl ∷
    Id (Erased A) ([ t ]) ([ t ])

opaque

  -- []-cong is supported for the strength s, the mode m, and the
  -- universe level l, for grades for which "Π 𝟘" are allowed, if
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
    Has-computing-[]-cong s m l q₁ q₂ q₃ q₄
  []-cong⊎J⊎𝟘ᵐ⊎Trivial→[]-cong {s} {m} ok ok₁ ok₂ ok₃ ok₄ =
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
        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl        ⇒*⟨ β-red-⇒₄ (W.wkTerm (W.wk₀∷ʷ⊇ (wfTerm ⊢A)) ⊢[]-cong) ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢

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
    ▸[]-cong″ (inj₁ (_ , ok))               = λ ▸A ▸t ▸u ▸v →
      []-congₘ ▸A ▸t ▸u ▸v ok
    ▸[]-cong″ (inj₂ (inj₁ (_ , ≡not-none))) = ▸[]-cong-J ≡not-none
    ▸[]-cong″ (inj₂ (inj₂ (inj₁ (_ , PE.refl)))) = λ ▸A ▸t ▸u ▸v →
      ▸[]-cong-J-𝟘ᵐ (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t)
        (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸[]-cong″ (inj₂ (inj₂ (inj₂ trivial))) = ▸[]-cong-J-trivial trivial

    ⊢[]-cong″ :
      let open Erased s in
      ∀ ok →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ []-cong″ ok A t u v ∷ Id (Erased A) [ t ] ([ u ])
    ⊢[]-cong″ (inj₁ (ok , _)) = []-congⱼ′ ok
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
    []-cong″-β-⇒ (inj₁ (ok , _)) ⊢t = []-cong-β-⇒ (refl ⊢t) ok
    []-cong″-β-⇒ (inj₂ _)  ⊢t = []-cong-J-β-⇒ Erased-ok ⊢t

    []-cong′ : Term 0
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong″ ok′ (var x3) (var x2) (var x1) (var x0)

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, and η-equality is not
  -- allowed for weak unit types unless a certain condition is
  -- satisfied, then []-cong is not supported for the mode 𝟙ᵐ.

  ¬-[]-cong :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    ¬ Has-[]-cong s 𝟙ᵐ l q₁ q₂ q₃ q₄
  ¬-[]-cong nem Unitʷ-η→ (_ , ▸[]-cong , ⊢[]-cong) =
    case lemma
           (lemma
              (lemma
                 (lemma (idSubst , id , _ , ▸[]-cong , ⊢[]-cong) ⊢A)
                 ⊢t)
              ⊢t)
           (rflⱼ ⊢t) of λ {
      (_ , ⊢σ , _ , ▸t , ⊢t) →
    case red-Id ⊢t of λ where
      (_ , rflₙ , ⇒*rfl) →
        case var-only-equal-to-itself (neₙ (var _)) (ne (var _)) $
             prod-cong⁻¹
               (inversion-rfl-Id $
                wf-⊢≡∷ (subset*Term ⇒*rfl) .proj₂ .proj₂)
               .proj₂ .proj₁ of λ ()
      (_ , ne u-ne , t⇒*u) →
        neutral-not-well-resourced nem (λ _ → inhabited-consistent ⊢σ)
          u-ne (wf-⊢≡∷ (subset*Term t⇒*u) .proj₂ .proj₂)
          (usagePres*Term Unitʷ-η→ ▸t t⇒*u) }
    where
    A′ : Universe-level → Term 0
    A′ 0      = ℕ
    A′ (1+ l) = U l

    t″ : Universe-level → Term 0
    t″ 0      = zero
    t″ 1      = ℕ
    t″ (2+ l) = U l

    ⊢A : ε ⊢ A′ l ∷ U l
    ⊢A {l = 0}    = ℕⱼ ε
    ⊢A {l = 1+ _} = Uⱼ ε

    ⊢t : ε ⊢ t″ l ∷ A′ l
    ⊢t {l = 0}    = zeroⱼ ε
    ⊢t {l = 1}    = ℕⱼ ε
    ⊢t {l = 2+ _} = Uⱼ ε

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
               (λ _ → inhabited-consistent ⊢σ) v-n
               (wf-⊢≡∷ (subset*Term t⇒*v) .proj₂ .proj₂)
               (usagePres*Term Unitʷ-η→ ▸t t⇒*v)
           (lam _ v , lamₙ , t⇒*lam) →
             case inv-usage-lam
                    (usagePres*Term Unitʷ-η→ ▸t t⇒*lam) of λ {
               (invUsageLam ▸v 𝟘≤) →
             case inversion-lam-Π
                    (wf-⊢≡∷ (subset*Term t⇒*lam) .proj₂ .proj₂) of λ {
               (⊢v , PE.refl , _) →
               _
             , sub ▸v (𝟘≤ ∙ ≤-reflexive (PE.sym (·-zeroʳ _)))
             , ⊢v }})

------------------------------------------------------------------------
-- Has-weaker-[]-cong

-- A "weaker" variant of Has-[]-cong.

Has-weaker-[]-cong :
  Strength → Mode → Universe-level → M → M → M → M → Set a
Has-weaker-[]-cong s m l q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ ([]-cong : Term 0) →
  ε ▸[ m ] []-cong ×
  ε ⊢ []-cong ∷
    Π ω , q₁ ▷ U l ▹
    Π ω , q₂ ▷ var x0 ▹
    Π ω , q₃ ▷ var x1 ▹
    Π 𝟘 , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x3)) [ var x2 ] ([ var x1 ])

-- A "weaker" variant of Has-computing-[]-cong.

Has-weaker-computing-[]-cong :
  Strength → Mode → Universe-level → M → M → M → M → Set a
Has-weaker-computing-[]-cong s m l q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-weaker-[]-cong s m l q₁ q₂ q₃ q₄) →
  ∀ n (Γ : Con Term n) (A t : Term n) →
  Γ ⊢ A ∷ U l →
  Γ ⊢ t ∷ A →
  Γ ⊢ wk wk₀ []-cong′ ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∘⟨ ω ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡ rfl ∷
    Id (Erased A) [ t ] ([ t ])

opaque

  -- Has-weaker-[]-cong is no stronger than Has-[]-cong (given certain
  -- assumptions).

  Has-[]-cong→Has-weaker-[]-cong :
    (Π-allowed 𝟘 q₁ → Π-allowed ω q₁) →
    (Π-allowed 𝟘 q₂ → Π-allowed ω q₂) →
    (Π-allowed 𝟘 q₃ → Π-allowed ω q₃) →
    Has-[]-cong s m l q₁ q₂ q₃ q₄ →
    Has-weaker-[]-cong s m l q₁ q₂ q₃ q₄
  Has-[]-cong→Has-weaker-[]-cong
    {q₁} {q₂} {q₃} {s} {m} {l} {q₄}
    hyp₁ hyp₂ hyp₃ ([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    []-cong″ , ▸[]-cong″ , ⊢[]-cong″
    where
    open Erased s

    []-cong″ : Term 0
    []-cong″ =
       lam ω $ lam ω $ lam ω $ lam 𝟘 $
       wk wk₀ []-cong′
         ∘⟨ 𝟘 ⟩ var x3 ∘⟨ 𝟘 ⟩ var x2 ∘⟨ 𝟘 ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0

    ▸[]-cong″ : ε ▸[ m ] []-cong″
    ▸[]-cong″ =
      lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub ((((wkUsage wk₀ ▸[]-cong′ ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ var) $
      (begin
         ε ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · 𝟘  ≤⟨ ε ∙ lemma ∙ lemma ∙ lemma ∙ ≤-reflexive (·-zeroʳ _) ⟩

         𝟘ᶜ                                                 ≈˘⟨ ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                ≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _ ⟩
         (((𝟘ᶜ +ᶜ 𝟘 ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
           𝟘 ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
          𝟘 ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝)                        ∎)
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

    ⊢[]-cong″ :
      ε ⊢ []-cong″ ∷
        Π ω , q₁ ▷ U l ▹
        Π ω , q₂ ▷ var x0 ▹
        Π ω , q₃ ▷ var x1 ▹
        Π 𝟘 , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (var x3)) ([ var x2 ]) ([ var x1 ])
    ⊢[]-cong″ =
      case inversion-ΠΣ $ syntacticTerm ⊢[]-cong′ of λ
        (_ , ⊢Π , ok₁) →
      case inversion-ΠΣ ⊢Π of λ
        (_ , ⊢Π , ok₂) →
      case inversion-ΠΣ ⊢Π of λ
        (_ , ⊢Π , ok₃) →
      case inversion-ΠΣ ⊢Π of λ
        (_ , _ , ok₄) →
      lamⱼ′ (hyp₁ ok₁) $
      lamⱼ′ (hyp₂ ok₂) $
      lamⱼ′ (hyp₃ ok₃) $
      lamⱼ′ ok₄ $
      flip _∘ⱼ_ (var₀ ⊢Id) $
      flip _∘ⱼ_ (var₁ ⊢Id) $
      flip _∘ⱼ_ (var₂ ⊢Id) $
      flip _∘ⱼ_ (var₃ ⊢Id) $
      W.wkTerm (W.wk₀∷ʷ⊇ (∙ ⊢Id)) ⊢[]-cong′
      where
      ⊢1 : ε ∙ U l ∙ var x0 ⊢ var x1
      ⊢1 = univ (var₁ (univ (var₀ (Uⱼ ε))))

      ⊢Id : ε ∙ U l ∙ var x0 ∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
      ⊢Id = Idⱼ′ (var₁ ⊢1) (var₀ ⊢1)

opaque
  unfolding Has-[]-cong→Has-weaker-[]-cong

  -- Has-weaker-computing-[]-cong is no stronger than
  -- Has-computing-[]-cong (given certain assumptions).

  Has-computing-[]-cong→Has-weaker-computing-[]-cong :
    (Π-allowed 𝟘 q₁ → Π-allowed ω q₁) →
    (Π-allowed 𝟘 q₂ → Π-allowed ω q₂) →
    (Π-allowed 𝟘 q₃ → Π-allowed ω q₃) →
    Has-computing-[]-cong s m l q₁ q₂ q₃ q₄ →
    Has-weaker-computing-[]-cong s m l q₁ q₂ q₃ q₄
  Has-computing-[]-cong→Has-weaker-computing-[]-cong
    hyp₁ hyp₂ hyp₃ (has-[]-cong@([]-cong′ , _ , _) , []-cong′≡) =
    let has-[]-cong′@(_ , _ , ⊢[]-cong″) =
          Has-[]-cong→Has-weaker-[]-cong hyp₁ hyp₂ hyp₃ has-[]-cong
    in
      has-[]-cong′
    , λ _ _ A t ⊢A ⊢t →
        wk wk₀
          (lam ω $ lam ω $ lam ω $ lam 𝟘 $
           wk wk₀ []-cong′
             ∘⟨ 𝟘 ⟩ var x3 ∘⟨ 𝟘 ⟩ var x2 ∘⟨ 𝟘 ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0)
          ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∘⟨ ω ⟩ t ∘⟨ 𝟘 ⟩ rfl                        ⇒*⟨ β-red-⇒₄ (W.wkTerm (W.wk₀∷ʷ⊇ (wfTerm ⊢A)) ⊢[]-cong″)
                                                                             ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        (wk (liftn wk₀ 4) (wk wk₀ []-cong′)
           [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ])
          ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl                        ≡⟨ PE.cong (λ []-cong → []-cong ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _) $
                                                                          PE.trans
                                                                            (PE.cong _[ _ ] $
                                                                             PE.trans (wk-comp _ _ []-cong′) $
                                                                             PE.cong (flip wk _) $
                                                                             liftn-wk₀-•-wk₀ 4) $
                                                                          PE.trans (subst-wk []-cong′) $
                                                                          PE.sym $ wk≡subst _ _ ⟩⊢≡

        wk wk₀ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl          ≡⟨ []-cong′≡ _ _ _ _ ⊢A ⊢t ⟩⊢∎

        rfl                                                            ∎

opaque

  -- Has-weaker-[]-cong is at least as strong as Has-[]-cong (given
  -- certain assumptions).

  Has-weaker-[]-cong→Has-[]-cong :
    (¬ T 𝟘ᵐ-allowed → Trivial) →
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ? (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (Π-allowed ω q₁ → Π-allowed 𝟘 q₁) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃) →
    Has-weaker-[]-cong s m l q₁ q₂ q₃ q₄ →
    Has-[]-cong s m l q₁ q₂ q₃ q₄
  Has-weaker-[]-cong→Has-[]-cong
    {s} {q₁} {q₂} {q₃} {m} {l} {q₄}
    trivial prodrec-ok hyp₁ hyp₂ hyp₃
    ([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    []-cong″ , ▸[]-cong″ , ⊢[]-cong″
    where
    open Erased s
    open ErasedU s

    []-cong″ : Term 0
    []-cong″ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      cong 𝟘 (Erased (Erased (var x3))) [ [ var x2 ] ] [ [ var x1 ] ]
        (Erased (var x3))
        (mapᴱ (Erased (var x4)) (erased (var x5) (var x0)) (var x0))
        (wk wk₀ []-cong′ ∘⟨ ω ⟩ Erased (var x3) ∘⟨ ω ⟩ [ var x2 ]
           ∘⟨ ω ⟩ [ var x1 ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1) (Erased (var x3))
                    [ var x0 ] (var x0))

    opaque

      ⊢[]-cong″ :
        ε ⊢ []-cong″ ∷
        Π 𝟘 , q₁ ▷ U l ▹
        Π 𝟘 , q₂ ▷ var x0 ▹
        Π 𝟘 , q₃ ▷ var x1 ▹
        Π 𝟘 , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong″ =
        case inversion-ΠΣ $ syntacticTerm ⊢[]-cong′ of λ
          (_ , ⊢Π , ok₁) →
        case inversion-ΠΣ ⊢Π of λ
          (_ , ⊢Π , ok₂) →
        case inversion-ΠΣ ⊢Π of λ
          (_ , ⊢Π , ok₃) →
        case inversion-ΠΣ ⊢Π of λ
          (_ , ⊢Id , ok₄) →
        case inversion-Erased _ $ inversion-Id ⊢Id .proj₁ of λ
          (_ , Erased-ok) →
        case _⊢_.univ $ var₁ $ _⊢_.univ $ var₀ $ Uⱼ ε of λ
          ⊢1 →
        case Idⱼ′ (var₁ ⊢1) (var₀ ⊢1) of λ
          ⊢Id →
        case _⊢_.univ $ var₃ ⊢Id of λ
          ⊢3 →
        case Erasedⱼ Erased-ok ⊢3 of λ
          ⊢Erased-3 →
        case Erasedⱼ Erased-ok ⊢Erased-3 of λ
          ⊢Erased-Erased-3 →
        case
          (∀ t →
           ε ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢
             t ∷ var x3 →
           ε ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢
             mapᴱ (Erased (var x4)) (erased (var x5) (var x0)) (var x0)
               [ [ [ t ] ] ]₀ ≡
             [ t ] ∷
             Erased (var x3)) ∋
          (λ t ⊢t →
             mapᴱ (Erased (var x4)) (erased (var x5) (var x0)) (var x0)
               [ [ [ t ] ] ]₀                                            ≡⟨ PE.trans mapᴱ-[] $
                                                                            PE.cong (flip (mapᴱ _) _) erased-[] ⟩⊢≡

             mapᴱ (Erased (var x3)) (erased (var x4) (var x0))
               ([ [ t ] ])                                               ≡⟨ mapᴱ-β Erased-ok (erasedⱼ $ var₀ ⊢Erased-3) ([]ⱼ Erased-ok ⊢t) ⟩⊢

             [ erased (var x4) (var x0) [ [ t ] ]₀ ]                     ≡⟨ PE.cong [_] erased-[] ⟩⊢≡

             [ erased (var x3) ([ t ]) ]                                 ≡⟨ ET.[]-cong′ Erased-ok $
                                                                            Erased-β Erased-ok ⊢t ⟩⊢∎
             [ t ]                                                       ∎)
        of λ
          lemma →
        lamⱼ′ (hyp₁ ok₁) $
        lamⱼ′ (hyp₂ ok₂) $
        lamⱼ′ (hyp₃ ok₃) $
        lamⱼ′ ok₄ $
        _⊢_∷_.conv
          (⊢cong
             (⊢mapᴱ
                (erasedⱼ $ var₀ $ Erasedⱼ Erased-ok $
                 _⊢_.univ $ var₄ ⊢Erased-Erased-3) $
              var₀ ⊢Erased-Erased-3) $
           flip _∘ⱼ_
             (⊢cong ([]ⱼ Erased-ok $ var₀ ⊢3) $
              var₀ ⊢Id) $
           flip _∘ⱼ_ ([]ⱼ Erased-ok $ var₁ ⊢Id) $
           flip _∘ⱼ_ ([]ⱼ Erased-ok $ var₂ ⊢Id) $
           flip _∘ⱼ_ (Erasedⱼ-U Erased-ok $ var₃ ⊢Id) $
           W.wkTerm (W.wk₀∷ʷ⊇ (wf ⊢Erased-Erased-3)) ⊢[]-cong′) $
        Id-cong (refl ⊢Erased-3) (lemma _ (var₂ ⊢Id))
          (lemma _ (var₁ ⊢Id))

      ▸[]-cong″ : ε ▸[ m ] []-cong″
      ▸[]-cong″ =
        lamₘ $ lamₘ $ lamₘ $ lamₘ $
        sub
          (▸cong (▸Erased (▸Erased var)) (▸[] (▸[] var))
             (▸[] (▸[] var)) (▸Erased var)
             (sub
                (▸mapᴱ′ (λ _ → trivial) (λ _ → trivial′) prodrec-ok
                   (λ _ → _ , ▸Erased var)
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
                (▸cong var var var (▸Erased var)
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
              flip _∘ₘ_ (▸Erased var) $
              wkUsage wk₀ ▸[]-cong′)
             (λ _ → begin
                𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                𝟘ᶜ              ∎)
             (λ _ → begin
                𝟘ᶜ                                  ≈˘⟨ ≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _)) $
                                                        +ᶜ-identityʳ _ ⟩
                (⌜ m ⌝ · 𝟘) ·ᶜ 𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ  ∎)) $
        (begin
           ε ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘       ≈⟨ ε ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩

           𝟘ᶜ                                                      ≤⟨ ε ∙ lemma₂ ∙ lemma₁ ∙ lemma₁ ∙ lemma₁ ⟩

           ω ·ᶜ ω ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝)                           ≈˘⟨ ·ᶜ-congˡ $
                                                                       ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                       ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                       ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                       ≈ᶜ-trans
                                                                         (+ᶜ-cong
                                                                            (≈ᶜ-trans
                                                                               (+ᶜ-cong
                                                                                  (≈ᶜ-trans (+ᶜ-cong (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _)) $
                                                                                   +ᶜ-identityʳ _)
                                                                                  (·ᶜ-zeroʳ _)) $
                                                                             +ᶜ-identityʳ _)
                                                                            (·ᶜ-zeroˡ _)) $
                                                                       +ᶜ-identityʳ _ ⟩
           ω ·ᶜ
           (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ
            ((((𝟘ᶜ +ᶜ ω ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝)) +ᶜ ω ·ᶜ 𝟘ᶜ) +ᶜ
              ω ·ᶜ 𝟘ᶜ) +ᶜ
             𝟘 ·ᶜ ω ·ᶜ
             ((𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ
              (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝) +ᶜ 𝟘ᶜ)) +ᶜ
            𝟘ᶜ)                                                    ∎)
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
    (Π-allowed ω q₁ → Π-allowed 𝟘 q₁) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃) →
    Has-weaker-computing-[]-cong s m l q₁ q₂ q₃ q₄ →
    Has-computing-[]-cong s m l q₁ q₂ q₃ q₄
  Has-weaker-computing-[]-cong→Has-computing-[]-cong
    {s} {q₁} {q₂} {q₃} {m} {l} {q₄}
    trivial prodrec-ok hyp₁ hyp₂ hyp₃
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    has-[]-cong′ , []-cong″-computes
    where
    open Erased s

    has-[]-cong′ : Has-[]-cong s m l q₁ q₂ q₃ q₄
    has-[]-cong′ =
      Has-weaker-[]-cong→Has-[]-cong
        trivial prodrec-ok hyp₁ hyp₂ hyp₃ has-[]-cong

    []-cong″ : Term 0
    []-cong″ = has-[]-cong′ .proj₁

    opaque

      lemma :
        (A t : Term n) (u : Term 0) →
        wk wk₀ u
          U.[ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ₛ•
              liftn wk₀ 4 ] PE.≡
        wk wk₀ u
      lemma A t u =
        wk wk₀ u
          U.[ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ₛ•
              liftn wk₀ 4 ]                                              ≡⟨ subst-wk u ⟩

        u U.[ (consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ₛ•
               liftn wk₀ 4) ₛ•
              wk₀ ]                                                      ≡˘⟨ wk≡subst _ _ ⟩

        wk wk₀ u                                                         ∎
        where
        open Tools.Reasoning.PropositionalEquality

    []-cong″-computes :
      ∀ n (Γ : Con Term n) (A t : Term n) →
      Γ ⊢ A ∷ U l →
      Γ ⊢ t ∷ A →
      Γ ⊢ wk wk₀ []-cong″ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡ rfl ∷
        Id (Erased A) [ t ] ([ t ])
    []-cong″-computes _ Γ A t ⊢A ⊢t =
      wk wk₀
        (lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
         cong 𝟘 (Erased (Erased (var x3))) [ [ var x2 ] ]
           [ [ var x1 ] ] (Erased (var x3))
           (mapᴱ (Erased (var x4)) (erased (var x5) (var x0))
              (var x0))
           (wk wk₀ []-cong′ ∘⟨ ω ⟩ Erased (var x3) ∘⟨ ω ⟩ [ var x2 ]
              ∘⟨ ω ⟩ [ var x1 ]
              ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                       (Erased (var x3)) [ var x0 ] (var x0)))
        ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ∷
        Id (Erased A) [ t ] ([ t ])                                    ⇒*⟨ β-red-⇒₄
                                                                             (W.wkTerm (W.wk₀∷ʷ⊇ (wfTerm ⊢A)) $ has-[]-cong′ .proj₂ .proj₂)
                                                                             ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢∷
                                                                        ˘⟨ Id-cong (refl ⊢Erased-A) mapᴱ-lemma mapᴱ-lemma ⟩≡
      wk (liftn wk₀ 4)
        (cong 𝟘 (Erased (Erased (var x3))) [ [ var x2 ] ]
           [ [ var x1 ] ] (Erased (var x3))
           (mapᴱ (Erased (var x4)) (erased (var x5) (var x0))
              (var x0))
           (wk wk₀ []-cong′ ∘⟨ ω ⟩ Erased (var x3) ∘⟨ ω ⟩ [ var x2 ]
              ∘⟨ ω ⟩ [ var x1 ]
              ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                       (Erased (var x3)) [ var x0 ] (var x0)))
        U.[ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ] ∷
        Id (Erased A)
          (mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0)
             [ [ [ t ] ] ]₀)
          (mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0)
             [ [ [ t ] ] ]₀)                                           ≡⟨ PE.trans (subst-wk (cong _ _ _ _ _ _ _)) $
                                                                          PE.trans cong-[] $
                                                                          PE.cong₂ (cong _ _ _ _ _)
                                                                            (PE.trans mapᴱ-[] $
                                                                             PE.cong₂ (mapᴱ _) erased-[] PE.refl)
                                                                            (PE.cong₂ _∘⟨ 𝟘 ⟩_
                                                                               (PE.cong (_∘⟨ ω ⟩ [ t ]) $
                                                                                PE.cong (_∘⟨ ω ⟩ [ t ]) $
                                                                                PE.cong (_∘⟨ _ ⟩ _) $
                                                                                lemma _ _ _)
                                                                               cong-[]) ⟩⊢∷≡
      cong 𝟘 (Erased (Erased A)) [ [ t ] ] [ [ t ] ] (Erased A)
        (mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0))
        (wk wk₀ []-cong′ ∘⟨ ω ⟩ Erased A ∘⟨ ω ⟩ [ t ] ∘⟨ ω ⟩ [ t ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 A t t (Erased A) [ var x0 ] rfl)              ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                            (refl ⊢Erased-A) (refl ⊢mapᴱ-0) $
                                                                          PE.subst (_⊢_≡_∷_ _ _ _)
                                                                            (PE.cong₃ Id wk3-[]₂[]₁[]₀ wk2-[]₁[]₀ (wk1-sgSubst _ _)) $
                                                                          _⊢_≡_∷_.app-cong
                                                                            (_⊢_≡_∷_.refl $
                                                                             PE.subst (_⊢_∷_ _ _)
                                                                               (PE.cong₂ (Π_,_▷_▹_ 𝟘 q₄)
                                                                                  (PE.cong₃ Id wk2-[]₁[]₀ (wk1-sgSubst _ _) PE.refl) $
                                                                                PE.refl) $
                                                                             flip _∘ⱼ_ ⊢[t] $
                                                                             PE.subst (_⊢_∷_ _ _)
                                                                               (PE.cong₂ (Π_,_▷_▹_ ω q₃) (wk1-sgSubst _ _) PE.refl) $
                                                                             flip _∘ⱼ_ ⊢[t] $
                                                                             flip _∘ⱼ_ ⊢Erased-A∷U $
                                                                             W.wkTerm (W.wk₀∷ʷ⊇ (wfTerm ⊢A)) ⊢[]-cong′) $
                                                                          cong-≡ ⊢t ([]ⱼ Erased-ok (var₀ (univ ⊢A))) ⟩⊢
      cong 𝟘 (Erased (Erased A)) [ [ t ] ] [ [ t ] ] (Erased A)
        (mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0))
        (wk wk₀ []-cong′ ∘⟨ ω ⟩ Erased A ∘⟨ ω ⟩ [ t ] ∘⟨ ω ⟩ [ t ]
           ∘⟨ 𝟘 ⟩ rfl)                                                 ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                            (refl ⊢Erased-A) (refl ⊢mapᴱ-0) $
                                                                          []-cong′≡ _ _ _ _ ⊢Erased-A∷U ⊢[t] ⟩⊢
      cong 𝟘 (Erased (Erased A)) [ [ t ] ] [ [ t ] ] (Erased A)
        (mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0))
        rfl                                                            ⇒⟨ cong-⇒ ⊢[[t]] ⊢mapᴱ-0 ⟩⊢∎

      rfl                                                              ∎
      where
      Erased-ok : Erased-allowed s
      Erased-ok =
        proj₂ $ inversion-Erased _ $
        proj₁ $ inversion-Id $
        proj₁ $ proj₂ $ inversion-ΠΣ $
        proj₁ $ proj₂ $ inversion-ΠΣ $
        proj₁ $ proj₂ $ inversion-ΠΣ $
        proj₁ $ proj₂ $ inversion-ΠΣ $
        syntacticTerm $ has-[]-cong′ .proj₂ .proj₂

      ⊢[t] : Γ ⊢ [ t ] ∷ Erased A
      ⊢[t] = []ⱼ Erased-ok ⊢t

      ⊢[[t]] : Γ ⊢ [ [ t ] ] ∷ Erased (Erased A)
      ⊢[[t]] = []ⱼ Erased-ok ⊢[t]

      ⊢Erased-A : Γ ⊢ Erased A
      ⊢Erased-A = syntacticTerm ⊢[t]

      ⊢Erased-Erased-A : Γ ⊢ Erased (Erased A)
      ⊢Erased-Erased-A = syntacticTerm ⊢[[t]]

      ⊢Erased-A∷U : Γ ⊢ Erased A ∷ U l
      ⊢Erased-A∷U = Erasedⱼ-U Erased-ok ⊢A

      ⊢mapᴱ-0 :
        Γ ∙ Erased (Erased A) ⊢
          mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0) ∷
          Erased (wk1 A)
      ⊢mapᴱ-0 =
        ⊢mapᴱ (erasedⱼ (var₀ (W.wk₁ ⊢Erased-Erased-A ⊢Erased-A)))
          (var₀ ⊢Erased-Erased-A)

      mapᴱ-lemma :
        Γ ⊢
          mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0)
            [ [ [ t ] ] ]₀ ≡
          [ t ] ∷
          Erased A
      mapᴱ-lemma =
        mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0)
          [ [ [ t ] ] ]₀                                          ≡⟨ PE.trans mapᴱ-[] $
                                                                     PE.cong₃ mapᴱ
                                                                       (wk1-sgSubst _ _)
                                                                       (PE.trans erased-[] $
                                                                        PE.cong₂ erased wk2-[]₁ PE.refl)
                                                                       PE.refl ⟩⊢≡

        mapᴱ (Erased A) (erased (wk1 A) (var x0)) ([ [ t ] ])     ≡⟨ mapᴱ-β Erased-ok (erasedⱼ (var₀ ⊢Erased-A)) ([]ⱼ Erased-ok ⊢t) ⟩⊢

        [ erased (wk1 A) (var x0) [ [ t ] ]₀ ]                    ≡⟨ PE.cong ([_]) $
                                                                     PE.trans erased-[] $
                                                                     PE.cong₂ erased (wk1-sgSubst _ _) PE.refl ⟩⊢≡

        [ erased A ([ t ]) ]                                      ≡⟨ ET.[]-cong′ Erased-ok $
                                                                     Erased-β Erased-ok ⊢t ⟩⊢∎
        [ t ]                                                     ∎

opaque

  -- A variant of ¬-[]-cong for Has-weaker-[]-cong.

  ¬-Has-weaker-[]-cong :
    (s PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ[ ok ] (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    (Π-allowed ω q₁ → Π-allowed 𝟘 q₁) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃) →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    ¬ Has-weaker-[]-cong s 𝟙ᵐ l q₁ q₂ q₃ q₄
  ¬-Has-weaker-[]-cong
    {s} {ok} {q₁} {q₂} {q₃} {l} {q₄}
    prodrec-ok hyp₁ hyp₂ hyp₃ nem Unitʷ-η→ =
    Has-weaker-[]-cong s 𝟙ᵐ l q₁ q₂ q₃ q₄  →⟨ Has-weaker-[]-cong→Has-[]-cong (⊥-elim ∘→ (_$ ok))
                                                (PE.subst (λ m → Prodrec-allowed m _ _ _) (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ∘→ prodrec-ok)
                                                hyp₁ hyp₂ hyp₃ ⟩
    Has-[]-cong s 𝟙ᵐ l q₁ q₂ q₃ q₄         →⟨ ¬-[]-cong ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄ nem Unitʷ-η→ ⟩
    ⊥                                      □
