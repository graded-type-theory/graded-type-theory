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
open import Definition.Typed.Weakening TR as W using (_»_∷ʷ_⊇_)
import Definition.Typed.Weakening.Definition TR as WD
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M as U
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
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
open import Tools.Nat using (Nat; 1+; 2+; 3+; 4+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  b                                        : Bool
  n n′                                     : Nat
  Δ                                        : Con Term _
  Γ                                        : Cons _ _
  A A₁ A₂ B C t t₁ t₂ t′ u u₁ u₂ v v₁ v₂ w : Term _
  σ                                        : Subst _ _
  p q q₁ q₁′ q₂ q₂′ q₃ q₃′ q₄              : M
  γ γ₁ γ₂ γ₃ γ₄                            : Conₘ _
  m                                        : Mode
  s                                        : Strength
  l l′                                     : Universe-level
  sem                                      : Some-erased-matches
  str                                      : T.Strictness
  ok                                       : T _

------------------------------------------------------------------------
-- Some lemmas

private opaque

  -- Some lemmas used below.

  ⊢Id-2-1-0 :
    ⊢ Γ →
    Γ »∙ U l »∙ var x0 »∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
  ⊢Id-2-1-0 {Γ} ⊢Γ = Idⱼ′ (var₁ ⊢1) (var₀ ⊢1)
    where
    ⊢1 : Γ »∙ U l »∙ var x0 ⊢ var x1
    ⊢1 = univ (var₁ (univ (var₀ (Uⱼ ⊢Γ))))

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
  -- available for J and 𝟘ᵐ is allowed, when the mode is 𝟘ᵐ[ ok ], or
  -- when the modality is trivial. Note that the lemmas in this
  -- section do not include assumptions of the form
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
    γ₁ ▸[ 𝟘ᵐ[ ok ] ] A →
    γ₂ ▸[ 𝟘ᵐ[ ok ] ] t →
    γ₃ ▸[ 𝟘ᵐ[ ok ] ] u →
    γ₄ ▸[ 𝟘ᵐ[ ok ] ] v →
    𝟘ᶜ ▸[ m ] []-cong-J s A t u v
  ▸[]-cong-J {m} {ok} {s} ≡not-none ▸A ▸t ▸u ▸v =
    let ▸A = ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) (▸-𝟘 ▸A)
        ▸t = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t
        ▸u = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸u
        ▸v = ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸v
    in
    case PE.singleton $ erased-matches-for-J m of λ where
      (not-none _ , ≡not-none) → sub
        (▸subst-𝟘 ≡not-none ▸A
           (Idₘ-generalised (▸Erased (wkUsage _ ▸A))
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
    γ₁ ▸[ 𝟘ᵐ[ ok ] ] A →
    γ₂ ▸[ 𝟘ᵐ[ ok ] ] t →
    γ₃ ▸[ 𝟘ᵐ[ ok ] ] u →
    γ₄ ▸[ 𝟘ᵐ[ ok ] ] v →
    𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] []-cong-J s A t u v
  ▸[]-cong-J-𝟘ᵐ {γ₁} {s} ▸A ▸t ▸u ▸v =
    case ▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A of λ
      ▸A →
    ▸-𝟘 $
    ▸subst ▸A
      (Idₘ-generalised (▸Erased (wkUsage (step id) ▸A))
         (▸[] (wkUsage (step id) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t))) (▸[] var)
         (λ _ → begin
            γ₁ ∧ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            γ₁ ∧ᶜ 𝟘ᶜ ∙ 𝟘      ≤⟨ ∧ᶜ-decreasingʳ _ _ ∙ ≤-refl ⟩
            𝟘ᶜ                ∎)
         (λ _ → begin
            γ₁ ∧ᶜ 𝟘ᶜ ∙ 𝟘 · 𝟘      ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            γ₁ ∧ᶜ 𝟘ᶜ ∙ 𝟘          ≤⟨ ∧ᶜ-decreasingˡ _ _ ∙ ≤-refl ⟩
            γ₁ ∙ 𝟘                ≈˘⟨ ≈ᶜ-trans (+ᶜ-congˡ (+ᶜ-identityʳ _)) (+ᶜ-identityʳ _) ⟩
            (γ₁ ∙ 𝟘) +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎))
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
          P.[]-cong′ ok $ refl ⊢t)
         (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk1-sgSubst _ _) $
          P.[]-cong′ ok t≡t′))

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
         (P.[]-cong′ ok (W.wkEqTerm₁ ⊢A₁ t₁≡t₂))
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

opaque
  unfolding []-cong-J subst

  -- The result of "extracting" an application of []-cong-J is an
  -- application of loop?.

  erase-[]-cong-J : erase′ b str ([]-cong-J s A t u v) PE.≡ loop? str
  erase-[]-cong-J = PE.refl

------------------------------------------------------------------------
-- Has-[]-cong

-- The property of supporting a []-cong combinator for a certain mode,
-- a certain erased variable context, a certain type, and certain
-- grades.

Has-[]-cong-for :
  Strength → Mode → Con Term n → Term n → M → M → M → Set a
Has-[]-cong-for {n} s m Γ A q₁ q₂ q₃ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ A ▹
    Π 𝟘 , q₂ ▷ wk1 A ▹
    Π 𝟘 , q₃ ▷ Id (wk[ 2 ]′ A) (var x1) (var x0) ▹
    Id (Erased (wk[ 3 ]′ A)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator (with certain
-- grades) for a certain mode, a certain universe level, and a certain
-- erased variable context.
--
-- Note that, unlike the []-cong primitive, the first argument must be
-- a type in U l for some l.

Has-[]-cong :
  Strength → Mode → Universe-level → Con Term n → M → M → M → M → Set a
Has-[]-cong {n} s m l Γ q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π 𝟘 , q₁ ▷ U l ▹
    Π 𝟘 , q₂ ▷ var x0 ▹
    Π 𝟘 , q₃ ▷ var x1 ▹
    Π 𝟘 , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong :
  Strength → Mode → Universe-level → Con Term n → M → M → M → M → Set a
Has-computing-[]-cong {n} s m l Γ q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s m l Γ q₁ q₂ q₃ q₄) →
  ∀ m n′ (Δ : Cons m n′) (A t : Term n′) (ρ : Wk n′ n) →
  Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
  Δ ⊢ A ∷ U l →
  Δ ⊢ t ∷ A →
  Δ ⊢ wk ρ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡ rfl ∷
    Id (Erased A) ([ t ]) ([ t ])

opaque

  -- []-cong is supported for the strength s, the mode m, the universe
  -- level l, and a well-formed variable context, for grades for which
  -- "Π 𝟘" are allowed, if
  --
  -- * []-cong is allowed for s, or
  -- * Erased is allowed for s and
  --   * erased matches are available for J and 𝟘ᵐ is allowed, or
  --   * m is 𝟘ᵐ, or
  --   * the modality is trivial, or
  --   * equality reflection is allowed.

  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong :
    {Γ : Con Term n} →
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
    Has-computing-[]-cong s m l Γ q₁ q₂ q₃ q₄
  []-cong⊎J⊎𝟘ᵐ⊎Trivial⊎Equality-reflection→[]-cong
    {n} {s} {m} ok ⊢Γ ok₁ ok₂ ok₃ ok₄ =
    let ⊢[]-cong″ = ⊢[]-cong″ ok′ (var₀ (⊢Id-2-1-0 ⊢Γ)) in
      ( []-cong′
      , (lamₘ $ lamₘ $ lamₘ $ lamₘ $
         sub (▸[]-cong″ ok′ var var var var) $ begin
           𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                                                  ∎)
      , lamⱼ′ ok₁ (lamⱼ′ ok₂ (lamⱼ′ ok₃ (lamⱼ′ ok₄ ⊢[]-cong″)))
      )
    , λ _ _ _ A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) .proj₂ in
        wk ρ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl          ⇒*⟨ β-red-⇒₄′ ok₁ ok₂ ok₃ ok₄
                                                                           (W.wkTerm (W.liftnʷ Δ⊇Γ (∙ ⊢Id-2-1-0 (WD.defn-wk′ ⊇ε ⊢Γ))) $
                                                                            WD.defn-wkTerm ⊇ε ⊢[]-cong″)
                                                                           ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        wk (liftn ρ 4)
          ([]-cong″ ok′ (var x3) (var x2) (var x1) (var x0))
          [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ]  ≡⟨ PE.trans (subst-wk ([]-cong″ ok′ _ _ _ _)) $
                                                                        []-cong″-[] ok′ ⟩⊢≡

        []-cong″ ok′ A t t rfl                                       ⇒*⟨ []-cong″-β-⇒* ok′ ⊢t ⟩⊢∎

        rfl                                                          ∎
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

    []-cong″ : OK → Term n′ → Term n′ → Term n′ → Term n′ → Term n′
    []-cong″ (inj₁ _)        = []-cong s
    []-cong″ (inj₂ (inj₁ _)) = λ _ _ _ _ → rfl
    []-cong″ (inj₂ (inj₂ _)) = []-cong-J s

    ▸[]-cong″ :
      ∀ ok →
      γ₁ ▸[ 𝟘ᵐ? ] A →
      γ₂ ▸[ 𝟘ᵐ? ] t →
      γ₃ ▸[ 𝟘ᵐ? ] u →
      γ₄ ▸[ 𝟘ᵐ? ] v →
      𝟘ᶜ ▸[ m ] []-cong″ ok A t u v
    ▸[]-cong″ (inj₁ (_ , ok)) ▸A ▸t ▸u ▸v =
      []-congₘ ▸A ▸t ▸u ▸v ok
    ▸[]-cong″ (inj₂ (inj₁ ok)) _ _ _ _ =
      rflₘ
    ▸[]-cong″ (inj₂ (inj₂ (inj₁ ((_ , ≡not-none) , ok)))) ▸A ▸t ▸u ▸v =
      ▸[]-cong-J {ok = ok} ≡not-none (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A)
        (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸[]-cong″ (inj₂ (inj₂ (inj₂ (inj₁ (_ , PE.refl))))) ▸A ▸t ▸u ▸v =
      ▸[]-cong-J-𝟘ᵐ (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t)
        (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸u) (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸v)
    ▸[]-cong″ (inj₂ (inj₂ (inj₂ (inj₂ trivial)))) =
      ▸[]-cong-J-trivial trivial

    ⊢[]-cong″ :
      let open Erased s in
      ∀ ok →
      Γ ⊢ v ∷ Id A t u →
      Γ ⊢ []-cong″ ok A t u v ∷ Id (Erased A) [ t ] ([ u ])
    ⊢[]-cong″ (inj₁ (ok , _))  = []-congⱼ′ ok
    ⊢[]-cong″ (inj₂ (inj₂ _))  = []-cong-Jⱼ Erased-ok
    ⊢[]-cong″ (inj₂ (inj₁ ok)) = λ ⊢v →
      []-cong-with-equality-reflection ok Erased-ok ⊢v

    []-cong″-[] :
      ∀ ok →
      []-cong″ ok A t u v [ σ ] PE.≡
      []-cong″ ok (A [ σ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
    []-cong″-[] (inj₁ _)         = PE.refl
    []-cong″-[] (inj₂ (inj₁ ok)) = PE.refl
    []-cong″-[] (inj₂ (inj₂ _))  = []-cong-J-[]

    []-cong″-β-⇒* :
      let open Erased s in
      ∀ ok →
      Γ ⊢ t ∷ A →
      Γ ⊢ []-cong″ ok A t t rfl ⇒* rfl ∷ Id (Erased A) [ t ] ([ t ])
    []-cong″-β-⇒* (inj₁ (ok , _))  ⊢t =
      redMany ([]-cong-β-⇒ (refl ⊢t) ok)
    []-cong″-β-⇒* (inj₂ (inj₂ _))  ⊢t =
      redMany ([]-cong-J-β-⇒ Erased-ok ⊢t)
    []-cong″-β-⇒* (inj₂ (inj₁ ok)) ⊢t =
      id ([]-cong-with-equality-reflection ok Erased-ok (rflⱼ ⊢t))

    []-cong′ : Term n
    []-cong′ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
      []-cong″ ok′ (var x3) (var x2) (var x1) (var x0)

opaque

  -- Has-[]-cong implies Has-[]-cong-for, given certain assumptions.

  Has-[]-cong→Has-[]-cong-for :
    γ ▸[ 𝟘ᵐ? ] A →
    ε » Δ ⊢ A ∷ U l →
    Has-[]-cong s m l Δ q₁ q₂ q₃ q₄ →
    Has-[]-cong-for s m Δ A q₂ q₃ q₄
  Has-[]-cong→Has-[]-cong-for
    {γ} {A} {s} {m} {q₂} {q₃} {q₄}
    ▸A ⊢A ([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    []-cong′ ∘⟨ 𝟘 ⟩ A ,
    (sub (▸[]-cong′ ∘ₘ ▸-cong (PE.sym $ ᵐ·-zeroʳ m) ▸A) $ begin
       𝟘ᶜ            ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
       𝟘 ·ᶜ γ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
       𝟘ᶜ +ᶜ 𝟘 ·ᶜ γ  ∎) ,
    PE.subst (_⊢_∷_ _ _)
      (PE.cong₂ (Π 𝟘 , q₂ ▷_▹_) PE.refl $
       PE.cong₂ (Π 𝟘 , q₃ ▷_▹_) PE.refl $
       PE.cong₂ (Π 𝟘 , q₄ ▷_▹_)
         (PE.cong₃ Id wk[]≡wk[]′ PE.refl PE.refl)
         (PE.cong₃ Id (PE.cong Erased wk[]≡wk[]′) PE.refl PE.refl))
      (⊢[]-cong′ ∘ⱼ ⊢A)
    where
    open ≤ᶜ-reasoning
    open Erased s

opaque

  -- If the modality's zero is well-behaved, erased matches (including
  -- the []-cong primitive) are not allowed, equality reflection is
  -- not allowed, and η-equality is not allowed for weak unit types
  -- unless a certain condition is satisfied, then []-cong is not
  -- supported for the mode 𝟙ᵐ and a "consistent" well-formed type A
  -- without η-equality.

  ¬-[]-cong-for :
    {Γ : Con Term n}
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    No-η-equality ε A →
    ε » Γ ⊢ A →
    Consistent (ε » Γ ∙ A) →
    ¬ Has-[]-cong-for s 𝟙ᵐ Γ A q₁ q₂ q₃
  ¬-[]-cong-for {n} {A} {Γ} nem Unitʷ-η→ no-η ⊢A consistent (_ , hyp) =
    let ▸[]-cong′ , ⊢[]-cong′ = lemma (lemma (lemma hyp)) in
    case red-Id ⦃ ok = included ⦄ ⊢[]-cong′ of λ where
      (_ , rflₙ , ⇒*rfl) →
        case var-only-equal-to-itself (wk-No-η-equality no-η)
               (ne (var _ _)) $
             prod-cong⁻¹ ⦃ ok = included ⦄
               (inversion-rfl-Id ⦃ ok = included ⦄ $
                wf-⊢≡∷ (subset*Term ⇒*rfl) .proj₂ .proj₂)
               .proj₂ .proj₁ of λ ()
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
    ¬ Has-[]-cong s 𝟙ᵐ l Γ q₁ q₂ q₃ q₄
  ¬-[]-cong
    {n} {s} {l} {q₁} {q₂} {q₃} {q₄} {Γ}
    nem Unitʷ-η→ consistent has-[]-cong@(_ , hyp) =
                                            $⟨ has-[]-cong ⟩
    Has-[]-cong s 𝟙ᵐ l Γ q₁ q₂ q₃ q₄        →⟨ Has-[]-cong→Has-[]-cong-for ▸A ⊢A ⟩
    Has-[]-cong-for s 𝟙ᵐ Γ (A′ l) q₂ q₃ q₄  →⟨ ¬-[]-cong-for nem Unitʷ-η→ No-η-equality-A (univ ⊢A)
                                                 (subst-Consistent (⊢ˢʷ∷-sgSubst ⊢t) consistent) ⟩
    ⊥                                       □
    where
    ⊢Γ : ε »⊢ Γ
    ⊢Γ = wfTerm (hyp .proj₂)

    A′ : Universe-level → Term n
    A′ 0      = ℕ
    A′ (1+ l) = U l

    t″ : Universe-level → Term n
    t″ 0      = zero
    t″ 1      = ℕ
    t″ (2+ l) = U l

    ⊢A : ε » Γ ⊢ A′ l′ ∷ U l′
    ⊢A {l′ = 0}    = ℕⱼ ⊢Γ
    ⊢A {l′ = 1+ _} = Uⱼ ⊢Γ

    ⊢t : ε » Γ ⊢ t″ l′ ∷ A′ l′
    ⊢t {l′ = 0}    = zeroⱼ ⊢Γ
    ⊢t {l′ = 1}    = ℕⱼ ⊢Γ
    ⊢t {l′ = 2+ _} = Uⱼ ⊢Γ

    ▸A : 𝟘ᶜ ▸[ 𝟘ᵐ? ] A′ l′
    ▸A {l′ = 0}    = ▸-cong (ᵐ·-zeroʳ 𝟙ᵐ) ℕₘ
    ▸A {l′ = 1+ _} = ▸-cong (ᵐ·-zeroʳ 𝟙ᵐ) Uₘ

    No-η-equality-A : No-η-equality ε (A′ l′)
    No-η-equality-A {l′ = 0}    = ℕₙ
    No-η-equality-A {l′ = 1+ _} = Uₙ

------------------------------------------------------------------------
-- Has-weaker-[]-cong

-- A "weaker" variant of Has-[]-cong.

Has-weaker-[]-cong :
  Strength → Mode → Universe-level → Con Term n → M → M → M → M → Set a
Has-weaker-[]-cong {n} s m l Γ q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π ω , q₁ ▷ U l ▹
    Π ω , q₂ ▷ var x0 ▹
    Π ω , q₃ ▷ var x1 ▹
    Π 𝟘 , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (var x3)) [ var x2 ] ([ var x1 ])

-- A "weaker" variant of Has-computing-[]-cong.

Has-weaker-computing-[]-cong :
  Strength → Mode → Universe-level → Con Term n → M → M → M → M → Set a
Has-weaker-computing-[]-cong {n} s m l Γ q₁ q₂ q₃ q₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-weaker-[]-cong s m l Γ q₁ q₂ q₃ q₄) →
  ∀ m n′ (Δ : Cons m n′) (A t : Term n′) (ρ : Wk n′ n) →
  Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
  Δ ⊢ A ∷ U l →
  Δ ⊢ t ∷ A →
  Δ ⊢ wk ρ []-cong′ ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∘⟨ ω ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡ rfl ∷
    Id (Erased A) [ t ] ([ t ])

-- Some definitions/lemmas used below.

private
  module Has-[]-cong→Has-weaker-[]-cong
    {Γ : Con Term n}
    (hyp₁ : Π-allowed 𝟘 q₁ → Π-allowed ω q₁′)
    (hyp₂ : Π-allowed 𝟘 q₂ → Π-allowed ω q₂′)
    (hyp₃ : Π-allowed 𝟘 q₃ → Π-allowed ω q₃′)
    (([]-cong′ , _ , ⊢[]-cong′) : Has-[]-cong s m l Γ q₁ q₂ q₃ q₄)
    where

    open Erased s

    []-cong″ : Term (4+ n)
    []-cong″ =
       wk (stepn id 4) []-cong′
         ∘⟨ 𝟘 ⟩ var x3 ∘⟨ 𝟘 ⟩ var x2 ∘⟨ 𝟘 ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0

    ⊢[]-cong″ :
      ε » Γ ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢
        []-cong″ ∷ Id (Erased (var x3)) [ var x2 ] ([ var x1 ])
    ⊢[]-cong″ =
      flip _∘ⱼ_ (var₀ ⊢Id) $
      flip _∘ⱼ_ (var₁ ⊢Id) $
      flip _∘ⱼ_ (var₂ ⊢Id) $
      flip _∘ⱼ_ (var₃ ⊢Id) $
      W.wkTerm (W.ʷ⊇-drop (∙ ⊢Id)) ⊢[]-cong′
      where
      ⊢Id :
        ε » Γ ∙ U l ∙ var x0 ∙ var x1 ⊢ Id (var x2) (var x1) (var x0)
      ⊢Id = ⊢Id-2-1-0 (wfTerm ⊢[]-cong′)

    oks :
      Π-allowed ω q₁′ × Π-allowed ω q₂′ × Π-allowed ω q₃′ ×
      Π-allowed 𝟘 q₄
    oks =
      case inversion-ΠΣ $ syntacticTerm ⊢[]-cong′ of λ
        (_ , ⊢Π , ok₁) →
      case inversion-ΠΣ ⊢Π of λ
        (_ , ⊢Π , ok₂) →
      case inversion-ΠΣ ⊢Π of λ
        (_ , ⊢Π , ok₃) →
      case inversion-ΠΣ ⊢Π of λ
        (_ , _ , ok₄) →
      hyp₁ ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , ok₄

opaque

  -- Has-weaker-[]-cong is no stronger than Has-[]-cong (given certain
  -- assumptions).

  Has-[]-cong→Has-weaker-[]-cong :
    {Γ : Con Term n} →
    (Π-allowed 𝟘 q₁ → Π-allowed ω q₁′) →
    (Π-allowed 𝟘 q₂ → Π-allowed ω q₂′) →
    (Π-allowed 𝟘 q₃ → Π-allowed ω q₃′) →
    Has-[]-cong s m l Γ q₁ q₂ q₃ q₄ →
    Has-weaker-[]-cong s m l Γ q₁′ q₂′ q₃′ q₄
  Has-[]-cong→Has-weaker-[]-cong
    {n} {q₁′} {q₂′} {q₃′} {s} {m} {l} {q₄} {Γ}
    hyp₁ hyp₂ hyp₃ has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open Has-[]-cong→Has-weaker-[]-cong hyp₁ hyp₂ hyp₃ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ = lam ω $ lam ω $ lam ω $ lam 𝟘 []-cong″

    ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
    ▸[]-cong‴ =
      lamₘ $ lamₘ $ lamₘ $ lamₘ $
      sub ((((wkUsage _ ▸[]-cong′ ∘ₘ var) ∘ₘ var) ∘ₘ var) ∘ₘ var) $
      (begin
         𝟘ᶜ ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · ω ∙ ⌜ m ⌝ · 𝟘  ≤⟨ ≤ᶜ-refl ∙ lemma ∙ lemma ∙ lemma ∙ ≤-reflexive (·-zeroʳ _) ⟩

         𝟘ᶜ                                                  ≈˘⟨ ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                 ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                 ≈ᶜ-trans (≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _) $
                                                                 ≈ᶜ-trans (+ᶜ-congˡ $ ·ᶜ-zeroˡ _) $ +ᶜ-identityʳ _ ⟩
         (((𝟘ᶜ +ᶜ 𝟘 ·ᶜ (𝟘ᶜ , x3 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
           𝟘 ·ᶜ (𝟘ᶜ , x2 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
          𝟘 ·ᶜ (𝟘ᶜ , x1 ≔ ⌜ m ᵐ· 𝟘 ⌝)) +ᶜ
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ m ᵐ· 𝟘 ⌝)                         ∎)
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
        Π ω , q₁′ ▷ U l ▹
        Π ω , q₂′ ▷ var x0 ▹
        Π ω , q₃′ ▷ var x1 ▹
        Π 𝟘 , q₄  ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (var x3)) ([ var x2 ]) ([ var x1 ])
    ⊢[]-cong‴ =
      let ok₁ , ok₂ , ok₃ , ok₄ = oks in
      lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ ⊢[]-cong″

opaque
  unfolding Has-[]-cong→Has-weaker-[]-cong

  -- Has-weaker-computing-[]-cong is no stronger than
  -- Has-computing-[]-cong (given certain assumptions).

  Has-computing-[]-cong→Has-weaker-computing-[]-cong :
    (Π-allowed 𝟘 q₁ → Π-allowed ω q₁′) →
    (Π-allowed 𝟘 q₂ → Π-allowed ω q₂′) →
    (Π-allowed 𝟘 q₃ → Π-allowed ω q₃′) →
    Has-computing-[]-cong s m l Δ q₁ q₂ q₃ q₄ →
    Has-weaker-computing-[]-cong s m l Δ q₁′ q₂′ q₃′ q₄
  Has-computing-[]-cong→Has-weaker-computing-[]-cong
    hyp₁ hyp₂ hyp₃
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    let open Has-[]-cong→Has-weaker-[]-cong hyp₁ hyp₂ hyp₃ has-[]-cong

        ok₁ , ok₂ , ok₃ , ok₄ = oks
    in
      Has-[]-cong→Has-weaker-[]-cong hyp₁ hyp₂ hyp₃ has-[]-cong
    , λ _ _ _ A t ρ Δ⊇Γ ⊢A ⊢t →
        let ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) .proj₂ in
        wk ρ
          (lam ω $ lam ω $ lam ω $ lam 𝟘 $
           wk (stepn id 4) []-cong′
             ∘⟨ 𝟘 ⟩ var x3 ∘⟨ 𝟘 ⟩ var x2 ∘⟨ 𝟘 ⟩ var x1 ∘⟨ 𝟘 ⟩ var x0)
          ∘⟨ ω ⟩ A ∘⟨ ω ⟩ t ∘⟨ ω ⟩ t ∘⟨ 𝟘 ⟩ rfl                        ⇒*⟨ β-red-⇒₄′ ok₁ ok₂ ok₃ ok₄
                                                                             (W.wkTerm
                                                                                (W.liftnʷ Δ⊇Γ $ ∙_ $ ⊢Id-2-1-0 $ wfTerm $
                                                                                 WD.defn-wkTerm ⊇ε ⊢[]-cong′) $
                                                                                WD.defn-wkTerm ⊇ε ⊢[]-cong″)
                                                                             ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢
        (wk (liftn ρ 4) (wk (stepn id 4) []-cong′)
           [ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ])
          ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl                        ≡⟨ PE.cong (λ []-cong → []-cong ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _ ∘⟨ _ ⟩ _) $
                                                                          PE.trans
                                                                            (PE.cong _[ _ ] $
                                                                             PE.trans (wk-comp _ _ []-cong′) $
                                                                             PE.cong (flip wk _) $
                                                                             PE.sym $ liftn-stepn-comp 4) $
                                                                          PE.trans (subst-wk []-cong′) $
                                                                          PE.sym $ wk≡subst _ _ ⟩⊢≡

        wk ρ []-cong′ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl            ≡⟨ []-cong′≡ _ _ _ _ _ _ Δ⊇Γ ⊢A ⊢t ⟩⊢∎

        rfl                                                            ∎

-- Some definitions/lemmas used below.

private
  module Has-weaker-[]-cong→Has-[]-cong
    {Γ : Con Term n}
    (hyp₁ : Π-allowed ω q₁ → Π-allowed 𝟘 q₁′)
    (hyp₂ : Π-allowed ω q₂ → Π-allowed 𝟘 q₂′)
    (hyp₃ : Π-allowed ω q₃ → Π-allowed 𝟘 q₃′)
    (([]-cong′ , _ , ⊢[]-cong′) : Has-weaker-[]-cong s m l Γ q₁ q₂ q₃ q₄)
    where

    open Erased s

    []-cong″ : Term (4+ n)
    []-cong″ =
      cong 𝟘 (Erased (Erased (var x3))) [ [ var x2 ] ] [ [ var x1 ] ]
        (Erased (var x3))
        (mapᴱ (Erased (var x4)) (erased (var x5) (var x0)) (var x0))
        (wk (stepn id 4) []-cong′ ∘⟨ ω ⟩ Erased (var x3)
           ∘⟨ ω ⟩ [ var x2 ] ∘⟨ ω ⟩ [ var x1 ]
           ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1) (Erased (var x3))
                    [ var x0 ] (var x0))

    ⊢[]-cong″ :
      Π-allowed 𝟘 q₁′ × Π-allowed 𝟘 q₂′ ×
      Π-allowed 𝟘 q₃′ × Π-allowed 𝟘 q₄ ×
      ε » Γ ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢
        []-cong″ ∷ Id (Erased (var x3)) [ var x2 ] ([ var x1 ])
    ⊢[]-cong″ =
        case inversion-ΠΣ $ syntacticTerm ⊢[]-cong′ of λ
          (_ , ⊢Π , ok₁) →
        case inversion-ΠΣ ⊢Π of λ
          (_ , ⊢Π , ok₂) →
        case inversion-ΠΣ ⊢Π of λ
          (_ , ⊢Π , ok₃) →
        case inversion-ΠΣ ⊢Π of λ
          (_ , ⊢Id , ok₄) →
        case inversion-Erased $ inversion-Id ⊢Id .proj₁ of λ
          (_ , Erased-ok) →
        case ⊢Id-2-1-0 (wfTerm ⊢[]-cong′) of λ
          ⊢Id →
        case _⊢_.univ $ var₃ ⊢Id of λ
          ⊢3 →
        case Erasedⱼ Erased-ok ⊢3 of λ
          ⊢Erased-3 →
        case Erasedⱼ Erased-ok ⊢Erased-3 of λ
          ⊢Erased-Erased-3 →
        case
          (∀ t →
           ε »
             Γ ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢
             t ∷ var x3 →
           ε »
             Γ ∙ U l ∙ var x0 ∙ var x1 ∙ Id (var x2) (var x1) (var x0) ⊢
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

             [ erased (var x3) ([ t ]) ]                                 ≡⟨ P.[]-cong′ Erased-ok $
                                                                            Erased-β Erased-ok ⊢t ⟩⊢∎
             [ t ]                                                       ∎)
        of λ
          lemma →
        hyp₁ ok₁ , hyp₂ ok₂ , hyp₃ ok₃ , ok₄ ,
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
           W.wkTerm (W.ʷ⊇-drop (∙ ⊢Id)) ⊢[]-cong′)
          (Id-cong (refl ⊢Erased-3) (lemma _ (var₂ ⊢Id))
             (lemma _ (var₁ ⊢Id)))

opaque

  -- Has-weaker-[]-cong is at least as strong as Has-[]-cong (given
  -- certain assumptions).

  Has-weaker-[]-cong→Has-[]-cong :
    {Γ : Con Term n} →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed ω q₁ → Π-allowed 𝟘 q₁′) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂′) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃′) →
    Has-weaker-[]-cong s m l Γ q₁ q₂ q₃ q₄ →
    Has-[]-cong s m l Γ q₁′ q₂′ q₃′ q₄
  Has-weaker-[]-cong→Has-[]-cong
    {n} {s} {q₁′} {q₂′} {q₃′} {m} {l} {q₄} {Γ}
    trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ has-[]-cong@(_ , ▸[]-cong′ , _) =
    []-cong‴ , ▸[]-cong‴ , ⊢[]-cong‴
    where
    open Erased s
    open ErasedU s
    open Has-weaker-[]-cong→Has-[]-cong hyp₁ hyp₂ hyp₃ has-[]-cong

    []-cong‴ : Term n
    []-cong‴ =
      lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 []-cong″

    opaque

      ⊢[]-cong‴ :
        ε » Γ ⊢ []-cong‴ ∷
        Π 𝟘 , q₁′ ▷ U l ▹
        Π 𝟘 , q₂′ ▷ var x0 ▹
        Π 𝟘 , q₃′ ▷ var x1 ▹
        Π 𝟘 , q₄  ▷ Id (var x2) (var x1) (var x0) ▹
        Id (Erased (var x3)) [ var x2 ] ([ var x1 ])
      ⊢[]-cong‴ =
        let ok₁ , ok₂ , ok₃ , ok₄ , ⊢[]-cong″ = ⊢[]-cong″ in
        lamⱼ′ ok₁ $ lamⱼ′ ok₂ $ lamⱼ′ ok₃ $ lamⱼ′ ok₄ ⊢[]-cong″

      ▸[]-cong‴ : 𝟘ᶜ ▸[ m ] []-cong‴
      ▸[]-cong‴ =
        lamₘ $ lamₘ $ lamₘ $ lamₘ $
        sub
          (▸cong (▸Erased (▸Erased var)) (▸[] (▸[] var)) (▸[] (▸[] var))
             (sub (▸Erased var) lemma)
             (sub
                (▸mapᴱ′ trivial 𝟘≤𝟙 (λ _ → _ , ▸Erased var)
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
                (▸cong var var var (sub (▸Erased var) lemma)
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
              flip _∘ₘ_ (sub (▸Erased var) lemma) $
              wkUsage _ ▸[]-cong′)
             (λ _ → begin
                𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                𝟘ᶜ              ∎)
             (λ _ → begin
                𝟘ᶜ                                  ≈˘⟨ ≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _))) $
                                                        +ᶜ-identityʳ _ ⟩
                (⌜ m ⌝ · 𝟘) ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (𝟙 + 𝟙) ·ᶜ 𝟘ᶜ  ∎)) $
        (begin
           𝟘ᶜ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘      ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩

           𝟘ᶜ                                                      ≈˘⟨ ≈ᶜ-trans
                                                                         (·ᶜ-congˡ $
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
                                                                          ≈ᶜ-trans (+ᶜ-identityʳ _) $
                                                                          ·ᶜ-zeroʳ _) $
                                                                       ·ᶜ-zeroʳ _ ⟩
           ω ·ᶜ
           (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ
            ((((𝟘ᶜ +ᶜ ω ·ᶜ 𝟘ᶜ) +ᶜ ω ·ᶜ 𝟘ᶜ) +ᶜ ω ·ᶜ 𝟘ᶜ) +ᶜ
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

        lemma : 𝟘ᶜ {n = 4+ n} ≤ᶜ 𝟘ᶜ , x3 ≔ ⌜ 𝟘ᵐ? ⌝
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
    (Π-allowed ω q₁ → Π-allowed 𝟘 q₁′) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂′) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃′) →
    Has-weaker-computing-[]-cong s m l Γ q₁ q₂ q₃ q₄ →
    Has-computing-[]-cong s m l Γ q₁′ q₂′ q₃′ q₄
  Has-weaker-computing-[]-cong→Has-computing-[]-cong
    {n} {s} {q₁′} {q₂′} {q₃} {q₃′} {m} {l} {q₄} {Γ}
    trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃
    (has-[]-cong@([]-cong′ , _ , ⊢[]-cong′) , []-cong′≡) =
    has-[]-cong′ , []-cong″-computes
    where
    open Erased s

    has-[]-cong′ : Has-[]-cong s m l Γ q₁′ q₂′ q₃′ q₄
    has-[]-cong′ =
      Has-weaker-[]-cong→Has-[]-cong
        trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ has-[]-cong

    []-cong″ : Term n
    []-cong″ = has-[]-cong′ .proj₁

    opaque

      lemma :
        (ρ : Wk n′ n) (A t : Term n′) (u : Term n) →
        wk (stepn id 4) u
          U.[ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ₛ•
              liftn ρ 4 ] PE.≡
        wk ρ u
      lemma ρ A t u =
        wk (stepn id 4) u
          U.[ consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ₛ•
              liftn ρ 4 ]                                                ≡⟨ subst-wk u ⟩

        u U.[ (consSubst (consSubst (consSubst (sgSubst A) t) t) rfl ₛ•
               liftn ρ 4) ₛ•
              stepn id 4 ]                                               ≡˘⟨ wk≡subst _ _ ⟩

        wk ρ u                                                           ∎
        where
        open Tools.Reasoning.PropositionalEquality

    []-cong″-computes :
      ∀ m n′ (Δ : Cons m n′) (A t : Term n′) (ρ : Wk n′ n) →
      Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
      Δ ⊢ A ∷ U l →
      Δ ⊢ t ∷ A →
      Δ ⊢ wk ρ []-cong″ ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡ rfl ∷
        Id (Erased A) [ t ] ([ t ])
    []-cong″-computes _ _ Δ A t ρ Δ⊇Γ ⊢A ⊢t =
      let open Has-weaker-[]-cong→Has-[]-cong hyp₁ hyp₂ hyp₃ has-[]-cong

          ok₁ , ok₂ , ok₃ , ok₄ , ⊢[]-cong″ = ⊢[]-cong″

          ⊇ε = WD.»⊇ε (defn-wf (wfTerm ⊢A)) .proj₂
      in
      wk ρ
        (lam 𝟘 $ lam 𝟘 $ lam 𝟘 $ lam 𝟘 $
         cong 𝟘 (Erased (Erased (var x3))) [ [ var x2 ] ]
           [ [ var x1 ] ] (Erased (var x3))
           (mapᴱ (Erased (var x4)) (erased (var x5) (var x0))
              (var x0))
           (wk (stepn id 4) []-cong′ ∘⟨ ω ⟩ Erased (var x3)
              ∘⟨ ω ⟩ [ var x2 ] ∘⟨ ω ⟩ [ var x1 ]
              ∘⟨ 𝟘 ⟩ cong 𝟘 (var x3) (var x2) (var x1)
                       (Erased (var x3)) [ var x0 ] (var x0)))
        ∘⟨ 𝟘 ⟩ A ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ t ∘⟨ 𝟘 ⟩ rfl ∷
        Id (Erased A) [ t ] ([ t ])                                    ⇒*⟨ β-red-⇒₄′ ok₁ ok₂ ok₃ ok₄
                                                                             (W.wkTerm
                                                                                (W.liftnʷ Δ⊇Γ $ ∙_ $ ⊢Id-2-1-0 $ wfTerm $
                                                                                 WD.defn-wkTerm ⊇ε ⊢[]-cong′) $
                                                                                WD.defn-wkTerm ⊇ε ⊢[]-cong″)
                                                                             ⊢A ⊢t ⊢t (rflⱼ ⊢t) ⟩⊢∷
                                                                        ˘⟨ Id-cong (refl ⊢Erased-A) mapᴱ-lemma mapᴱ-lemma ⟩≡
      wk (liftn ρ 4)
        (cong 𝟘 (Erased (Erased (var x3))) [ [ var x2 ] ]
           [ [ var x1 ] ] (Erased (var x3))
           (mapᴱ (Erased (var x4)) (erased (var x5) (var x0))
              (var x0))
           (wk (stepn id 4) []-cong′ ∘⟨ ω ⟩ Erased (var x3)
              ∘⟨ ω ⟩ [ var x2 ] ∘⟨ ω ⟩ [ var x1 ]
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
                                                                                lemma _ _ _ _)
                                                                               cong-[]) ⟩⊢∷≡
      cong 𝟘 (Erased (Erased A)) [ [ t ] ] [ [ t ] ] (Erased A)
        (mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0))
        (wk ρ []-cong′ ∘⟨ ω ⟩ Erased A ∘⟨ ω ⟩ [ t ] ∘⟨ ω ⟩ [ t ]
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
                                                                             W.wkTerm Δ⊇Γ $
                                                                             WD.defn-wkTerm ⊇ε ⊢[]-cong′) $
                                                                          cong-≡ ⊢t ([]ⱼ Erased-ok (var₀ (univ ⊢A))) ⟩⊢
      cong 𝟘 (Erased (Erased A)) [ [ t ] ] [ [ t ] ] (Erased A)
        (mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0))
        (wk ρ []-cong′ ∘⟨ ω ⟩ Erased A ∘⟨ ω ⟩ [ t ] ∘⟨ ω ⟩ [ t ]
           ∘⟨ 𝟘 ⟩ rfl)                                                 ≡⟨ cong-cong (refl ⊢Erased-Erased-A) (refl ⊢[[t]]) (refl ⊢[[t]])
                                                                            (refl ⊢Erased-A) (refl ⊢mapᴱ-0) $
                                                                          []-cong′≡ _ _ _ _ _ _ Δ⊇Γ ⊢Erased-A∷U ⊢[t] ⟩⊢
      cong 𝟘 (Erased (Erased A)) [ [ t ] ] [ [ t ] ] (Erased A)
        (mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0))
        rfl                                                            ⇒⟨ cong-⇒ ⊢[[t]] ⊢mapᴱ-0 ⟩⊢∎

      rfl                                                              ∎
      where
      Erased-ok : Erased-allowed s
      Erased-ok =
        proj₂ $ inversion-Erased $
        proj₁ $ inversion-Id $
        proj₁ $ proj₂ $ inversion-ΠΣ $
        proj₁ $ proj₂ $ inversion-ΠΣ $
        proj₁ $ proj₂ $ inversion-ΠΣ $
        proj₁ $ proj₂ $ inversion-ΠΣ $
        syntacticTerm $ has-[]-cong′ .proj₂ .proj₂

      ⊢[t] : Δ ⊢ [ t ] ∷ Erased A
      ⊢[t] = []ⱼ Erased-ok ⊢t

      ⊢[[t]] : Δ ⊢ [ [ t ] ] ∷ Erased (Erased A)
      ⊢[[t]] = []ⱼ Erased-ok ⊢[t]

      ⊢Erased-A : Δ ⊢ Erased A
      ⊢Erased-A = syntacticTerm ⊢[t]

      ⊢Erased-Erased-A : Δ ⊢ Erased (Erased A)
      ⊢Erased-Erased-A = syntacticTerm ⊢[[t]]

      ⊢Erased-A∷U : Δ ⊢ Erased A ∷ U l
      ⊢Erased-A∷U = Erasedⱼ-U Erased-ok ⊢A

      ⊢mapᴱ-0 :
        Δ »∙ Erased (Erased A) ⊢
          mapᴱ (Erased (wk1 A)) (erased (wk2 A) (var x0)) (var x0) ∷
          Erased (wk1 A)
      ⊢mapᴱ-0 =
        ⊢mapᴱ (erasedⱼ (var₀ (W.wk₁ ⊢Erased-Erased-A ⊢Erased-A)))
          (var₀ ⊢Erased-Erased-A)

      mapᴱ-lemma :
        Δ ⊢
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

        [ erased A ([ t ]) ]                                      ≡⟨ P.[]-cong′ Erased-ok $
                                                                     Erased-β Erased-ok ⊢t ⟩⊢∎
        [ t ]                                                     ∎

opaque

  -- A variant of ¬-[]-cong for Has-weaker-[]-cong.

  ¬-Has-weaker-[]-cong :
    ⦃ not-ok : No-equality-reflection ⦄
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    (s PE.≡ 𝕨 → ¬ T 𝟘ᵐ-allowed → Trivial × Prodrec-allowed 𝟙ᵐ 𝟘 𝟘 𝟘) →
    (s PE.≡ 𝕤 → ¬ T 𝟘ᵐ-allowed → 𝟘 ≤ 𝟙) →
    (Π-allowed ω q₁ → Π-allowed 𝟘 q₁′) →
    (Π-allowed ω q₂ → Π-allowed 𝟘 q₂′) →
    (Π-allowed ω q₃ → Π-allowed 𝟘 q₃′) →
    No-erased-matches TR UR →
    (∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘) →
    Consistent (ε » Δ) →
    ¬ Has-weaker-[]-cong s 𝟙ᵐ l Δ q₁ q₂ q₃ q₄
  ¬-Has-weaker-[]-cong
    {s} {q₁} {q₁′} {q₂} {q₂′} {q₃} {q₃′} {Δ} {l} {q₄}
    trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ nem Unitʷ-η→ consistent =
    Has-weaker-[]-cong s 𝟙ᵐ l Δ q₁ q₂ q₃ q₄  →⟨ Has-weaker-[]-cong→Has-[]-cong trivial 𝟘≤𝟙 hyp₁ hyp₂ hyp₃ ⟩
    Has-[]-cong s 𝟙ᵐ l Δ q₁′ q₂′ q₃′ q₄      →⟨ ¬-[]-cong nem Unitʷ-η→ consistent ⟩
    ⊥                                        □
