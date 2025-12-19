------------------------------------------------------------------------
-- Inversion properties of the heap reduction relations.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Reduction.Inversion
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄 𝐌)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (∣ε∣ : M)
  where

open Type-variant type-variant
open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Reduction type-variant UR factoring-nr ∣ε∣

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  m n m′ n′ n″ k : Nat
  H : Heap _ _
  x : Fin _
  A B t u v w : Term _
  ρ ρ′ : Wk _ _
  S : Stack _
  s : State _ _ _
  s′ : Strength
  l l₁ l₂ : Universe-level
  p p′ q q′ r : M

opaque

  -- Inversion of variables

  ⇾ₑ-inv-var :
    ⟨ H , var x , ρ , S ⟩ ⇾ₑ s →
    ∃ λ p → ∣ S ∣≡ p × State.stack s ≡ S ×
    H ⊢ wkVar ρ x ↦[ p ] State.head s , State.env s ⨾ State.heap s
  ⇾ₑ-inv-var (var x y) = _ , x , refl , y
  ⇾ₑ-inv-var (⇒ₑ ())

opaque

  -- Inversion of variables

  ⇢ₑ-inv-var :
    ⟨ H , var x , ρ , S ⟩ ⇢ₑ s →
    State.heap s ≡ H × State.stack s ≡ S ×
    H ⊢ wkVar ρ x ↦ (State.head s , State.env s)
  ⇢ₑ-inv-var (var x) = refl , refl , x
  ⇢ₑ-inv-var (⇒ₑ ())

opaque

  -- Inversion of application

  ⇒ₑ-inv-∘ :
    ⟨ H , t ∘⟨ p ⟩ u , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , ∘ₑ p u ρ ∙ S ⟩
  ⇒ₑ-inv-∘ appₕ = refl

opaque

  -- Inversion of fst

  ⇒ₑ-inv-fst :
    ⟨ H , fst p t , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , fstₑ p ∙ S ⟩
  ⇒ₑ-inv-fst fstₕ = refl

opaque

  -- Inversion of snd

  ⇒ₑ-inv-snd :
    ⟨ H , snd p t , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , sndₑ p ∙ S ⟩
  ⇒ₑ-inv-snd sndₕ = refl

opaque

  -- Inversion of prodrec

  ⇒ₑ-inv-prodrec :
    ⟨ H , prodrec r p q A t u , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , prodrecₑ r p q A u ρ ∙ S ⟩
  ⇒ₑ-inv-prodrec prodrecₕ = refl

opaque

  -- Inversion of natrec

  ⇒ₑ-inv-natrec :
    ⟨ H , natrec p q r A u v t , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , natrecₑ p q r A u v ρ ∙ S ⟩
  ⇒ₑ-inv-natrec natrecₕ = refl

opaque

  -- Inversion of unitrec

  ⇒ₑ-inv-unitrec :
    ⟨ H , unitrec l p q A t u , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , unitrecₑ l p q A u ρ ∙ S ⟩ × ¬ Unitʷ-η
  ⇒ₑ-inv-unitrec (unitrecₕ x) = refl , x

opaque

  -- Inversion of emptyrec

  ⇒ₑ-inv-emptyrec :
    ⟨ H , emptyrec p A t , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , emptyrecₑ p A ρ ∙ S ⟩
  ⇒ₑ-inv-emptyrec emptyrecₕ = refl

opaque

  -- Inversion of J

  ⇒ₑ-inv-J :
    ⟨ H , J p q A u B v w t , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , Jₑ p q A u B v w ρ ∙ S ⟩
  ⇒ₑ-inv-J Jₕ = refl

opaque

  -- Inversion of K

  ⇒ₑ-inv-K : ⟨ H , K p A u B v t , ρ , S ⟩ ⇒ₑ s →
             s ≡ ⟨ H , t , ρ , Kₑ p A u B v ρ ∙ S ⟩
  ⇒ₑ-inv-K Kₕ = refl

opaque

  -- Inversion of []-cong

  ⇒ₑ-inv-[]-cong :
    ⟨ H , []-cong s′ A u v t , ρ , S ⟩ ⇒ₑ s →
    s ≡ ⟨ H , t , ρ , []-congₑ s′ A u v ρ ∙ S ⟩
  ⇒ₑ-inv-[]-cong []-congₕ = refl

opaque

  -- Inversion of lambda

  ⇒ᵥ-inv-lam :
    {H : Heap k m′} {t : Term (1+ n′)} {s : State _ m n} →
    ⟨ H , lam p t , ρ , S ⟩ ⇒ᵥ s →
    ∃₅ λ k q u (ρ′ : Wk _ k) S′ → ∣ S′ ∣≡ q × S ≡ ∘ₑ p u ρ′ ∙ S′ ×
       Σ (m ≡ 1+ m′) λ m≡ → Σ (n ≡ 1+ n′) λ n≡ →
         subst₂ (State _) m≡ n≡ s ≡
           ⟨ H ∙ (q · p , u , ρ′) , t , lift ρ , wk1ˢ S′ ⟩
  ⇒ᵥ-inv-lam (lamₕ x) = _ , _ , _ , _ , _ , x , refl , refl , refl , refl

opaque

  -- Inversion of lambda with an application on top of the stack

  ⇒ᵥ-inv-lam-∘ₑ :
    {H : Heap k m′} {t : Term (1+ n′)} {s : State _ m n} →
    ⟨ H , lam p t , ρ , ∘ₑ q u ρ′ ∙ S ⟩ ⇒ᵥ s →
    ∃ λ q → ∣ S ∣≡ q ×
    Σ (m ≡ 1+ m′) λ m≡ → Σ (n ≡ 1+ n′) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡
        ⟨ H ∙ (q · p , u , ρ′) , t , lift ρ , wk1ˢ S ⟩
  ⇒ᵥ-inv-lam-∘ₑ d =
    case ⇒ᵥ-inv-lam d of λ {
      (_ , _ , _ , _ , _ , ∣S∣≡ , refl , refl , refl , refl) →
    _ , ∣S∣≡ , refl , refl , refl }

opaque

  -- Inversion of prodˢ

  ⇒ᵥ-inv-prodˢ :
    {H : Heap k m′} {t : Term n′} {s : State _ m n} →
    ⟨ H , prodˢ p t u , ρ , S ⟩ ⇒ᵥ s →
    ∃ λ S′ → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
      (S ≡ fstₑ p ∙ S′ × subst₂ (State _) m≡ n≡ s ≡ ⟨ H , t , ρ , S′ ⟩ ⊎
       S ≡ sndₑ p ∙ S′ × subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ , S′ ⟩)
  ⇒ᵥ-inv-prodˢ prodˢₕ₁ = _ , refl , refl , inj₁ (refl , refl)
  ⇒ᵥ-inv-prodˢ prodˢₕ₂ = _ , refl , refl , inj₂ (refl , refl)

opaque

  -- Inversion of prodˢ with a first projection on top of the stack

  ⇒ᵥ-inv-prodˢ-fstₑ :
    {H : Heap k m′} {t : Term n′} {s : State _ m n} →
    ⟨ H , prodˢ p t u , ρ , fstₑ q ∙ S ⟩ ⇒ᵥ s →
    Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡ ⟨ H , t , ρ , S ⟩
  ⇒ᵥ-inv-prodˢ-fstₑ d =
    case ⇒ᵥ-inv-prodˢ d of λ where
      (_ , refl , refl , inj₁ (refl , refl)) →
        refl , refl , refl
      (_ , _ , _ , inj₂ (() , _))

opaque

  -- Inversion of prodˢ with a second projection on top of the stack

  ⇒ᵥ-inv-prodˢ-sndₑ :
    {H : Heap k m′} {t : Term n′} {s : State _ m n} →
    ⟨ H , prodˢ p t u , ρ , sndₑ q ∙ S ⟩ ⇒ᵥ s →
      Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
        subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ , S ⟩
  ⇒ᵥ-inv-prodˢ-sndₑ d =
    case ⇒ᵥ-inv-prodˢ d of λ where
      (_ , _    , _    , inj₁ (() , _))
      (_ , refl , refl , inj₂ (refl , refl)) →
        refl , refl , refl

opaque

  -- Inversion of prodʷ

  ⇒ᵥ-inv-prodʷ :
    {H : Heap k m′} {t u : Term n′} {s : State _ m n} →
    ⟨ H , prodʷ p t u , ρ , S ⟩ ⇒ᵥ s →
    ∃₈ λ k r q q′ A v (ρ′ : Wk _ k) S′ → ∣ S′ ∣≡ q′ × S ≡ prodrecₑ r p q A v ρ′ ∙ S′ ×
    Σ (m ≡ 2+ m′) λ m≡ → Σ (n ≡ 2+ k) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡
        ⟨ H ∙ (q′ · r · p , t , ρ) ∙ (q′ · r , u , step ρ) , v
           , liftn ρ′ 2 , wk2ˢ S′ ⟩
  ⇒ᵥ-inv-prodʷ (prodʷₕ x) =
    _ , _ , _ , _ , _ , _ , _ , _ , x , refl , refl , refl , refl

opaque

  -- Inversion of prodʷ with prodrec on top of the stack

  ⇒ᵥ-inv-prodʷ-prodrecₑ :
    {H : Heap k m′} {v : Term (2+ n″)} {s : State _ m n} →
    ⟨ H , prodʷ p t u , ρ , prodrecₑ r p′ q A v ρ′ ∙ S ⟩ ⇒ᵥ s →
    ∃ λ q′ → ∣ S ∣≡ q′ ×
    Σ (m ≡ 2+ m′) λ m≡ → Σ (n ≡ 2+ n″) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡
        ⟨ H ∙ (q′ · r · p , t , ρ) ∙ (q′ · r , u , step ρ) , v
           , liftn ρ′ 2 , wk2ˢ S ⟩
  ⇒ᵥ-inv-prodʷ-prodrecₑ d =
    case ⇒ᵥ-inv-prodʷ d of λ {
      (_ , _ , _  , _ , _ , _ , _ , _ , ∣S∣≡ , refl , refl , refl , refl) →
    _ , ∣S∣≡ , refl , refl , refl}

opaque

  -- Inversion of zero

  ⇒ᵥ-inv-zero :
    {H : Heap k m′} {s : State _ m n} →
    ⟨ H , zero , ρ , S ⟩ ⇒ᵥ s →
    ∃₉ λ n′ p q r A u v (ρ′ : Wk _ n′) S′ →
       S ≡ natrecₑ p q r A u v ρ′ ∙ S′ ×
       Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
         subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ′ , S′ ⟩
  ⇒ᵥ-inv-zero zeroₕ =
    _ , _ , _ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl

opaque

  -- Inversion of zero with natrec on top of the stack

  ⇒ᵥ-inv-zero-natrecₑ :
    {H : Heap k m′} {u : Term n′} {s : State _ m n} →
    ⟨ H , zero , ρ , natrecₑ p q r A u v ρ′ ∙ S ⟩ ⇒ᵥ s →
    Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ′ , S ⟩
  ⇒ᵥ-inv-zero-natrecₑ d =
    case ⇒ᵥ-inv-zero d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _
         , refl , refl , refl , refl) →
    refl , refl , refl }

opaque

  -- Inversion of suc

  ⇒ᵥ-inv-suc :
    {H : Heap k m′} {t : Term n′} {s : State _ m n} →
    ⟨ H , suc t , ρ , S ⟩ ⇒ᵥ s →
    ∃₁₁ λ n′ p q r q′ p′ A u v (ρ′ : Wk _ n′) S′ →
       ∣ S′ ∣≡ q′ × ∣natrec p , r ∣≡ p′ ×
       S ≡ natrecₑ p q r A u v ρ′ ∙ S′ ×
       Σ (m ≡ 2+ m′) λ m≡ → Σ (n ≡ 2+ n′) λ n≡ →
         subst₂ (State _) m≡ n≡ s ≡
           ⟨ H ∙ (q′ · p′ , t , ρ)
              ∙ (q′ · r , natrec p q r (wk (lift (step id)) A)
                              (wk1 u) (wk (liftn (step id) 2) v) (var x0)
                            , lift ρ′)
              , v , liftn ρ′ 2  , wk2ˢ S′ ⟩
  ⇒ᵥ-inv-suc (sucₕ ∣S∣≡ ∣nr∣≡) =
    _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ∣S∣≡ , ∣nr∣≡ , refl , refl , refl , refl

opaque

  -- Inversion of suc with natrec on top of the stack

  ⇒ᵥ-inv-suc-natrecₑ :
    {H : Heap k m′} {u : Term n′} {s : State _ m n} →
    ⟨ H , suc t , ρ , natrecₑ p q r A u v ρ′ ∙ S ⟩ ⇒ᵥ s →
    ∃₂ λ q′ p′ → ∣ S ∣≡ q′ × ∣natrec p , r ∣≡ p′ ×
    Σ (m ≡ 2+ m′) λ m≡ → Σ (n ≡ 2+ n′) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡
        ⟨ H ∙ (q′ · p′ , t , ρ)
            ∙ (q′ · r , natrec p q r (wk (lift (step id)) A) (wk1 u)
                             (wk (liftn (step id) 2) v) (var x0)
                         , lift ρ′)
            , v , liftn ρ′ 2  , wk2ˢ S ⟩
  ⇒ᵥ-inv-suc-natrecₑ d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _
         , ∣S∣≡ , ∣nr∣≡ , refl , refl , refl , refl) →
    _ , _ , ∣S∣≡ , ∣nr∣≡ , refl , refl , refl}

opaque

  -- Inversion of starʷ

  ⇒ᵥ-inv-starʷ :
    {H : Heap k m′} {s : State _ m n} →
    ⟨ H , starʷ l , ρ , S ⟩ ⇒ᵥ s →
    ∃₇ λ n′ p q A u (ρ′ : Wk _ n′) S′ →
    S ≡ unitrecₑ l p q A u ρ′ ∙ S′ ×
    ∃₂ λ (m≡ : m ≡ m′) (n≡ : n ≡ n′) →
    subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ′ , S′ ⟩
  ⇒ᵥ-inv-starʷ starʷₕ =
    _ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl

opaque

  -- Inversion of starʷ with unitrec on top of the stack

  ⇒ᵥ-inv-starʷ-unitrecₑ :
    {H : Heap k m′} {u : Term n′} {s : State _ m n} →
    ⟨ H , starʷ l₁ , ρ , unitrecₑ l₂ p q A u ρ′ ∙ S ⟩ ⇒ᵥ s →
    l₁ ≡ l₂ × ∃₂ λ (m≡ : m ≡ m′) (n≡ : n ≡ n′) →
    subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ′ , S ⟩
  ⇒ᵥ-inv-starʷ-unitrecₑ d =
    case ⇒ᵥ-inv-starʷ d of λ {
      (_ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl) →
    refl , refl , refl , refl }

opaque

  -- Inversion of unitrec with eta equality turned on

  ⇒ᵥ-inv-unitrec-η :
    {H : Heap k m′} {s : State _ m n} →
    ⟨ H , unitrec l p q A t u , ρ , S ⟩ ⇒ᵥ s →
    Unitʷ-η × ∃₂ λ (m≡ : m ≡ m′) (n≡ : n ≡ n′) →
    subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ , S ⟩
  ⇒ᵥ-inv-unitrec-η (unitrec-ηₕ x) = x , refl , refl , refl

opaque

  -- Inversion of rfl

  ⇒ᵥ-inv-rfl :
    {H : Heap k m′} {s : State _ m n} →
    ⟨ H , rfl , ρ , S ⟩ ⇒ᵥ s →
    ∃₅ λ S′ A t u ρ′ → Σ (m ≡ m′) λ m≡ →
      (∃₄ λ p q B v → S ≡ Jₑ p q A t B u v ρ′ ∙ S′ ×
          subst (λ m → State _ m _) m≡ s ≡ ⟨ H , u , ρ′ , S′ ⟩) ⊎
      (∃₂ λ p B → S ≡ Kₑ p A t B u ρ′ ∙ S′ ×
          subst (λ m → State _ m _) m≡ s ≡ ⟨ H , u , ρ′ , S′ ⟩) ⊎
      (∃ λ s′ → S ≡ []-congₑ s′ A t u ρ′ ∙ S′ ×
         subst (λ m → State _ m _) m≡ s ≡ ⟨ H , rfl , ρ′ , S′ ⟩)
  ⇒ᵥ-inv-rfl rflₕⱼ =
    _ , _ , _ , _ , _ , refl , inj₁ (_ , _ , _ , _ , refl , refl)
  ⇒ᵥ-inv-rfl rflₕₖ =
    _ , _ , _ , _ , _ , refl , inj₂ (inj₁ (_ , _ , refl , refl))
  ⇒ᵥ-inv-rfl rflₕₑ =
    _ , _ , _ , _ , _ , refl , inj₂ (inj₂ (_ , refl , refl))

opaque

  -- Inversion of rfl with Jₑ on top of the stack

  ⇒ᵥ-inv-rfl-Jₑ :
    {H : Heap k m′} {t : Term n′} {s : State _ m n} →
    ⟨ H , rfl , ρ , Jₑ p q A t B u v ρ′ ∙ S ⟩ ⇒ᵥ s →
    Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ′ , S ⟩
  ⇒ᵥ-inv-rfl-Jₑ d =
    case ⇒ᵥ-inv-rfl d of λ where
      (_ , _ , _ , _ , _ , refl , inj₁ (_ , _ , _ , _ , refl , refl)) →
        refl , refl , refl
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₁ (_ , _ , () , _)))
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₂ ()))

opaque

  -- Inversion of rfl with Kₑ on top of the stack

  ⇒ᵥ-inv-rfl-Kₑ :
    {H : Heap k m′} {t : Term n′} {s : State _ m n} →
    ⟨ H , rfl , ρ , Kₑ p A t B u ρ′ ∙ S ⟩ ⇒ᵥ s →
    Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , ρ′ , S ⟩
  ⇒ᵥ-inv-rfl-Kₑ d =
    case ⇒ᵥ-inv-rfl d of λ where
      (_ , _ , _ , _ , _ , refl , inj₁ (_ , _ , _ , _ , () , _))
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₁ (_ , _ , refl , refl))) →
        refl , refl , refl
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₂ ()))

opaque

  -- Inversion of rfl with []-congₑ on top of the stack

  ⇒ᵥ-inv-rfl-[]-congₑ :
    {H : Heap k m′} {t : Term n′} {s : State _ m n} →
    ⟨ H , rfl , ρ , []-congₑ s′ A t u ρ′ ∙ S ⟩ ⇒ᵥ s →
    Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
      subst₂ (State _) m≡ n≡ s ≡ ⟨ H , rfl , ρ′ , S ⟩
  ⇒ᵥ-inv-rfl-[]-congₑ d =
    case ⇒ᵥ-inv-rfl d of λ where
      (_ , _ , _ , _ , _ , refl , inj₁ (_ , _ , _ , _ , () , _))
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₁ (_ , _ , () , _)))
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₂ (_ , refl , refl))) →
        refl , refl , refl

opaque

  -- Inversion of suc

  ⇒ₙ-inv-suc :
    ¬ Numeral t → ⟨ H , suc t , ρ , S ⟩ ⇒ₙ s →
    ∃ λ k → S ≡ sucₛ k × s ≡ ⟨ H , t , ρ , sucₑ ∙ S ⟩
  ⇒ₙ-inv-suc _ (sucₕ _) = _ , refl , refl
  ⇒ₙ-inv-suc ¬n (numₕ (sucₙ n)) = ⊥-elim (¬n n)

opaque

  -- Inversion of numerals

  ⇒ₙ-inv-num :
    Numeral t → ⟨ H , t , ρ , S ⟩ ⇒ₙ s →
    ∃ λ S′ → S ≡ sucₑ ∙ S′ × s ≡ ⟨ H , suc t , ρ , S′ ⟩
  ⇒ₙ-inv-num (sucₙ n) (sucₕ ¬n) = ⊥-elim (¬n n)
  ⇒ₙ-inv-num _ (numₕ _) = _ , refl , refl

opaque

  -- Inversion of variable

  ⇒ᵥ-inv-var : ⟨ H , var x , ρ , S ⟩ ⇒ᵥ s → ⊥
  ⇒ᵥ-inv-var ()

opaque

  -- Inversion of lambda

  ⇒ₑ-inv-lam : ⟨ H , lam p t , ρ , S ⟩ ⇒ₑ s → ⊥
  ⇒ₑ-inv-lam ()

opaque

  -- Inversion of prod

  ⇒ₑ-inv-prod : ⟨ H , prod s′ p t u , ρ , S ⟩ ⇒ₑ s → ⊥
  ⇒ₑ-inv-prod ()

opaque

  -- Inversion of zero

  ⇒ₑ-inv-zero : ⟨ H , zero , ρ , S ⟩ ⇒ₑ s → ⊥
  ⇒ₑ-inv-zero ()

opaque

  -- Inversion of suc

  ⇒ₑ-inv-suc : ⟨ H , suc t , ρ , S ⟩ ⇒ₑ s → ⊥
  ⇒ₑ-inv-suc ()

opaque

  -- Inversion of star

  ⇒ₑ-inv-star : ⟨ H , star s′ l , ρ , S ⟩ ⇒ₑ s → ⊥
  ⇒ₑ-inv-star ()

opaque

  -- Inversion of unitrec with η-equality

  ⇒ₑ-inv-unitrec-η :
    Unitʷ-η → ⟨ H , unitrec l p q A t u , ρ , S ⟩ ⇒ₑ s → ⊥
  ⇒ₑ-inv-unitrec-η η (unitrecₕ no-η) = no-η η

opaque

  -- Inversion of rfl

  ⇒ₑ-inv-rfl : ⟨ H , rfl , ρ , S ⟩ ⇒ₑ s → ⊥
  ⇒ₑ-inv-rfl ()

opaque

  -- Inversion of variable

  ⇒ₙ-inv-var : ⟨ H , var x , ρ , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-var (numₕ ())

opaque

  -- Inversion of natrec

  ⇒ₙ-inv-natrec : ⟨ H , natrec p q r A t u v , ρ , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-natrec (numₕ ())

opaque

  -- Inversion of sucᵏ

  ↠-inv-sucᵏ : ⟨ H , sucᵏ k , ρ , ε ⟩ ↠ s → ⊥
  ↠-inv-sucᵏ {k = 0} (⇾ₑ′ x) = ⇒ₑ-inv-zero x
  ↠-inv-sucᵏ {k = 1+ k} (⇾ₑ′ x) = ⇒ₑ-inv-suc x
  ↠-inv-sucᵏ {k = 0} (⇒ᵥ ())
  ↠-inv-sucᵏ {k = 1+ k} (⇒ᵥ ())
  ↠-inv-sucᵏ {k = 0} (⇒ₙ ())
  ↠-inv-sucᵏ {k = 1+ k} (⇒ₙ x) =
    case ⇒ₙ-inv-num (sucᵏ-Numeral _) x of λ where
      (_ , () , _)
