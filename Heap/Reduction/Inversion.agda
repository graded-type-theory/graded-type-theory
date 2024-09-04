------------------------------------------------------------------------
-- Inversion properties of the heap reduction relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Tools.Bool
open import Heap.Options
open import Definition.Typed.Variant

module Heap.Reduction.Inversion
  {a} {M : Set a} (𝕄 : Modality M)
  (type-variant : Type-variant)
  (opts : Options)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open Options opts
open Type-variant type-variant

open import Definition.Untyped M

open import Heap.Untyped 𝕄 type-variant
open import Heap.Untyped.Properties 𝕄 type-variant
open import Heap.Reduction 𝕄 type-variant opts

open import Graded.Modality.Nr-instances

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum hiding (id)

private variable
  m n m′ n′ n″ k : Nat
  H : Heap _ _
  x : Fin _
  A B t u v w : Term _
  E E′ : Env _ _
  S : Stack _
  s : State _ _ _
  s′ : Strength
  p p′ q r : M

opaque

  -- Inversion of variables

  ⇒ₙ-inv-var : ⦃ Track-resources ⦄
             → ⟨ H , var x , E , S ⟩ ⇒ₙ s
             → State.stack s ≡ S ×
               H ⊢ wkVar E x ↦[ ∣ S ∣ ] State.head s , State.env s ⨾ State.heap s
  ⇒ₙ-inv-var (varₕ x) = refl , x
  ⇒ₙ-inv-var (varₕ′ x) = ⊥-elim not-tracking-and-no-tracking

opaque

  -- Inversion of variables

  ⇒ₙ-inv-var′ : ⦃ ¬Track-resources ⦄
              → ⟨ H , var x , E , S ⟩ ⇒ₙ s
              → State.heap s ≡ H × State.stack s ≡ S ×
              H ⊢ wkVar E x ↦ (State.head s , State.env s)
  ⇒ₙ-inv-var′ (varₕ x) = ⊥-elim not-tracking-and-no-tracking
  ⇒ₙ-inv-var′ (varₕ′ x) = refl , refl , x

opaque

  -- Inversion of application

  ⇒ₙ-inv-∘ : {t : Term n} {s : State _ _ m}
           → ⟨ H , t ∘⟨ p ⟩ u , E , S ⟩ ⇒ₙ s
           → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , ∘ₑ p u E ∙ S ⟩
  ⇒ₙ-inv-∘ appₕ = refl , refl

opaque

  -- Inversion of fst

  ⇒ₙ-inv-fst : {t : Term n} {s : State _ _ m}
             → ⟨ H , fst p t , E , S ⟩ ⇒ₙ s
             → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , fstₑ p ∙ S ⟩
  ⇒ₙ-inv-fst fstₕ = refl , refl

opaque

  -- Inversion of snd

  ⇒ₙ-inv-snd : {t : Term n} {s : State _ _ m}
             → ⟨ H , snd p t , E , S ⟩ ⇒ₙ s
             → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , sndₑ p ∙ S ⟩
  ⇒ₙ-inv-snd sndₕ = refl , refl

opaque

  -- Inversion of prodrec

  ⇒ₙ-inv-prodrec : {t : Term n} {s : State _ _ m}
                 → ⟨ H , prodrec r p q A t u , E , S ⟩ ⇒ₙ s
                 → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , prodrecₑ r p q A u E ∙ S ⟩
  ⇒ₙ-inv-prodrec prodrecₕ = refl , refl

opaque

  -- Inversion of natrec

  ⇒ₙ-inv-natrec : {t : Term n} {s : State _ _ m}
                → ⟨ H , natrec p q r A u v t , E , S ⟩ ⇒ₙ s
                → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , natrecₑ p q r A u v E ∙ S ⟩
  ⇒ₙ-inv-natrec natrecₕ = refl , refl

opaque

  -- Inversion of unitrec

  ⇒ₙ-inv-unitrec : {t : Term n} {s : State _ _ m}
                 → ⟨ H , unitrec p q A t u , E , S ⟩ ⇒ₙ s
                 → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , unitrecₑ p q A u E ∙ S ⟩
  ⇒ₙ-inv-unitrec (unitrecₕ _) = refl , refl

opaque

  -- Inversion of J

  ⇒ₙ-inv-J : {t : Term n} {s : State _ _ m}
           → ⟨ H , J p q A u B v w t , E , S ⟩ ⇒ₙ s
           → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , Jₑ p q A u B v w E ∙ S ⟩
  ⇒ₙ-inv-J Jₕ = refl , refl

opaque

  -- Inversion of K

  ⇒ₙ-inv-K : {t : Term n} {s : State _ _ m}
           → ⟨ H , K p A u B v t , E , S ⟩ ⇒ₙ s
           → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , Kₑ p A u B v E ∙ S ⟩
  ⇒ₙ-inv-K Kₕ = refl , refl

opaque

  -- Inversion of []-cong

  ⇒ₙ-inv-[]-cong : {t : Term n} {s : State _ _ m}
                 → ⟨ H , []-cong s′ A u v t , E , S ⟩ ⇒ₙ s
                 → Σ (m ≡ n) λ m≡n → subst (State _ _) m≡n s ≡ ⟨ H , t , E , []-congₑ s′ A u v E ∙ S ⟩
  ⇒ₙ-inv-[]-cong []-congₕ = refl , refl

opaque

  -- Inversion of lambda

  ⇒ᵥ-inv-lam : {H : Heap k m′} {t : Term (1+ n′)} {s : State _ m n}
             → ⟨ H , lam p t , E , S ⟩ ⇒ᵥ s
             → ∃₄ λ k u (E′ : Env _ k) S′ → S ≡ ∘ₑ p u E′ ∙ S′ ×
               Σ (m ≡ 1+ m′) λ m≡ → Σ (n ≡ 1+ n′) λ n≡ →
                   subst₂ (State _) m≡ n≡ s ≡ ⟨ H ∙ (∣ S′ ∣ · p , u , E′) , t , lift E , wk1ˢ S′ ⟩
  ⇒ᵥ-inv-lam lamₕ = _ , _ , _ , _ , refl , refl , refl , refl

opaque

  -- Inversion of lambda with an application on top of the stack

  ⇒ᵥ-inv-lam-∘ₑ : {H : Heap k m′} {t : Term (1+ n′)} {s : State _ m n}
                → ⟨ H , lam p t , E , ∘ₑ q u E′ ∙ S ⟩ ⇒ᵥ s
                → Σ (m ≡ 1+ m′) λ m≡ → Σ (n ≡ 1+ n′) λ n≡ →
                   subst₂ (State _) m≡ n≡ s ≡ ⟨ H ∙ (∣ S ∣ · p , u , E′) , t , lift E , wk1ˢ S ⟩
  ⇒ᵥ-inv-lam-∘ₑ d =
    case ⇒ᵥ-inv-lam d of λ {
      (_ , _ , _ , _ , refl , refl , refl , refl) →
    refl , refl , refl }

opaque

  -- Inversion of prodˢ

  ⇒ᵥ-inv-prodˢ : {H : Heap k m′} {t : Term n′} {s : State _ m n}
               → ⟨ H , prodˢ p t u , E , S ⟩ ⇒ᵥ s
               → ∃ λ S′ → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                  (S ≡ fstₑ p ∙ S′ × subst₂ (State _) m≡ n≡ s ≡ ⟨ H , t , E , S′ ⟩ ⊎
                   S ≡ sndₑ p ∙ S′ × subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E , S′ ⟩)
  ⇒ᵥ-inv-prodˢ prodˢₕ₁ = _ , refl , refl , inj₁ (refl , refl)
  ⇒ᵥ-inv-prodˢ prodˢₕ₂ = _ , refl , refl , inj₂ (refl , refl)

opaque

  -- Inversion of strong pairs with a first projection on top of the stack

  ⇒ᵥ-inv-prodˢ-fstₑ : {H : Heap k m′} {t : Term n′} {s : State _ m n}
                    → ⟨ H , prodˢ p t u , E , fstₑ q ∙ S ⟩ ⇒ᵥ s
                    → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                       subst₂ (State _) m≡ n≡ s ≡ ⟨ H , t , E , S ⟩
  ⇒ᵥ-inv-prodˢ-fstₑ d =
    case ⇒ᵥ-inv-prodˢ d of λ {
      (_ , refl , refl , inj₁ (refl , refl)) →
    refl , refl , refl }

opaque

  -- Inversion of prodˢ with a second projection on top of the stack

  ⇒ᵥ-inv-prodˢ-sndₑ : {H : Heap k m′} {t : Term n′} {s : State _ m n}
                    → ⟨ H , prodˢ p t u , E , sndₑ q ∙ S ⟩ ⇒ᵥ s
                    → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                       subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E , S ⟩
  ⇒ᵥ-inv-prodˢ-sndₑ d =
    case ⇒ᵥ-inv-prodˢ d of λ {
      (_ , refl , refl , inj₂ (refl , refl)) →
    refl , refl , refl }

opaque

  -- Inversion of prodʷ

  ⇒ᵥ-inv-prodʷ : {H : Heap k m′} {t u : Term n′} {s : State _ m n}
               → ⟨ H , prodʷ p t u , E , S ⟩ ⇒ᵥ s
               → ∃₄ λ k r q A → ∃₃ λ v (E′ : Env _ k) S′ → S ≡ prodrecₑ r p q A v E′ ∙ S′ ×
                 Σ (m ≡ 2+ m′) λ m≡ → Σ (n ≡ 2+ k) λ n≡ →
                   subst₂ (State _) m≡ n≡ s ≡
                   ⟨ H ∙ (∣ S′ ∣ · r · p , t , E) ∙ (∣ S′ ∣ · r , u , step E) , v , liftn E′ 2 , wk2ˢ S′ ⟩
  ⇒ᵥ-inv-prodʷ prodʷₕ = _ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl

opaque

  -- Inversion of prodʷ with prodrec on top of the stack

  ⇒ᵥ-inv-prodʷ-prodrecₑ : {H : Heap k m′} {t u : Term n′} {v : Term (2+ n″)} {s : State _ m n}
                        → ⟨ H , prodʷ p t u , E , prodrecₑ r p′ q A v E′ ∙ S ⟩ ⇒ᵥ s
                        → Σ (m ≡ 2+ m′) λ m≡ → Σ (n ≡ 2+ n″) λ n≡ →
                          subst₂ (State _) m≡ n≡ s ≡
                            ⟨ H ∙ (∣ S ∣ · r · p , t , E) ∙ (∣ S ∣ · r , u , step E) , v , liftn E′ 2 , wk2ˢ S ⟩
  ⇒ᵥ-inv-prodʷ-prodrecₑ d =
    case ⇒ᵥ-inv-prodʷ d of λ {
      (_ , _ , _  , _ , _ , _ , _ , refl , refl , refl , refl) →
    refl , refl , refl}

opaque

  -- Inversion of zero

  ⇒ᵥ-inv-zero : {H : Heap k m′} {s : State _ m n}
              → ⟨ H , zero , E , S ⟩ ⇒ᵥ s
              → ∃ λ n′ → ∃₄ λ p q r A → ∃₄ λ u v (E′ : Env _ n′) S′ →
                S ≡ natrecₑ p q r A u v E′ ∙ S′ ×
                Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                  subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E′ , S′ ⟩
  ⇒ᵥ-inv-zero zeroₕ = _ , _ , _ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl

opaque

  -- Inversion of zero with natrec on top of the stack

  ⇒ᵥ-inv-zero-natrecₑ : {H : Heap k m′} {u : Term n′} {s : State _ m n}
                      → ⟨ H , zero , E , natrecₑ p q r A u v E′ ∙ S ⟩ ⇒ᵥ s
                      → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                        subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E′ , S ⟩
  ⇒ᵥ-inv-zero-natrecₑ d =
    case ⇒ᵥ-inv-zero d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl) →
    refl , refl , refl }

opaque

  -- Inversion of suc

  ⇒ᵥ-inv-suc : {H : Heap k m′} {t : Term n′} {s : State _ m n}
              → ⟨ H , suc t , E , S ⟩ ⇒ᵥ s
              → ∃ λ n′ → ∃₄ λ p q r A → ∃₄ λ u v (E′ : Env _ n′) S′ →
                S ≡ natrecₑ p q r A u v E′ ∙ S′ ×
                Σ (m ≡ 2+ m′) λ m≡ → Σ (n ≡ 2+ n′) λ n≡ →
                  subst₂ (State _) m≡ n≡ s ≡
                  ⟨ H ∙ (∣ S′ ∣ · nr₂ p r , t , E) ∙ (∣ S′ ∣ · r , natrec p q r (wk (lift (step id)) A) (wk1 u) (wk (liftn (step id) 2) v) (var x0)
                      , lift E′) , v , liftn E′ 2  , wk2ˢ S′ ⟩
  ⇒ᵥ-inv-suc sucₕ = _ , _ , _ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl

opaque

  -- Inversion of suc with natrec on top of the stack

  ⇒ᵥ-inv-suc-natrecₑ : {H : Heap k m′} {u : Term n′} {s : State _ m n}
                     → ⟨ H , suc t , E , natrecₑ p q r A u v E′ ∙ S ⟩ ⇒ᵥ s
                      → Σ (m ≡ 2+ m′) λ m≡ → Σ (n ≡ 2+ n′) λ n≡ →
                        subst₂ (State _) m≡ n≡ s ≡
                          ⟨ H ∙ (∣ S ∣ · nr₂ p r , t , E) ∙ (∣ S ∣ · r , natrec p q r (wk (lift (step id)) A) (wk1 u) (wk (liftn (step id) 2) v) (var x0)
                              , lift E′) , v , liftn E′ 2  , wk2ˢ S ⟩
  ⇒ᵥ-inv-suc-natrecₑ d =
    case ⇒ᵥ-inv-suc d of λ {
      (_ , _ , _ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl) →
    refl , refl , refl}

opaque

  -- Inversion of starʷ

  ⇒ᵥ-inv-starʷ : {H : Heap k m′} {s : State _ m n}
               → ⟨ H , starʷ , E , S ⟩ ⇒ᵥ s
               → ∃₃ λ n′ p q → ∃₄ λ A u (E′ : Env _ n′) S′ →
               S ≡ unitrecₑ p q A u E′ ∙ S′ × Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                 subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E′ , S′ ⟩
  ⇒ᵥ-inv-starʷ starʷₕ = _ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl

opaque

  -- Inversion of starʷ with unitrec on top of the stack

  ⇒ᵥ-inv-starʷ-unitrecₑ : {H : Heap k m′} {u : Term n′} {s : State _ m n}
                        → ⟨ H , starʷ , E , unitrecₑ p q A u E′ ∙ S ⟩ ⇒ᵥ s
                        → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                        subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E′ , S ⟩
  ⇒ᵥ-inv-starʷ-unitrecₑ d =
    case ⇒ᵥ-inv-starʷ d of λ {
      (_ , _ , _ , _ , _ , _ , _ , refl , refl , refl , refl) →
    refl , refl , refl}

opaque

  -- Inversion of unitrec with eta equality turned on

  ⇒ᵥ-inv-unitrec-η : {H : Heap k m′} {s : State _ m n}
                   → ⟨ H , unitrec p q A t u , E , S ⟩ ⇒ᵥ s
                   → Unitʷ-η ×
                    Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                      subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E , S ⟩
  ⇒ᵥ-inv-unitrec-η (unitrec-ηₕ x) = x , refl , refl , refl

opaque

  -- Inversion of rfl

  ⇒ᵥ-inv-rfl : {H : Heap k m′} {s : State _ m n}
             → ⟨ H , rfl , E , S ⟩ ⇒ᵥ s
             → ∃ λ S′ → ∃₄ λ A t u E′ → Σ (m ≡ m′) λ m≡ →
               (∃₄ λ p q B v → S ≡ Jₑ p q A t B u v E′ ∙ S′ × subst (λ m → State _ m _) m≡ s ≡ ⟨ H , u , E′ , S′ ⟩) ⊎
               (∃₂ λ p B → S ≡ Kₑ p A t B u E′ ∙ S′ × subst (λ m → State _ m _) m≡ s ≡ ⟨ H , u , E′ , S′ ⟩) ⊎
               (∃ λ s′ → S ≡ []-congₑ s′ A t u E′ ∙ S′ × subst (λ m → State _ m _) m≡ s ≡ ⟨ H , rfl , E′ , S′ ⟩)
  ⇒ᵥ-inv-rfl rflₕⱼ = _ , _ , _ , _ , _ , refl , inj₁ (_ , _ , _ , _ , refl , refl)
  ⇒ᵥ-inv-rfl rflₕₖ = _ , _ , _ , _ , _ , refl , inj₂ (inj₁ (_ , _ , refl , refl))
  ⇒ᵥ-inv-rfl rflₕₑ = _ , _ , _ , _ , _ , refl , inj₂ (inj₂ (_ , refl , refl))

opaque

  -- Inversion of rfl with Jₑ on top of the stack

  ⇒ᵥ-inv-rfl-Jₑ : {H : Heap k m′} {t : Term n′} {s : State _ m n}
                → ⟨ H , rfl , E , Jₑ p q A t B u v E′ ∙ S ⟩ ⇒ᵥ s
                → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                  subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E′ , S ⟩
  ⇒ᵥ-inv-rfl-Jₑ d =
    case ⇒ᵥ-inv-rfl d of λ where
      (_ , _ , _ , _ , _ , refl , inj₁ (_ , _ , _ , _ , refl , refl)) → refl , refl , refl
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₁ (_ , _ , () , _)))
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₂ ()))

opaque

  -- Inversion of rfl with Kₑ on top of the stack

  ⇒ᵥ-inv-rfl-Kₑ : {H : Heap k m′} {t : Term n′} {s : State _ m n}
                → ⟨ H , rfl , E , Kₑ p A t B u E′ ∙ S ⟩ ⇒ᵥ s
                → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                  subst₂ (State _) m≡ n≡ s ≡ ⟨ H , u , E′ , S ⟩
  ⇒ᵥ-inv-rfl-Kₑ d =
    case ⇒ᵥ-inv-rfl d of λ where
      (_ , _ , _ , _ , _ , refl , inj₁ (_ , _ , _ , _ , () , _))
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₁ (_ , _ , refl , refl))) → refl , refl , refl
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₂ ()))

opaque

  -- Inversion of rfl with []-congₑ on top of the stack

  ⇒ᵥ-inv-rfl-[]-congₑ : {H : Heap k m′} {t : Term n′} {s : State _ m n}
                → ⟨ H , rfl , E , []-congₑ s′ A t u E′ ∙ S ⟩ ⇒ᵥ s
                → Σ (m ≡ m′) λ m≡ → Σ (n ≡ n′) λ n≡ →
                  subst₂ (State _) m≡ n≡ s ≡ ⟨ H , rfl , E′ , S ⟩
  ⇒ᵥ-inv-rfl-[]-congₑ d =
    case ⇒ᵥ-inv-rfl d of λ where
      (_ , _ , _ , _ , _ , refl , inj₁ (_ , _ , _ , _ , () , _))
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₁ (_ , _ , () , _)))
      (_ , _ , _ , _ , _ , refl , inj₂ (inj₂ (_ , refl , refl))) → refl , refl , refl

opaque

  -- Inversion of suc

  ⇒ₛ-inv-suc : ¬ Numeral t
             → ⟨ H , suc t , E , S ⟩ ⇒ₛ s
             → ∃ λ k → S ≡ sucₛ k × s ≡ ⟨ H , t , E , sucₑ ∙ S ⟩
  ⇒ₛ-inv-suc _ (sucₕ _) = _ , refl , refl
  ⇒ₛ-inv-suc ¬n (numₕ (sucₙ n)) = ⊥-elim (¬n n)

opaque

  -- Inversion of numerals

  ⇒ₛ-inv-num : Numeral t
             → ⟨ H , t , E , S ⟩ ⇒ₛ s
             → ∃ λ S′ → S ≡ sucₑ ∙ S′ × s ≡ ⟨ H , suc t , E , S′ ⟩
  ⇒ₛ-inv-num (sucₙ n) (sucₕ ¬n) = ⊥-elim (¬n n)
  ⇒ₛ-inv-num _ (numₕ _) = _ , refl , refl

opaque

  -- Inversion of lambda

  ⇒ₙ-inv-lam : ⟨ H , lam p t , E , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-lam ()

opaque

  -- Inversion of prod

  ⇒ₙ-inv-prod : ⟨ H , prod s′ p t u , E , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-prod ()

opaque

  -- Inversion of zero

  ⇒ₙ-inv-zero : ⟨ H , zero , E , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-zero ()

opaque

  -- Inversion of suc

  ⇒ₙ-inv-suc : ⟨ H , suc t , E , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-suc ()

opaque

  -- Inversion of star

  ⇒ₙ-inv-star : ⟨ H , star s′ , E , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-star ()

opaque

  -- Inversion of unitrec with η-equality

  ⇒ₙ-inv-unitrec-η : Unitʷ-η
                   → ⟨ H , unitrec p q A t u , E , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-unitrec-η η (unitrecₕ no-η) = no-η η

opaque

  -- Inversion of rfl

  ⇒ₙ-inv-rfl : ⟨ H , rfl , E , S ⟩ ⇒ₙ s → ⊥
  ⇒ₙ-inv-rfl ()
