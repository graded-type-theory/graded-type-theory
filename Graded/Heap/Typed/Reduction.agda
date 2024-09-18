------------------------------------------------------------------------
-- Properties of heap typing related to the reduction relation.
-- In particular type preservation/subject reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Heap.Options

module Graded.Heap.Typed.Reduction
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (opts : Options)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open Type-restrictions TR
open Options opts

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed TR as T
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Weakening TR using (id; step; _∷_⊇_)
import Definition.Typed.Weakening TR as W
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inequality TR
open import Definition.Typed.Consequences.Injectivity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
import Graded.Derived.Erased.Typed TR as ET

open import Graded.Heap.Reduction type-variant UR opts
open import Graded.Heap.Reduction.Properties type-variant UR opts
open import Graded.Heap.Typed UR TR ℕ-fullred
open import Graded.Heap.Typed.Inversion UR TR ℕ-fullred
open import Graded.Heap.Typed.Properties UR TR ℕ-fullred
open import Graded.Heap.Typed.Weakening UR TR ℕ-fullred
open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum hiding (id; sym)

private variable
  n : Nat
  Γ Δ : Con Term _
  H H′ : Heap _ _
  e : Elim _
  t t′ u A B C : Term _
  y : Ptr _
  c : Entry _ _
  S S′ : Stack _
  s s′ : State _ _ _
  ρ ρ′ : Wk _ _
  p q q′ r : M

------------------------------------------------------------------------
-- Typing is preserved by heap lookups

opaque

  -- Eliminator typing is preserved by heap lookups/updates

  heapUpdate-⊢ᵉ : Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ B → H ⊢ y ↦[ q ] c ⨾ H′ → Δ ⨾ H′ ⊢ᵉ e ⟨ t ⟩∷ A ↝ B
  heapUpdate-⊢ᵉ {H} {H′} (∘ₑ {ρ} {u} {A} {B} {p} {q} ⊢u ⊢B) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk ρ u [ x ] ∷ _) H≡H′ ⊢u of λ
      ⊢u′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ ∘ₑ p u ρ ⟨ _ ⟩∷ _ ↝ B [ wk ρ u [ x ] ]₀)
      (PE.sym H≡H′) (∘ₑ {A = A} {B = B} ⊢u′ ⊢B)
  heapUpdate-⊢ᵉ (fstₑ ⊢A ⊢B) d =
    fstₑ ⊢A ⊢B
  heapUpdate-⊢ᵉ {t} {H′} (sndₑ {B} ⊢A ⊢B) d =
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ t ⟩∷ _ ↝ B [ fst _ t [ x ] ]₀)
      (PE.sym (heapUpdateSubst d))
      (sndₑ ⊢A ⊢B)
  heapUpdate-⊢ᵉ {Δ} {H} {t} {H′} (prodrecₑ {ρ} {u} {A} ⊢u ⊢A) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → Δ ∙ _ ∙ _ ⊢
                          wk (liftn ρ 2) u [ liftSubstn x 2 ] ∷
                          wk (lift ρ) A [ liftSubst x ] [ _ ]↑²)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst (λ x → Δ ∙ _ ⊢ wk (lift ρ) A [ liftSubst x ]) H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → Δ ⨾ H′ ⊢ᵉ _ ⟨ _ ⟩∷ _ ↝ wk (lift ρ) A [ liftSubst x ] [ t [ x ] ]₀)
      (PE.sym H≡H′) (prodrecₑ ⊢u′ ⊢A′)
  heapUpdate-⊢ᵉ {H} {t} {H′} (natrecₑ {ρ} {z} {A} {s} ⊢z ⊢s ⊢A) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk ρ z [ x ] ∷ wk (lift ρ) A [ liftSubst x ] [ zero ]₀)
           H≡H′ ⊢z of λ
      ⊢z′ →
    case PE.subst (λ x → _ ∙ ℕ ∙ wk (lift ρ) A [ liftSubst x ] ⊢
                         wk (liftn ρ 2) s [ liftSubstn x 2 ] ∷
                         wk (lift ρ) A [ liftSubst x ] [ suc (var x1) ]↑²)
           H≡H′ ⊢s of λ
      ⊢s′ →
    case PE.subst (λ x → _ ∙ ℕ ⊢ wk (lift ρ) A [ liftSubst x ]) H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ _ ⟩∷ ℕ ↝ wk (lift ρ) A [ liftSubst x ] [ t [ x ] ]₀)
      (PE.sym H≡H′) (natrecₑ ⊢z′ ⊢s′ ⊢A′)
  heapUpdate-⊢ᵉ (unitrecₑ ⊢u ⊢A no-η) d
    rewrite heapUpdateSubst d =
    unitrecₑ ⊢u ⊢A no-η
  heapUpdate-⊢ᵉ {H} {t} {H′} (emptyrecₑ {ρ} {A} ⊢A) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk ρ A [ x ]) H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ t ⟩∷ Empty ↝ (wk ρ A [ x ]))
      (PE.sym H≡H′) (emptyrecₑ ⊢A′)
  heapUpdate-⊢ᵉ {t = w} {H′} (Jₑ {ρ} {A} {B} {t} {u} {v} {p} {q} ⊢u ⊢B) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst
           (λ x → _ ⊢ wk ρ u [ x ] ∷ wk (liftn ρ 2) B [ liftSubstn x 2 ] [ wk ρ t [ x ] , rfl ]₁₀)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst
           (λ x → _ ∙ wk ρ A [ x ] ∙ Id (wk1 (wk ρ A [ x ])) (wk1 (wk ρ t [ x ])) (var x0) ⊢ wk (liftn ρ 2) B [ liftSubstn x 2 ])
           H≡H′ ⊢B  of λ
      ⊢B′ →
    PE.subst
      (λ x → _ ⨾ H′ ⊢ᵉ _ ⟨ w ⟩∷ wk ρ (Id A t v) [ x ] ↝ ((wk (liftn ρ 2) B [ liftSubstn x 2 ]) [ wk ρ v [ x ] , w [ x ] ]₁₀))
      (PE.sym H≡H′) (Jₑ ⊢u′ ⊢B′)
  heapUpdate-⊢ᵉ {t = v} {H′} (Kₑ {ρ} {u} {B} {A} {t} {p} ⊢u ⊢B ok) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst
           (λ x → _ ⊢ wk ρ u [ x ] ∷ wk (lift ρ) B [ liftSubst x ] [ rfl ]₀)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst
           (λ x → _ ∙ wk ρ (Id A t t) [ x ] ⊢ wk (lift ρ) B [ liftSubst x ])
           H≡H′ ⊢B of λ
      ⊢B′ →
    PE.subst
      (λ x → _ ⨾ H′ ⊢ᵉ Kₑ p A t B u ρ ⟨ v ⟩∷ wk ρ (Id A t t) [ x ] ↝ wk (lift ρ) B [ liftSubst x ] [ v [ x ] ]₀)
      (PE.sym H≡H′) (Kₑ ⊢u′ ⊢B′ ok)
  heapUpdate-⊢ᵉ {t = v} {H′} ([]-congₑ {s′ = s} {A} {t} {u} {ρ} ok) d =
    PE.subst (λ x → _ ⨾ H′ ⊢ᵉ []-congₑ s A t u ρ ⟨ v ⟩∷ wk ρ (Id A t u) [ x ] ↝ wk ρ (Id (E.Erased A) E.[ t ] E.[ u ]) [ x ])
      (PE.sym (heapUpdateSubst d)) ([]-congₑ ok)
    where
    import Graded.Derived.Erased.Untyped 𝕄 s as E
  heapUpdate-⊢ᵉ sucₑ d = sucₑ
  heapUpdate-⊢ᵉ (conv ⊢e x) d =
    conv (heapUpdate-⊢ᵉ ⊢e d) x

opaque

  -- Stack typing is preserved by heap lookups/updates

  heapUpdate-⊢ˢ : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B → H ⊢ y ↦[ q ] c ⨾ H′ → Δ ⨾ H′ ⊢ S ⟨ t ⟩∷ A ↝ B
  heapUpdate-⊢ˢ ε d = ε
  heapUpdate-⊢ˢ {H} {S = e ∙ S} {t} (⊢e ∙ ⊢S) d =
      heapUpdate-⊢ᵉ ⊢e d ∙ heapUpdate-⊢ˢ ⊢S d

opaque

  -- Heap typing is preserved by heap lookups/updates

  heapUpdate-⊢ʰ : Δ ⊢ʰ H ∷ Γ → H ⊢ y ↦[ q ] c ⨾ H′ → Δ ⊢ʰ H′ ∷ Γ
  heapUpdate-⊢ʰ (⊢H ∙ ⊢t) (here _) = ⊢H ∙ ⊢t
  heapUpdate-⊢ʰ {c = u , _} (_∙_ {ρ} {t} {A = A} ⊢H ⊢t) (there d) =
    case heapUpdate-⊢ʰ ⊢H d of λ
      ⊢H′ →
    case heapUpdateSubst d of λ
      H≡H′ →
    ⊢H′ ∙ PE.subst₂ (_ ⊢_∷_) (PE.cong (wk ρ t [_]) H≡H′)
            (PE.cong (A [_]) H≡H′) ⊢t
  heapUpdate-⊢ʰ (_∙●_ {Δ} {A} ⊢H ⊢A) (there● d) =
    case heapUpdate-⊢ʰ ⊢H d of λ
      ⊢H′ →
    case heapUpdateSubst d of λ
      H≡H′ →
    PE.subst (λ x → Δ ∙ A [ x ] ⊢ʰ _ ∷ _) (PE.sym H≡H′) (⊢H′ ∙● ⊢A)

------------------------------------------------------------------------
-- State typing is preserved by reduction


opaque

  -- Type preservation for _⇒ᵥ_

  ⊢ₛ-⇒ᵥ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ᵥ s′
        → ∃₂ λ ρ Γ′ → (ρ ∷ Γ′ ⊇ Γ) × Δ ⨾ Γ′ ⊢ s′ ∷ A
  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢λt , ⊢e ∙ ⊢S) (lamₕ {H} {p} {t} {ρ} {u} {ρ′}) =
    case inversion-∘ₑ ⊢e of λ {
      (F , G , q , ⊢u , PE.refl , B≡Gu) →
    case inversion-lam-Π ⊢λt of λ
      (⊢t , _ , ok) →
    case substTerm ⊢t ⊢u of λ
      ⊢t′ →
    case singleSubstComp (wk ρ′ u [ H ]ₕ)
         (toSubstₕ H) (wk (lift ρ) t) of λ
      t≡t′ →
    _ , _ , step {A = wk (toWkₕ H) F} id , _
      , ⊢H ∙ PE.subst (_ ⊢ _ ∷_) (PE.sym (toWkₕ-toSubstₕ H F)) ⊢u
      , conv (PE.subst (_ ⊢_∷ _) t≡t′ ⊢t′) (sym B≡Gu)
      , ⊢ˢ-convₜ (wk-⊢ˢ (step id) ⊢S)
          (conv
            (wk1 (lam p (wk (lift ρ) t) ∘ wk ρ′ u) [ H ∙ (p , u , ρ′) ]ₕ ≡⟨ wk1-tail (lam p (wk (lift ρ) t) ∘ wk ρ′ u) ⟩⊢≡
            (lam p (wk (lift ρ) t) ∘⟨ p ⟩ wk ρ′ u) [ H ]ₕ                 ≡⟨⟩⊢
            (wk ρ (lam p t) [ H ]ₕ) ∘⟨ p ⟩ (wk ρ′ u [ H ]ₕ)               ≡⟨ β-red-≡ ⊢t ⊢u ok ⟩⊢∎≡
            (wk (lift ρ) t [ H ]⇑ₕ) [ wk ρ′ u [ H ]ₕ ]₀                  ≡⟨ singleSubstComp (wk ρ′ u [ H ]ₕ) (toSubstₕ H) (wk (lift ρ) t) ⟩
            wk (lift ρ) t [ H ∙ (p , u , ρ′) ]ₕ                          ∎)
            (sym B≡Gu) )}

  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) prodˢₕ₁ =
    case inversion-fstₑ ⊢e of λ {
      (F , G , q , ⊢F , ⊢G , PE.refl , B≡F) →
    case inversion-prod-Σ ⊢t of λ
      (⊢t₁ , ⊢t₂ , _ , _ , ok) →
    _ , _ , id , _ , ⊢H , conv ⊢t₁ (sym B≡F)
      , ⊢ˢ-convₜ ⊢S (conv (Σ-β₁-≡ ⊢G ⊢t₁ ⊢t₂ ok) (sym B≡F))}

  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) prodˢₕ₂ =
    case inversion-sndₑ ⊢e of λ {
      (F , G , q , ⊢F , ⊢G , PE.refl , B≡G₊) →
    case inversion-prod-Σ ⊢t of λ
      (⊢t₁ , ⊢t₂ , _ , _ , ok) →
    case Σ-β₁-≡ ⊢G ⊢t₁ ⊢t₂ ok of λ
      fstt≡t₁ →
    _ , _ , id , _ , ⊢H
      , conv ⊢t₂ (sym (trans (B≡G₊ ⊢t) (substTypeEq (refl ⊢G) fstt≡t₁)))
      , ⊢ˢ-convₜ ⊢S
         (conv (Σ-β₂-≡ ⊢G ⊢t₁ ⊢t₂ ok) (sym (B≡G₊ ⊢t))) }

  ⊢ₛ-⇒ᵥ {(k)} {(_)} {(m)} (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) (prodʷₕ {H} {p} {t₁} {t₂} {ρ} {r} {q} {A} {u} {ρ′} {S}) =
    case inversion-prodrecₑ ⊢e of λ {
      (F , G , _ , ⊢u , ⊢A , PE.refl , B≡A₊) →
    case inversion-prod-Σ ⊢t of λ
      (⊢t₁ , ⊢t₂ , _ , _ , ok) →
    case begin
          (wk (liftn ρ′ 2) u) [ liftSubstn (toSubstₕ H) 2 ] [ wk ρ t₁ [ H ]ₕ , wk ρ t₂ [ H ]ₕ ]₁₀
            ≡⟨ doubleSubstComp (wk (liftn ρ′ 2) u) _ _ _ ⟩
          wk (liftn ρ′ 2) u [ consSubst (consSubst (toSubstₕ H) (wk ρ t₁ [ H ]ₕ)) (wk ρ t₂ [ H ]ₕ) ]
            ≡˘⟨ PE.cong (λ x → wk (liftn ρ′ 2) u [ consSubst (toSubstₕ H₁) x ]) (step-consSubst t₂) ⟩
          wk (liftn ρ′ 2) u [ H₂ ]ₕ ∎ of λ
      u≡u′ →
    case substitutionTerm {σ = consSubst (sgSubst (wk ρ t₁ [ H ]ₕ)) (wk ρ t₂ [ H ]ₕ)}
           ⊢u (singleSubst ⊢t₁ , ⊢t₂) (wfTerm ⊢t₁) of λ
      ⊢u′ →
    case begin
           wk (lift ρ′) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑² [ wk ρ t₁ [ H ]ₕ , wk ρ t₂ [ H ]ₕ ]₁₀
             ≡˘⟨ substCompProdrec (wk (lift ρ′) A [ H ]⇑ₕ) _ _ idSubst ⟩
           wk (lift ρ′) A [ H ]⇑ₕ [ liftSubst idSubst ] [ wk ρ (prodʷ p t₁ t₂) [ H ]ₕ ]₀
             ≡⟨ PE.cong (_[ prodʷ p (wk ρ t₁ [ H ]ₕ) (wk ρ t₂ [ H ]ₕ) ]₀) (substVar-to-subst subst-lift-id (wk (lift ρ′) A [ H ]⇑ₕ)) ⟩
           wk (lift ρ′) A [ H ]⇑ₕ [ idSubst ] [ wk ρ (prodʷ p t₁ t₂) [ H ]ₕ ]₀
             ≡⟨ PE.cong (_[ prodʷ p (wk ρ t₁ [ H ]ₕ) (wk ρ t₂ [ H ]ₕ) ]₀) (subst-id (wk (lift ρ′) A [ H ]⇑ₕ)) ⟩
           wk (lift ρ′) A [ H ]⇑ₕ [ wk ρ (prodʷ p t₁ t₂) [ H ]ₕ ]₀ ∎ of λ
      A₊≡ →
    case PE.subst₂ (_ ⊢_∷_) u≡u′ A₊≡ ⊢u′ of λ
      ⊢u″ →
    case begin
           G [ wk ρ t₁ [ H ]ₕ ]₀               ≡⟨ substVar-to-subst (λ { x0 → PE.refl
                                                                      ; (x +1) → PE.sym (toWkₕ-toSubstₕ-var H x)
                                                                      }) G ⟩
           G [ toSubstₕ H₁ ₛ• lift (toWkₕ H) ] ≡˘⟨ subst-wk G ⟩
           wk (lift (toWkₕ H)) G [ H₁ ]ₕ       ∎ of λ
      Gt₁≡ →
    _ , _ , step {A = wk (lift (toWkₕ H)) G} (step {A = wk (toWkₕ H) F} id) , _
      , ⊢H ∙ PE.subst (_ ⊢ _ ∷_) (PE.sym (toWkₕ-toSubstₕ H F)) ⊢t₁
           ∙ PE.subst₂ (_ ⊢_∷_) (PE.sym (step-consSubst t₂)) Gt₁≡ ⊢t₂
      , conv ⊢u″ (sym (B≡A₊ ⊢t))
      , ⊢ˢ-convₜ (wk-⊢ˢ (step (step id)) ⊢S) (conv
         (wk (step (step id)) (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) [ H₂ ]ₕ
           ≡⟨ step-consSubst (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) ⟩⊢≡
         wk (step id) (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) [ H₁ ]ₕ
           ≡⟨ step-consSubst (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) ⟩⊢≡
         wk id (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) [ H ]ₕ
           ≡⟨ PE.cong (_[ H ]ₕ) (wk-id (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u))) ⟩⊢≡
         prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u) [ H ]ₕ
           ≡⟨ prodrec-β-≡ ⊢A ⊢t₁ ⊢t₂ ⊢u ok ⟩⊢∎≡
         (wk (liftn ρ′ 2) u) [ liftSubstn (toSubstₕ H) 2 ] [ wk ρ t₁ [ H ]ₕ , wk ρ t₂ [ H ]ₕ ]₁₀
           ≡⟨ u≡u′ ⟩
         wk (liftn ρ′ 2) u [ H₂ ]ₕ ∎)
         (sym (B≡A₊ ⊢t)))}
    where
    H₁ : Heap k (1+ m)
    H₁ = H ∙ (∣ S ∣ · r · p , t₁ , ρ)
    H₂ : Heap k (2+ m)
    H₂ = H ∙ (∣ S ∣ · r · p , t₁ , ρ) ∙ (∣ S ∣ · r , t₂ , step ρ)

  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) zeroₕ =
    case inversion-natrecₑ ⊢e of λ {
      (⊢z , ⊢s , ⊢A , PE.refl , B≡) →
    _ , _ , id , _ , ⊢H
      , conv ⊢z (sym (B≡ ⊢t))
      , ⊢ˢ-convₜ ⊢S (conv (natrec-zero ⊢A ⊢z ⊢s) (sym (B≡ ⊢t))) }
  ⊢ₛ-⇒ᵥ {Δ} (_ , ⊢H , ⊢t , ⊢e ∙ ⊢S) (sucₕ {H} {t} {ρ} {p} {q} {r} {(n)} {A} {z} {s} {ρ′}) =
    case inversion-natrecₑ ⊢e of λ {
      (⊢z , ⊢s , ⊢A , PE.refl , B≡) →
    case inversion-suc ⊢t of λ
      (⊢t′ , _) →
    case natrecⱼ ⊢A ⊢z ⊢s ⊢t′ of λ
      ⊢natrec →
    case PE.subst₂ (Δ ⊢_∷_) (lift-step-natrec A z s _)
          (singleSubstComp (wk ρ t [ H ]ₕ) (toSubstₕ H) (wk (lift ρ′) A))
          ⊢natrec of λ
      ⊢natrec′ →
    case PE.subst₂ (Δ ⊢_≡_∷ wk (lift ρ′) A [ H ]⇑ₕ [ suc (wk ρ t [ H ]ₕ) ]₀)
           (lift-step-natrec′ {σ = toSubstₕ H} {ρ = ρ′} A z s (suc (wk ρ t)))
           (PE.trans (substCompEq (wk (liftn ρ′ 2) s))
             (substVar-to-subst (λ { x0 → lift-step-natrec A z s _
                                   ; (x0 +1) → PE.refl
                                   ; (x +2) → PE.trans (wk1-tail (wk1 (toSubstₕ H x))) (wk1-sgSubst (toSubstₕ H x) _)})
               (wk (liftn ρ′ 2) s)))
           (natrec-suc ⊢A ⊢z ⊢s ⊢t′) of λ
      nr-β-≡ →
    case syntacticEqTerm nr-β-≡ of λ
      (_ , _ , ⊢s₊) →
    _ , _ , step {A = wk (lift ρ′) A} (step {A = ℕ} id) , _
      , ⊢H ∙ ⊢t′ ∙ ⊢natrec′
      , conv ⊢s₊ (sym (B≡ ⊢t))
      , ⊢ˢ-convₜ (wk-⊢ˢ (step (step id)) ⊢S)
          (conv nr-β-≡ (sym (B≡ ⊢t)))}
  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) starʷₕ =
    case inversion-unitrecₑ ⊢e of λ {
      (⊢u , ⊢A , no-η , PE.refl , B≡) →
    case ⊢∷Unit→Unit-allowed ⊢t of λ
      ok →
    _ , _ , id , _
      , ⊢H , conv ⊢u (sym (B≡ ⊢t))
      , ⊢ˢ-convₜ ⊢S (conv (unitrec-β-≡ ⊢A ⊢u) (sym (B≡ ⊢t))) }
  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢t , ⊢S) (unitrec-ηₕ η) =
    case inversion-unitrec ⊢t of λ
      (⊢A , ⊢t , ⊢u , A≡) →
    _ , _ , id , _ , ⊢H
      , conv ⊢u (trans (substTypeEq (refl ⊢A) (Unit-η-≡ (inj₂ η) ⊢t)) (sym A≡))
      , ⊢ˢ-convₜ ⊢S (conv (unitrec-β-η-≡ ⊢A ⊢t ⊢u η) (sym A≡))
  ⊢ₛ-⇒ᵥ (_ , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) (rflₕⱼ {H} {p} {q} {A} {t} {B} {u} {v} {ρ′}) =
    case inversion-Jₑ ⊢e of λ {
      (⊢u , ⊢B , PE.refl , B′≡) →
    case inversion-rfl-Id ⊢rfl of λ
      t≡v →
    case syntacticEqTerm t≡v of λ
      (⊢A , ⊢t , ⊢v) →
    case J-motive-rfl-cong (refl ⊢B) t≡v of λ
      Bt≡Bv →
    _ , _ , id , _ , ⊢H
      , conv ⊢u (trans Bt≡Bv (sym (B′≡ ⊢rfl)))
      , ⊢ˢ-convₜ ⊢S (conv
        (⦅ Jₑ p q A t B u v ρ′ ⦆ᵉ rfl [ H ]ₕ
          ≡⟨ J-cong′ (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (sym t≡v) (refl (rflⱼ′ t≡v)) ⟩⊢
        ⦅ Jₑ p q A t B u t ρ′ ⦆ᵉ rfl [ H ]ₕ
          ≡⟨ conv (J-β-≡ ⊢t ⊢B ⊢u) (J-motive-rfl-cong (refl ⊢B) t≡v) ⟩⊢∎
        wk ρ′ u [ H ]ₕ ∎)
        (sym (B′≡ ⊢rfl))) }
  ⊢ₛ-⇒ᵥ (_ , ⊢H , ⊢rfl , ⊢e ∙ ⊢S)  (rflₕₖ {H} {p} {A} {t} {B} {u} {ρ′}) =
    case inversion-Kₑ ⊢e of λ {
      (⊢u , ⊢B , ok , PE.refl , B′≡) →
    _ , _ , id , _ , ⊢H
      , conv ⊢u (sym (B′≡ ⊢rfl))
      , ⊢ˢ-convₜ ⊢S (conv (K-β-≡ ⊢B ⊢u ok) (sym (B′≡ ⊢rfl))) }
  ⊢ₛ-⇒ᵥ (A , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) rflₕₑ =
    case inversion-[]-congₑ ⊢e of λ {
      (ok , PE.refl , B≡) →
    case inversion-rfl-Id ⊢rfl of λ
      t≡u →
    case syntacticEqTerm t≡u of λ
      (⊢A , ⊢t , ⊢u) →
    _ , _ , id , _ , ⊢H
      , conv (rflⱼ′ (ET.[]-cong′ ([]-cong→Erased ok) t≡u)) (sym (B≡ ⊢t ⊢u))
      , ⊢ˢ-convₜ ⊢S (conv ([]-cong-β-≡ t≡u ok) (sym (B≡ ⊢t ⊢u))) }

opaque

  -- Type preservation for _⇒ₙ_

  ⊢ₛ-⇒ₙ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ₙ s′
        → Δ ⨾ Γ ⊢ s′ ∷ A
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) (varₕ {t} d) =
    case heapUpdate-⊢ʰ ⊢H d of λ
      ⊢H′ →
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (_ ⊢ _ ≡_∷ A)
           (heapSubstVar d) (refl ⊢t) of λ
      x[H]≡t[H] →
    _ , ⊢H′
      , PE.subst (_ ⊢_∷ A)
          (PE.trans (heapSubstVar d)
            (PE.cong (wk _ t [_]) H≡H′)) ⊢t
      , heapUpdate-⊢ˢ (⊢ˢ-convₜ ⊢S x[H]≡t[H]) d
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) (varₕ′ d) =
    case PE.subst (_ ⊢ _ ≡_∷ A)
           (heapSubstVar′ d) (refl ⊢t) of λ
      x[H]≡t[H] →
    _ , ⊢H , PE.subst (_ ⊢_∷ A) (heapSubstVar′ d) ⊢t
      , ⊢ˢ-convₜ ⊢S x[H]≡t[H]
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) appₕ =
    case inversion-app ⊢t of λ
      (F , G , q , ⊢t , ⊢u , A≡Gu) →
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ
      (⊢F , ⊢G , ok) →
     _ , ⊢H , ⊢t
       , conv (∘ₑ ⊢u ⊢G) (sym A≡Gu) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) fstₕ =
    case inversion-fst ⊢t of λ
      (F , G , q , ⊢F , ⊢G , ⊢t , A≡F) →
    _ , ⊢H , ⊢t
      , conv (fstₑ ⊢F ⊢G) (sym A≡F) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) sndₕ =
    case inversion-snd ⊢t of λ
      (F , G , q , ⊢F , ⊢G , ⊢t , A≡Gt) →
    _ , ⊢H , ⊢t
      , conv (sndₑ ⊢F ⊢G) (sym A≡Gt) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) prodrecₕ =
    case inversion-prodrec ⊢t of λ
      (F , G , q , ⊢F , ⊢G , ⊢B , ⊢t , ⊢u , A≡Bt) →
    _ , ⊢H , ⊢t , conv (prodrecₑ ⊢u ⊢B) (sym A≡Bt) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) natrecₕ =
    case inversion-natrec ⊢t of λ
      (⊢A , ⊢z , ⊢s , ⊢n , C≡) →
    _ , ⊢H , ⊢n
      , conv (natrecₑ ⊢z ⊢s ⊢A) (sym C≡) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) (unitrecₕ no-η) =
    case inversion-unitrec ⊢t of λ
      (⊢A , ⊢t , ⊢u , B≡At) →
    _ , ⊢H , ⊢t
      , conv (unitrecₑ ⊢u ⊢A no-η) (sym B≡At) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) emptyrecₕ =
    case inversion-emptyrec ⊢t of λ
      (⊢A , ⊢t , A≡) →
    _ , ⊢H , ⊢t , conv (emptyrecₑ ⊢A) (sym A≡) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) Jₕ =
    case inversion-J ⊢t of λ
      (_ , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , A≡B₊) →
     _ , ⊢H , ⊢w , conv (Jₑ ⊢u ⊢B) (sym A≡B₊) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) Kₕ =
    case inversion-K ⊢t of λ
      (_ , ⊢t , ⊢B , ⊢u , ⊢v , ok , A≡B₊) →
    _ , ⊢H , ⊢v , conv (Kₑ ⊢u ⊢B ok) (sym A≡B₊) ∙ ⊢S
  ⊢ₛ-⇒ₙ (A , ⊢H , ⊢t , ⊢S) []-congₕ =
    case inversion-[]-cong ⊢t of λ
      (_ , ⊢t , ⊢u , ⊢v , ok , A≡Id) →
    _ , ⊢H , ⊢v , conv ([]-congₑ ok) (sym A≡Id) ∙ ⊢S

opaque

  -- Type preservation for _⇒ₙ*_

  ⊢ₛ-⇒ₙ* : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ₙ* s′
         → Δ ⨾ Γ ⊢ s′ ∷ A
  ⊢ₛ-⇒ₙ* ⊢s id = ⊢s
  ⊢ₛ-⇒ₙ* ⊢s (d ⇨ d′) = ⊢ₛ-⇒ₙ* (⊢ₛ-⇒ₙ ⊢s d) d′

opaque

  -- Type preservation for _⇒ₛ_

  ⊢ₛ-⇒ₛ : ⦃ ℕ-Fullred ⦄
        → Δ ⨾ Γ ⊢ s ∷ A → s ⇒ₛ s′
        → Δ ⨾ Γ ⊢ s′ ∷ A
  ⊢ₛ-⇒ₛ (A , ⊢H , ⊢t , ⊢S) (sucₕ x) =
    case inversion-suc ⊢t of λ
      (⊢t , A≡ℕ) →
    _ , ⊢H , ⊢t , conv sucₑ (sym A≡ℕ) ∙ ⊢S
  ⊢ₛ-⇒ₛ (A , ⊢H , ⊢t , ⊢e ∙ ⊢S) (numₕ x) =
    case inversion-sucₑ ⊢e of λ {
      (ok , PE.refl , B≡ℕ) →
    _ , ⊢H , conv (sucⱼ ⊢t) (sym (B≡ℕ (wfTerm ⊢t))) , ⊢S}

opaque

  -- Type preservation for _⇒_

  ⊢ₛ-⇒ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ s′
       → ∃₂ λ ρ Γ′ → (ρ ∷ Γ′ ⊇ Γ) × Δ ⨾ Γ′ ⊢ s′ ∷ A
  ⊢ₛ-⇒ ⊢s (⇒ₙ d) = _ , _ , id , ⊢ₛ-⇒ₙ ⊢s d
  ⊢ₛ-⇒ ⊢s (⇒ᵥ d) = ⊢ₛ-⇒ᵥ ⊢s d
  ⊢ₛ-⇒ ⊢s (⇒ₛ d) = _ , _ , id , ⊢ₛ-⇒ₛ ⊢s d


opaque

  -- Type preservation for _⇒*_

  ⊢ₛ-⇒* : Δ ⨾ Γ ⊢ s ∷ A → s ⇒* s′
        → ∃₂ λ ρ Γ′ → (ρ ∷ Γ′ ⊇ Γ) × Δ ⨾ Γ′ ⊢ s′ ∷ A
  ⊢ₛ-⇒* ⊢s id = _ , _ , id , ⊢s
  ⊢ₛ-⇒* ⊢s (d ⇨ d′) =
    case ⊢ₛ-⇒ ⊢s d of λ
      (_ , _ , ρ , ⊢s′) →
    case ⊢ₛ-⇒* ⊢s′ d′ of λ
      (_ , _ , ρ′ , ⊢s″) →
    _ , _ , (ρ′ W.•ₜ ρ) , ⊢s″

private

  opaque

    -- A relation which is either definitional equality or reduction
    -- depending on a boolean.
    -- Used to reduce code duplication between ⇒ᵥ→⇒ and ⇒ᵥ→≡ below.

    _⊢⟨_⟩_⇒/≡_∷_ : (Γ : Con Term n) (b : Bool) (t u A : Term n) → Set a
    Γ ⊢⟨ true ⟩ t ⇒/≡ u ∷ A = _⊢_⇒_∷_ Γ t u A
    Γ ⊢⟨ false ⟩ t ⇒/≡ u ∷ A = Γ ⊢ t ≡ u ∷ A

  opaque
    unfolding _⊢⟨_⟩_⇒/≡_∷_

    -- The relation respects reduction

    ⊢⦅⦆ˢ-subst/cong : (b : Bool) → (T b → ¬ℕ-Fullred)
                   → Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B
                   → Δ ⊢ t [ H ]ₕ ⇒ u [ H ]ₕ ∷ A
                   → Δ ⊢⟨ b ⟩ ⦅ S ⦆ˢ t [ H ]ₕ ⇒/≡ ⦅ S ⦆ˢ u [ H ]ₕ ∷ B
    ⊢⦅⦆ˢ-subst/cong true prop ⊢S t⇒u = ⊢⦅⦆ˢ-subst ⦃ prop _ ⦄ ⊢S t⇒u
    ⊢⦅⦆ˢ-subst/cong false _ ⊢S t≡u = ⊢⦅⦆ˢ-cong ⊢S (subsetTerm t≡u)

  opaque

    -- The relation respects _⇒ᵥ_

    ⇒ᵥ→⇒/≡ : (b : Bool) → (T b → ¬ℕ-Fullred)
           → Δ ⨾ Γ ⊢ s ∷ A → s ⇒ᵥ s′
           → Δ ⊢⟨ b ⟩ ⦅ s ⦆ ⇒/≡ ⦅ s′ ⦆ ∷ A
    ⇒ᵥ→⇒/≡ {A} b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S)
           (lamₕ {H} {p} {t} {ρ} {u} {ρ′} {S}) =
      case inversion-∘ₑ ⊢e of λ {
        (F , G , q , ⊢u , PE.refl , C≡Gu) →
      case PE.subst (_ ⊢ (wk ρ (lam p t) ∘⟨ p ⟩ wk ρ′ u) [ H ]ₕ ⇒_∷ _)
             (PE.trans (singleSubstComp (wk ρ′ u [ H ]ₕ) (toSubstₕ H) (wk (lift ρ) t))
               (substConsId {t = wk ρ′ u} (wk (lift ρ) t)))
             (β-red-⇒₁ ⊢t ⊢u) of λ
        β-⇒ →
      PE.subst (_ ⊢⟨ b ⟩ ⦅ S ⦆ˢ (wk ρ (lam p t) ∘ wk ρ′ u) [ H ]ₕ ⇒/≡_∷ A) lemma
        (⊢⦅⦆ˢ-subst/cong {u = wk (lift ρ) t [ wk ρ′ u ]₀} b prop ⊢S (conv β-⇒ (sym C≡Gu)))}
      where
      lemma : ⦅ S ⦆ˢ (wk (lift ρ) t [ wk ρ′ u ]₀) [ H ]ₕ
            PE.≡ ⦅ wk1ˢ S ⦆ˢ (wk (lift ρ) t) [ H ∙ (p , u , ρ′) ]ₕ
      lemma = begin
        ⦅ S ⦆ˢ (wk (lift ρ) t [ wk ρ′ u ]₀) [ H ]ₕ
          ≡⟨ PE.cong (_[ H ]ₕ) (⦅⦆ˢ-sgSubst S) ⟩
        ⦅ wk1ˢ S ⦆ˢ (wk (lift ρ) t) [ wk ρ′ u ]₀ [ H ]ₕ
          ≡⟨ singleSubstLift (⦅ wk1ˢ S ⦆ˢ (wk (lift ρ) t)) (wk ρ′ u) ⟩
        ⦅ wk1ˢ S ⦆ˢ (wk (lift ρ) t) [ liftSubst (toSubstₕ H) ] [ wk ρ′ u [ H ]ₕ ]₀
          ≡⟨ singleSubstComp _ (toSubstₕ H) (⦅ wk1ˢ S ⦆ˢ (wk (lift ρ) t)) ⟩
        ⦅ wk1ˢ S ⦆ˢ (wk (lift ρ) t) [ H ∙ (p , u , ρ′) ]ₕ ∎

    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S) prodˢₕ₁ =
      case inversion-fstₑ ⊢e of λ {
      (F′ , G′ , q′ , ⊢F′ , ⊢G′ , PE.refl , C≡F′) →
      case inversion-prod ⊢t of λ
        (F , G , q , ⊢F , ⊢G , ⊢t₁ , ⊢t₂ , B≡Σ , ok) →
      case Σ-injectivity (sym B≡Σ) of λ
        (F≡F′ , _) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (Σ-β₁-⇒ ⊢G ⊢t₁ ⊢t₂ ok)
        (trans F≡F′ (sym C≡F′))) }

    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S) prodˢₕ₂ =
      case inversion-sndₑ ⊢e of λ {
        (F′ , G′ , q′ , ⊢F′ , ⊢G′ , PE.refl , C≡G′₊) →
      case inversion-prod ⊢t of λ
        (F , G , q , ⊢F , ⊢G , ⊢t₁ , ⊢t₂ , B≡Σ , ok) →
      case Σ-injectivity (sym B≡Σ) of λ
        (F≡F′ , G≡G′ , _) →
      case substTypeEq G≡G′ (refl (conv (fstⱼ′ ⊢t) (sym F≡F′))) of λ
        G₊≡G′₊ →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (Σ-β₂-⇒ ⊢G ⊢t₁ ⊢t₂ ok)
        (trans G₊≡G′₊ (sym (C≡G′₊ ⊢t)))) }

    ⇒ᵥ→⇒/≡ {(k)} {(_)} {(m)} b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S)
           (prodʷₕ {H} {p} {t₁} {t₂} {ρ} {r} {q} {A} {u} {ρ′} {S}) =
      case inversion-prodrecₑ ⊢e of λ {
        (F , G , q′ , ⊢u , ⊢A , PE.refl , C≡) →
      case PE.subst (_ ⊢ prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u) [ H ]ₕ ⇒_∷ _)
             (PE.sym ([,]-[]-commute {u = wk ρ t₁} {v = wk ρ t₂} (wk (liftn ρ′ 2) u)))
             (prodrec-β-⇒₁ ⊢A ⊢t ⊢u) of λ
        β-⇒ →
      PE.subst (_ ⊢⟨ b ⟩ ⦅ S ⦆ˢ (prodrec r p q _ _ _) [ H ]ₕ ⇒/≡_∷ _) lemma
        (⊢⦅⦆ˢ-subst/cong {u = wk (liftn ρ′ 2) u [ wk ρ t₁ , wk ρ t₂ ]₁₀}
                       b prop ⊢S (conv β-⇒ (sym (C≡ ⊢t))))}
      where
      H₂ : Heap k (2+ m)
      H₂ = H ∙ (∣ S ∣ · r · p , t₁ , ρ) ∙ (∣ S ∣ · r , t₂ , step ρ)
      lemma : ⦅ S ⦆ˢ ((wk (liftn ρ′ 2) u) [ wk ρ t₁ , wk ρ t₂ ]₁₀) [ H ]ₕ
            PE.≡ ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) u) [ H₂ ]ₕ
      lemma = begin
        ⦅ S ⦆ˢ ((wk (liftn ρ′ 2) u) [ wk ρ t₁ , wk ρ t₂ ]₁₀) [ H ]ₕ
          ≡⟨ PE.cong (_[ H ]ₕ) (⦅⦆ˢ-[,] S) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) u) [ wk ρ t₁ , wk ρ t₂ ]₁₀ [ H ]ₕ
          ≡⟨ [,]-[]-fusion (⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) u)) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) u) [ consSubst (consSubst (toSubstₕ H) (wk ρ t₁ [ H ]ₕ)) (wk ρ t₂ [ H ]ₕ) ]
          ≡⟨ PE.cong (λ x → ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) u) [ consSubst _ x ]) (PE.sym (step-consSubst t₂)) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) u) [ H₂ ]ₕ ∎


    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S) zeroₕ =
      case inversion-natrecₑ ⊢e of λ {
        (⊢z , ⊢s , ⊢A , PE.refl , B≡) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (natrec-zero ⊢A ⊢z ⊢s)
        (sym (B≡ ⊢t))) }

    ⇒ᵥ→⇒/≡ {(k)} {(_)} {(m)} b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S)
      (sucₕ {H} {t} {ρ} {p} {q} {r} {(n)} {A} {z} {s} {ρ′} {S}) =
      case inversion-natrecₑ ⊢e of λ {
        (⊢z , ⊢s , ⊢A , PE.refl , B≡) →
      case PE.subst (_ ⊢ nr (wk ρ (suc t)) [ H ]ₕ ⇒_∷ _)
             (PE.sym ([,]-[]-commute (wk (liftn ρ′ 2) s)))
             (natrec-suc ⊢A ⊢z ⊢s (inversion-suc ⊢t .proj₁)) of λ
        β-⇒ →
      case ⊢⦅⦆ˢ-subst/cong {u = wk (liftn ρ′ 2) s [ wk ρ t , nr (wk ρ t) ]₁₀}
             b prop ⊢S (conv β-⇒ (sym (B≡ ⊢t))) of λ
        d →
      PE.subst (_ ⊢⟨ b ⟩ ⦅ S ⦆ˢ (nr (wk ρ (suc t))) [ H ]ₕ ⇒/≡_∷ _)
        lemma d }
      where
      nr : Term m → Term m
      nr = natrec p q r (wk (lift ρ′) A) (wk ρ′ z) (wk (liftn ρ′ 2) s)
      nr′ : Term (1+ n)
      nr′ = natrec p q r (wk (lift (step id)) A) (wk1 z) (wk (liftn (step id) 2) s) (var x0)
      H₂ : Heap k (2+ m)
      H₂ = H ∙ (p + r , t , ρ) ∙ (r , nr′ , lift ρ′)
      lemma′ : nr (wk ρ t) [ H ]ₕ PE.≡ wk (lift ρ′) nr′ [ H ∙ (p + r , t , ρ) ]ₕ
      lemma′ = begin
        nr (wk ρ t) [ H ]ₕ ≡⟨ lift-step-natrec A z s _ ⟩
        wk (lift ρ′) nr′ [ H ∙ (p + r , t , ρ) ]ₕ ∎
      lemma : ⦅ S ⦆ˢ ((wk (liftn ρ′ 2) s) [ wk ρ t , nr (wk ρ t) ]₁₀) [ H ]ₕ
            PE.≡ ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ H₂ ]ₕ
      lemma = begin
        ⦅ S ⦆ˢ ((wk (liftn ρ′ 2) s) [ wk ρ t , nr (wk ρ t) ]₁₀) [ H ]ₕ
          ≡⟨ PE.cong (_[ H ]ₕ) (⦅⦆ˢ-[,] S) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ wk ρ t , nr (wk ρ t) ]₁₀ [ H ]ₕ
              ≡⟨ [,]-[]-fusion (⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s)) ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ consSubst (consSubst (toSubstₕ H) (wk ρ t [ H ]ₕ)) (nr (wk ρ t) [ H ]ₕ) ]
          ≡⟨ PE.cong (λ x → ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ consSubst (consSubst (toSubstₕ H) (wk ρ t [ H ]ₕ)) x ]) lemma′ ⟩
        ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ H₂ ]ₕ ∎

    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢e ∙ ⊢S) starʷₕ =
      case inversion-unitrecₑ ⊢e of λ {
        (⊢u , ⊢A , no-η , PE.refl , C≡A₊) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (unitrec-β-⇒ ⊢A ⊢u) (sym (C≡A₊ ⊢t)))}
    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢t , ⊢S) (unitrec-ηₕ η) =
      case inversion-unitrec ⊢t of λ
        (⊢A , ⊢t , ⊢u , A≡) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S
        (conv (unitrec-β-η-⇒ ⊢A ⊢t ⊢u η) (sym A≡))

    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) rflₕⱼ =
      case inversion-Jₑ ⊢e of λ {
        (⊢w , ⊢B , PE.refl , ≡B) →
      case inversion-rfl-Id ⊢rfl of λ
        t≡v →
      case trans (J-motive-rfl-cong (refl ⊢B) t≡v) (sym (≡B ⊢rfl)) of λ
        ≡B′ →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (J-β-⇒ t≡v ⊢B ⊢w) ≡B′)}
    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) rflₕₖ =
      case inversion-Kₑ ⊢e of λ {
        (⊢v , ⊢B , ok , PE.refl , B′≡)  →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv (K-β-⇒ ⊢B ⊢v ok) (sym (B′≡ ⊢rfl)))}
    ⇒ᵥ→⇒/≡ b prop (B , ⊢H , ⊢rfl , ⊢e ∙ ⊢S) rflₕₑ =
      case inversion-[]-congₑ ⊢e of λ {
        (ok , PE.refl , B′≡) →
      case inversion-rfl-Id ⊢rfl of λ
        t≡u →
      case syntacticEqTerm t≡u of λ
        (_ , ⊢t , ⊢u) →
      ⊢⦅⦆ˢ-subst/cong b prop ⊢S (conv ([]-cong-β-⇒ t≡u ok) (sym (B′≡ ⊢t ⊢u))) }

opaque
  unfolding _⊢⟨_⟩_⇒/≡_∷_

  -- Reduction of values correspond to one step in the wh cbn reduction

  ⇒ᵥ→⇒ : ⦃ ¬fr : ¬ℕ-Fullred ⦄
       → Δ ⨾ Γ ⊢ s ∷ A → s ⇒ᵥ s′ → _⊢_⇒_∷_ Δ ⦅ s ⦆ ⦅ s′ ⦆ A
  ⇒ᵥ→⇒ ⦃ ¬fr ⦄ = ⇒ᵥ→⇒/≡ true (λ _ → ¬fr)

opaque
  unfolding _⊢⟨_⟩_⇒/≡_∷_

  -- Reduction of values preserves definitional equality

  ⇒ᵥ→≡ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ᵥ s′ → Δ ⊢ ⦅ s ⦆ ≡ ⦅ s′ ⦆ ∷ A
  ⇒ᵥ→≡ = ⇒ᵥ→⇒/≡ false (λ ())

opaque

  -- Reduction preserves definitional equality

  ⇒→≡ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒ s′ → Δ ⊢ ⦅ s ⦆ ≡ ⦅ s′ ⦆ ∷ A
  ⇒→≡ (_ , _ , ⊢t , ⊢S) (⇒ₙ d) =
    PE.subst (_ ⊢ _ ≡_∷ _) (⇒ₙ-⦅⦆-≡ d) (refl (⊢⦅⦆ˢ ⊢S ⊢t))
  ⇒→≡ ⊢s (⇒ᵥ d) =
    ⇒ᵥ→≡ ⊢s d
  ⇒→≡ (_ , _ , ⊢t , ⊢S) (⇒ₛ d) =
    PE.subst (_ ⊢ _ ≡_∷ _) (⇒ₛ-⦅⦆-≡ d) (refl (⊢⦅⦆ˢ ⊢S ⊢t))

opaque

  -- Reduction preserves definitional equality

  ⇒*→≡ : Δ ⨾ Γ ⊢ s ∷ A → s ⇒* s′ → Δ ⊢ ⦅ s ⦆ ≡ ⦅ s′ ⦆ ∷ A
  ⇒*→≡ (_ , _ , ⊢t , ⊢S) id = refl (⊢⦅⦆ˢ ⊢S ⊢t)
  ⇒*→≡ ⊢s (x ⇨ d) =
    trans (⇒→≡ ⊢s x) (⇒*→≡ (⊢ₛ-⇒ ⊢s x .proj₂ .proj₂ .proj₂) d)

opaque

  -- Values in non-empty stacks always reduce

  ⊢ˢValue-⇒ᵥ : ⦃ ¬fr : ¬ℕ-Fullred ⦄
              → Δ ⨾ H ⊢ᵉ e ⟨ wk ρ t ⟩∷ A ↝ B → Δ ⊢ wk ρ t [ H ]ₕ ∷ A → Value t
              → ∃₃ λ m n (s : State _ m n) → ⟨ H , t , ρ , e ∙ S ⟩ ⇒ᵥ s
  -- Ok cases:
  ⊢ˢValue-⇒ᵥ (conv ⊢e x) ⊢t v =
    ⊢ˢValue-⇒ᵥ ⊢e ⊢t v
  ⊢ˢValue-⇒ᵥ ⊢e ⊢t (unitrec-ηᵥ η) =
    _ , _ , _ , unitrec-ηₕ η
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t lamᵥ =
    case inversion-lam-Π ⊢t of λ {
      (_ , PE.refl , _) →
    _ , _ , _ , lamₕ}
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t prodᵥ =
    case inversion-prod-Σ ⊢t of λ {
      (_ , _ , PE.refl , PE.refl , _) →
    _ , _ , _ , prodˢₕ₁}
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t prodᵥ =
    case inversion-prod-Σ ⊢t of λ {
      (_ , _ , PE.refl , PE.refl , _) →
    _ , _ , _ , prodˢₕ₂}
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t prodᵥ =
    case inversion-prod-Σ ⊢t of λ {
      (_ , _ , PE.refl , PE.refl , _) →
    _ , _ , _ , prodʷₕ}
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t zeroᵥ =
    _ , _ , _ , zeroₕ
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t sucᵥ =
        _ , _ , _ , sucₕ
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t starᵥ =
    case inversion-star-Unit ⊢t of λ {
      (PE.refl , PE.refl , _) →
    _ , _ , _ , starʷₕ }
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t rflᵥ =
    _ , _ , _ , rflₕⱼ
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t rflᵥ =
    _ , _ , _ , rflₕₖ
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t rflᵥ =
    _ , _ , _ , rflₕₑ

  -- Impossible cases:
  ⊢ˢValue-⇒ᵥ sucₑ ⊢t v = ⊥-elim not-ℕ-Fullred-and-¬ℕ-Fullred
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Σ≡Π , _) →
    ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Σ≡Π , _) →
    ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Σ≡Π , _) →
    ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , ℕ≡Π , _) →
    ⊥-elim (ℕ≢Π ℕ≡Π)
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Unit≡Π , _) →
    ⊥-elim (Unit≢Πⱼ Unit≡Π)
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Empty≡Π , _) →
    ⊥-elim (Empty≢Πⱼ Empty≡Π)
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Id≡Π , _) →
    ⊥-elim (Id≢Π Id≡Π)
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Id≡Π , _) →
    ⊥-elim (Id≢Π Id≡Π)
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Id≡Π , _) →
    ⊥-elim (Id≢Π Id≡Π)
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t zeroᵥ =
    ⊥-elim (ℕ≢Π (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t zeroᵥ =
    ⊥-elim (ℕ≢Σ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t zeroᵥ =
    ⊥-elim (ℕ≢Σ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t zeroᵥ =
    ⊥-elim (ℕ≢Σ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t zeroᵥ =
    ⊥-elim (ℕ≢Unitⱼ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t zeroᵥ =
    ⊥-elim (ℕ≢Emptyⱼ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t zeroᵥ =
    ⊥-elim (Id≢ℕ (inversion-zero ⊢t))
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t zeroᵥ =
    ⊥-elim (Id≢ℕ (inversion-zero ⊢t))
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t zeroᵥ =
    ⊥-elim (Id≢ℕ (inversion-zero ⊢t))
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t sucᵥ =
    ⊥-elim (ℕ≢Π (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t sucᵥ =
    (⊥-elim (ℕ≢Σ (sym (inversion-suc ⊢t .proj₂))))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t sucᵥ =
    ⊥-elim (ℕ≢Σ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t sucᵥ =
    ⊥-elim (ℕ≢Σ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t sucᵥ =
    ⊥-elim (ℕ≢Unitⱼ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t sucᵥ =
    ⊥-elim (ℕ≢Emptyⱼ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t sucᵥ =
    ⊥-elim (Id≢ℕ (inversion-suc ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t sucᵥ =
    ⊥-elim (Id≢ℕ (inversion-suc ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t sucᵥ =
    ⊥-elim (Id≢ℕ (inversion-suc ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t starᵥ =
    ⊥-elim (Unit≢Πⱼ (sym (inversion-star ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t starᵥ =
    ⊥-elim (Unit≢Σⱼ (sym (inversion-star ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t starᵥ =
    ⊥-elim (Unit≢Σⱼ (sym (inversion-star ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t starᵥ =
    ⊥-elim (Unit≢Σⱼ (sym (inversion-star ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t starᵥ =
    ⊥-elim (ℕ≢Unitⱼ (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t starᵥ =
    ⊥-elim (Empty≢Unitⱼ (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t starᵥ =
    ⊥-elim (Id≢Unit (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t starᵥ =
    ⊥-elim (Id≢Unit (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t starᵥ =
    ⊥-elim (Id≢Unit (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Π≡Σ , _) →
    ⊥-elim (Π≢Σⱼ Π≡Σ)
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , ℕ≡Σ , _) →
    ⊥-elim (ℕ≢Σ ℕ≡Σ)
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Unit≡Σ , _) →
    ⊥-elim (Unit≢Σⱼ Unit≡Σ)
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Empty≡Σ , _) →
    ⊥-elim (Empty≢Σⱼ Empty≡Σ)
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
    ⊥-elim (Id≢Σ Id≡Σ)
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
    ⊥-elim (Id≢Σ Id≡Σ)
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
    ⊥-elim (Id≢Σ Id≡Σ)
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Π≡Id) →
    ⊥-elim (Id≢Π (sym Π≡Id))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Σ≡Id) →
    ⊥-elim (Id≢Σ (sym Σ≡Id))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Σ≡Id) →
    ⊥-elim (Id≢Σ (sym Σ≡Id))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Σ≡Id) →
    ⊥-elim (Id≢Σ (sym Σ≡Id))
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , ℕ≡Id) →
    ⊥-elim (Id≢ℕ (sym ℕ≡Id))
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Unit≡Id) →
    ⊥-elim (Id≢Unit (sym Unit≡Id))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Empty≡Id) →
    ⊥-elim (Id≢Empty (sym Empty≡Id))
  ⊢ˢValue-⇒ᵥ ⊢e ⊢t Uᵥ =
    ⊥-elim (hole-type-not-U ⊢e (inversion-U ⊢t))
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Π≡U , _) →
    ⊥-elim (U≢Π (sym Π≡U))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U , _) →
    ⊥-elim (U≢Σ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U , _) →
    ⊥-elim (U≢Σ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U , _) →
    ⊥-elim (U≢Σ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , ℕ≡U , _) →
    ⊥-elim (U≢ℕ (sym ℕ≡U))
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Unit≡U , _) →
    ⊥-elim (U≢Unitⱼ (sym Unit≡U))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Empty≡U , _) →
    ⊥-elim (U≢Emptyⱼ (sym Empty≡U))
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U , _) →
    ⊥-elim (Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U , _) →
    ⊥-elim (Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U , _) →
    ⊥-elim (Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t ℕᵥ =
    ⊥-elim (U≢Π (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t ℕᵥ =
    ⊥-elim (U≢Σ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t ℕᵥ =
    ⊥-elim (U≢Σ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t ℕᵥ =
    ⊥-elim (U≢Σ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t ℕᵥ =
    ⊥-elim (U≢ℕ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t ℕᵥ =
    ⊥-elim (U≢Unitⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t ℕᵥ =
    ⊥-elim (U≢Emptyⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t ℕᵥ =
    ⊥-elim (Id≢U (inversion-ℕ ⊢t))
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t ℕᵥ =
    ⊥-elim (Id≢U (inversion-ℕ ⊢t))
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t ℕᵥ =
    ⊥-elim (Id≢U (inversion-ℕ ⊢t))
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t Unitᵥ =
    ⊥-elim (U≢Π (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t Unitᵥ =
    ⊥-elim (U≢Σ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t Unitᵥ =
    ⊥-elim (U≢Σ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t Unitᵥ =
    ⊥-elim (U≢Σ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t Unitᵥ =
    ⊥-elim (U≢ℕ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t Unitᵥ =
    ⊥-elim (U≢Unitⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t Unitᵥ =
    ⊥-elim (U≢Emptyⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t Unitᵥ =
    ⊥-elim (Id≢U (inversion-Unit-U ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t Unitᵥ =
    ⊥-elim (Id≢U (inversion-Unit-U ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t Unitᵥ =
    ⊥-elim (Id≢U (inversion-Unit-U ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t Emptyᵥ =
    ⊥-elim (U≢Π (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t Emptyᵥ =
    ⊥-elim (U≢Σ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t Emptyᵥ =
    ⊥-elim (U≢Σ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t Emptyᵥ =
    ⊥-elim (U≢Σ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t Emptyᵥ =
    ⊥-elim (U≢ℕ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t Emptyᵥ =
    ⊥-elim (U≢Unitⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t Emptyᵥ =
    ⊥-elim (U≢Emptyⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t Emptyᵥ =
    ⊥-elim (Id≢U (inversion-Empty ⊢t))
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t Emptyᵥ =
    ⊥-elim (Id≢U (inversion-Empty ⊢t))
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t Emptyᵥ =
    ⊥-elim (Id≢U (inversion-Empty ⊢t))
  ⊢ˢValue-⇒ᵥ (∘ₑ x x₁) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Π≡U) →
    ⊥-elim (U≢Π (sym Π≡U))
  ⊢ˢValue-⇒ᵥ (fstₑ x x₁) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U) →
    ⊥-elim (U≢Σ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ (sndₑ x x₁) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U) →
    ⊥-elim (U≢Σ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ (prodrecₑ x x₁) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U) →
    ⊥-elim (U≢Σ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ (natrecₑ x x₁ x₂) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , ℕ≡U) →
    ⊥-elim (U≢ℕ (sym ℕ≡U))
  ⊢ˢValue-⇒ᵥ (unitrecₑ x x₁ x₂) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Unit≡U) →
    ⊥-elim (U≢Unitⱼ (sym Unit≡U))
  ⊢ˢValue-⇒ᵥ (emptyrecₑ x) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Empty≡U) →
    ⊥-elim (U≢Emptyⱼ (sym Empty≡U))
  ⊢ˢValue-⇒ᵥ (Jₑ x x₁) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U) →
    ⊥-elim (Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ (Kₑ x x₁ x₂) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U) →
    ⊥-elim (Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ ([]-congₑ x) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U) →
    ⊥-elim (Id≢U Id≡U)

opaque

  -- Values in non-empty stacks always reduce

  ⊢Value-⇒ᵥ : ⦃ ¬fr : ¬ℕ-Fullred ⦄
              → Δ ⨾ Γ ⊢ ⟨ H , t , ρ , e ∙ S ⟩ ∷ A → Value t
              → ∃₃ λ m n (s : State _ m n) → ⟨ H , t , ρ , e ∙ S ⟩ ⇒ᵥ s
  ⊢Value-⇒ᵥ (_ , _ , ⊢t , ⊢e ∙ _) v = ⊢ˢValue-⇒ᵥ ⊢e ⊢t v
