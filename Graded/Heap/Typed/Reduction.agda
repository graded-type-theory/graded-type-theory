------------------------------------------------------------------------
-- Properties of heap typing related to the reduction relation.
-- In particular type preservation/subject reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Typed.Reduction
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (UR : Usage-restrictions 𝕄 𝐌)
  (TR : Type-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  (∣ε∣ : M)
  where

open Type-restrictions TR
open Modality 𝕄

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as E
open import Definition.Untyped.Properties M
import Definition.Untyped.Whnf M type-variant as WHNF
open import Definition.Typed TR as T
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
import Definition.Typed.Reasoning.Term TR as TmR
import Definition.Typed.Reasoning.Type TR as TyR
open import Definition.Typed.Substitution TR
open import Definition.Typed.Syntactic TR
open import Definition.Typed.Well-formed TR
open import Definition.Typed.Consequences.Admissible 𝐌 TR
import Definition.Typed.Consequences.Inequality TR as I
open import Definition.Typed.Consequences.Injectivity TR
open import Definition.Typed.Consequences.Inversion TR

open import Graded.Heap.Reduction type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Typed UR TR factoring-nr ∣ε∣
open import Graded.Heap.Typed.Inversion UR TR factoring-nr ∣ε∣
open import Graded.Heap.Typed.Properties UR TR factoring-nr ∣ε∣
open import Graded.Heap.Typed.Weakening UR TR factoring-nr ∣ε∣
open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr ∣ε∣

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat renaming (_+_ to _+ⁿ_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum
open import Tools.Relation

private variable
  n : Nat
  Γ Δ : Con Term _
  H H′ : Heap _ _
  c : Cont _
  t t′ u A B C : Term _
  y : Ptr _
  e : Entry _ _
  S S′ : Stack _
  s s′ : State _ _ _
  ρ ρ′ : Wk _ _
  p q q′ r : M

------------------------------------------------------------------------
-- Typing is preserved by heap lookups

opaque

  -- Continuation typing is preserved by heap lookups/updates

  heapUpdate-⊢ᶜ : Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ B → H ⊢ y ↦[ q ] e ⨾ H′ → Δ ⨾ H′ ⊢ᶜ c ⟨ t ⟩∷ A ↝ B
  heapUpdate-⊢ᶜ (lowerₑ ⊢B) d =
    lowerₑ ⊢B
  heapUpdate-⊢ᶜ {H} {H′} (∘ₑ {ρ} {u} {A} {B} {p} {q} ⊢u ⊢B) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk ρ u [ x ] ∷ _) H≡H′ ⊢u of λ
      ⊢u′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᶜ ∘ₑ p u ρ ⟨ _ ⟩∷ _ ↝ B [ wk ρ u [ x ] ]₀)
      (PE.sym H≡H′) (∘ₑ {A = A} {B = B} ⊢u′ ⊢B)
  heapUpdate-⊢ᶜ (fstₑ ⊢B) d =
    fstₑ ⊢B
  heapUpdate-⊢ᶜ {t} {H′} (sndₑ {B} ⊢B) d =
    PE.subst (λ x → _ ⨾ H′ ⊢ᶜ _ ⟨ t ⟩∷ _ ↝ B [ fst _ t [ x ] ]₀)
      (PE.sym (heapUpdateSubst d))
      (sndₑ ⊢B)
  heapUpdate-⊢ᶜ {Δ} {H} {t} {H′} (prodrecₑ {ρ} {u} {A} ⊢u ⊢A) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢
                          wk (liftn ρ 2) u [ liftSubstn x 2 ] ∷
                          wk (lift ρ) A [ liftSubst x ] [ _ ]↑²)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst (λ x → _ ⊢ wk (lift ρ) A [ liftSubst x ]) H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → Δ ⨾ H′ ⊢ᶜ _ ⟨ _ ⟩∷ _ ↝ wk (lift ρ) A [ liftSubst x ] [ t [ x ] ]₀)
      (PE.sym H≡H′) (prodrecₑ ⊢u′ ⊢A′)
  heapUpdate-⊢ᶜ {H} {t} {H′} (natrecₑ {ρ} {z} {A} {s} ⊢z ⊢s) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk ρ z [ x ] ∷ wk (lift ρ) A [ liftSubst x ] [ zero ]₀)
           H≡H′ ⊢z of λ
      ⊢z′ →
    case PE.subst (λ x → _ » _ ∙ ℕ ∙ wk (lift ρ) A [ liftSubst x ] ⊢
                         wk (liftn ρ 2) s [ liftSubstn x 2 ] ∷
                         wk (lift ρ) A [ liftSubst x ] [ suc (var x1) ]↑²)
           H≡H′ ⊢s of λ
      ⊢s′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᶜ _ ⟨ _ ⟩∷ ℕ ↝ wk (lift ρ) A [ liftSubst x ] [ t [ x ] ]₀)
      (PE.sym H≡H′) (natrecₑ ⊢z′ ⊢s′)
  heapUpdate-⊢ᶜ (unitrecₑ ⊢u ⊢A no-η) d
    rewrite heapUpdateSubst d =
    unitrecₑ ⊢u ⊢A no-η
  heapUpdate-⊢ᶜ {H} {t} {H′} (emptyrecₑ {ρ} {A} ⊢A) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst (λ x → _ ⊢ wk ρ A [ x ]) H≡H′ ⊢A of λ
      ⊢A′ →
    PE.subst (λ x → _ ⨾ H′ ⊢ᶜ _ ⟨ t ⟩∷ Empty ↝ (wk ρ A [ x ]))
      (PE.sym H≡H′) (emptyrecₑ ⊢A′)
  heapUpdate-⊢ᶜ {t = w} {H′} (Jₑ {ρ} {A} {B} {t} {u} {v} {p} {q} ⊢u ⊢B) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst
           (λ x → _ ⊢ wk ρ u [ x ] ∷ wk (liftn ρ 2) B [ liftSubstn x 2 ] [ wk ρ t [ x ] , rfl ]₁₀)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst
           (λ x →
              _ »
              _ ∙ wk ρ A [ x ] ∙
                Id (wk1 (wk ρ A [ x ])) (wk1 (wk ρ t [ x ])) (var x0) ⊢
              wk (liftn ρ 2) B [ liftSubstn x 2 ])
           H≡H′ ⊢B  of λ
      ⊢B′ →
    PE.subst
      (λ x → _ ⨾ H′ ⊢ᶜ _ ⟨ w ⟩∷ wk ρ (Id A t v) [ x ] ↝ ((wk (liftn ρ 2) B [ liftSubstn x 2 ]) [ wk ρ v [ x ] , w [ x ] ]₁₀))
      (PE.sym H≡H′) (Jₑ ⊢u′ ⊢B′)
  heapUpdate-⊢ᶜ {t = v} {H′} (Kₑ {ρ} {u} {B} {A} {t} {p} ⊢u ⊢B ok) d =
    case heapUpdateSubst d of λ
      H≡H′ →
    case PE.subst
           (λ x → _ ⊢ wk ρ u [ x ] ∷ wk (lift ρ) B [ liftSubst x ] [ rfl ]₀)
           H≡H′ ⊢u of λ
      ⊢u′ →
    case PE.subst
           (λ x →
              _ » _ ∙ wk ρ (Id A t t) [ x ] ⊢
              wk (lift ρ) B [ liftSubst x ])
           H≡H′ ⊢B of λ
      ⊢B′ →
    PE.subst
      (λ x → _ ⨾ H′ ⊢ᶜ Kₑ p A t B u ρ ⟨ v ⟩∷ wk ρ (Id A t t) [ x ] ↝ wk (lift ρ) B [ liftSubst x ] [ v [ x ] ]₀)
      (PE.sym H≡H′) (Kₑ ⊢u′ ⊢B′ ok)
  heapUpdate-⊢ᶜ
    {t = v} {H′} ([]-congₑ {s′ = s} {ρ} {l} {A} {t} {u} ok ⊢l) d =
    PE.subst
      (λ x →
         _ ⨾ H′ ⊢ᶜ []-congₑ s l A t u ρ ⟨ v ⟩∷ wk ρ (Id A t u) [ x ] ↝
         wk ρ (Id (E′.Erased l A) E′.[ t ] E′.[ u ]) [ x ])
      (PE.sym (heapUpdateSubst d))
      ([]-congₑ ok $
       PE.subst (λ H → _ ⊢ wk _ l [ H ] ∷Level) (heapUpdateSubst d) ⊢l)
    where
    module E′ = E s
  heapUpdate-⊢ᶜ (conv ⊢c x) d =
    conv (heapUpdate-⊢ᶜ ⊢c d) x

opaque

  -- Stack typing is preserved by heap lookups/updates

  heapUpdate-⊢ˢ : Δ ⨾ H ⊢ S ⟨ t ⟩∷ A ↝ B → H ⊢ y ↦[ q ] e ⨾ H′ → Δ ⨾ H′ ⊢ S ⟨ t ⟩∷ A ↝ B
  heapUpdate-⊢ˢ ε d = ε
  heapUpdate-⊢ˢ {H} {S = c ∙ S} {t} (⊢c ∙ ⊢S) d =
      heapUpdate-⊢ᶜ ⊢c d ∙ heapUpdate-⊢ˢ ⊢S d

opaque

  -- Heap typing is preserved by heap lookups/updates

  heapUpdate-⊢ʰ : Δ ⊢ʰ H ∷ Γ → H ⊢ y ↦[ q ] e ⨾ H′ → Δ ⊢ʰ H′ ∷ Γ
  heapUpdate-⊢ʰ ε         ()
  heapUpdate-⊢ʰ (⊢H ∙ ⊢t) (here _) = ⊢H ∙ ⊢t
  heapUpdate-⊢ʰ {e = u , _} (_∙_ {ρ} {t} {A = A} ⊢H ⊢t) (there d) =
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

-- The properties below are proved under the assumption that equality
-- reflection is not allowed or the context is empty.

opaque

  -- Type preservation for _⇒ᵥ_

  ⊢ₛ-⇒ᵥ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇒ᵥ s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇒ᵥ ⊢s (lamₕ {H} {p} {t} {ρ} {u} {ρ′} _) =
    case ⊢ₛ-inv′ ⊢s of λ
      (Γ , _ , _ , ⊢H , ⊢λt , ⊢c , ⊢S) →
    case inversion-∘ₑ ⊢c of λ {
      (F , G , q , ⊢u , PE.refl , B≡Gu) →
    let _ , ⊢t , ≡G , _ , ok = inversion-lam-Π ⊢λt
        ≡G[u]₀ = ≡G (refl ⊢u)
        ⊢t′ = conv (subst-⊢₀ ⊢t ⊢u) ≡G[u]₀
        t≡t′ = singleSubstComp (wk ρ′ u [ H ]ₕ)
                 (toSubstₕ H) (wk (lift ρ) t)
    in  ⊢ₛ {Γ = Γ ∙ wk (toWkₕ H) F}
           (⊢H ∙ PE.subst (_ ⊢ wk ρ′ u [ H ]ₕ ∷_) (PE.sym (toWkₕ-toSubstₕ H F)) ⊢u)
           (conv (PE.subst (_ ⊢_∷ _) t≡t′ ⊢t′) (sym B≡Gu))
           (⊢ˢ-convₜ (wk-⊢ˢ (step id) ⊢S)
             (conv
               (wk1 (lam p (wk (lift ρ) t) ∘ wk ρ′ u) [ H ∙ (p , u , ρ′) ]ₕ ≡⟨ wk1-tail (lam p (wk (lift ρ) t) ∘ wk ρ′ u) ⟩⊢≡
               (lam p (wk (lift ρ) t) ∘⟨ p ⟩ wk ρ′ u) [ H ]ₕ                 ≡⟨⟩⊢
               (wk ρ (lam p t) [ H ]ₕ) ∘⟨ p ⟩ (wk ρ′ u [ H ]ₕ)               ≡⟨ β-red-≡ ⊢t ⊢u ok ⟩⊢∎≡
               (wk (lift ρ) t [ H ]⇑ₕ) [ wk ρ′ u [ H ]ₕ ]₀                  ≡⟨ singleSubstComp (wk ρ′ u [ H ]ₕ) (toSubstₕ H) (wk (lift ρ) t) ⟩
               wk (lift ρ) t [ H ∙ (p , u , ρ′) ]ₕ                          ∎)
               (sym (trans B≡Gu (sym ≡G[u]₀))))) }
    where
    open TmR

  ⊢ₛ-⇒ᵥ ⊢s liftₕ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢e , ⊢S) →
    case inversion-lowerₑ ⊢e of λ {
      (u , F , ⊢F , PE.refl , B≡F) →
    let ⊢t′ = inversion-lift-Lift ⊢t
    in ⊢ₛ ⊢H (conv ⊢t′ (sym B≡F))
        (⊢ˢ-convₜ ⊢S (conv (Lift-β′ ⊢t′) (sym B≡F))) }

  ⊢ₛ-⇒ᵥ ⊢s prodˢₕ₁ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-fstₑ ⊢c of λ {
      (F , G , q , ⊢G , PE.refl , B≡F) →
    let ⊢t₁ , ⊢t₂ , _ , _ , ok = inversion-prod-Σ ⊢t
    in  ⊢ₛ ⊢H (conv ⊢t₁ (sym B≡F))
           (⊢ˢ-convₜ ⊢S (conv (Σ-β₁-≡ ⊢G ⊢t₁ ⊢t₂ ok) (sym B≡F))) }

  ⊢ₛ-⇒ᵥ ⊢s (prodˢₕ₂ {H} {p} {t₁} {t₂} {ρ}) =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , B , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-sndₑ ⊢c of λ {
      (F , G , q , ⊢G , PE.refl , B≡G₊) →
    let ⊢t₁ , ⊢t₂ , _ , _ , ok = inversion-prod-Σ ⊢t
        G₊≡B                   =
          G [ wk ρ t₁ [ toSubstₕ H ] ]₀                ≡˘⟨ subst-⊢≡₀ ⊢G (Σ-β₁-≡ ⊢G ⊢t₁ ⊢t₂ ok) ⟩⊢
          G [ fst p (wk ρ (prod 𝕤 p t₁ t₂)) [ H ]ₕ ]₀  ≡˘⟨ B≡G₊ ⊢t ⟩⊢∎
          B                                            ∎
    in  ⊢ₛ ⊢H (conv ⊢t₂ G₊≡B)
           (⊢ˢ-convₜ ⊢S (conv (Σ-β₂-≡ ⊢G ⊢t₁ ⊢t₂ ok) G₊≡B)) }
    where
    open TyR

  ⊢ₛ-⇒ᵥ ⊢s (prodʷₕ {S} {q′} {H} {p} {t₁} {t₂} {ρ} {r} {q} {A} {u} {ρ′} _) =
    case ⊢ₛ-inv′ ⊢s of λ
      (Γ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-prodrecₑ ⊢c of λ {
      (F , G , _ , ⊢u , ⊢A , PE.refl , B≡A₊) →
    let ⊢t₁ , ⊢t₂ , _ = inversion-prod-Σ ⊢t
        H₁ = H ∙ (q′ · r · p , t₁ , ρ)
        H₂ = H₁ ∙ (q′ · r , t₂ , step ρ)
        u≡u′ = begin
          (wk (liftn ρ′ 2) u) [ liftSubstn (toSubstₕ H) 2 ] [ wk ρ t₁ [ H ]ₕ , wk ρ t₂ [ H ]ₕ ]₁₀
            ≡⟨ doubleSubstComp (wk (liftn ρ′ 2) u) _ _ _ ⟩
          wk (liftn ρ′ 2) u [ consSubst (consSubst (toSubstₕ H) (wk ρ t₁ [ H ]ₕ)) (wk ρ t₂ [ H ]ₕ) ]
            ≡˘⟨ PE.cong (λ x → wk (liftn ρ′ 2) u [ consSubst (toSubstₕ H₁) x ]) (step-consSubst t₂) ⟩
          wk (liftn ρ′ 2) u [ H₂ ]ₕ ∎
        ⊢u′ = subst-⊢∷ {σ = consSubst (sgSubst (wk ρ t₁ [ H ]ₕ)) (wk ρ t₂ [ H ]ₕ)}
                ⊢u (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢t₁) ⊢t₂)
        A₊≡ = begin
           wk (lift ρ′) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑² [ wk ρ t₁ [ H ]ₕ , wk ρ t₂ [ H ]ₕ ]₁₀
             ≡˘⟨ substCompProdrec (wk (lift ρ′) A [ H ]⇑ₕ) _ _ idSubst ⟩
           wk (lift ρ′) A [ H ]⇑ₕ [ liftSubst idSubst ] [ wk ρ (prodʷ p t₁ t₂) [ H ]ₕ ]₀
             ≡⟨ PE.cong (_[ prodʷ p (wk ρ t₁ [ H ]ₕ) (wk ρ t₂ [ H ]ₕ) ]₀) (substVar-to-subst subst-lift-id (wk (lift ρ′) A [ H ]⇑ₕ)) ⟩
           wk (lift ρ′) A [ H ]⇑ₕ [ idSubst ] [ wk ρ (prodʷ p t₁ t₂) [ H ]ₕ ]₀
             ≡⟨ PE.cong (_[ prodʷ p (wk ρ t₁ [ H ]ₕ) (wk ρ t₂ [ H ]ₕ) ]₀) (subst-id (wk (lift ρ′) A [ H ]⇑ₕ)) ⟩
           wk (lift ρ′) A [ H ]⇑ₕ [ wk ρ (prodʷ p t₁ t₂) [ H ]ₕ ]₀ ∎
        ⊢u″ = PE.subst₂ (_ ⊢_∷_) u≡u′ A₊≡ ⊢u′
        Gt₁≡ = begin
           G [ wk ρ t₁ [ H ]ₕ ]₀               ≡⟨ substVar-to-subst (λ { x0 → PE.refl
                                                                      ; (x +1) → PE.sym (toWkₕ-toSubstₕ-var H x)
                                                                      }) G ⟩
           G [ toSubstₕ H₁ ₛ• lift (toWkₕ H) ] ≡˘⟨ subst-wk G ⟩
           wk (lift (toWkₕ H)) G [ H₁ ]ₕ       ∎
    in  ⊢ₛ {Γ = Γ ∙ wk (toWkₕ H) F ∙ wk (lift (toWkₕ H)) G}
           (⊢H ∙ PE.subst (_ ⊢ _ ∷_) (PE.sym (toWkₕ-toSubstₕ H F)) ⊢t₁
               ∙ PE.subst₂ (_ ⊢_∷_) (PE.sym (step-consSubst t₂)) Gt₁≡ ⊢t₂)
           (conv ⊢u″ (sym (B≡A₊ ⊢t)))
           (⊢ˢ-convₜ (wk-⊢ˢ (step (step id)) ⊢S) (conv
             (wk (step (step id)) (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) [ H₂ ]ₕ
               ≡⟨ step-consSubst (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) ⟩⊢≡
             wk (step id) (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) [ H₁ ]ₕ
               ≡⟨ step-consSubst (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) ⟩⊢≡
             wk id (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u)) [ H ]ₕ
               ≡⟨ PE.cong (_[ H ]ₕ) (wk-id (prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u))) ⟩⊢≡
             prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u) [ H ]ₕ
               ≡⟨ prodrec-β-≡ ⊢A ⊢t₁ ⊢t₂ ⊢u ⟩⊢∎≡
             (wk (liftn ρ′ 2) u) [ liftSubstn (toSubstₕ H) 2 ] [ wk ρ t₁ [ H ]ₕ , wk ρ t₂ [ H ]ₕ ]₁₀
               ≡⟨ u≡u′ ⟩
             wk (liftn ρ′ 2) u [ H₂ ]ₕ ∎)
             (sym (B≡A₊ ⊢t))))}
    where
    open TmR

  ⊢ₛ-⇒ᵥ ⊢s zeroₕ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-natrecₑ ⊢c of λ {
      (⊢z , ⊢s , PE.refl , B≡) →
    ⊢ₛ ⊢H (conv ⊢z (sym (B≡ ⊢t)))
       (⊢ˢ-convₜ ⊢S (conv (natrec-zero ⊢z ⊢s) (sym (B≡ ⊢t)))) }

  ⊢ₛ-⇒ᵥ {Δ} ⊢s (sucₕ {p} {r} {H} {t} {ρ} {q} {(n)} {A} {z} {s} {ρ′} _ _) =
    case ⊢ₛ-inv′ ⊢s of λ
      (Γ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-natrecₑ ⊢c of λ {
      (⊢z , ⊢s , PE.refl , B≡) →
    let ⊢t′ , _ = inversion-suc ⊢t
        ⊢natrec = natrecⱼ ⊢z ⊢s ⊢t′
        ⊢natrec′ = PE.subst₂ (ε » Δ ⊢_∷_) (lift-step-natrec A z s _)
                     (singleSubstComp (wk ρ t [ H ]ₕ) (toSubstₕ H) (wk (lift ρ′) A))
                     ⊢natrec
        nr-β-≡ = PE.subst₂
                   (ε » Δ ⊢_≡_∷
                    wk (lift ρ′) A [ H ]⇑ₕ [ suc (wk ρ t [ H ]ₕ) ]₀)
                   (lift-step-natrec′ {σ = toSubstₕ H} {ρ = ρ′} A z s (suc (wk ρ t)))
                   (PE.trans (substCompEq (wk (liftn ρ′ 2) s))
                     (substVar-to-subst (λ { x0 → lift-step-natrec A z s _
                                           ; (x0 +1) → PE.refl
                                           ; (x +2) → PE.trans (wk1-tail (wk1 (toSubstₕ H x))) (wk1-sgSubst (toSubstₕ H x) _)})
                       (wk (liftn ρ′ 2) s)))
                   (natrec-suc ⊢z ⊢s ⊢t′)
        _ , _ , ⊢s₊ = syntacticEqTerm nr-β-≡
    in  ⊢ₛ {Γ = Γ ∙ ℕ ∙ wk (lift ρ′) A} (⊢H ∙ ⊢t′ ∙ ⊢natrec′)
           (conv ⊢s₊ (sym (B≡ ⊢t)))
           (⊢ˢ-convₜ (wk-⊢ˢ (step (step id)) ⊢S) (conv nr-β-≡ (sym (B≡ ⊢t)))) }

  ⊢ₛ-⇒ᵥ ⊢s starʷₕ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-unitrecₑ ⊢c of λ {
      (⊢u , ⊢A , no-η , PE.refl , B≡) →
    ⊢ₛ ⊢H (conv ⊢u (sym (B≡ ⊢t)))
       (⊢ˢ-convₜ ⊢S (conv (unitrec-β-≡ ⊢A ⊢u) (sym (B≡ ⊢t)))) }

  ⊢ₛ-⇒ᵥ ⊢s (unitrec-ηₕ η) =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        ⊢A , ⊢t , ⊢u , A≡ = inversion-unitrec ⊢t
    in  ⊢ₛ ⊢H (conv ⊢u (trans (subst-⊢≡₀ ⊢A (Unit-η-≡ (inj₂ η) ⊢t)) (sym A≡)))
           (⊢ˢ-convₜ ⊢S (conv (unitrec-β-η-≡ ⊢A ⊢t ⊢u η) (sym A≡)))

  ⊢ₛ-⇒ᵥ ⊢s (rflₕⱼ {H} {p} {q} {A} {t} {B} {u} {v} {ρ′}) =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢rfl , ⊢c , ⊢S) →
    case inversion-Jₑ ⊢c of λ {
      (⊢u , ⊢B , PE.refl , B′≡) →
    let t≡v = inversion-rfl-Id ⊢rfl
        ⊢A , ⊢t , ⊢v = syntacticEqTerm t≡v
        Bt≡Bv = J-motive-rfl-cong (refl ⊢B) t≡v
    in  ⊢ₛ ⊢H (conv ⊢u (trans Bt≡Bv (sym (B′≡ ⊢rfl))))
           (⊢ˢ-convₜ ⊢S (conv
             (⦅ Jₑ p q A t B u v ρ′ ⦆ᶜ rfl [ H ]ₕ
               ≡⟨ J-cong′ (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (sym′ t≡v) (refl (rflⱼ′ t≡v)) ⟩⊢
             ⦅ Jₑ p q A t B u t ρ′ ⦆ᶜ rfl [ H ]ₕ
               ≡⟨ conv (J-β-≡ ⊢t ⊢B ⊢u) (J-motive-rfl-cong (refl ⊢B) t≡v) ⟩⊢∎
             wk ρ′ u [ H ]ₕ ∎)
             (sym (B′≡ ⊢rfl))))}
    where
    open TmR

  ⊢ₛ-⇒ᵥ ⊢s rflₕₖ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢rfl , ⊢c , ⊢S) →
    case inversion-Kₑ ⊢c of λ {
      (⊢u , ⊢B , ok , PE.refl , B′≡) →
    ⊢ₛ ⊢H (conv ⊢u (sym (B′≡ ⊢rfl)))
       (⊢ˢ-convₜ ⊢S (conv (K-β ⊢B ⊢u ok) (sym (B′≡ ⊢rfl)))) }

  ⊢ₛ-⇒ᵥ ⊢s rflₕₑ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢rfl , ⊢e , ⊢S) →
    case inversion-[]-congₑ ⊢e of λ {
      (ok , ⊢l , PE.refl , B≡) →
    let t≡u         = inversion-rfl-Id ⊢rfl
        _ , ⊢t , ⊢u = syntacticEqTerm t≡u
        ≡B          = sym (B≡ ⊢t ⊢u)
    in
    ⊢ₛ ⊢H (conv (rflⱼ′ ([]-cong′ ([]-cong→Erased ok) ⊢l t≡u)) ≡B)
      (⊢ˢ-convₜ ⊢S (conv ([]-cong-β-≡ ⊢l t≡u ok) ≡B)) }

opaque

  -- Type preservation for _⇒ₑ_

  ⊢ₛ-⇒ₑ : Δ ⊢ₛ s ∷ A → s ⇒ₑ s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇒ₑ ⊢s lowerₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        _ , _ , ⊢t , A≡F = inversion-lower ⊢t
    in  ⊢ₛ ⊢H ⊢t (conv (lowerₑ (syntacticEq A≡F .proj₂)) (sym A≡F) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s appₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        _ , _ , _ , ⊢t , ⊢u , A≡Gu = inversion-app ⊢t
        _ , ⊢G , _ = inversion-ΠΣ (syntacticTerm ⊢t)
    in  ⊢ₛ ⊢H ⊢t (conv (∘ₑ ⊢u ⊢G) (sym A≡Gu) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s fstₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        _ , _ , _ , _ , ⊢G , ⊢t , A≡F = inversion-fst ⊢t
    in  ⊢ₛ ⊢H ⊢t (conv (fstₑ ⊢G) (sym A≡F) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s sndₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        _ , _ , _ , _ , ⊢G , ⊢t , A≡Gt = inversion-snd ⊢t
    in  ⊢ₛ ⊢H ⊢t (conv (sndₑ ⊢G) (sym A≡Gt) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s prodrecₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        _ , _ , _ , _ , _ , ⊢B , ⊢t , ⊢u , A≡Bt = inversion-prodrec ⊢t
    in  ⊢ₛ ⊢H ⊢t (conv (prodrecₑ ⊢u ⊢B) (sym A≡Bt) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s natrecₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        _ , ⊢z , ⊢s , ⊢n , C≡ = inversion-natrec ⊢t
    in  ⊢ₛ ⊢H ⊢n (conv (natrecₑ ⊢z ⊢s) (sym C≡) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s (unitrecₕ no-η) =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        ⊢A , ⊢t , ⊢u , B≡At = inversion-unitrec ⊢t
    in  ⊢ₛ ⊢H ⊢t (conv (unitrecₑ ⊢u ⊢A no-η) (sym B≡At) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s emptyrecₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        ⊢A , ⊢t , A≡ = inversion-emptyrec ⊢t
    in  ⊢ₛ ⊢H ⊢t (conv (emptyrecₑ ⊢A) (sym A≡) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s Jₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        _ , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , A≡B₊ = inversion-J ⊢t
    in  ⊢ₛ ⊢H ⊢w (conv (Jₑ ⊢u ⊢B) (sym A≡B₊) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s Kₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        _ , ⊢t , ⊢B , ⊢u , ⊢v , ok , A≡B₊ = inversion-K ⊢t
    in  ⊢ₛ ⊢H ⊢v (conv (Kₑ ⊢u ⊢B ok) (sym A≡B₊) ∙ ⊢S)
  ⊢ₛ-⇒ₑ ⊢s []-congₕ =
    let _ , _ , ⊢H , ⊢t , ⊢S            = ⊢ₛ-inv ⊢s
        ⊢l , _ , _ , _ , ⊢v , ok , A≡Id = inversion-[]-cong ⊢t
    in
    ⊢ₛ ⊢H ⊢v
      (conv ([]-congₑ ok ⊢l)
         (sym (PE.subst (_⊢_≡_ _ _) (E.wk-Id-Erased-[]-[] _) A≡Id)) ∙
       ⊢S)

opaque

  -- Type preservation for _⇾ₑ_

  ⊢ₛ-⇾ₑ : Δ ⊢ₛ s ∷ A → s ⇾ₑ s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇾ₑ ⊢s (var {t} _ d) =
    let _ , A , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        ⊢H′ = heapUpdate-⊢ʰ ⊢H d
        H≡H′ = heapUpdateSubst d
        x[H]≡t[H] = PE.subst (_ ⊢ _ ≡_∷ A) (heapSubstVar d) (refl ⊢t)
    in  ⊢ₛ ⊢H′
           (PE.subst (_ ⊢_∷ A) (PE.trans (heapSubstVar d) (PE.cong (wk _ t [_]) H≡H′)) ⊢t)
           (heapUpdate-⊢ˢ (⊢ˢ-convₜ ⊢S x[H]≡t[H]) d)
  ⊢ₛ-⇾ₑ ⊢s (⇒ₑ d) = ⊢ₛ-⇒ₑ ⊢s d

opaque

  -- Type preservation for _⇢ₑ_

  ⊢ₛ-⇢ₑ : Δ ⊢ₛ s ∷ A → s ⇢ₑ s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇢ₑ ⊢s (var d) =
    let _ , A , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
    in  ⊢ₛ ⊢H (PE.subst (_ ⊢_∷ A) (heapSubstVar′ d) ⊢t)
           (⊢ˢ-convₜ ⊢S (PE.subst (_ ⊢ _ ≡_∷ A) (heapSubstVar′ d) (refl ⊢t)))
  ⊢ₛ-⇢ₑ ⊢s (⇒ₑ d) = ⊢ₛ-⇒ₑ ⊢s d

opaque

  -- Type preservation for _⇾ₑ*_

  ⊢ₛ-⇾ₑ* : Δ ⊢ₛ s ∷ A → s ⇾ₑ* s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇾ₑ* ⊢s id = ⊢s
  ⊢ₛ-⇾ₑ* ⊢s (d ⇨ d′) = ⊢ₛ-⇾ₑ* (⊢ₛ-⇾ₑ ⊢s d) d′

opaque

  -- Type preservation for _⇾_

  ⊢ₛ-⇾ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇾ s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇾ ⊢s (⇾ₑ d) = ⊢ₛ-⇾ₑ ⊢s d
  ⊢ₛ-⇾ ⊢s (⇒ᵥ d) = ⊢ₛ-⇒ᵥ ⊢s d

opaque

  -- Type preservation for _⇢_

  ⊢ₛ-⇢ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇢ s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇢ ⊢s (⇢ₑ d) = ⊢ₛ-⇢ₑ ⊢s d
  ⊢ₛ-⇢ ⊢s (⇒ᵥ d) = ⊢ₛ-⇒ᵥ ⊢s d

opaque

  -- Type preservation for _⇾*_

  ⊢ₛ-⇾* :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇾* s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇾* ⊢s id = ⊢s
  ⊢ₛ-⇾* ⊢s (d ⇨ d′) = ⊢ₛ-⇾* (⊢ₛ-⇾ ⊢s d) d′

opaque

  -- Type preservation for _⇢*_

  ⊢ₛ-⇢* :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇢* s′ → Δ ⊢ₛ s′ ∷ A
  ⊢ₛ-⇢* ⊢s id = ⊢s
  ⊢ₛ-⇢* ⊢s (d ⇨ d′) = ⊢ₛ-⇢* (⊢ₛ-⇢ ⊢s d) d′

opaque

  -- _⇒ₙ_ does not preserve typing.

  ¬⊢ₛ-⇒ₙ : Δ ⊢ₛ s ∷ A → s ⇒ₙ s′ → Δ ⊢ₛ s′ ∷ A → ⊥
  ¬⊢ₛ-⇒ₙ ⊢s (sucₕ x) ⊢s′ =
    let _ , _ , _ , _ , _ , ⊢c , _ = ⊢ₛ-inv′ ⊢s′
    in  inversion-sucₑ ⊢c
  ¬⊢ₛ-⇒ₙ ⊢s (numₕ x) ⊢s′ =
    let _ , _ , _ , _ , _ , ⊢c , _ = ⊢ₛ-inv′ ⊢s
    in  inversion-sucₑ ⊢c

opaque

  -- _↠_ does not preserve typing.

  ¬⊢ₛ-↠ : (∀ {k m n n′ Δ A} {s : State k m n} {s′ : State k m n′} → Δ ⊢ₛ s ∷ A → s ↠ s′ → Δ ⊢ₛ s′ ∷ A) → ⊥
  ¬⊢ₛ-↠ ⊢ₛ-↠ =
    let ⊢εℕℕ = ∙ ⊢ℕ (∙ ⊢ℕ εε)
        ⊢s = ⊢ₛ ε (sucⱼ (natrecⱼ (zeroⱼ εε) (zeroⱼ ⊢εℕℕ) (zeroⱼ εε))) ε
        d = sucₕ λ ()
    in  ¬⊢ₛ-⇒ₙ {s = ⟨ ε , suc (natrec 𝟘 𝟘 𝟘 ℕ zero zero zero) , id , ε ⟩} ⊢s d (⊢ₛ-↠ ⊢s (⇒ₙ d))

opaque

  -- Reduction of values correspond to one step in the wh cbn reduction

  ⇒ᵥ→⇒ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇒ᵥ s′ → ε » Δ ⊢ ⦅ s ⦆ ⇒ ⦅ s′ ⦆ ∷ A
  ⇒ᵥ→⇒ ⊢s liftₕ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢e , ⊢S) →
    case inversion-lowerₑ ⊢e of λ {
      (u′ , F′ , ⊢F′ , PE.refl , C≡F′) →
    let l , D , ⊢t′ , B≡Lift = inversion-lift ⊢t
        _ , F≡F′ = Lift-injectivity (sym B≡Lift)
    in  ⊢⦅⦆ˢ-subst ⊢S (conv (Lift-β⇒ ⊢t′) (trans F≡F′ (sym C≡F′))) }
  ⇒ᵥ→⇒ {A} ⊢s (lamₕ {S} {H} {p} {t} {ρ} {u} {ρ′} _) =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-∘ₑ ⊢c of λ {
      (F , G , q , ⊢u , PE.refl , C≡Gu) →
    let β-⇒ = PE.subst (_ ⊢ (wk ρ (lam p t) ∘⟨ p ⟩ wk ρ′ u) [ H ]ₕ ⇒_∷ _)
                (PE.trans (singleSubstComp (wk ρ′ u [ H ]ₕ) (toSubstₕ H) (wk (lift ρ) t))
                  (substConsId (wk (lift ρ) t)))
                (β-red-⇒₁ ⊢t ⊢u)
    in  PE.subst (_ ⊢ ⦅ S ⦆ˢ wk ρ (lam p t) ∘ wk ρ′ u [ H ]ₕ ⇒_∷ A)
          lemma (⊢⦅⦆ˢ-subst ⊢S (conv β-⇒ (sym C≡Gu))) }
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
  ⇒ᵥ→⇒ ⊢s prodˢₕ₁ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-fstₑ ⊢c of λ {
      (F′ , G′ , q′ , ⊢G′ , PE.refl , C≡F′) →
    let F , G , q , ⊢F , ⊢G , ⊢t₁ , ⊢t₂ , B≡Σ , ok = inversion-prod ⊢t
        F≡F′ , _ = ΠΣ-injectivity (sym B≡Σ)
    in  ⊢⦅⦆ˢ-subst ⊢S (conv (Σ-β₁-⇒ ⊢G ⊢t₁ ⊢t₂ ok) (trans F≡F′ (sym C≡F′))) }
  ⇒ᵥ→⇒ ⊢s prodˢₕ₂ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-sndₑ ⊢c of λ {
      (F′ , G′ , q′ , ⊢G′ , PE.refl , C≡G′₊) →
    let F , G , q , ⊢F , ⊢G , ⊢t₁ , ⊢t₂ , B≡Σ , ok = inversion-prod ⊢t
        F≡F′ , G≡G′ , _ = ΠΣ-injectivity (sym B≡Σ)
        G₊≡G′₊ = G≡G′ (sym′ (Σ-β₁-≡ ⊢G ⊢t₁ ⊢t₂ ok))
    in  ⊢⦅⦆ˢ-subst ⊢S (conv (Σ-β₂-⇒ ⊢G ⊢t₁ ⊢t₂ ok) (trans G₊≡G′₊ (sym (C≡G′₊ ⊢t)))) }
  ⇒ᵥ→⇒ {(k)} {(_)} {(m)} ⊢s (prodʷₕ {S} {q′} {H} {p} {t₁} {t₂} {ρ} {r} {q} {A} {u} {ρ′} _) =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-prodrecₑ ⊢c of λ {
      (F , G , q′ , ⊢u , ⊢A , PE.refl , C≡) →
    let β-⇒ = PE.subst (_ ⊢ prodrec r p q (wk (lift ρ′) A) (wk ρ (prodʷ p t₁ t₂)) (wk (liftn ρ′ 2) u) [ H ]ₕ ⇒_∷ _)
                (PE.sym ([,]-[]-commute {u = wk ρ t₁} {v = wk ρ t₂} (wk (liftn ρ′ 2) u)))
                (prodrec-β-⇒₁ ⊢A ⊢t ⊢u)
    in  PE.subst (_ ⊢ ⦅ S ⦆ˢ prodrec r p q _ _ _ [ H ]ₕ ⇒_∷ _)
          lemma (⊢⦅⦆ˢ-subst ⊢S (conv β-⇒ (sym (C≡ ⊢t)))) }
    where
    H₂ : Heap k (2+ m)
    H₂ = H ∙ (q′ · r · p , t₁ , ρ) ∙ (q′ · r , t₂ , step ρ)
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
  ⇒ᵥ→⇒ ⊢s zeroₕ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-natrecₑ ⊢c of λ {
        (⊢z , ⊢s , PE.refl , B≡) →
    ⊢⦅⦆ˢ-subst ⊢S (conv (natrec-zero ⊢z ⊢s) (sym (B≡ ⊢t))) }
  ⇒ᵥ→⇒ {(k)} {(_)} {(m)} ⊢s (sucₕ {S} {p} {r} {H} {t} {ρ} {q} {(n)} {A} {z} {s} {ρ′} _ _) =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-natrecₑ ⊢c of λ {
      (⊢z , ⊢s , PE.refl , B≡) →
    let β-⇒ = PE.subst (_ ⊢ nr″ (wk ρ (suc t)) [ H ]ₕ ⇒_∷ _)
                (PE.sym ([,]-[]-commute (wk (liftn ρ′ 2) s)))
                (natrec-suc ⊢z ⊢s (inversion-suc ⊢t .proj₁))
    in  PE.subst (_ ⊢ ⦅ S ⦆ˢ nr″ (wk ρ (suc t)) [ H ]ₕ ⇒_∷ _) lemma
          (⊢⦅⦆ˢ-subst ⊢S (conv β-⇒ (sym (B≡ ⊢t))))}
    where
    nr″ : Term m → Term m
    nr″ = natrec p q r (wk (lift ρ′) A) (wk ρ′ z) (wk (liftn ρ′ 2) s)
    nr′ : Term (1+ n)
    nr′ = natrec p q r (wk (lift (step id)) A) (wk1 z) (wk (liftn (step id) 2) s) (var x0)
    H₂ : Heap k (2+ m)
    H₂ = H ∙ (p + r , t , ρ) ∙ (r , nr′ , lift ρ′)
    lemma′ : nr″ (wk ρ t) [ H ]ₕ PE.≡ wk (lift ρ′) nr′ [ H ∙ (p + r , t , ρ) ]ₕ
    lemma′ = begin
      nr″ (wk ρ t) [ H ]ₕ ≡⟨ lift-step-natrec A z s _ ⟩
      wk (lift ρ′) nr′ [ H ∙ (p + r , t , ρ) ]ₕ ∎
    lemma : ⦅ S ⦆ˢ ((wk (liftn ρ′ 2) s) [ wk ρ t , nr″ (wk ρ t) ]₁₀) [ H ]ₕ
          PE.≡ ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ H₂ ]ₕ
    lemma = begin
      ⦅ S ⦆ˢ ((wk (liftn ρ′ 2) s) [ wk ρ t , nr″ (wk ρ t) ]₁₀) [ H ]ₕ
        ≡⟨ PE.cong (_[ H ]ₕ) (⦅⦆ˢ-[,] S) ⟩
      ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ wk ρ t , nr″ (wk ρ t) ]₁₀ [ H ]ₕ
            ≡⟨ [,]-[]-fusion (⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s)) ⟩
      ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ consSubst (consSubst (toSubstₕ H) (wk ρ t [ H ]ₕ)) (nr″ (wk ρ t) [ H ]ₕ) ]
        ≡⟨ PE.cong (λ x → ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ consSubst (consSubst (toSubstₕ H) (wk ρ t [ H ]ₕ)) x ]) lemma′ ⟩
      ⦅ wk2ˢ S ⦆ˢ (wk (liftn ρ′ 2) s) [ H₂ ]ₕ ∎
  ⇒ᵥ→⇒ ⊢s starʷₕ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢t , ⊢c , ⊢S) →
    case inversion-unitrecₑ ⊢c of λ {
      (⊢u , ⊢A , no-η , PE.refl , C≡A₊) →
    ⊢⦅⦆ˢ-subst ⊢S (conv (unitrec-β-⇒ ⊢A ⊢u) (sym (C≡A₊ ⊢t))) }
  ⇒ᵥ→⇒ ⊢s (unitrec-ηₕ η) =
    let _ , _ , ⊢H , ⊢t , ⊢S = ⊢ₛ-inv ⊢s
        ⊢A , ⊢t , ⊢u , A≡ = inversion-unitrec ⊢t
    in  ⊢⦅⦆ˢ-subst ⊢S (conv (unitrec-β-η-⇒ ⊢A ⊢t ⊢u η) (sym A≡))
  ⇒ᵥ→⇒ ⊢s rflₕⱼ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢rfl , ⊢c , ⊢S) →
    case inversion-Jₑ ⊢c of λ {
      (⊢w , ⊢B , PE.refl , ≡B) →
    let t≡v = inversion-rfl-Id ⊢rfl
        ≡B′ = trans (J-motive-rfl-cong (refl ⊢B) t≡v) (sym (≡B ⊢rfl))
    in  ⊢⦅⦆ˢ-subst ⊢S (conv (J-β-⇒ t≡v ⊢B ⊢w) ≡B′) }
  ⇒ᵥ→⇒ ⊢s rflₕₖ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢rfl , ⊢c , ⊢S) →
    case inversion-Kₑ ⊢c of λ {
      (⊢v , ⊢B , ok , PE.refl , B′≡)  →
    ⊢⦅⦆ˢ-subst ⊢S (conv (K-β ⊢B ⊢v ok) (sym (B′≡ ⊢rfl))) }
  ⇒ᵥ→⇒ ⊢s rflₕₑ =
    case ⊢ₛ-inv′ ⊢s of λ
      (_ , _ , _ , ⊢H , ⊢rfl , ⊢e , ⊢S) →
    case inversion-[]-congₑ ⊢e of λ {
        (ok , ⊢A , PE.refl , B′≡) →
    let t≡u = inversion-rfl-Id ⊢rfl
        _ , ⊢t , ⊢u = syntacticEqTerm t≡u
    in
    ⊢⦅⦆ˢ-subst ⊢S $
    conv ([]-cong-β ⊢A t≡u ok) (sym (B′≡ ⊢t ⊢u)) }

opaque

  -- For states with sucₑ on the stack, the previous property does not
  -- hold, i.e. there is a counterexample. (Assuming a certain Π-type
  -- is allowed).

  ¬sucₑ-⇒ᵥ→⇒ :
    Π-allowed 𝟙 q →
    ∃₇ λ m n m′ n′ (s : State 0 m n) (s′ : State 0 m′ n′) A →
    s ⇒ᵥ s′ × ε » ε ⊢ ⦅ s ⦆ ∷ A × ¬ (ε » ε ⊢ ⦅ s ⦆ ⇒ ⦅ s′ ⦆ ∷ A)
  ¬sucₑ-⇒ᵥ→⇒ ok =
    _ , _ , _ , _
      , ⟨ ε , lam 𝟙 (var x0) , id , ∘ₑ 𝟙 zero id ∙ (sucₑ ∙ ε) ⟩
      , _
      , ℕ , lamₕ (sucₑ ∙ ε)
      , sucⱼ
          ((lamⱼ (⊢ℕ (∙ ⊢ℕ εε)) (var (∙ ⊢ℕ εε) here) ok) ∘ⱼ (zeroⱼ εε))
      , λ d → whnfRedTerm d WHNF.sucₙ

opaque

  -- Reduction of values preserves definitional equality

  ⇒ᵥ→≡ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇒ᵥ s′ → ε » Δ ⊢ ⦅ s ⦆ ≡ ⦅ s′ ⦆ ∷ A
  ⇒ᵥ→≡ ⊢s d = subsetTerm (⇒ᵥ→⇒ ⊢s d)

opaque

  -- Reduction preserves definitional equality

  ⇾→≡ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇾ s′ → ε » Δ ⊢ ⦅ s ⦆ ≡ ⦅ s′ ⦆ ∷ A
  ⇾→≡ ⊢s (⇾ₑ d) =
    PE.subst (_ ⊢ _ ≡_∷ _) (⇾ₑ-⦅⦆-≡ d) (refl (⊢⦅⦆ ⊢s))
  ⇾→≡ ⊢s (⇒ᵥ d) =
    ⇒ᵥ→≡ ⊢s d

opaque

  -- Reduction preserves definitional equality

  ⇢→≡ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇢ s′ → ε » Δ ⊢ ⦅ s ⦆ ≡ ⦅ s′ ⦆ ∷ A
  ⇢→≡ ⊢s (⇢ₑ d) =
    PE.subst (_ ⊢ _ ≡_∷ _) (⇢ₑ-⦅⦆-≡ d) (refl (⊢⦅⦆ ⊢s))
  ⇢→≡ ⊢s (⇒ᵥ d) =
    ⇒ᵥ→≡ ⊢s d

opaque

  -- Reduction preserves definitional equality

  ⇾*→≡ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇾* s′ → ε » Δ ⊢ ⦅ s ⦆ ≡ ⦅ s′ ⦆ ∷ A
  ⇾*→≡ ⊢s id = refl (⊢⦅⦆ ⊢s)
  ⇾*→≡ ⊢s (x ⇨ d) =
    trans (⇾→≡ ⊢s x) (⇾*→≡ (⊢ₛ-⇾ ⊢s x) d)

opaque

  -- Reduction preserves definitional equality

  ⇢*→≡ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A → s ⇢* s′ → ε » Δ ⊢ ⦅ s ⦆ ≡ ⦅ s′ ⦆ ∷ A
  ⇢*→≡ ⊢s id = refl (⊢⦅⦆ ⊢s)
  ⇢*→≡ ⊢s (x ⇨ d) =
    trans (⇢→≡ ⊢s x) (⇢*→≡ (⊢ₛ-⇢ ⊢s x) d)

opaque

  -- Values in non-empty stacks always reduce (assuming that the stack
  -- multiplicity exists).

  ⊢ˢValue-⇒ᵥ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    ∣ c ∙ S ∣≡ p →
    Δ ⨾ H ⊢ᶜ c ⟨ wk ρ t ⟩∷ A ↝ B → ε » Δ ⊢ wk ρ t [ H ]ₕ ∷ A → Value t →
    ∃₃ λ m n (s : State _ m n) → ⟨ H , t , ρ , c ∙ S ⟩ ⇒ᵥ s
  -- Ok cases:
  ⊢ˢValue-⇒ᵥ ∣S∣≡ (conv ⊢c x) ⊢t v =
    ⊢ˢValue-⇒ᵥ ∣S∣≡ ⊢c ⊢t v
  ⊢ˢValue-⇒ᵥ _ ⊢c ⊢t (unitrec-ηᵥ η) =
    _ , _ , _ , unitrec-ηₕ η
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t liftᵥ =
    case inversion-lift-Lift ⊢t of λ
      ⊢t′ →
    _ , _ , _ , liftₕ
  ⊢ˢValue-⇒ᵥ (_ ∙ ∣S∣≡) (∘ₑ x x₁) ⊢t lamᵥ =
    case inversion-lam-Π ⊢t of λ {
      (_ , _ , _ , PE.refl , _) →
    _ , _ , _ , lamₕ ∣S∣≡}
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t prodᵥ =
    case inversion-prod-Σ ⊢t of λ {
      (_ , _ , PE.refl , PE.refl , _) →
    _ , _ , _ , prodˢₕ₁}
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t prodᵥ =
    case inversion-prod-Σ ⊢t of λ {
      (_ , _ , PE.refl , PE.refl , _) →
    _ , _ , _ , prodˢₕ₂}
  ⊢ˢValue-⇒ᵥ (_ ∙ ∣S∣≡) (prodrecₑ x x₁) ⊢t prodᵥ =
    case inversion-prod-Σ ⊢t of λ {
      (_ , _ , PE.refl , PE.refl , _) →
    _ , _ , _ , prodʷₕ ∣S∣≡}
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t zeroᵥ =
    _ , _ , _ , zeroₕ
  ⊢ˢValue-⇒ᵥ (natrecₑ ∣nr∣≡ ∙ ∣S∣≡) (natrecₑ _ _) ⊢t sucᵥ =
        _ , _ , _ , sucₕ ∣S∣≡ ∣nr∣≡
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t starᵥ =
    case inversion-star-Unit ⊢t of λ {
      (PE.refl , _) →
    _ , _ , _ , starʷₕ }
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t rflᵥ =
    _ , _ , _ , rflₕⱼ
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t rflᵥ =
    _ , _ , _ , rflₕₖ
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) _ rflᵥ =
    _ , _ , _ , rflₕₑ

  -- Impossible cases:
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t Levelᵥ =
    ⊥-elim (I.U≢Liftⱼ (sym (inversion-Level ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t Levelᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Level ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t Levelᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Level ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t Levelᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Level ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t Levelᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Level ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ x x₁) ⊢t Levelᵥ =
    ⊥-elim (I.U≢ℕ (sym (inversion-Level ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t Levelᵥ =
    ⊥-elim (I.U≢Unitⱼ (sym (inversion-Level ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t Levelᵥ =
    ⊥-elim (I.U≢Emptyⱼ (sym (inversion-Level ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t Levelᵥ =
    ⊥-elim (I.Id≢U (inversion-Level ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t Levelᵥ =
    ⊥-elim (I.Id≢U (inversion-Level ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t Levelᵥ =
    ⊥-elim (I.Id≢U (inversion-Level ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Lift≢Level (inversion-zeroᵘ ⊢t))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Level≢ΠΣⱼ (sym (inversion-zeroᵘ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Level≢ΠΣⱼ (sym (inversion-zeroᵘ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Level≢ΠΣⱼ (sym (inversion-zeroᵘ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Level≢ΠΣⱼ (sym (inversion-zeroᵘ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ x x₁) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Level≢ℕ (sym (inversion-zeroᵘ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Level≢Unitⱼ (sym (inversion-zeroᵘ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Level≢Empty (sym (inversion-zeroᵘ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Id≢Level (inversion-zeroᵘ ⊢t))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Id≢Level (inversion-zeroᵘ ⊢t))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t zeroᵘᵥ =
    ⊥-elim (I.Id≢Level (inversion-zeroᵘ ⊢t))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t sucᵘᵥ =
    (⊥-elim (I.Lift≢Level (inversion-sucᵘ ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t sucᵘᵥ =
    ⊥-elim (I.Level≢ΠΣⱼ (sym (inversion-sucᵘ ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t sucᵘᵥ =
    (⊥-elim (I.Level≢ΠΣⱼ (sym (inversion-sucᵘ ⊢t .proj₂))))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t sucᵘᵥ =
    ⊥-elim (I.Level≢ΠΣⱼ (sym (inversion-sucᵘ ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t sucᵘᵥ =
    ⊥-elim (I.Level≢ΠΣⱼ (sym (inversion-sucᵘ ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ x x₁) ⊢t sucᵘᵥ =
    ⊥-elim (I.Level≢ℕ (sym (inversion-sucᵘ ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t sucᵘᵥ =
    ⊥-elim (I.Level≢Unitⱼ (sym (inversion-sucᵘ ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t sucᵘᵥ =
    ⊥-elim (I.Level≢Empty (sym (inversion-sucᵘ ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t sucᵘᵥ =
    ⊥-elim (I.Id≢Level (inversion-sucᵘ ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t sucᵘᵥ =
    ⊥-elim (I.Id≢Level (inversion-sucᵘ ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t sucᵘᵥ =
    ⊥-elim (I.Id≢Level (inversion-sucᵘ ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Lift≡Π , _) →
    ⊥-elim (I.Lift≢ΠΣⱼ Lift≡Π)
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Σ≡Π , _) →
    ⊥-elim (I.Π≢Σⱼ (sym Σ≡Π))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Σ≡Π , _) →
    ⊥-elim (I.Π≢Σⱼ (sym Σ≡Π))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Σ≡Π , _) →
    ⊥-elim (I.Π≢Σⱼ (sym Σ≡Π))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , ℕ≡Π , _) →
    ⊥-elim (I.ℕ≢ΠΣⱼ ℕ≡Π)
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Unit≡Π , _) →
    ⊥-elim (I.Unit≢ΠΣⱼ Unit≡Π)
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Empty≡Π , _) →
    ⊥-elim (I.Empty≢ΠΣⱼ Empty≡Π)
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Id≡Π , _) →
    ⊥-elim (I.Id≢ΠΣ Id≡Π)
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Id≡Π , _) →
    ⊥-elim (I.Id≢ΠΣ Id≡Π)
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t lamᵥ =
    case inversion-lam ⊢t of λ
      (_ , _ , _ , _ , _ , Id≡Π , _) →
    ⊥-elim (I.Id≢ΠΣ Id≡Π)
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t zeroᵥ =
    ⊥-elim (I.Lift≢ℕ (inversion-zero ⊢t))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t zeroᵥ =
    ⊥-elim (I.ℕ≢ΠΣⱼ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t zeroᵥ =
    ⊥-elim (I.ℕ≢ΠΣⱼ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t zeroᵥ =
    ⊥-elim (I.ℕ≢ΠΣⱼ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t zeroᵥ =
    ⊥-elim (I.ℕ≢ΠΣⱼ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t zeroᵥ =
    ⊥-elim (I.ℕ≢Unitⱼ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t zeroᵥ =
    ⊥-elim (I.ℕ≢Emptyⱼ (sym (inversion-zero ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t zeroᵥ =
    ⊥-elim (I.Id≢ℕ (inversion-zero ⊢t))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t zeroᵥ =
    ⊥-elim (I.Id≢ℕ (inversion-zero ⊢t))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t zeroᵥ =
    ⊥-elim (I.Id≢ℕ (inversion-zero ⊢t))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t sucᵥ =
    (⊥-elim (I.Lift≢ℕ (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t sucᵥ =
    ⊥-elim (I.ℕ≢ΠΣⱼ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t sucᵥ =
    (⊥-elim (I.ℕ≢ΠΣⱼ (sym (inversion-suc ⊢t .proj₂))))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t sucᵥ =
    ⊥-elim (I.ℕ≢ΠΣⱼ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t sucᵥ =
    ⊥-elim (I.ℕ≢ΠΣⱼ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t sucᵥ =
    ⊥-elim (I.ℕ≢Unitⱼ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t sucᵥ =
    ⊥-elim (I.ℕ≢Emptyⱼ (sym (inversion-suc ⊢t .proj₂)))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t sucᵥ =
    ⊥-elim (I.Id≢ℕ (inversion-suc ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t sucᵥ =
    ⊥-elim (I.Id≢ℕ (inversion-suc ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t sucᵥ =
    ⊥-elim (I.Id≢ℕ (inversion-suc ⊢t .proj₂))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t starᵥ =
    ⊥-elim (I.Lift≢Unitⱼ (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t starᵥ =
    ⊥-elim (I.Unit≢ΠΣⱼ (sym (inversion-star ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t starᵥ =
    ⊥-elim (I.Unit≢ΠΣⱼ (sym (inversion-star ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t starᵥ =
    ⊥-elim (I.Unit≢ΠΣⱼ (sym (inversion-star ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t starᵥ =
    ⊥-elim (I.Unit≢ΠΣⱼ (sym (inversion-star ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t starᵥ =
    ⊥-elim (I.ℕ≢Unitⱼ (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t starᵥ =
    ⊥-elim (I.Empty≢Unitⱼ (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t starᵥ =
    ⊥-elim (I.Id≢Unit (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t starᵥ =
    ⊥-elim (I.Id≢Unit (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t starᵥ =
    ⊥-elim (I.Id≢Unit (inversion-star ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Lift≡Σ , _) →
    ⊥-elim (I.Lift≢ΠΣⱼ Lift≡Σ)
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Π≡Σ , _) →
    ⊥-elim (I.Π≢Σⱼ Π≡Σ)
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , ℕ≡Σ , _) →
    ⊥-elim (I.ℕ≢ΠΣⱼ ℕ≡Σ)
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Unit≡Σ , _) →
    ⊥-elim (I.Unit≢ΠΣⱼ Unit≡Σ)
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Empty≡Σ , _) →
    ⊥-elim (I.Empty≢ΠΣⱼ Empty≡Σ)
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
    ⊥-elim (I.Id≢ΠΣ Id≡Σ)
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
    ⊥-elim (I.Id≢ΠΣ Id≡Σ)
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t prodᵥ =
    case inversion-prod ⊢t of λ
      (_ , _ , _ , _ , _ , _ , _ , Id≡Σ , _) →
    ⊥-elim (I.Id≢ΠΣ Id≡Σ)
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Lift≡Id) →
    ⊥-elim (I.Id≢Lift (sym Lift≡Id))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Π≡Id) →
    ⊥-elim (I.Id≢ΠΣ (sym Π≡Id))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Σ≡Id) →
    ⊥-elim (I.Id≢ΠΣ (sym Σ≡Id))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Σ≡Id) →
    ⊥-elim (I.Id≢ΠΣ (sym Σ≡Id))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Σ≡Id) →
    ⊥-elim (I.Id≢ΠΣ (sym Σ≡Id))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , ℕ≡Id) →
    ⊥-elim (I.Id≢ℕ (sym ℕ≡Id))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Unit≡Id) →
    ⊥-elim (I.Id≢Unit (sym Unit≡Id))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t rflᵥ =
    case inversion-rfl ⊢t of λ
      (_ , _ , _ , _ , Empty≡Id) →
    ⊥-elim (I.Id≢Empty (sym Empty≡Id))
  ⊢ˢValue-⇒ᵥ _ ⊢e ⊢t Uᵥ =
    ⊥-elim (hole-type-not-U ⊢e (inversion-U ⊢t))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Lift≡U , _) →
    ⊥-elim (I.U≢Liftⱼ (sym Lift≡U))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Π≡U , _) →
    ⊥-elim (I.U≢ΠΣⱼ (sym Π≡U))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U , _) →
    ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U , _) →
    ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U , _) →
    ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , ℕ≡U , _) →
    ⊥-elim (I.U≢ℕ (sym ℕ≡U))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Unit≡U , _) →
    ⊥-elim (I.U≢Unitⱼ (sym Unit≡U))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Empty≡U , _) →
    ⊥-elim (I.U≢Emptyⱼ (sym Empty≡U))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U , _) →
    ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U , _) →
    ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t ΠΣᵥ =
    case inversion-ΠΣ-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U , _) →
    ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t ℕᵥ =
    ⊥-elim (I.U≢Liftⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t ℕᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t ℕᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t ℕᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t ℕᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t ℕᵥ =
    ⊥-elim (I.U≢ℕ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t ℕᵥ =
    ⊥-elim (I.U≢Unitⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t ℕᵥ =
    ⊥-elim (I.U≢Emptyⱼ (sym (inversion-ℕ ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t ℕᵥ =
    ⊥-elim (I.Id≢U (inversion-ℕ ⊢t))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t ℕᵥ =
    ⊥-elim (I.Id≢U (inversion-ℕ ⊢t))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t ℕᵥ =
    ⊥-elim (I.Id≢U (inversion-ℕ ⊢t))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t Unitᵥ =
    ⊥-elim (I.U≢Liftⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t Unitᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t Unitᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t Unitᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t Unitᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t Unitᵥ =
    ⊥-elim (I.U≢ℕ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t Unitᵥ =
    ⊥-elim (I.U≢Unitⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t Unitᵥ =
    ⊥-elim (I.U≢Emptyⱼ (sym (inversion-Unit-U ⊢t .proj₁)))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t Unitᵥ =
    ⊥-elim (I.Id≢U (inversion-Unit-U ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t Unitᵥ =
    ⊥-elim (I.Id≢U (inversion-Unit-U ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t Unitᵥ =
    ⊥-elim (I.Id≢U (inversion-Unit-U ⊢t .proj₁))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t Emptyᵥ =
    ⊥-elim (I.U≢Liftⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t Emptyᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t Emptyᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t Emptyᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t Emptyᵥ =
    ⊥-elim (I.U≢ΠΣⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t Emptyᵥ =
    ⊥-elim (I.U≢ℕ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t Emptyᵥ =
    ⊥-elim (I.U≢Unitⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t Emptyᵥ =
    ⊥-elim (I.U≢Emptyⱼ (sym (inversion-Empty ⊢t)))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t Emptyᵥ =
    ⊥-elim (I.Id≢U (inversion-Empty ⊢t))
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t Emptyᵥ =
    ⊥-elim (I.Id≢U (inversion-Empty ⊢t))
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t Emptyᵥ =
    ⊥-elim (I.Id≢U (inversion-Empty ⊢t))
  ⊢ˢValue-⇒ᵥ _ (lowerₑ _) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Lift≡U) →
    ⊥-elim (I.U≢Liftⱼ (sym Lift≡U))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Π≡U) →
    ⊥-elim (I.U≢ΠΣⱼ (sym Π≡U))
  ⊢ˢValue-⇒ᵥ _ (fstₑ _) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U) →
    ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (sndₑ _) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U) →
    ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Σ≡U) →
    ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ _ _) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , ℕ≡U) →
    ⊥-elim (I.U≢ℕ (sym ℕ≡U))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Unit≡U) →
    ⊥-elim (I.U≢Unitⱼ (sym Unit≡U))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Empty≡U) →
    ⊥-elim (I.U≢Emptyⱼ (sym Empty≡U))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U) →
    ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U) →
    ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t Idᵥ =
    case inversion-Id-U ⊢t of λ
      (_ , _ , _ , _ , Id≡U) →
    ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ (lowerₑ x) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Lift≡U)
    → ⊥-elim (I.U≢Liftⱼ (sym Lift≡U))
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Π≡U)
    → ⊥-elim (I.U≢ΠΣⱼ (sym Π≡U))
  ⊢ˢValue-⇒ᵥ _ (fstₑ x) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Σ≡U)
    → ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (sndₑ x) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Σ≡U)
    → ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Σ≡U)
    → ⊥-elim (I.U≢ΠΣⱼ (sym Σ≡U))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ x x₁) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , ℕ≡U)
    → ⊥-elim (I.U≢ℕ (sym ℕ≡U))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Unit≡U)
    → ⊥-elim (I.U≢Unitⱼ (sym Unit≡U))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Empty≡U)
    → ⊥-elim (I.U≢Emptyⱼ (sym Empty≡U))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Id≡U)
    → ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Id≡U)
    → ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t Liftᵥ =
    case inversion-Lift∷ ⊢t of λ
      (_ , _ , _ , Id≡U)
    → ⊥-elim (I.Id≢U Id≡U)
  ⊢ˢValue-⇒ᵥ _ (∘ₑ x x₁) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Π≡Lift)
    → ⊥-elim (I.Lift≢ΠΣⱼ (sym Π≡Lift))
  ⊢ˢValue-⇒ᵥ _ (fstₑ x) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Σ≡Lift)
    → ⊥-elim (I.Lift≢ΠΣⱼ (sym Σ≡Lift))
  ⊢ˢValue-⇒ᵥ _ (sndₑ x) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Σ≡Lift)
    → ⊥-elim (I.Lift≢ΠΣⱼ (sym Σ≡Lift))
  ⊢ˢValue-⇒ᵥ _ (prodrecₑ x x₁) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Σ≡Lift)
    → ⊥-elim (I.Lift≢ΠΣⱼ (sym Σ≡Lift))
  ⊢ˢValue-⇒ᵥ _ (natrecₑ x x₁) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , ℕ≡Lift)
    → ⊥-elim (I.Lift≢ℕ (sym ℕ≡Lift))
  ⊢ˢValue-⇒ᵥ _ (unitrecₑ x x₁ x₂) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Unit≡Lift)
    → ⊥-elim (I.Lift≢Unitⱼ (sym Unit≡Lift))
  ⊢ˢValue-⇒ᵥ _ (emptyrecₑ x) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Empty≡Lift)
    → ⊥-elim (I.Lift≢Emptyⱼ (sym Empty≡Lift))
  ⊢ˢValue-⇒ᵥ _ (Jₑ x x₁) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Id≡Lift)
    → ⊥-elim (I.Id≢Lift Id≡Lift)
  ⊢ˢValue-⇒ᵥ _ (Kₑ x x₁ x₂) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Id≡Lift)
    → ⊥-elim (I.Id≢Lift Id≡Lift)
  ⊢ˢValue-⇒ᵥ _ ([]-congₑ _ _) ⊢t liftᵥ =
    case inversion-lift ⊢t of λ
      (_ , _ , _ , Id≡Lift)
    → ⊥-elim (I.Id≢Lift Id≡Lift)

opaque

  -- Values in non-empty stacks always reduce (assuming that the stack
  -- multiplicity exists)

  ⊢Value-⇒ᵥ :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    ∣ c ∙ S ∣≡ p →
    Δ ⊢ₛ ⟨ H , t , ρ , c ∙ S ⟩ ∷ A → Value t →
    ∃₃ λ m n (s : State _ m n) → ⟨ H , t , ρ , c ∙ S ⟩ ⇒ᵥ s
  ⊢Value-⇒ᵥ ∣S∣≡ ⊢s v =
    let _ , _ , _ , _ , ⊢t , ⊢e , _ = ⊢ₛ-inv′ ⊢s
    in  ⊢ˢValue-⇒ᵥ ∣S∣≡ ⊢e ⊢t v

opaque

  -- Well-typed states with values in head position and a non-empty
  -- stack have a matching head and stack (assuming that the stack
  -- multiplicity exists)

  ⊢Matching :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    ∣ c ∙ S ∣≡ p →
    Δ ⊢ₛ ⟨ H , t , ρ , c ∙ S ⟩ ∷ A →
    Value t →
    Matching t (c ∙ S)
  ⊢Matching ∣S∣≡ ⊢s v =
    let _ , _ , _ , d = ⊢Value-⇒ᵥ ∣S∣≡ ⊢s v
    in  ⇒ᵥ→Matching d

opaque

  -- For well-typed states there are four reasons why a state can be
  -- Final:
  -- 1. It has a variable in head position but lookup does not succeed
  --    (for the number of copies matching the current stack
  --    multiplicity).
  -- 2. It has an application of _supᵘ_ in head position.
  -- 3. It has a value in head position, the stack is non-empty and the
  --    stack multiplicity does not exist.
  -- 4. It has a value in head position and the stack is empty.
  -- 5. It has a name in head position.

  ⊢Final-reasons :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    Final ⟨ H , t , ρ , S ⟩ →
    (∃ λ x → t PE.≡ var x ×
         (∀ {p n H′} {e : Entry _ n} → ∣ S ∣≡ p → H ⊢ wkVar ρ x ↦[ p ] e ⨾ H′ → ⊥)) ⊎
    (∃₂ λ u v → t PE.≡ u supᵘ v) ⊎
    (∃₂ λ c S′ → S PE.≡ c ∙ S′ × Value t × ¬ (∃ ∣ S ∣≡_)) ⊎
    Value t × S PE.≡ ε ⊎
    (∃ λ α → t PE.≡ defn α)
  ⊢Final-reasons ⊢s f =
    case Final-reasons _ f of λ where
      (inj₁ (inj₁ x)) → inj₁ x
      (inj₁ (inj₂ x)) → inj₂ (inj₁ x)
      (inj₂ (inj₁ (_ , _ , PE.refl , v , prop))) →
        inj₂ $ inj₂ $ inj₁
          (_ , _ , PE.refl , v ,
           λ (p , ∣S∣≡p) → prop (⊢Matching ∣S∣≡p ⊢s v , (_ , ∣S∣≡p)))
      (inj₂ (inj₂ x)) → inj₂ (inj₂ (inj₂ x))

opaque

  -- A variant of the above property.

  ⊢⇘-reasons :
    ⦃ ok : No-equality-reflection or-empty Δ ⦄ →
    Δ ⊢ₛ s ∷ A →
    s ⇘ ⟨ H , t , ρ , S ⟩ →
    (∃ λ x → t PE.≡ var x ×
         (∀ {p n H′} {e : Entry _ n} → ∣ S ∣≡ p → H ⊢ wkVar ρ x ↦[ p ] e ⨾ H′ → ⊥)) ⊎
    (∃₂ λ u v → t PE.≡ u supᵘ v) ⊎
    (∃₂ λ c S′ → S PE.≡ c ∙ S′ × Value t × ¬ (∃ ∣ S ∣≡_)) ⊎
    Value t × S PE.≡ ε ⊎
    (∃ λ α → t PE.≡ defn α)
  ⊢⇘-reasons ⊢s (d , f) =
    ⊢Final-reasons (⊢ₛ-⇾* ⊢s d) f
