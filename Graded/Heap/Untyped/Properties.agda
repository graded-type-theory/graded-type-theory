------------------------------------------------------------------------
-- Properties of machine states.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Untyped.Properties
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
open IsMode 𝐌

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; +-suc) renaming (_+_ to _+ⁿ_)
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Relation
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Instance UR

open import Definition.Untyped M
open import Definition.Untyped.Names-below M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Graded.Heap.Untyped type-variant UR factoring-nr ∣ε∣

private variable
  k n n′ n″ m m′ m″ : Nat
  t t′ t″ u v A z : Term _
  H H′ H″ : Heap _ _
  ρ ρ′ ρ″ : Wk _ _
  S S′ S″ : Stack _
  p p′ q q′ r r′ : M
  y y′ : Ptr _
  x : Fin _
  e : Entry _ _
  ∇ : DCon (Term 0) _
  Γ : Con Term _
  c c′ c″ : Cont _
  s s′ : State _ _ _
  σ : Subst _ _
  em em′ : Erased-matches
  mo mo′ : Mode
  V : Set a

------------------------------------------------------------------------
-- Properties of states

opaque

  -- Injectivity of states

  State-injectivity :
    {H : Heap _ _} →
    ⟨ H , t , ρ , S ⟩ ≡ ⟨ H′ , t′ , ρ′ , S′ ⟩ →
    H ≡ H′ × t ≡ t′ × ρ ≡ ρ′ × S ≡ S′
  State-injectivity refl = refl , refl , refl , refl

------------------------------------------------------------------------
-- Properties of values

opaque

  -- Values applied to weakenings are values

  wkValue : (ρ : Wk m n) → Value t → Value (wk ρ t)
  wkValue ρ lamᵥ = lamᵥ
  wkValue ρ zeroᵥ = zeroᵥ
  wkValue ρ sucᵥ = sucᵥ
  wkValue ρ starᵥ = starᵥ
  wkValue ρ prodᵥ = prodᵥ
  wkValue ρ rflᵥ = rflᵥ
  wkValue ρ Uᵥ = Uᵥ
  wkValue ρ ΠΣᵥ = ΠΣᵥ
  wkValue ρ ℕᵥ = ℕᵥ
  wkValue ρ Unitᵥ = Unitᵥ
  wkValue ρ Emptyᵥ = Emptyᵥ
  wkValue ρ Idᵥ = Idᵥ
  wkValue ρ (unitrec-ηᵥ η) = unitrec-ηᵥ η

opaque

  -- Values applied to substitutions are values

  substValue : (σ : Subst m n) → Value t → Value (t [ σ ])
  substValue σ lamᵥ = lamᵥ
  substValue σ zeroᵥ = zeroᵥ
  substValue σ sucᵥ = sucᵥ
  substValue σ starᵥ = starᵥ
  substValue σ prodᵥ = prodᵥ
  substValue σ rflᵥ = rflᵥ
  substValue σ Uᵥ = Uᵥ
  substValue σ ΠΣᵥ = ΠΣᵥ
  substValue σ ℕᵥ = ℕᵥ
  substValue σ Unitᵥ = Unitᵥ
  substValue σ Emptyᵥ = Emptyᵥ
  substValue σ Idᵥ = Idᵥ
  substValue ρ (unitrec-ηᵥ η) = unitrec-ηᵥ η

opaque

  -- Values are non-neutrals

  Value→¬Neutral : Value t → ¬ Neutral⁺ ∇ t
  Value→¬Neutral lamᵥ ()
  Value→¬Neutral zeroᵥ ()
  Value→¬Neutral sucᵥ ()
  Value→¬Neutral starᵥ ()
  Value→¬Neutral prodᵥ ()
  Value→¬Neutral rflᵥ ()
  Value→¬Neutral Uᵥ ()
  Value→¬Neutral ΠΣᵥ ()
  Value→¬Neutral ℕᵥ ()
  Value→¬Neutral Unitᵥ ()
  Value→¬Neutral Emptyᵥ ()
  Value→¬Neutral Idᵥ ()
  Value→¬Neutral (unitrec-ηᵥ η) (unitrecₙ no-η _) = no-η η

opaque

  -- If t is a value, then either t is in WHNF, or t is an application
  -- of unitrec and η-equality is allowed for weak unit types.

  Value→Whnf :
    Value t →
    Whnf ∇ t ⊎ ∃₆ λ l p q A u v → t ≡ unitrec l p q A u v × Unitʷ-η
  Value→Whnf lamᵥ = inj₁ lamₙ
  Value→Whnf zeroᵥ = inj₁ zeroₙ
  Value→Whnf sucᵥ = inj₁ sucₙ
  Value→Whnf starᵥ = inj₁ starₙ
  Value→Whnf prodᵥ = inj₁ prodₙ
  Value→Whnf rflᵥ = inj₁ rflₙ
  Value→Whnf Uᵥ = inj₁ Uₙ
  Value→Whnf ΠΣᵥ = inj₁ ΠΣₙ
  Value→Whnf ℕᵥ = inj₁ ℕₙ
  Value→Whnf Unitᵥ = inj₁ Unitₙ
  Value→Whnf Emptyᵥ = inj₁ Emptyₙ
  Value→Whnf Idᵥ = inj₁ Idₙ
  Value→Whnf (unitrec-ηᵥ x) = inj₂ (_ , _ , _ , _ , _ , _ , refl , x)

------------------------------------------------------------------------
-- Properties of the lookup relations

opaque

  -- Variable lookup with heap update is deterministic.

  lookup-det : {H : Heap k m} {t : Term n} {u : Term n′}
             → H ⊢ y ↦[ r ] t , ρ ⨾ H′
             → H ⊢ y ↦[ r ] u , ρ′ ⨾ H″
             → Σ (n ≡ n′) λ p → subst Term p t ≡ u
               × subst (Wk m) p ρ ≡ ρ′ × H′ ≡ H″
  lookup-det (here p-𝟙≡q) (here p-𝟙≡q′) =
    case -≡-functional p-𝟙≡q p-𝟙≡q′ of λ {
      refl →
    refl , refl , refl , refl }
  lookup-det (there x) (there y) =
    case lookup-det x y of λ {
      (refl , refl , refl , refl) →
    refl , refl , refl , refl }
  lookup-det (there● x) (there● y) =
    case lookup-det x y of λ {
      (refl , refl , refl , refl) →
    refl , refl , refl , refl}

opaque

  -- Variable lookup without heap update is deterministic.

  lookup-det′ : {H : Heap k m} {t : Term n} {u : Term n′}
             → H ⊢ y ↦ (t , ρ)
             → H ⊢ y ↦ (u , ρ′)
             → Σ (n ≡ n′) λ p → subst Term p t ≡ u × subst (Wk m) p ρ ≡ ρ′
  lookup-det′ here here = refl , refl , refl
  lookup-det′ (there d) (there d′) =
    case lookup-det′ d d′ of λ {
      (refl , refl , refl) →
    refl , refl , refl }
  lookup-det′ (there● d) (there● d′) =
    case lookup-det′ d d′ of λ {
      (refl , refl , refl) →
    refl , refl , refl }

opaque

  -- Lookup will either yield an entry or a dummy entry

  ↦⊎↦● : ∀ y → (∃₂ λ n (c : Entry _ n) → H ⊢ y ↦ c) ⊎ H ⊢ y ↦●
  ↦⊎↦● {H = ε} ()
  ↦⊎↦● {H = H ∙ c} y0 = inj₁ (_ , _ , here)
  ↦⊎↦● {H = H ∙●} y0 = inj₂ here
  ↦⊎↦● {H = H ∙ c} (y +1) =
    case ↦⊎↦● y of λ where
      (inj₁ (_ , _ , d)) → inj₁ (_ , _ , there d)
      (inj₂ d) → inj₂ (there d)
  ↦⊎↦● {H = H ∙●} (y +1) =
    case ↦⊎↦● y of λ where
      (inj₁ (_ , _ , d)) → inj₁ (_ , _ , there● d)
      (inj₂ d) → inj₂ (there● d)

opaque

  -- Lookup cannot yield both an entry and a dummy entry.

  ¬↦∧↦● : H ⊢ y ↦ e → H ⊢ y ↦● → ⊥
  ¬↦∧↦● here ()
  ¬↦∧↦● (there d) (there d′) = ¬↦∧↦● d d′
  ¬↦∧↦● (there● d) (there● d′) = ¬↦∧↦● d d′

opaque

  -- If a heap does not contain erased entries then lookup to ● will
  -- always fail.

  ¬erased-heap→¬↦● : {H : Heap k _} → H ⊢ y ↦● → k ≡ 0 → ⊥
  ¬erased-heap→¬↦● here ()
  ¬erased-heap→¬↦● (there d) k≡0 = ¬erased-heap→¬↦● d k≡0
  ¬erased-heap→¬↦● (there● d) ()

opaque

  ¬erased-heap→↦ :
    {H : Heap k m} → k ≡ 0 → (y : Ptr m) →
    ∃₂ λ n (e : Entry m n) → H ⊢ y ↦ e
  ¬erased-heap→↦ k≡0 y =
    case ↦⊎↦● y of λ where
      (inj₁ x) → x
      (inj₂ x) → ⊥-elim (¬erased-heap→¬↦● x k≡0)

opaque

  -- If heap lookup with update succeeds lookup without heap update
  -- succeeds with the same result.

  ↦[]→↦ : H ⊢ y ↦[ q ] e ⨾ H′ → H ⊢ y ↦ e
  ↦[]→↦ (here x) = here
  ↦[]→↦ (there d) = there (↦[]→↦ d)
  ↦[]→↦ (there● d) = there● (↦[]→↦ d)

opaque

  -- Heap lookups match the corresponding substitution.

  heapSubstVar : H ⊢ y ↦[ q ] t , ρ ⨾ H′ → toSubstₕ H y ≡ wk ρ t [ H ]ₕ
  heapSubstVar {t} (here _) =
    sym (step-consSubst t)
  heapSubstVar {t} (there d) =
    trans (heapSubstVar d) (sym (step-consSubst t))
  heapSubstVar {H = H ∙●} {t} {ρ = step ρ} (there● d) =
    trans (cong wk1 (heapSubstVar d))
      (trans (sym (wk1-liftSubst (wk ρ t)))
        (cong (_[ H ]⇑ₕ) (wk1-wk ρ t)))

opaque

  -- Heap lookups match the corresponding substitution.

  heapSubstVar′ : H ⊢ y ↦ (t , ρ) → toSubstₕ H y ≡ wk ρ t [ H ]ₕ
  heapSubstVar′ {t} here =
    sym (step-consSubst t)
  heapSubstVar′ {t} (there d) =
    trans (heapSubstVar′ d) (sym (step-consSubst t))
  heapSubstVar′ {H = H ∙●} {t} {ρ = step ρ} (there● d) =
    trans (cong wk1 (heapSubstVar′ d))
      (trans (sym (wk1-liftSubst (wk ρ t)))
        (cong (_[ H ]⇑ₕ) (wk1-wk ρ t)))

opaque

  -- If subtraction of the grade correspoding to a heap entry cannot
  -- by subtracted by q then lookup of q copies fails.

  -≢-no-lookup :
    (∀ {r} → H ⟨ y ⟩ʰ - q ≡ r → ⊥) →
    H ⊢ y ↦[ q ] e ⨾ H′ → ⊥
  -≢-no-lookup p-q≢r (here p-q≡r) =
    p-q≢r p-q≡r
  -≢-no-lookup p-q≢r (there d) =
    -≢-no-lookup p-q≢r d
  -≢-no-lookup p-q≢r (there● d) =
    -≢-no-lookup p-q≢r d

------------------------------------------------------------------------
-- Properties of stacks and continuations

opaque

  -- Applying a single substitution to a term and then to a continuation

  ⦅⦆ᶜ-sgSubst : ∀ c → ⦅ c ⦆ᶜ (t [ u ]₀) ≡ ⦅ wk1ᶜ c ⦆ᶜ t [ u ]₀
  ⦅⦆ᶜ-sgSubst (∘ₑ p u ρ) =
    cong (_ ∘_) (sym (step-sgSubst _ _))
  ⦅⦆ᶜ-sgSubst (fstₑ p) = refl
  ⦅⦆ᶜ-sgSubst (sndₑ p) = refl
  ⦅⦆ᶜ-sgSubst {u = v} (prodrecₑ r p q A u ρ) =
    cong₂ (λ u A → prodrec r p q A _ u)
      (lifts-step-sgSubst 2 u)
      (lifts-step-sgSubst 1 A)
  ⦅⦆ᶜ-sgSubst {u} (natrecₑ p q r A z s ρ) =
    cong₃ (λ A z s → natrec p q r A z s _)
      (lifts-step-sgSubst 1 A)
      (lifts-step-sgSubst 0 z)
      (lifts-step-sgSubst 2 s)
  ⦅⦆ᶜ-sgSubst {u = v} (unitrecₑ _ p q A u ρ) =
    cong₂ (λ u A → unitrec _ p q A _ u)
      (sym (step-sgSubst _ _))
      (lifts-step-sgSubst 1 A)
  ⦅⦆ᶜ-sgSubst (emptyrecₑ p A ρ) =
    cong (λ A → emptyrec p A _)
      (lifts-step-sgSubst 0 A)
  ⦅⦆ᶜ-sgSubst (Jₑ p q A t B u v ρ) =
    sym (cong₅ (λ A t B u v → J p q A t B u v _)
      (step-sgSubst A _) (step-sgSubst t _)
      (sym (lifts-step-sgSubst 2 B))
      (step-sgSubst u _) (step-sgSubst v _))
  ⦅⦆ᶜ-sgSubst (Kₑ p A t B u ρ) =
    sym (cong₄ (λ A t B u → K p A t B u _)
      (step-sgSubst A _) (step-sgSubst t _)
      (sym (lifts-step-sgSubst 1 B))
      (step-sgSubst u _))
  ⦅⦆ᶜ-sgSubst ([]-congₑ s A t u ρ) =
    sym (cong₃ (λ A t u → []-cong s A t u _)
      (step-sgSubst A _) (step-sgSubst t _)
      (step-sgSubst u _))
  ⦅⦆ᶜ-sgSubst sucₑ = refl

opaque

  -- Applying a single substitution to a term and then to a stack

  ⦅⦆ˢ-sgSubst : ∀ S → ⦅ S ⦆ˢ (t [ u ]₀) ≡ ⦅ wk1ˢ S ⦆ˢ t [ u ]₀
  ⦅⦆ˢ-sgSubst ε = refl
  ⦅⦆ˢ-sgSubst {t} {u} (e ∙ S) = begin
   ⦅ e ∙ S ⦆ˢ (t [ u ]₀)              ≡⟨⟩
   ⦅ S ⦆ˢ (⦅ e ⦆ᶜ (t [ u ]₀))          ≡⟨ cong ⦅ S ⦆ˢ_ (⦅⦆ᶜ-sgSubst e) ⟩
   ⦅ S ⦆ˢ (⦅ wk1ᶜ e ⦆ᶜ t [ u ]₀)       ≡⟨ ⦅⦆ˢ-sgSubst S ⟩
   ⦅ wk1ˢ S ⦆ˢ (⦅ wk1ᶜ e ⦆ᶜ t) [ u ]₀  ≡⟨⟩
   ⦅ wk1ˢ (e ∙ S) ⦆ˢ t [ u ]₀         ∎

opaque

  -- Applying a double substitution to a term and then to a continuation

  ⦅⦆ᶜ-[,] : ∀ e → ⦅ e ⦆ᶜ (t [ u , v ]₁₀) ≡ ⦅ wk2ᶜ e ⦆ᶜ t [ u , v ]₁₀
  ⦅⦆ᶜ-[,] (∘ₑ p u ρ) =
    cong (_ ∘_) (lifts-step-[,] 0 u)
  ⦅⦆ᶜ-[,] (fstₑ x) = refl
  ⦅⦆ᶜ-[,] (sndₑ x) = refl
  ⦅⦆ᶜ-[,] (prodrecₑ r p q A u ρ) =
    cong₂ (λ x y → prodrec r p q x _ y)
      (lifts-step-[,] 1 A)
      (lifts-step-[,] 2 u)
  ⦅⦆ᶜ-[,] (natrecₑ p q r A z s ρ) =
    cong₃ (λ A z s → natrec p q r A z s _)
      (lifts-step-[,] 1 A)
      (lifts-step-[,] 0 z)
      (lifts-step-[,] 2 s)
  ⦅⦆ᶜ-[,] (unitrecₑ _ p q A u ρ) =
    cong₂ (λ x y → unitrec _ p q x _ y)
      (lifts-step-[,] 1 A) (lifts-step-[,] 0 u)
  ⦅⦆ᶜ-[,] (emptyrecₑ p A ρ) =
    cong (λ A → emptyrec p A _) (lifts-step-[,] 0 A)
  ⦅⦆ᶜ-[,] (Jₑ p q A t B u v ρ) =
    cong₅ (λ A t B u v → J p q A t B u v _)
      (lifts-step-[,] 0 A) (lifts-step-[,] 0 t)
      (lifts-step-[,] 2 B) (lifts-step-[,] 0 u)
      (lifts-step-[,] 0 v)
  ⦅⦆ᶜ-[,] (Kₑ p A t B u ρ) =
    cong₄ (λ A t B u → K p A t B u _)
      (lifts-step-[,] 0 A) (lifts-step-[,] 0 t)
      (lifts-step-[,] 1 B) (lifts-step-[,] 0 u)
  ⦅⦆ᶜ-[,] ([]-congₑ s A t u ρ) =
    cong₃ (λ A t u → []-cong s A t u _)
      (lifts-step-[,] 0 A) (lifts-step-[,] 0 t)
      (lifts-step-[,] 0 u)
  ⦅⦆ᶜ-[,] sucₑ = refl

opaque

  -- Applying a double substitution to a term and then to a stack

  ⦅⦆ˢ-[,] : ∀ S → ⦅ S ⦆ˢ (t [ u , v ]₁₀) ≡ ⦅ wk2ˢ S ⦆ˢ t [ u , v ]₁₀
  ⦅⦆ˢ-[,] ε = refl
  ⦅⦆ˢ-[,] {t} {u} {v} (e ∙ S) = begin
    ⦅ e ∙ S ⦆ˢ (t [ u , v ]₁₀)             ≡⟨⟩
    ⦅ S ⦆ˢ (⦅ e ⦆ᶜ (t [ u , v ]₁₀))         ≡⟨ cong ⦅ S ⦆ˢ_ (⦅⦆ᶜ-[,] e) ⟩
    ⦅ S ⦆ˢ (⦅ wk2ᶜ e ⦆ᶜ t [ u , v ]₁₀)      ≡⟨ ⦅⦆ˢ-[,] S ⟩
    ⦅ wk2ˢ S ⦆ˢ (⦅ wk2ᶜ e ⦆ᶜ t) [ u , v ]₁₀ ≡⟨⟩
    ⦅ wk2ˢ (e ∙ S) ⦆ˢ t [ u , v ]₁₀        ∎

opaque

  -- Weakening of a continuation applied to a Term

  wk-⦅⦆ᶜ : ∀ {ρ : Wk m n} e → wk ρ (⦅ e ⦆ᶜ t) ≡ ⦅ wkᶜ ρ e ⦆ᶜ (wk ρ t)
  wk-⦅⦆ᶜ {ρ} (∘ₑ p u ρ′) =
    cong (_ ∘_) (wk-comp ρ ρ′ u)
  wk-⦅⦆ᶜ (fstₑ p) = refl
  wk-⦅⦆ᶜ (sndₑ p) = refl
  wk-⦅⦆ᶜ {ρ} (prodrecₑ r p q A u ρ′) =
    cong₂ (λ A u → prodrec r p q A _ u)
      (wk-comp (lift ρ) (lift ρ′) A)
      (wk-comp (liftn ρ 2) (liftn ρ′ 2) u)
  wk-⦅⦆ᶜ {ρ} (natrecₑ p q r A z s ρ′) =
    cong₃ (λ A z s → natrec p q r A z s _)
      (wk-comp (lift ρ) (lift ρ′) A)
      (wk-comp ρ ρ′ z)
      (wk-comp (liftn ρ 2) (liftn ρ′ 2) s)
  wk-⦅⦆ᶜ {ρ} (unitrecₑ _ p q A u ρ′) =
    cong₂ (λ A u → unitrec _ p q A _ u)
      (wk-comp (lift ρ) (lift ρ′) A)
      (wk-comp ρ ρ′ u)
  wk-⦅⦆ᶜ {ρ} (emptyrecₑ p A ρ′) =
    cong (λ A → emptyrec p A _) (wk-comp ρ ρ′ A)
  wk-⦅⦆ᶜ {ρ} (Jₑ p q A t B u v ρ′) =
    cong₅ (λ A t B u v → J p q A t B u v _)
      (wk-comp ρ ρ′ A) (wk-comp ρ ρ′ t)
      (wk-comp (liftn ρ 2) (liftn ρ′ 2) B)
      (wk-comp ρ ρ′ u) (wk-comp ρ ρ′ v)
  wk-⦅⦆ᶜ {ρ} (Kₑ p A t B u ρ′) =
    cong₄ (λ A t B u → K p A t B u _)
      (wk-comp ρ ρ′ A) (wk-comp ρ ρ′ t)
      (wk-comp (lift ρ) (lift ρ′) B) (wk-comp ρ ρ′ u)
  wk-⦅⦆ᶜ {ρ} ([]-congₑ s A t u ρ′) =
    cong₃ (λ A t u → []-cong s A t u _)
      (wk-comp ρ ρ′ A) (wk-comp ρ ρ′ t)
      (wk-comp ρ ρ′ u)
  wk-⦅⦆ᶜ {ρ} sucₑ = refl

opaque

  -- A congruence property for continuations

  ⦅⦆ᶜ-cong : ∀ e → t [ σ ] ≡ u [ σ ]
         → ⦅ e ⦆ᶜ t [ σ ] ≡ ⦅ e ⦆ᶜ u [ σ ]
  ⦅⦆ᶜ-cong (∘ₑ p u ρ) t≡u =
    cong (_∘ _) t≡u
  ⦅⦆ᶜ-cong (fstₑ x) t≡u =
    cong (fst _) t≡u
  ⦅⦆ᶜ-cong (sndₑ x) t≡u =
    cong (snd _) t≡u
  ⦅⦆ᶜ-cong (prodrecₑ r p q A u ρ) t≡u =
    cong (λ t → prodrec _ _ _ _ t _) t≡u
  ⦅⦆ᶜ-cong (natrecₑ p q r A z s ρ) t≡u =
    cong (λ t → natrec _ _ _ _ _ _ t) t≡u
  ⦅⦆ᶜ-cong (unitrecₑ _ p q A u ρ) t≡u =
    cong (λ t → unitrec _ _ _ _ t _) t≡u
  ⦅⦆ᶜ-cong (emptyrecₑ p A ρ) t≡u =
    cong (emptyrec _ _) t≡u
  ⦅⦆ᶜ-cong (Jₑ p q A t B u v ρ) t≡u =
    cong (J _ _ _ _ _ _ _) t≡u
  ⦅⦆ᶜ-cong (Kₑ p A t B u ρ) t≡u =
    cong (K _ _ _ _ _) t≡u
  ⦅⦆ᶜ-cong ([]-congₑ s A t u ρ) t≡u =
    cong ([]-cong _ _ _ _) t≡u
  ⦅⦆ᶜ-cong sucₑ t≡u =
    cong suc t≡u

opaque

  -- A congruence property for stacks

  ⦅⦆ˢ-cong : ∀ S → t [ σ ] ≡ u [ σ ]
         → ⦅ S ⦆ˢ t [ σ ] ≡ ⦅ S ⦆ˢ u [ σ ]
  ⦅⦆ˢ-cong ε t≡u = t≡u
  ⦅⦆ˢ-cong (e ∙ S) t≡u = ⦅⦆ˢ-cong S (⦅⦆ᶜ-cong e t≡u)

opaque

  -- Weakening of sucₛ k

  wk-sucₛ : (ρ : Wk m n) (k : Nat) → wkˢ ρ (sucₛ k) ≡ sucₛ k
  wk-sucₛ ρ 0 = refl
  wk-sucₛ ρ (1+ k) = cong (sucₑ ∙_) (wk-sucₛ ρ k)

opaque

  -- The empty stack is a right identity for _++_

  ++-identityʳ : S ++ ε ≡ S
  ++-identityʳ {S = ε} = refl
  ++-identityʳ {S = c ∙ S} = cong (c ∙_) ++-identityʳ

opaque

  -- An inversion lemma for multiplicity of non-empty stacks

  ∣∣∙-inv : ∣ c ∙ S ∣≡ p → ∃₂ λ q r → ∣ c ∣ᶜ[ ⌞ r ⌟ ]≡ q × ∣ S ∣≡ r × p ≡ r · q
  ∣∣∙-inv (e ∙ S) = _ , _ , e , S , refl

opaque

  -- Continuation weakening preserves multiplicity

  wk-∣∣ᶜ : ∣ c ∣ᶜ[ mo ]≡ p → ∣ wkᶜ ρ c ∣ᶜ[ mo ]≡ p
  wk-∣∣ᶜ ∘ₑ = ∘ₑ
  wk-∣∣ᶜ fstₑ = fstₑ
  wk-∣∣ᶜ sndₑ = sndₑ
  wk-∣∣ᶜ (natrecₑ x) = natrecₑ x
  wk-∣∣ᶜ prodrecₑ = prodrecₑ
  wk-∣∣ᶜ unitrecₑ = unitrecₑ
  wk-∣∣ᶜ emptyrecₑ = emptyrecₑ
  wk-∣∣ᶜ (Jₑ x) = Jₑ x
  wk-∣∣ᶜ (Kₑ x) = Kₑ x
  wk-∣∣ᶜ []-congₑ = []-congₑ
  wk-∣∣ᶜ sucₑ = sucₑ

opaque

  -- Stack weakening preserves multiplicity

  wk-∣∣ : ∣ S ∣≡ p → ∣ wkˢ ρ S ∣≡ p
  wk-∣∣ ε = ε
  wk-∣∣ (e ∙ S) = wk-∣∣ᶜ e ∙ wk-∣∣ S

opaque

  -- The multiplicity relation for natrecₑ is functional

  ∣natrec∣ᶜ-functional :
    ∣natrec p , r ∣≡ q → ∣natrec p , r ∣≡ q′ → q ≡ q′
  ∣natrec∣ᶜ-functional
    (has-nrₑ ⦃ has-nr ⦄) (has-nrₑ ⦃ has-nr = has-nr′ ⦄) =
    case Nr-available-propositional _ has-nr has-nr′ of λ where
      refl → refl
  ∣natrec∣ᶜ-functional (has-nrₑ ⦃ has-nr ⦄) (no-nrₑ ⦃ no-nr ⦄ x) =
    ⊥-elim (¬[Nr∧No-nr-glb] _ has-nr no-nr)
  ∣natrec∣ᶜ-functional (no-nrₑ ⦃ no-nr ⦄ x) (has-nrₑ ⦃ has-nr ⦄) =
    ⊥-elim (¬[Nr∧No-nr-glb] _ has-nr no-nr)
  ∣natrec∣ᶜ-functional (no-nrₑ x) (no-nrₑ y) =
    GLB-unique x y

opaque

  -- The multiplicity relation for Jₑ is functional

  ∣J∣ᶜ-functional : ∣J em , p , q ∣≡ r → ∣J em , p , q ∣≡ r′ → r ≡ r′
  ∣J∣ᶜ-functional J-all J-all = refl
  ∣J∣ᶜ-functional (J-some₀ _ _) (J-some₀ _ _) = refl
  ∣J∣ᶜ-functional (J-some₀ p≡𝟘 q≡𝟘) (J-some false) =
    ⊥-elim (false (p≡𝟘 , q≡𝟘))
  ∣J∣ᶜ-functional (J-some false) (J-some₀ p≡𝟘 q≡𝟘) =
    ⊥-elim (false (p≡𝟘 , q≡𝟘))
  ∣J∣ᶜ-functional (J-some _) (J-some _) = refl
  ∣J∣ᶜ-functional J-none J-none = refl

opaque

  -- The multiplicity relation for Kₑ is functional

  ∣K∣ᶜ-functional : ∣K em , p ∣≡ r → ∣K em , p ∣≡ r′ → r ≡ r′
  ∣K∣ᶜ-functional K-all K-all = refl
  ∣K∣ᶜ-functional (K-some₀ _) (K-some₀ _) = refl
  ∣K∣ᶜ-functional (K-some₀ p≡𝟘) (K-some p≢𝟘) =
    ⊥-elim (p≢𝟘 p≡𝟘)
  ∣K∣ᶜ-functional (K-some p≢𝟘) (K-some₀ p≡𝟘) =
    ⊥-elim (p≢𝟘 p≡𝟘)
  ∣K∣ᶜ-functional (K-some _) (K-some _) = refl
  ∣K∣ᶜ-functional K-none K-none = refl

opaque

  -- The multiplicity relation for continuations is functional

  ∣∣ᶜ-functional : ∣ c ∣ᶜ[ mo ]≡ p → ∣ c ∣ᶜ[ mo ]≡ q → p ≡ q
  ∣∣ᶜ-functional ∘ₑ ∘ₑ = refl
  ∣∣ᶜ-functional fstₑ fstₑ = refl
  ∣∣ᶜ-functional sndₑ sndₑ = refl
  ∣∣ᶜ-functional prodrecₑ prodrecₑ = refl
  ∣∣ᶜ-functional (natrecₑ x) (natrecₑ y) =
    ∣natrec∣ᶜ-functional x y
  ∣∣ᶜ-functional unitrecₑ unitrecₑ = refl
  ∣∣ᶜ-functional emptyrecₑ emptyrecₑ = refl
  ∣∣ᶜ-functional (Jₑ x) (Jₑ y) = ∣J∣ᶜ-functional x y
  ∣∣ᶜ-functional (Kₑ x) (Kₑ y) = ∣K∣ᶜ-functional x y
  ∣∣ᶜ-functional []-congₑ []-congₑ = refl
  ∣∣ᶜ-functional sucₑ sucₑ = refl

opaque

  -- The multiplicity relation for stacks is functional

  ∣∣-functional : ∣ S ∣≡ p → ∣ S ∣≡ q → p ≡ q
  ∣∣-functional ε ε = refl
  ∣∣-functional (e ∙ S) (e′ ∙ S′) =
    let ∣S∣≡∣S∣′ = ∣∣-functional S S′
    in  ·-cong ∣S∣≡∣S∣′
         (∣∣ᶜ-functional e (subst (λ p → ∣ _ ∣ᶜ[ ⌞ p ⌟ ]≡ _) (sym ∣S∣≡∣S∣′) e′))

opaque

  -- The multiplicity for natrecₑ always exists if e is not natrecₑ when
  -- the usage rule with greatest lower bounds is used.

  ∣nr∣≡ : ⦃ has-nr : Nr-available ⦄ → ∃ λ q → ∣natrec p , r ∣≡ q
  ∣nr∣≡ = _ , has-nrₑ

opaque

  -- The multiplicity relation for Jₑ is always inhabited

  ∣J∣≡ : ∃ λ r → ∣J em , p , q ∣≡ r
  ∣J∣≡ {em = none} = _ , J-none
  ∣J∣≡ {em = all} = _ , J-all
  ∣J∣≡ {em = some} {p} {q} =
    case is-𝟘? p of λ where
      (yes p≡𝟘) →
        case is-𝟘? q of λ where
          (yes q≡𝟘) → _ , J-some₀ p≡𝟘 q≡𝟘
          (no q≢𝟘) → _ , J-some λ (_ , q≡𝟘) → q≢𝟘 q≡𝟘
      (no p≢𝟘) → _ , J-some (λ (p≡𝟘 , _) → p≢𝟘 p≡𝟘)

opaque

  -- The multiplicity relation for Kₑ is always inhabited

  ∣K∣≡ : ∃ λ r → ∣K em , p ∣≡ r
  ∣K∣≡ {em = none} = _ , K-none
  ∣K∣≡ {em = all} = _ , K-all
  ∣K∣≡ {em = some} {p} =
    case is-𝟘? p of λ where
      (yes p≡𝟘) → _ , K-some₀ p≡𝟘
      (no p≢𝟘) → _ , K-some p≢𝟘

opaque

  -- The multiplicity for a continuation c always exists if when c is
  -- natrecₑ then the usage rule for natrec using an nr function is used.

  ∣∣ᶜ≡ :
    (∀ {n p q r A u v ρ} → c ≡ natrecₑ {n = n} p q r A u v ρ → Nr-available) →
    ∃ ∣ c ∣ᶜ[ mo ]≡_
  ∣∣ᶜ≡ {c = ∘ₑ p u ρ} _ = 𝟙 , ∘ₑ
  ∣∣ᶜ≡ {c = fstₑ x} _ = 𝟙 , fstₑ
  ∣∣ᶜ≡ {c = sndₑ x} _ = 𝟙 , sndₑ
  ∣∣ᶜ≡ {c = prodrecₑ r p q A u ρ} _ = r , prodrecₑ
  ∣∣ᶜ≡ {c = natrecₑ p q r A z s ρ} has-nr =
    _ , natrecₑ (∣nr∣≡ ⦃ has-nr refl ⦄ .proj₂)
  ∣∣ᶜ≡ {c = unitrecₑ l p q A u ρ} _ = p , unitrecₑ
  ∣∣ᶜ≡ {c = emptyrecₑ p A ρ} _ = p , emptyrecₑ
  ∣∣ᶜ≡ {c = Jₑ p q A t B u v ρ} _ = _ , Jₑ (∣J∣≡ .proj₂)
  ∣∣ᶜ≡ {c = Kₑ p A t B u ρ} _ = _ , Kₑ (∣K∣≡ .proj₂)
  ∣∣ᶜ≡ {c = []-congₑ s A t u ρ} _ = 𝟘 , []-congₑ
  ∣∣ᶜ≡ {c = sucₑ} _ = 𝟙 , sucₑ

opaque

  -- The multiplicity relation for stacks is always inhabited is whenever
  -- the stack contains natrecₑ the usage rule for natrec using nr
  -- functions is used.

  ∣∣≡ : (∀ {p r} → natrec p , r ∈ S → Nr-available) → ∃ ∣ S ∣≡_
  ∣∣≡ {S = ε} _ = ∣ε∣ , ε
  ∣∣≡ {S = e ∙ S} has-nr =
    let _ , ∣S∣≡ = ∣∣≡ (has-nr ∘→ there)
        _ , ∣e∣≡ = ∣∣ᶜ≡ λ { refl → has-nr here}
    in  _ , ∣e∣≡ ∙ ∣S∣≡

opaque

  -- A variant of the above for it assumed that the stack does not
  -- contain any occurences of natrecₑ.

  nr∉-∣∣≡ : (∀ {p r} → ¬ natrec p , r ∈ S) → ∃ ∣ S ∣≡_
  nr∉-∣∣≡ nr∉ = ∣∣≡ (λ nr∈ → ⊥-elim (nr∉ nr∈))

opaque

  -- An inequality satisfied by the multiplicity of natrecₑ

  ∣natrec∣≤ : ∣natrec p , r ∣≡ q → q ≤ p + r · q
  ∣natrec∣≤ has-nrₑ = nr₂≤
  ∣natrec∣≤ (no-nrₑ x) = nrᵢ-GLB-≤ x

opaque

  -- Under some conditions, the multiplicity of Jₑ is ω

  ∣J∣≡ω :
    em ≤ᵉᵐ some → (em ≡ some → ¬ (p ≡ 𝟘 × q ≡ 𝟘)) →
    ∣J em , p , q ∣≡ ω
  ∣J∣≡ω {(none)} _ _ = J-none
  ∣J∣≡ω {(all)} () _
  ∣J∣≡ω {(some)} _ ≢𝟘 = J-some (≢𝟘 refl)

opaque

  -- Under some conditions, the multiplicity of Kₑ is ω

  ∣K∣≡ω :
    em ≤ᵉᵐ some → (em ≡ some → p ≢ 𝟘) →
    ∣K em , p ∣≡ ω
  ∣K∣≡ω {(none)} _ _ = K-none
  ∣K∣≡ω {(all)} () _
  ∣K∣≡ω {(some)} _ ≢𝟘 = K-some (≢𝟘 refl)

opaque

  -- The multiplicity of Kₑ is either 𝟘 or ω

  ∣K∣≡𝟘⊎ω : ∣K em , p ∣≡ q → q ≡ 𝟘 ⊎ q ≡ ω
  ∣K∣≡𝟘⊎ω K-all = inj₁ refl
  ∣K∣≡𝟘⊎ω (K-some₀ x) = inj₁ refl
  ∣K∣≡𝟘⊎ω (K-some x) = inj₂ refl
  ∣K∣≡𝟘⊎ω K-none = inj₂ refl

opaque

  -- The multiplicity of Jₑ is either 𝟘 or ω

  ∣J∣≡𝟘⊎ω : ∣J em , p , q ∣≡ r → r ≡ 𝟘 ⊎ r ≡ ω
  ∣J∣≡𝟘⊎ω J-all = inj₁ refl
  ∣J∣≡𝟘⊎ω (J-some₀ x x₁) = inj₁ refl
  ∣J∣≡𝟘⊎ω (J-some x) = inj₂ refl
  ∣J∣≡𝟘⊎ω J-none = inj₂ refl

opaque

  -- The multiplicity of Jₑ respects _≤ᵉᵐ_

  ∣J∣-≤ᵉᵐ : em ≤ᵉᵐ em′ → ∣J em , p , q ∣≡ r → ∣J em′ , p , q ∣≡ r′ → r ≤ r′
  ∣J∣-≤ᵉᵐ _ J-all J-all = ≤-refl
  ∣J∣-≤ᵉᵐ _ J-all (J-some₀ _ _) = ≤-refl
  ∣J∣-≤ᵉᵐ () J-all (J-some _)
  ∣J∣-≤ᵉᵐ () J-all J-none
  ∣J∣-≤ᵉᵐ _ (J-some₀ x₁ x₂) J-all = ≤-refl
  ∣J∣-≤ᵉᵐ _ (J-some₀ x₁ x₂) (J-some₀ x₃ x₄) = ≤-refl
  ∣J∣-≤ᵉᵐ _ (J-some₀ p≡𝟘 q≡𝟘) (J-some pq≢𝟘) = ⊥-elim (pq≢𝟘 (p≡𝟘 , q≡𝟘))
  ∣J∣-≤ᵉᵐ () (J-some₀ _ _) J-none
  ∣J∣-≤ᵉᵐ _ (J-some _) ∣J∣≡r =
    case ∣J∣≡𝟘⊎ω ∣J∣≡r of λ where
      (inj₁ refl) → ω≤𝟘
      (inj₂ refl) → ≤-refl
  ∣J∣-≤ᵉᵐ _ J-none ∣J∣≡r =
    case ∣J∣≡𝟘⊎ω ∣J∣≡r of λ where
      (inj₁ refl) → ω≤𝟘
      (inj₂ refl) → ≤-refl

opaque

  -- The multiplicity of Kₑ respects _≤ᵉᵐ_

  ∣K∣-≤ᵉᵐ : em ≤ᵉᵐ em′ → ∣K em , p ∣≡ q → ∣K em′ , p ∣≡ r → q ≤ r
  ∣K∣-≤ᵉᵐ _ K-all K-all = ≤-refl
  ∣K∣-≤ᵉᵐ _ K-all (K-some₀ _) = ≤-refl
  ∣K∣-≤ᵉᵐ () K-all (K-some _)
  ∣K∣-≤ᵉᵐ () K-all K-none
  ∣K∣-≤ᵉᵐ _ (K-some₀ _) K-all = ≤-refl
  ∣K∣-≤ᵉᵐ _ (K-some₀ _) (K-some₀ _) = ≤-refl
  ∣K∣-≤ᵉᵐ _ (K-some₀ p≡𝟘) (K-some p≢𝟘) = ⊥-elim (p≢𝟘 p≡𝟘)
  ∣K∣-≤ᵉᵐ () (K-some₀ _) K-none
  ∣K∣-≤ᵉᵐ _ (K-some _) ∣K∣≡r =
    case ∣K∣≡𝟘⊎ω ∣K∣≡r of λ where
      (inj₁ refl) → ω≤𝟘
      (inj₂ refl) → ≤-refl
  ∣K∣-≤ᵉᵐ _ K-none ∣K∣≡r =
    case ∣K∣≡𝟘⊎ω ∣K∣≡r of λ where
      (inj₁ refl) → ω≤𝟘
      (inj₂ refl) → ≤-refl

opaque

  -- The multiplicity of Jₑ respects _≤ᵐ_

  ∣J∣-≤ᵐ :
    mo ≤ᵐ mo′ →
    ∣J erased-matches-for-J mo , p , q ∣≡ r →
    ∣J erased-matches-for-J mo′ , p , q ∣≡ r′ →
    r ≤ r′
  ∣J∣-≤ᵐ m≤m′ = ∣J∣-≤ᵉᵐ (erased-matches-for-J-≤ᵉᵐ m≤m′)

opaque

  -- The multiplicity of Kₑ respects _≤ᵐ_

  ∣K∣-≤ᵐ :
    mo ≤ᵐ mo′ →
    ∣K erased-matches-for-K mo , p ∣≡ r →
    ∣K erased-matches-for-K mo′ , p ∣≡ r′ →
    r ≤ r′
  ∣K∣-≤ᵐ m≤m′ = ∣K∣-≤ᵉᵐ (erased-matches-for-K-≤ᵉᵐ m≤m′)

opaque

  -- The mupltiplicity of the stack sucₛ k is ∣ε∣.

  ∣sucₛ∣≡∣ε∣ : ∀ k → ∣ sucₛ {m} k ∣≡ ∣ε∣
  ∣sucₛ∣≡∣ε∣ 0 = ε
  ∣sucₛ∣≡∣ε∣ (1+ k) =
    subst (∣ _ ∙ sucₛ k ∣≡_) (·-identityʳ _) (sucₑ ∙ ∣sucₛ∣≡∣ε∣ k)


opaque

  ∣S++sucₛ∣≡∣S∣ : ∣ S ∣≡ p → ∣ S ++ sucₛ k ∣≡ p
  ∣S++sucₛ∣≡∣S∣ ε = ∣sucₛ∣≡∣ε∣ _
  ∣S++sucₛ∣≡∣S∣ (e ∙ S) = e ∙ ∣S++sucₛ∣≡∣S∣ S

opaque

  -- If an erased prodrec token is on the stack then the stack
  -- multiplicity is zero (if it exists).

  pr₀∈→∣S∣≡𝟘 : ∣ S ∣≡ q → prodrec 𝟘 , p ∈ S → q ≡ 𝟘
  pr₀∈→∣S∣≡𝟘 ε ()
  pr₀∈→∣S∣≡𝟘 (prodrecₑ ∙ ∣S∣≡) here = ·-zeroʳ _
  pr₀∈→∣S∣≡𝟘 (_ ∙ ∣S∣≡) (there x) =
    trans (·-congʳ (pr₀∈→∣S∣≡𝟘 ∣S∣≡ x)) (·-zeroˡ _)

opaque

  -- If an erased unitrec token is on the stack then the stack
  -- multiplicity is zero (if it exists).

  ur₀∈→∣S∣≡𝟘 : ∣ S ∣≡ q → unitrec 𝟘 ∈ S → q ≡ 𝟘
  ur₀∈→∣S∣≡𝟘 ε ()
  ur₀∈→∣S∣≡𝟘 (unitrecₑ ∙ ∣S∣≡) here = ·-zeroʳ _
  ur₀∈→∣S∣≡𝟘 (_ ∙ ∣S∣≡) (there x) =
    trans (·-congʳ (ur₀∈→∣S∣≡𝟘 ∣S∣≡ x)) (·-zeroˡ _)

opaque

  -- If an erased emptyrec token is on the stack then the stack
  -- multiplicity is zero (if it exists).

  er₀∈→∣S∣≡𝟘 : ∣ S ∣≡ q → emptyrec 𝟘 ∈ S → q ≡ 𝟘
  er₀∈→∣S∣≡𝟘 ε ()
  er₀∈→∣S∣≡𝟘 (emptyrecₑ ∙ ∣S∣≡) here = ·-zeroʳ _
  er₀∈→∣S∣≡𝟘 (_ ∙ ∣S∣≡) (there x) =
    trans (·-congʳ (er₀∈→∣S∣≡𝟘 ∣S∣≡ x)) (·-zeroˡ _)

opaque

  -- Under some conditions, the stack multiplicity is 𝟘 (if it exists).

  ∣∣≡𝟘 :
    ∣ S ∣≡ q → prodrec 𝟘 , p ∈ S ⊎ (unitrec 𝟘 ∈ S) ⊎ (emptyrec 𝟘 ∈ S) →
    q ≡ 𝟘
  ∣∣≡𝟘 ∣S∣≡ (inj₁ pr₀∈) = pr₀∈→∣S∣≡𝟘 ∣S∣≡ pr₀∈
  ∣∣≡𝟘 ∣S∣≡ (inj₂ (inj₁ ur₀∈)) = ur₀∈→∣S∣≡𝟘 ∣S∣≡ ur₀∈
  ∣∣≡𝟘 ∣S∣≡ (inj₂ (inj₂ er₀∈)) = er₀∈→∣S∣≡𝟘 ∣S∣≡ er₀∈

opaque

  -- Under some conditions, the stack multiplicity is 𝟘.

  nr∉→∣∣≡𝟘 :
    (∀ {p r} → natrec p , r ∈ S → ⊥) →
    prodrec 𝟘 , p ∈ S ⊎ (unitrec 𝟘 ∈ S) ⊎ (emptyrec 𝟘 ∈ S) → ∣ S ∣≡ 𝟘
  nr∉→∣∣≡𝟘 nr∉ assumption =
    let _ , ∣S∣≡ = nr∉-∣∣≡ nr∉
    in  subst (∣ _ ∣≡_) (∣∣≡𝟘 ∣S∣≡ assumption) ∣S∣≡

opaque

  -- The multiplicity of natrecₑ is not 𝟘.

  ∣nr∣≢𝟘 :
   ⦃ Has-well-behaved-zero _ 𝕄 ⦄ →
   ∣natrec p , r ∣≡ q → q ≢ 𝟘
  ∣nr∣≢𝟘 has-nrₑ = nr₂≢𝟘
  ∣nr∣≢𝟘 (no-nrₑ x) refl = 𝟘≰𝟙 (x .proj₁ 0)

opaque

  -- If the stack multiplicity is 𝟘 then the stack contains an erased
  -- prodrec, unitrec or emptyrec or J, K or []-cong.

  ∣∣≡𝟘→erased-match :
    ⦃ Has-well-behaved-zero _ 𝕄 ⦄ →
    ∣ε∣ ≢ 𝟘 →
    ∣ S ∣≡ 𝟘 →
    (∃ λ p → prodrec 𝟘 , p ∈ S) ⊎ (unitrec 𝟘 ∈ S) ⊎ (emptyrec 𝟘 ∈ S) ⊎
    (∃₂ λ p q → J p , q ∈ S) ⊎ (∃ λ p → K p ∈ S) ⊎ ([]-cong∈ S)
  ∣∣≡𝟘→erased-match ∣ε∣≢𝟘 = lemma refl
    where
    there′ :
      (∃ λ p → prodrec 𝟘 , p ∈ S) ⊎ (unitrec 𝟘 ∈ S) ⊎ (emptyrec 𝟘 ∈ S) ⊎
      (∃₂ λ p q → J p , q ∈ S) ⊎ (∃ λ p → K p ∈ S) ⊎ ([]-cong∈ S) →
      (∃ λ p → prodrec 𝟘 , p ∈ (c ∙ S)) ⊎ (unitrec 𝟘 ∈ c ∙ S) ⊎ (emptyrec 𝟘 ∈ c ∙ S) ⊎
      (∃₂ λ p q → J p , q ∈ c ∙ S) ⊎ (∃ λ p → K p ∈ c ∙ S) ⊎ ([]-cong∈ c ∙ S)
    there′ (inj₁ (_ , x)) = inj₁ (_ , there x)
    there′ (inj₂ (inj₁ x)) = inj₂ (inj₁ (there x))
    there′ (inj₂ (inj₂ (inj₁ x))) = inj₂ (inj₂ (inj₁ (there x)))
    there′ (inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , x))))) = inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , there x))))
    there′ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , x)))))) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , there x)))))
    there′ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x))))) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (there x)))))
    here′ :
      q ≡ 𝟘 → ∣ c ∣ᶜ[ mo ]≡ q →
      (∃ λ p → prodrec 𝟘 , p ∈ (c ∙ S)) ⊎ (unitrec 𝟘 ∈ c ∙ S) ⊎ (emptyrec 𝟘 ∈ c ∙ S) ⊎
      (∃₂ λ p q → J p , q ∈ c ∙ S) ⊎ (∃ λ p → K p ∈ c ∙ S) ⊎ ([]-cong∈ c ∙ S)
    here′ q≡ ∘ₑ = ⊥-elim (non-trivial q≡)
    here′ q≡ fstₑ = ⊥-elim (non-trivial q≡)
    here′ q≡ sndₑ = ⊥-elim (non-trivial q≡)
    here′ refl prodrecₑ = inj₁ (_ , here)
    here′ q≡ (natrecₑ x) = ⊥-elim (∣nr∣≢𝟘 x q≡)
    here′ refl unitrecₑ = inj₂ (inj₁ here)
    here′ refl emptyrecₑ = inj₂ (inj₂ (inj₁ here))
    here′ q≡ (Jₑ x) = inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , here))))
    here′ q≡ (Kₑ x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , here)))))
    here′ q≡ []-congₑ = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ here))))
    here′ q≡ sucₑ = ⊥-elim (non-trivial q≡)
    lemma :
      q ≡ 𝟘 → ∣ S ∣≡ q →
      (∃ λ p → prodrec 𝟘 , p ∈ S) ⊎ (unitrec 𝟘 ∈ S) ⊎ (emptyrec 𝟘 ∈ S) ⊎
      (∃₂ λ p q → J p , q ∈ S) ⊎ (∃ λ p → K p ∈ S) ⊎ ([]-cong∈ S)
    lemma q≡ ε = ⊥-elim (∣ε∣≢𝟘 q≡)
    lemma q≡ (∣e∣≡ ∙ ∣S∣≡) =
      case zero-product q≡ of λ where
        (inj₁ x) → there′ (lemma x ∣S∣≡)
        (inj₂ x) → here′ x ∣e∣≡

opaque

  -- If a certain greatest lower bound does not exist then the stack
  -- multiplicity does not necessarily exist.

  ∣∣≢ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    ¬ (∃ λ q → Greatest-lower-bound q (nrᵢ r 𝟙 p)) →
    ∃ λ (S : Stack m) → ∀ q → ∣ S ∣≡ q → ⊥
  ∣∣≢ {r} {p} ⦃ no-nr ⦄ ¬glb =
    (natrecₑ p 𝟘 r ℕ zero zero id ∙ ε) ,
    λ { _ (natrecₑ (has-nrₑ ⦃ has-nr ⦄) ∙ _) → ¬[Nr∧No-nr-glb] _ has-nr no-nr
      ; _ (natrecₑ (no-nrₑ x) ∙ _) → ¬glb (_ , x)}

opaque

  -- Stack concatenation

  ⦅⦆ˢ++ : ∀ S S′ → ⦅ S ++ S′ ⦆ˢ t ≡ ⦅ S′ ⦆ˢ (⦅ S ⦆ˢ t)
  ⦅⦆ˢ++ ε S′ = refl
  ⦅⦆ˢ++ (c ∙ S) S′ = ⦅⦆ˢ++ S S′

opaque

  -- Weakening of stack concatenation

  wk-++ : (ρ : Wk m n) (S : Stack n) → wkˢ ρ (S ++ S′) ≡ wkˢ ρ S ++ wkˢ ρ S′
  wk-++ ρ ε = refl
  wk-++ ρ (c ∙ S) = cong (_ ∙_) (wk-++ ρ S)

opaque

  -- A specialized version of the property above

  wk-++sucₛ : (ρ : Wk m n) (S : Stack n) → wkˢ ρ (S ++ sucₛ k) ≡ wkˢ ρ S ++ sucₛ k
  wk-++sucₛ {k} ρ S = trans (wk-++ ρ S) (cong (_ ++_) (wk-sucₛ ρ k))

opaque

  -- Concatenation of sucₛ k

  sucₛ++sucₛ : ∀ k k′ → sucₛ {m} k ++ sucₛ k′ ≡ sucₛ (k +ⁿ k′)
  sucₛ++sucₛ 0 k′ = refl
  sucₛ++sucₛ (1+ k) k′ = cong (sucₑ ∙_) (sucₛ++sucₛ k k′)

opaque

  -- Applying a term to a continuation becomes neutral only if the
  -- term is neutral.

  ⦅⦆ᶜ-neutral : ∀ c → Neutral V ∇ (⦅ c ⦆ᶜ t) → Neutral V ∇ t
  ⦅⦆ᶜ-neutral (∘ₑ p u ρ) (∘ₙ n) = n
  ⦅⦆ᶜ-neutral (fstₑ x) (fstₙ n) = n
  ⦅⦆ᶜ-neutral (sndₑ x) (sndₙ n) = n
  ⦅⦆ᶜ-neutral (prodrecₑ r p q A u ρ) (prodrecₙ n) = n
  ⦅⦆ᶜ-neutral (natrecₑ p q r A z s ρ) (natrecₙ n) = n
  ⦅⦆ᶜ-neutral (unitrecₑ l p q A u ρ) (unitrecₙ x n) = n
  ⦅⦆ᶜ-neutral (emptyrecₑ p A ρ) (emptyrecₙ n) = n
  ⦅⦆ᶜ-neutral (Jₑ p q A t B u v ρ) (Jₙ n) = n
  ⦅⦆ᶜ-neutral (Kₑ p A t B u ρ) (Kₙ n) = n
  ⦅⦆ᶜ-neutral ([]-congₑ s A t u ρ) ([]-congₙ n) = n
  ⦅⦆ᶜ-neutral sucₑ ()

opaque

  -- Injectivity of stacks

  stack-injective : {c : Cont m} {S : Stack m}
                  → c ∙ S ≡ c′ ∙ S′ → c ≡ c′ × S ≡ S′
  stack-injective refl = refl , refl

opaque

  -- Injectivity of the stack sucₛ k

  sucₛ-injective : sucₛ {m} n ≡ sucₛ n′ → n ≡ n′
  sucₛ-injective {n = 0}    {n′ = 0}    _ = refl
  sucₛ-injective {n = 1+ _} {n′ = 1+ _} x =
    cong 1+ (sucₛ-injective (stack-injective x .proj₂))
  sucₛ-injective {n = 0}    {n′ = 1+ _} ()
  sucₛ-injective {n = 1+ _} {n′ = 0}    ()

------------------------------------------------------------------------
-- Properties of heap equality

opaque

  -- Heap equality is reflective

  ~ʰ-refl : H ~ʰ H
  ~ʰ-refl {H = ε} = ε
  ~ʰ-refl {H = H ∙ c} = ~ʰ-refl ∙ _
  ~ʰ-refl {H = H ∙●} = ~ʰ-refl ∙●

opaque

  -- Heap equality is symmetric

  ~ʰ-sym : H ~ʰ H′ → H′ ~ʰ H
  ~ʰ-sym ε = ε
  ~ʰ-sym (H~H′ ∙ c) = ~ʰ-sym H~H′ ∙ c
  ~ʰ-sym (H~H′ ∙●) = ~ʰ-sym H~H′ ∙●

opaque

  -- Heap equality is transitive

  ~ʰ-trans : H ~ʰ H′ → H′ ~ʰ H″ → H ~ʰ H″
  ~ʰ-trans ε ε = ε
  ~ʰ-trans (H~H′ ∙ c) (H′~H″ ∙ .c) = ~ʰ-trans H~H′ H′~H″ ∙ c
  ~ʰ-trans (H~H′ ∙●) (H′~H″ ∙●) = ~ʰ-trans H~H′ H′~H″ ∙●

opaque

  -- Heap lookup without update behaves the same on equal heaps

  ~ʰ-lookup : H ~ʰ H′ → H ⊢ y ↦ e → H′ ⊢ y ↦ e
  ~ʰ-lookup ε ()
  ~ʰ-lookup (H~H′ ∙ _) here = here
  ~ʰ-lookup (H~H′ ∙ _) (there d) = there (~ʰ-lookup H~H′ d)
  ~ʰ-lookup (H~H′ ∙●) (there● d) = there● (~ʰ-lookup H~H′ d)

opaque

  -- Heap lookup to ● behaves the same on equal heaps

  ~ʰ-lookup● : H ~ʰ H′ → H ⊢ y ↦● → H′ ⊢ y ↦●
  ~ʰ-lookup● ε ()
  ~ʰ-lookup● (H~H′ ∙●) here = here
  ~ʰ-lookup● (H~H′ ∙ _) (there d) = there (~ʰ-lookup● H~H′ d)
  ~ʰ-lookup● (H~H′ ∙●) (there● d) = there● (~ʰ-lookup● H~H′ d)

opaque

  -- Equal heaps are equal as substitutions

  ~ʰ-subst : H ~ʰ H′ → toSubstₕ H ≡ toSubstₕ H′
  ~ʰ-subst ε = refl
  ~ʰ-subst (H~H′ ∙ (t , ρ)) =
    case ~ʰ-subst H~H′ of λ
      H≡H′ →
    cong₂ consSubst H≡H′ (cong (wk ρ t [_]) H≡H′)
  ~ʰ-subst (H~H′ ∙●) =
    cong liftSubst (~ʰ-subst H~H′)

opaque

  -- An updated heap is equal to the original one (up to grades)

  update-~ʰ : H ⊢ y ↦[ q ] e ⨾ H′ → H ~ʰ H′
  update-~ʰ (here _) = ~ʰ-refl ∙ _
  update-~ʰ (there d) = update-~ʰ d ∙ _
  update-~ʰ (there● d) = update-~ʰ d ∙●

opaque

  -- p-equivalence for heaps is reflexive

  ~⟨⟩-refl : H ~⟨ p ⟩ H
  ~⟨⟩-refl {H = ε}     = ε
  ~⟨⟩-refl {H = H ∙ c} = ~⟨⟩-refl ∙ λ _ → refl
  ~⟨⟩-refl {H = H ∙●}  = ~⟨⟩-refl ∙●

opaque

  -- p-equivalence for heaps is symmetric

  ~⟨⟩-sym : H ~⟨ p ⟩ H′ → H′ ~⟨ p ⟩ H
  ~⟨⟩-sym ε = ε
  ~⟨⟩-sym (H~H′ ∙ t≡u) = ~⟨⟩-sym H~H′ ∙ (sym ∘→ t≡u)
  ~⟨⟩-sym (H~H′ ∙●) = ~⟨⟩-sym H~H′ ∙●

opaque

  -- p-equivalence for heaps is transitive

  ~⟨⟩-trans : H ~⟨ p ⟩ H′ → H′ ~⟨ p ⟩ H″ → H ~⟨ p ⟩ H″
  ~⟨⟩-trans ε ε = ε
  ~⟨⟩-trans (H~H′ ∙ t≡u) (H′~H″ ∙ u≡v) =
    ~⟨⟩-trans H~H′ H′~H″ ∙ λ q≤p → trans (t≡u q≤p) (u≡v q≤p)
  ~⟨⟩-trans (H~H′ ∙●) (H′~H″ ∙●) =
    ~⟨⟩-trans H~H′ H′~H″ ∙●

opaque

  -- p-equivalent heaps are also q-equivalent if q ≤ p.

  ~⟨⟩-≤ : H ~⟨ p ⟩ H′ → q ≤ p → H ~⟨ q ⟩ H′
  ~⟨⟩-≤ ε _ = ε
  ~⟨⟩-≤ (H~H′ ∙ t≡u) q≤p =
    ~⟨⟩-≤ H~H′ q≤p ∙ λ r≤q → t≡u (≤-trans r≤q q≤p)
  ~⟨⟩-≤ (H~H′ ∙●) q≤p =
    ~⟨⟩-≤ H~H′ q≤p ∙●

opaque

  -- An inversion lemma for p-equivalent heaps

  ~⟨⟩-inv-∙ :
    {ρ : Wk m n} {ρ′ : Wk m k} →
    H ∙ (q , t , ρ) ~⟨ p ⟩ H′ ∙ (r , u , ρ′) →
    Σ (k ≡ n) λ k≡n → H ~⟨ p ⟩ H′ ×
    ρ ≡ subst (Wk m) k≡n ρ′ × q ≡ r ×
    (q ≤ p → t ≡ subst Term k≡n u)
  ~⟨⟩-inv-∙ (H~H′ ∙ t≡u) =
    refl , H~H′ , refl , refl , t≡u

------------------------------------------------------------------------
-- Properties of states in normal form

opaque

  wk1-Normal : Normal ⟨ H , t , ρ , S ⟩ → Normal ⟨ H ∙ (p , e) , t , step ρ , wk1ˢ S ⟩
  wk1-Normal (val x) = val x
  wk1-Normal (var d) = var (there d)

opaque

  wk1●-Normal : Normal ⟨ H , t , ρ , S ⟩ → Normal ⟨ H ∙● , t , step ρ , wk1ˢ S ⟩
  wk1●-Normal (val x) = val x
  wk1●-Normal (var d) = var (there● d)

opaque

  -- The stack of a normal state can be replaced to give a normal state

  Normal-stack : Normal ⟨ H , t , ρ , S ⟩ → Normal ⟨ H , t , ρ , S′ ⟩
  Normal-stack (val x) = val x
  Normal-stack (var x) = var x

opaque

  -- The heap of a normal state can be replaced by an equal heap and the
  -- stack can be replaced with any stack to give a normal state.

  ~ʰ-Normal : H ~ʰ H′ → Normal ⟨ H , t , ρ , S ⟩ → Normal ⟨ H′ , t , ρ , S′ ⟩
  ~ʰ-Normal H~H′ (val x) = val x
  ~ʰ-Normal H~H′ (var x) = var (~ʰ-lookup● H~H′ x)

------------------------------------------------------------------------
-- Properties of heaps as substitutions

opaque

  -- Weakenings of heaps as substitutions

  wk-[]ₕ : ρ ∷ H ⊇ʰ H′ → (t : Term n) → t [ H′ ]ₕ ≡ wk ρ t [ H ]ₕ
  wk-[]ₕ {H} id t = cong (_[ H ]ₕ) (sym (wk-id t))
  wk-[]ₕ (step ρ) t = trans (wk-[]ₕ ρ t) (sym (step-consSubst t))
  wk-[]ₕ (lift {ρ} {H} {H′} {e = u , ρ′} [ρ]) t = begin
    t [ consSubst (toSubstₕ H′) (wk ρ′ u [ H′ ]ₕ) ]                     ≡˘⟨ singleSubstComp (wk ρ′ u [ H′ ]ₕ) (toSubstₕ H′) t ⟩
    t [ liftSubst (toSubstₕ H′) ] [ wk ρ′ u [ H′ ]ₕ ]₀                  ≡˘⟨ singleSubstLift t (wk ρ′ u) ⟩
    t [ wk ρ′ u ]₀ [ H′ ]ₕ                                              ≡⟨ wk-[]ₕ [ρ] (t [ wk ρ′ u ]₀) ⟩
    wk ρ (t [ wk ρ′ u ]₀) [ H ]ₕ                                        ≡⟨ cong (_[ H ]ₕ) (wk-β t) ⟩
    wk (lift ρ) t [ wk ρ (wk ρ′ u) ]₀ [ H ]ₕ                            ≡⟨ cong (λ x → wk (lift ρ) t [ x ]₀ [ H ]ₕ) (wk-comp ρ ρ′ u) ⟩
    wk (lift ρ) t [ wk (ρ • ρ′) u ]₀ [ H ]ₕ                             ≡⟨ singleSubstLift (wk (lift ρ) t) (wk (ρ • ρ′) u) ⟩
    wk (lift ρ) t [ liftSubst (toSubstₕ H) ] [ wk (ρ • ρ′) u [ H ]ₕ ]₀  ≡⟨ singleSubstComp (wk (ρ • ρ′) u [ H ]ₕ) (toSubstₕ H) (wk (lift ρ) t) ⟩
    wk (lift ρ) t [ consSubst (toSubstₕ H) (wk (ρ • ρ′) u [ H ]ₕ) ]     ∎

opaque

  -- A heap updated by a pointer lookup gives the same substitution
  -- as the original heap.

  heapUpdateSubst : H ⊢ y ↦[ q ] e ⨾ H′ → toSubstₕ H ≡ toSubstₕ H′
  heapUpdateSubst d = ~ʰ-subst (update-~ʰ d)

opaque

  -- Erased heaps are identity substitutions

  erasedHeap≡idsubst : ∀ x → toSubstₕ (erasedHeap n) x ≡ idSubst x
  erasedHeap≡idsubst x0 = refl
  erasedHeap≡idsubst (x +1) = cong wk1 (erasedHeap≡idsubst x)

opaque

  -- A collorary to the above property

  erasedHeap-subst : ∀ t → t [ erasedHeap n ]ₕ ≡ t
  erasedHeap-subst t = trans (substVar-to-subst erasedHeap≡idsubst t) (subst-id t)

opaque

  -- The weakening toWkₕ H acts as an "inverse" to toSubstₕ H

  toWkₕ-toSubstₕ-var : (H : Heap k m) (x : Fin k)
        → toSubstₕ H (wkVar (toWkₕ H) x) ≡ idSubst x
  toWkₕ-toSubstₕ-var ε ()
  toWkₕ-toSubstₕ-var (H ∙ c) x = toWkₕ-toSubstₕ-var H x
  toWkₕ-toSubstₕ-var (H ∙●) x0 = refl
  toWkₕ-toSubstₕ-var (H ∙●) (x +1) = cong wk1 (toWkₕ-toSubstₕ-var H x)

opaque

  -- The weakening toWkₕ H acts as an "inverse" to toSubstₕ H

  toWkₕ-toSubstₕ : (H : Heap k m) (t : Term k)
                 → wk (toWkₕ H) t [ H ]ₕ ≡ t
  toWkₕ-toSubstₕ H t = begin
    wk (toWkₕ H) t [ H ]ₕ       ≡⟨ subst-wk t ⟩
    t [ toSubstₕ H ₛ• toWkₕ H ] ≡⟨ substVar-to-subst (toWkₕ-toSubstₕ-var H) t ⟩
    t [ idSubst ]               ≡⟨ subst-id t ⟩
    t                           ∎

opaque

  -- Substituting a variable corresponding to a dummy entry

  toSubstₕ-erased : (H : Heap k m) (y : Fin m)
                  → H ⊢ y ↦● → ∃ λ y′ → toSubstₕ H y ≡ var y′
  toSubstₕ-erased ε () _
  toSubstₕ-erased (H ∙ c) y0 ()
  toSubstₕ-erased (H ∙ c) (y +1) (there d) = toSubstₕ-erased H y d
  toSubstₕ-erased (H ∙●) y0 d = y0 , refl
  toSubstₕ-erased (H ∙●) (y +1) (there● d) =
    case toSubstₕ-erased H y d of λ
      (y′ , ≡y′) →
    y′ +1 , cong wk1 ≡y′

opaque

  -- A term that is neutral at a variable with a dummy entry in the heap
  -- will still be neutral at the same variable after applying the heap
  -- substitution.

  toSubstₕ-NeutralAt :
    (d : H ⊢ y ↦●) →
    NeutralAt V ∇ (inj₂ y) t →
    NeutralAt V ∇ (inj₂ (toSubstₕ-erased H y d .proj₁)) (t [ H ]ₕ)
  toSubstₕ-NeutralAt d (var ok) with toSubstₕ-erased _ _ d
  … | (x′ , ≡x′) =
    subst (NeutralAt _ _ _) (sym ≡x′) (var ok)
  toSubstₕ-NeutralAt d (∘ₙ n) =
    ∘ₙ (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d (fstₙ n) =
    fstₙ (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d (sndₙ n) =
    sndₙ (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d (natrecₙ n) =
    natrecₙ (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d (prodrecₙ n) =
    prodrecₙ (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d (emptyrecₙ n) =
    emptyrecₙ (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d (unitrecₙ x n) =
    unitrecₙ x (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d (Jₙ n) =
    Jₙ (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d (Kₙ n) =
    Kₙ (toSubstₕ-NeutralAt d n)
  toSubstₕ-NeutralAt d ([]-congₙ n) =
    []-congₙ (toSubstₕ-NeutralAt d n)

opaque

  -- ⦅_⦆ is an inverse of initial.

  ⦅initial⦆≡ : ⦅ initial t ⦆ ≡ t
  ⦅initial⦆≡ = trans (erasedHeap-subst (wk id _)) (wk-id _)

------------------------------------------------------------------------
-- Some lemmas related to the No-names variants

opaque

  -- No-namesᶜ is closed under weakening.

  No-namesᶜ-wk : No-namesᶜ c → No-namesᶜ (wkᶜ ρ c)
  No-namesᶜ-wk (emptyrecₑ nn)           = emptyrecₑ nn
  No-namesᶜ-wk (unitrecₑ nn₁ nn₂)       = unitrecₑ nn₁ nn₂
  No-namesᶜ-wk (∘ₑ nn)                  = ∘ₑ nn
  No-namesᶜ-wk fstₑ                     = fstₑ
  No-namesᶜ-wk sndₑ                     = sndₑ
  No-namesᶜ-wk (prodrecₑ nn₁ nn₂)       = prodrecₑ nn₁ nn₂
  No-namesᶜ-wk sucₑ                     = sucₑ
  No-namesᶜ-wk (natrecₑ nn₁ nn₂ nn₃)    = natrecₑ nn₁ nn₂ nn₃
  No-namesᶜ-wk (Jₑ nn₁ nn₂ nn₃ nn₄ nn₅) = Jₑ nn₁ nn₂ nn₃ nn₄ nn₅
  No-namesᶜ-wk (Kₑ nn₁ nn₂ nn₃ nn₄)     = Kₑ nn₁ nn₂ nn₃ nn₄
  No-namesᶜ-wk ([]-congₑ nn₁ nn₂ nn₃)   = []-congₑ nn₁ nn₂ nn₃

opaque

  -- No-namesˢ is closed under weakening.

  No-namesˢ-wk : No-namesˢ S → No-namesˢ (wkˢ ρ S)
  No-namesˢ-wk ε             = ε
  No-namesˢ-wk (e-nn ∙ S-nn) = No-namesᶜ-wk e-nn ∙ No-namesˢ-wk S-nn

opaque

  -- There are no names in erasedHeap n.

  No-namesʰ-erasedHeap : No-namesʰ (erasedHeap n)
  No-namesʰ-erasedHeap {n = 0}    = ε
  No-namesʰ-erasedHeap {n = 1+ _} = No-namesʰ-erasedHeap ∙●

opaque

  -- If there are no names in t, then there are no names in initial t.

  No-namesₛ-initial : No-names t → No-namesₛ (initial t)
  No-namesₛ-initial t-nn = (No-namesʰ-erasedHeap , t-nn) , ε
