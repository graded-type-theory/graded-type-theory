------------------------------------------------------------------------
-- Properties of the heap semantics.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Tools.Bool
open import Definition.Typed.Variant

module Heap.Untyped.Properties
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; +-suc) renaming (_+_ to _+ⁿ_)
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Relation
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum hiding (id; sym)

open import Graded.Modality.Properties.Subtraction semiring-with-meet
open import Graded.Usage.Erased-matches

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Heap.Untyped type-variant UR

private variable
  k n n′ n″ m m′ m″ : Nat
  t t′ t″ u v A z : Term _
  H H′ H″ : Heap _ _
  E E′ E″ : Env _ _
  S S′ S″ : Stack _
  p p′ q r r′ : M
  y y′ : Ptr _
  x : Fin _
  c c′ : Closure _ _
  Γ : Con Term _
  e e′ : Elim _
  s : State _ _ _
  σ : Subst _ _
  ρ : Wk _ _

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

  Value→¬Neutral : Value t → ¬ Neutral t
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

-- opaque

--   -- Non-neutrals in whnf are values

--   Whnf→Value : ⦃ ¬ℕ-Fullred ⦄ → Whnf t → ¬ Neutral t → Value t
--   Whnf→Value Uₙ ¬ne = Uᵥ
--   Whnf→Value ΠΣₙ ¬ne = ΠΣᵥ
--   Whnf→Value ℕₙ ¬ne = ℕᵥ
--   Whnf→Value Unitₙ ¬ne = Unitᵥ
--   Whnf→Value Emptyₙ ¬ne = Emptyᵥ
--   Whnf→Value Idₙ ¬ne = Idᵥ
--   Whnf→Value lamₙ ¬ne = lamᵥ
--   Whnf→Value zeroₙ ¬ne = zeroᵥ
--   Whnf→Value sucₙ ¬ne = sucᵥ
--   Whnf→Value starₙ ¬ne = starᵥ
--   Whnf→Value prodₙ ¬ne = prodᵥ
--   Whnf→Value rflₙ ¬ne = rflᵥ
--   Whnf→Value (ne x) ¬ne = ⊥-elim (¬ne x)

-- opaque

--   -- Value t is decidable

--   dec-Value : (t : Term n) → Dec (Value t)
--   dec-Value (lam p t) = yes lamᵥ
--   dec-Value (prod s p t u) = yes prodᵥ
--   dec-Value zero = yes zeroᵥ
--   dec-Value (suc t) = yes {!!}
--   dec-Value (star s) = yes starᵥ
--   dec-Value rfl = yes rflᵥ
--   dec-Value U = yes Uᵥ
--   dec-Value (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) = yes ΠΣᵥ
--   dec-Value ℕ = yes ℕᵥ
--   dec-Value (Unit s) = yes Unitᵥ
--   dec-Value Empty = yes Emptyᵥ
--   dec-Value (Id A t u) = yes Idᵥ
--   dec-Value (var x) = no (λ ())
--   dec-Value (t ∘ u) = no (λ ())
--   dec-Value (unitrec p q A t u) = no (λ ())
--   dec-Value (emptyrec p A t) = no (λ ())
--   dec-Value (prodrec r p q A t u) = no (λ ())
--   dec-Value (natrec p q r A z s n) = no (λ ())
--   dec-Value (fst p t) = no (λ ())
--   dec-Value (snd p t) = no (λ ())
--   dec-Value (J p q A t B u v w) = no (λ ())
--   dec-Value (K p A t B u v) = no (λ ())
--   dec-Value ([]-cong s A t u v) = no (λ ())

-- opaque

--   -- Values are not equal to non-values

--   Value≢¬Value : Value t → ¬ Value u → t ≢ u
--   Value≢¬Value v ¬v refl = ¬v v

------------------------------------------------------------------------
-- Properties of the lookup relations

opaque

  -- Variable lookup with heap update is deterministic.

  lookup-det : {H : Heap k m} {t : Term n} {u : Term n′}
             → H ⊢ y ↦[ r ] t , E ⨾ H′
             → H ⊢ y ↦[ r ] u , E′ ⨾ H″
             → Σ (n ≡ n′) λ p → subst Term p t ≡ u
               × subst (Env m) p E ≡ E′ × H′ ≡ H″
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
             → H ⊢ y ↦ (t , E)
             → H ⊢ y ↦ (u , E′)
             → Σ (n ≡ n′) λ p → subst Term p t ≡ u × subst (Env m) p E ≡ E′
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

  -- If heap lookup with update succeeds lookup without heap update
  -- succeeds with the same result.

  ↦[]→↦ : H ⊢ y ↦[ q ] c ⨾ H′ → H ⊢ y ↦ c
  ↦[]→↦ (here x) = here
  ↦[]→↦ (there d) = there (↦[]→↦ d)
  ↦[]→↦ (there● d) = there● (↦[]→↦ d)

opaque

  -- Heap lookups match the corresponding substitution.

  heapSubstVar : H ⊢ y ↦[ q ] t , E ⨾ H′ → toSubstₕ H y ≡ wk E t [ H ]ₕ
  heapSubstVar {t} (here _) =
    sym (step-consSubst t)
  heapSubstVar {t} (there d) =
    trans (heapSubstVar d) (sym (step-consSubst t))
  heapSubstVar {H = H ∙●} {t} {E = step E} (there● d) =
    trans (cong wk1 (heapSubstVar d))
      (trans (sym (wk1-liftSubst (wk E t)))
        (cong (_[ H ]⇑ₕ) (wk1-wk E t)))

opaque

  -- Heap lookups match the corresponding substitution.

  heapSubstVar′ : H ⊢ y ↦ (t , E) → toSubstₕ H y ≡ wk E t [ H ]ₕ
  heapSubstVar′ {t} here =
    sym (step-consSubst t)
  heapSubstVar′ {t} (there d) =
    trans (heapSubstVar′ d) (sym (step-consSubst t))
  heapSubstVar′ {H = H ∙●} {t} {E = step E} (there● d) =
    trans (cong wk1 (heapSubstVar′ d))
      (trans (sym (wk1-liftSubst (wk E t)))
        (cong (_[ H ]⇑ₕ) (wk1-wk E t)))

------------------------------------------------------------------------
-- Properties of stacks and eliminators

opaque

  -- Applying a single substitution to a term and then to an eliminator

  ⦅⦆ᵉ-sgSubst : ∀ e → ⦅ e ⦆ᵉ (t [ u ]₀) ≡ ⦅ wk1ᵉ e ⦆ᵉ t [ u ]₀
  ⦅⦆ᵉ-sgSubst (∘ₑ p u E) =
    cong (_ ∘_) (sym (step-sgSubst _ _))
  ⦅⦆ᵉ-sgSubst (fstₑ p) = refl
  ⦅⦆ᵉ-sgSubst (sndₑ p) = refl
  ⦅⦆ᵉ-sgSubst {u = v} (prodrecₑ r p q A u E) =
    cong₂ (λ u A → prodrec r p q A _ u)
      (lifts-step-sgSubst 2 u)
      (lifts-step-sgSubst 1 A)
  ⦅⦆ᵉ-sgSubst {u} (natrecₑ p q r A z s E) =
    cong₃ (λ A z s → natrec p q r A z s _)
      (lifts-step-sgSubst 1 A)
      (lifts-step-sgSubst 0 z)
      (lifts-step-sgSubst 2 s)
  ⦅⦆ᵉ-sgSubst {u = v} (unitrecₑ p q A u E) =
    cong₂ (λ u A → unitrec p q A _ u)
      (sym (step-sgSubst _ _))
      (lifts-step-sgSubst 1 A)
  ⦅⦆ᵉ-sgSubst (emptyrecₑ p A E) =
    cong (λ A → emptyrec p A _)
      (lifts-step-sgSubst 0 A)
  ⦅⦆ᵉ-sgSubst (Jₑ p q A t B u v E) =
    sym (cong₅ (λ A t B u v → J p q A t B u v _)
      (step-sgSubst A _) (step-sgSubst t _)
      (sym (lifts-step-sgSubst 2 B))
      (step-sgSubst u _) (step-sgSubst v _))
  ⦅⦆ᵉ-sgSubst (Kₑ p A t B u E) =
    sym (cong₄ (λ A t B u → K p A t B u _)
      (step-sgSubst A _) (step-sgSubst t _)
      (sym (lifts-step-sgSubst 1 B))
      (step-sgSubst u _))
  ⦅⦆ᵉ-sgSubst ([]-congₑ s A t u E) =
    sym (cong₃ (λ A t u → []-cong s A t u _)
      (step-sgSubst A _) (step-sgSubst t _)
      (step-sgSubst u _))
  ⦅⦆ᵉ-sgSubst sucₑ = refl

opaque

  -- Applying a single substitution to a term and then to a stack

  ⦅⦆ˢ-sgSubst : ∀ S → ⦅ S ⦆ˢ (t [ u ]₀) ≡ ⦅ wk1ˢ S ⦆ˢ t [ u ]₀
  ⦅⦆ˢ-sgSubst ε = refl
  ⦅⦆ˢ-sgSubst {t} {u} (e ∙ S) = begin
   ⦅ e ∙ S ⦆ˢ (t [ u ]₀)              ≡⟨⟩
   ⦅ S ⦆ˢ (⦅ e ⦆ᵉ (t [ u ]₀))          ≡⟨ cong ⦅ S ⦆ˢ (⦅⦆ᵉ-sgSubst e) ⟩
   ⦅ S ⦆ˢ (⦅ wk1ᵉ e ⦆ᵉ t [ u ]₀)       ≡⟨ ⦅⦆ˢ-sgSubst S ⟩
   ⦅ wk1ˢ S ⦆ˢ (⦅ wk1ᵉ e ⦆ᵉ t) [ u ]₀  ≡⟨⟩
   ⦅ wk1ˢ (e ∙ S) ⦆ˢ t [ u ]₀         ∎

opaque

  -- Applying a double substitution to a term and then to an eliminator

  ⦅⦆ᵉ-[,] : ∀ e → ⦅ e ⦆ᵉ (t [ u , v ]₁₀) ≡ ⦅ wk2ᵉ e ⦆ᵉ t [ u , v ]₁₀
  ⦅⦆ᵉ-[,] (∘ₑ p u E) =
    cong (_ ∘_) (lifts-step-[,] 0 u)
  ⦅⦆ᵉ-[,] (fstₑ x) = refl
  ⦅⦆ᵉ-[,] (sndₑ x) = refl
  ⦅⦆ᵉ-[,] (prodrecₑ r p q A u E) =
    cong₂ (λ x y → prodrec r p q x _ y)
      (lifts-step-[,] 1 A)
      (lifts-step-[,] 2 u)
  ⦅⦆ᵉ-[,] (natrecₑ p q r A z s E) =
    cong₃ (λ A z s → natrec p q r A z s _)
      (lifts-step-[,] 1 A)
      (lifts-step-[,] 0 z)
      (lifts-step-[,] 2 s)
  ⦅⦆ᵉ-[,] (unitrecₑ p q A u E) =
    cong₂ (λ x y → unitrec p q x _ y)
      (lifts-step-[,] 1 A) (lifts-step-[,] 0 u)
  ⦅⦆ᵉ-[,] (emptyrecₑ p A E) =
    cong (λ A → emptyrec p A _) (lifts-step-[,] 0 A)
  ⦅⦆ᵉ-[,] (Jₑ p q A t B u v E) =
    cong₅ (λ A t B u v → J p q A t B u v _)
      (lifts-step-[,] 0 A) (lifts-step-[,] 0 t)
      (lifts-step-[,] 2 B) (lifts-step-[,] 0 u)
      (lifts-step-[,] 0 v)
  ⦅⦆ᵉ-[,] (Kₑ p A t B u E) =
    cong₄ (λ A t B u → K p A t B u _)
      (lifts-step-[,] 0 A) (lifts-step-[,] 0 t)
      (lifts-step-[,] 1 B) (lifts-step-[,] 0 u)
  ⦅⦆ᵉ-[,] ([]-congₑ s A t u E) =
    cong₃ (λ A t u → []-cong s A t u _)
      (lifts-step-[,] 0 A) (lifts-step-[,] 0 t)
      (lifts-step-[,] 0 u)
  ⦅⦆ᵉ-[,] sucₑ = refl

opaque

  -- Applying a double substitution to a term and then to a stack

  ⦅⦆ˢ-[,] : ∀ S → ⦅ S ⦆ˢ (t [ u , v ]₁₀) ≡ ⦅ wk2ˢ S ⦆ˢ t [ u , v ]₁₀
  ⦅⦆ˢ-[,] ε = refl
  ⦅⦆ˢ-[,] {t} {u} {v} (e ∙ S) = begin
    ⦅ e ∙ S ⦆ˢ (t [ u , v ]₁₀)             ≡⟨⟩
    ⦅ S ⦆ˢ (⦅ e ⦆ᵉ (t [ u , v ]₁₀))         ≡⟨ cong ⦅ S ⦆ˢ (⦅⦆ᵉ-[,] e) ⟩
    ⦅ S ⦆ˢ (⦅ wk2ᵉ e ⦆ᵉ t [ u , v ]₁₀)      ≡⟨ ⦅⦆ˢ-[,] S ⟩
    ⦅ wk2ˢ S ⦆ˢ (⦅ wk2ᵉ e ⦆ᵉ t) [ u , v ]₁₀ ≡⟨⟩
    ⦅ wk2ˢ (e ∙ S) ⦆ˢ t [ u , v ]₁₀        ∎

opaque

  -- Weakening of an eliminator applied to a Term

  wk-⦅⦆ᵉ : ∀ {ρ : Wk m n} e → wk ρ (⦅ e ⦆ᵉ t) ≡ ⦅ wkᵉ ρ e ⦆ᵉ (wk ρ t)
  wk-⦅⦆ᵉ {ρ} (∘ₑ p u E) =
    cong (_ ∘_) (wk-comp ρ E u)
  wk-⦅⦆ᵉ (fstₑ p) = refl
  wk-⦅⦆ᵉ (sndₑ p) = refl
  wk-⦅⦆ᵉ {ρ} (prodrecₑ r p q A u E) =
    cong₂ (λ A u → prodrec r p q A _ u)
      (wk-comp (lift ρ) (lift E) A)
      (wk-comp (liftn ρ 2) (liftn E 2) u)
  wk-⦅⦆ᵉ {ρ} (natrecₑ p q r A z s E) =
    cong₃ (λ A z s → natrec p q r A z s _)
      (wk-comp (lift ρ) (lift E) A)
      (wk-comp ρ E z)
      (wk-comp (liftn ρ 2) (liftn E 2) s)
  wk-⦅⦆ᵉ {ρ} (unitrecₑ p q A u E) =
    cong₂ (λ A u → unitrec p q A _ u)
      (wk-comp (lift ρ) (lift E) A)
      (wk-comp ρ E u)
  wk-⦅⦆ᵉ {ρ} (emptyrecₑ p A E) =
    cong (λ A → emptyrec p A _) (wk-comp ρ E A)
  wk-⦅⦆ᵉ {ρ} (Jₑ p q A t B u v E) =
    cong₅ (λ A t B u v → J p q A t B u v _)
      (wk-comp ρ E A) (wk-comp ρ E t)
      (wk-comp (liftn ρ 2) (liftn E 2) B)
      (wk-comp ρ E u) (wk-comp ρ E v)
  wk-⦅⦆ᵉ {ρ} (Kₑ p A t B u E) =
    cong₄ (λ A t B u → K p A t B u _)
      (wk-comp ρ E A) (wk-comp ρ E t)
      (wk-comp (lift ρ) (lift E) B) (wk-comp ρ E u)
  wk-⦅⦆ᵉ {ρ} ([]-congₑ s A t u E) =
    cong₃ (λ A t u → []-cong s A t u _)
      (wk-comp ρ E A) (wk-comp ρ E t)
      (wk-comp ρ E u)
  wk-⦅⦆ᵉ {ρ} sucₑ = refl

opaque

  -- A congruence property for eliminators

  ⦅⦆ᵉ-cong : ∀ e → t [ σ ] ≡ u [ σ ]
         → ⦅ e ⦆ᵉ t [ σ ] ≡ ⦅ e ⦆ᵉ u [ σ ]
  ⦅⦆ᵉ-cong (∘ₑ p u E) t≡u =
    cong (_∘ _) t≡u
  ⦅⦆ᵉ-cong (fstₑ x) t≡u =
    cong (fst _) t≡u
  ⦅⦆ᵉ-cong (sndₑ x) t≡u =
    cong (snd _) t≡u
  ⦅⦆ᵉ-cong (prodrecₑ r p q A u E) t≡u =
    cong (λ t → prodrec _ _ _ _ t _) t≡u
  ⦅⦆ᵉ-cong (natrecₑ p q r A z s E) t≡u =
    cong (λ t → natrec _ _ _ _ _ _ t) t≡u
  ⦅⦆ᵉ-cong (unitrecₑ p q A u E) t≡u =
    cong (λ t → unitrec _ _ _ t _) t≡u
  ⦅⦆ᵉ-cong (emptyrecₑ p A E) t≡u =
    cong (emptyrec _ _) t≡u
  ⦅⦆ᵉ-cong (Jₑ p q A t B u v E) t≡u =
    cong (J _ _ _ _ _ _ _) t≡u
  ⦅⦆ᵉ-cong (Kₑ p A t B u E) t≡u =
    cong (K _ _ _ _ _) t≡u
  ⦅⦆ᵉ-cong ([]-congₑ s A t u E) t≡u =
    cong ([]-cong _ _ _ _) t≡u
  ⦅⦆ᵉ-cong sucₑ t≡u =
    cong suc t≡u


opaque

  -- A congruence property for stacks

  ⦅⦆ˢ-cong : ∀ S → t [ σ ] ≡ u [ σ ]
         → ⦅ S ⦆ˢ t [ σ ] ≡ ⦅ S ⦆ˢ u [ σ ]
  ⦅⦆ˢ-cong ε t≡u = t≡u
  ⦅⦆ˢ-cong (e ∙ S) t≡u = ⦅⦆ˢ-cong S (⦅⦆ᵉ-cong e t≡u)

opaque

  -- Weakening of sucₛ k

  wk-sucₛ : (ρ : Wk m n) (k : Nat) → wkˢ ρ (sucₛ k) ≡ sucₛ k
  wk-sucₛ ρ 0 = refl
  wk-sucₛ ρ (1+ k) = cong (sucₑ ∙_) (wk-sucₛ ρ k)

opaque

  -- Multiplicity of weakened eliminators

  wk-∣e∣ : ⦃ _ : Has-nr M semiring-with-meet ⦄
         → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
         → (ρ : Wk k n) (e : Elim n) → ∣ e ∣ᵉ ≡ ∣ wkᵉ ρ e ∣ᵉ
  wk-∣e∣ ρ (∘ₑ p u E) = refl
  wk-∣e∣ ρ (fstₑ x) = refl
  wk-∣e∣ ρ (sndₑ x) = refl
  wk-∣e∣ ρ (prodrecₑ r p q A u E) = refl
  wk-∣e∣ ρ (natrecₑ p q r A z s E) = refl
  wk-∣e∣ ρ (unitrecₑ p q A u E) = refl
  wk-∣e∣ ρ (emptyrecₑ p A E) = refl
  wk-∣e∣ ρ (Jₑ p q A t B u v E) = refl
  wk-∣e∣ ρ (Kₑ p A t B u E) = refl
  wk-∣e∣ ρ ([]-congₑ s A t u E) = refl
  wk-∣e∣ ρ sucₑ = refl

opaque

  -- Multiplicity of weakened stacks

  wk-∣S∣ : ⦃ _ : Has-nr M semiring-with-meet ⦄
         → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
         → (ρ : Wk k n) (S : Stack n) → ∣ S ∣ ≡ ∣ wkˢ ρ S ∣
  wk-∣S∣ ρ ε = refl
  wk-∣S∣ ρ (e ∙ S) = cong₂ _·_ (wk-∣S∣ ρ S) (wk-∣e∣ ρ e)

opaque

  ∣∣ᵉ-J-ω : ∀ {e}
          → e ≤ᵉᵐ some
          → (e ≡ some → ¬ (p ≡ 𝟘 × q ≡ 𝟘))
          → ∣∣ᵉ-J e p q ≡ ω
  ∣∣ᵉ-J-ω {e = none} _ _ = refl
  ∣∣ᵉ-J-ω {p} {q} {e = some} _ P
    with is-𝟘? p
  … | no _ = refl
  … | yes p≡𝟘 with is-𝟘? q
  … | no _ = refl
  … | yes q≡𝟘 = ⊥-elim (P refl (p≡𝟘 , q≡𝟘))

opaque

  ∣∣ᵉ-J-some₀₀ : ∀ {e} → e ≡ some → ∣∣ᵉ-J e 𝟘 𝟘 ≡ 𝟘
  ∣∣ᵉ-J-some₀₀ refl with is-𝟘? 𝟘
  … | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  … | yes _ with is-𝟘? 𝟘
  … | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  … | yes _ = refl

opaque

  ∣∣ᵉ-J-all : ∀ {e} → e ≡ all → ∣∣ᵉ-J e p q ≡ 𝟘
  ∣∣ᵉ-J-all refl = refl

opaque

  ∣∣ᵉ-K-ω : ∀ {e}
          → e ≤ᵉᵐ some
          → (e ≡ some → p ≢ 𝟘)
          → ∣∣ᵉ-K e p ≡ ω
  ∣∣ᵉ-K-ω {e = none} _ _ = refl
  ∣∣ᵉ-K-ω {p} {e = some} _ p≢𝟘
    with is-𝟘? p
  … | no _ = refl
  … | yes p≡𝟘 = ⊥-elim (p≢𝟘 refl p≡𝟘)

opaque

  ∣∣ᵉ-K-some₀ : ∀ {e} → e ≡ some → ∣∣ᵉ-K e 𝟘 ≡ 𝟘
  ∣∣ᵉ-K-some₀ refl with is-𝟘? 𝟘
  … | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  … | yes _ = refl

opaque

  ∣∣ᵉ-K-all : ∀ {e} → e ≡ all → ∣∣ᵉ-K e p ≡ 𝟘
  ∣∣ᵉ-K-all refl = refl

opaque

  -- Multiplicity of sucₛ k

  ∣sucₛ∣≡𝟙 : ⦃ _ : Has-nr M semiring-with-meet ⦄
           → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
           → ∀ k → ∣ sucₛ {m} k ∣ ≡ 𝟙
  ∣sucₛ∣≡𝟙 0 = refl
  ∣sucₛ∣≡𝟙 (1+ k) = trans (·-identityʳ _) (∣sucₛ∣≡𝟙 k)

opaque

  -- Multiplicity of the stack S ++ sucₛ k

  ∣S++sucₛ∣≡∣S∣ : ⦃ _ : Has-nr M semiring-with-meet ⦄
                → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
                → (S : Stack m) → ∣ S ++ sucₛ k ∣ ≡ ∣ S ∣
  ∣S++sucₛ∣≡∣S∣ {k} ε = ∣sucₛ∣≡𝟙 k
  ∣S++sucₛ∣≡∣S∣ (e ∙ S) = ·-congʳ (∣S++sucₛ∣≡∣S∣ S)

opaque

  -- Stack concatenation

  ⦅⦆ˢ++ : ∀ S S′ → ⦅ S ++ S′ ⦆ˢ t ≡ ⦅ S′ ⦆ˢ (⦅ S ⦆ˢ t)
  ⦅⦆ˢ++ ε S′ = refl
  ⦅⦆ˢ++ (e ∙ S) S′ = ⦅⦆ˢ++ S S′

opaque

  -- Weakening of stack concatenation

  wk-++ : (ρ : Wk m n) (S : Stack n) → wkˢ ρ (S ++ S′) ≡ wkˢ ρ S ++ wkˢ ρ S′
  wk-++ ρ ε = refl
  wk-++ ρ (e ∙ S) = cong (_ ∙_) (wk-++ ρ S)

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

  ¬⦅⦆ᵉ-neutral : ∀ e → ¬ Neutral t → ¬ Neutral (⦅ e ⦆ᵉ t)
  ¬⦅⦆ᵉ-neutral (∘ₑ p u E) ¬n (∘ₙ n) = ¬n n
  ¬⦅⦆ᵉ-neutral (fstₑ x) ¬n (fstₙ n) = ¬n n
  ¬⦅⦆ᵉ-neutral (sndₑ x) ¬n (sndₙ n) = ¬n n
  ¬⦅⦆ᵉ-neutral (prodrecₑ r p q A u E) ¬n (prodrecₙ n) = ¬n n
  ¬⦅⦆ᵉ-neutral (natrecₑ p q r A z s E) ¬n (natrecₙ n) = ¬n n
  ¬⦅⦆ᵉ-neutral (unitrecₑ p q A u E) ¬n (unitrecₙ _ n) = ¬n n
  ¬⦅⦆ᵉ-neutral (emptyrecₑ p A E) ¬n (emptyrecₙ n) = ¬n n
  ¬⦅⦆ᵉ-neutral (Jₑ p q A t B u v E) ¬n (Jₙ n) = ¬n n
  ¬⦅⦆ᵉ-neutral (Kₑ p A t B u E) ¬n (Kₙ n) = ¬n n
  ¬⦅⦆ᵉ-neutral ([]-congₑ s A t u E) ¬n ([]-congₙ n) = ¬n n

opaque

  -- Injectivity of stacks

  stack-injective : {e : Elim m} {S : Stack m}
                  → e ∙ S ≡ e′ ∙ S′ → e ≡ e′ × S ≡ S′
  stack-injective refl = refl , refl

opaque

  -- Injectivity of sucₛ

  sucₛ-injective : sucₛ {m} n ≡ sucₛ n′ → n ≡ n′
  sucₛ-injective {n = 0} {(0)} _ = refl
  sucₛ-injective {n = 1+ n} {1+ n′} x =
    cong 1+ (sucₛ-injective (stack-injective x .proj₂))

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

  ~ʰ-lookup : H ~ʰ H′ → H ⊢ y ↦ c → H′ ⊢ y ↦ c
  ~ʰ-lookup (H~H′ ∙ _) here = here
  ~ʰ-lookup (H~H′ ∙ _) (there d) = there (~ʰ-lookup H~H′ d)
  ~ʰ-lookup (H~H′ ∙●) (there● d) = there● (~ʰ-lookup H~H′ d)

opaque

  -- Heap lookup to ● behaves the same on equal heaps

  ~ʰ-lookup● : H ~ʰ H′ → H ⊢ y ↦● → H′ ⊢ y ↦●
  ~ʰ-lookup● (H~H′ ∙●) here = here
  ~ʰ-lookup● (H~H′ ∙ _) (there d) = there (~ʰ-lookup● H~H′ d)
  ~ʰ-lookup● (H~H′ ∙●) (there● d) = there● (~ʰ-lookup● H~H′ d)

opaque

  -- Equal heaps are equal as substitutions

  ~ʰ-subst : H ~ʰ H′ → toSubstₕ H ≡ toSubstₕ H′
  ~ʰ-subst ε = refl
  ~ʰ-subst (H~H′ ∙ (t , E)) =
    case ~ʰ-subst H~H′ of λ
      H≡H′ →
    cong₂ consSubst H≡H′ (cong (wk E t [_]) H≡H′)
  ~ʰ-subst (H~H′ ∙●) =
    cong liftSubst (~ʰ-subst H~H′)

opaque

  -- An updated heap is equal to the original one (up to grades)

  update-~ʰ : H ⊢ y ↦[ q ] c ⨾ H′ → H ~ʰ H′
  update-~ʰ (here _) = ~ʰ-refl ∙ _
  update-~ʰ (there d) = update-~ʰ d ∙ _
  update-~ʰ (there● d) = update-~ʰ d ∙●

------------------------------------------------------------------------
-- Properties of substitutions

opaque

  -- Weakenings of heaps as substitutions

  wk-[]ₕ : ρ ∷ H ⊇ʰ H′ → (t : Term n) → t [ H′ ]ₕ ≡ wk ρ t [ H ]ₕ
  wk-[]ₕ {H} id t = cong (_[ H ]ₕ) (sym (wk-id t))
  wk-[]ₕ (step ρ) t = trans (wk-[]ₕ ρ t) (sym (step-consSubst t))
  -- wk-[]ₕ (lift {ρ} {H} {H′} {c = u , E} [ρ]) t = begin
  --   t [ consSubst (toSubstₕ H′) (wk E u [ H′ ]ₕ) ]                     ≡˘⟨ singleSubstComp (wk E u [ H′ ]ₕ) (toSubstₕ H′) t ⟩
  --   t [ liftSubst (toSubstₕ H′) ] [ wk E u [ H′ ]ₕ ]₀                  ≡˘⟨ singleSubstLift t (wk E u) ⟩
  --   t [ wk E u ]₀ [ H′ ]ₕ                                              ≡⟨ wk-[]ₕ [ρ] (t [ wk E u ]₀) ⟩
  --   wk ρ (t [ wk E u ]₀) [ H ]ₕ                                        ≡⟨ cong (_[ H ]ₕ) (wk-β t) ⟩
  --   wk (lift ρ) t [ wk ρ (wk E u) ]₀ [ H ]ₕ                            ≡⟨ cong (λ x → wk (lift ρ) t [ x ]₀ [ H ]ₕ) (wk-comp ρ E u) ⟩
  --   wk (lift ρ) t [ wk (ρ • E) u ]₀ [ H ]ₕ                             ≡⟨ singleSubstLift (wk (lift ρ) t) (wk (ρ • E) u) ⟩
  --   wk (lift ρ) t [ liftSubst (toSubstₕ H) ] [ wk (ρ • E) u [ H ]ₕ ]₀  ≡⟨ singleSubstComp (wk (ρ • E) u [ H ]ₕ) (toSubstₕ H) (wk (lift ρ) t) ⟩
  --   wk (lift ρ) t [ consSubst (toSubstₕ H) (wk (ρ • E) u [ H ]ₕ) ] ∎

opaque

  -- A heap updated by a pointer lookup gives the same substitution
  -- as the original heap.

  heapUpdateSubst : H ⊢ y ↦[ q ] c ⨾ H′ → toSubstₕ H ≡ toSubstₕ H′
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

  wk1-Normal : Normal ⟨ H , t , E , S ⟩ → Normal ⟨ H ∙ (p , c) , t , step E , wk1ˢ S ⟩
  wk1-Normal (val x) = val x
  wk1-Normal (var d) = var (there d)

opaque

  wk1●-Normal : Normal ⟨ H , t , E , S ⟩ → Normal ⟨ H ∙● , t , step E , wk1ˢ S ⟩
  wk1●-Normal (val x) = val x
  wk1●-Normal (var d) = var (there● d)

opaque

  -- The stack of a normal state can be replaced to give a normal state

  Normal-stack : Normal ⟨ H , t , E , S ⟩ → Normal ⟨ H , t , E , S′ ⟩
  Normal-stack (val x) = val x
  Normal-stack (var x) = var x

opaque

  State-injectivity : ⟨ H , t , E , S ⟩ ≡ ⟨ H′ , t′ , E′ , S′ ⟩
                    → H ≡ H′ × t ≡ t′ × E ≡ E′ × S ≡ S′
  State-injectivity refl = refl , refl , refl , refl

opaque

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

  toSubstₕ-NeutralAt : (d : H ⊢ y ↦●)
                     → NeutralAt y t
                     → NeutralAt (toSubstₕ-erased H y d .proj₁) (t [ H ]ₕ)
  toSubstₕ-NeutralAt d var with toSubstₕ-erased _ _ d
  … | (x′ , ≡x′) =
    subst (NeutralAt _) (sym ≡x′) var
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
