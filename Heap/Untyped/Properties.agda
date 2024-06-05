------------------------------------------------------------------------
-- Properties of the heap semantics.
------------------------------------------------------------------------

open import Graded.Modality
open import Tools.Bool
open import Definition.Typed.Variant

module Heap.Untyped.Properties
  {a} {M : Set a} (𝕄 : Modality M)
  (type-variant : Type-variant)
  where

open Modality 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+) renaming (_+_ to _+ⁿ_)
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Relation
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum hiding (id; sym)

open import Graded.Modality.Properties.Subtraction semiring-with-meet

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Heap.Untyped 𝕄 type-variant

private variable
  k n n′ n″ m m′ m″ : Nat
  t t′ t″ u v A z : Term _
  H H′ H″ : Heap _
  E E′ E″ : Env _ _
  S S′ S″ : Stack _
  p p′ q r r′ : M
  y y′ : Ptr _
  x : Fin _
  c c′ : Closure _ _
  Γ : Con Term _
  e e′ : Elim _
  s : State _ _
  σ : Subst _ _
  ρ : Wk _ _

------------------------------------------------------------------------
-- Properties of values

opaque

  -- Values applied to weakenings are values

  wkVal : (ρ : Wk m n) → Val t → Val (wk ρ t)
  wkVal ρ lamᵥ = lamᵥ
  wkVal ρ zeroᵥ = zeroᵥ
  wkVal ρ sucᵥ = sucᵥ
  wkVal ρ starᵥ = starᵥ
  wkVal ρ prodᵥ = prodᵥ
  wkVal ρ rflᵥ = rflᵥ
  wkVal ρ Uᵥ = Uᵥ
  wkVal ρ ΠΣᵥ = ΠΣᵥ
  wkVal ρ ℕᵥ = ℕᵥ
  wkVal ρ Unitᵥ = Unitᵥ
  wkVal ρ Emptyᵥ = Emptyᵥ
  wkVal ρ Idᵥ = Idᵥ

opaque

  -- Values applied to substitutions are values

  substVal : (σ : Subst m n) → Val t → Val (t [ σ ])
  substVal σ lamᵥ = lamᵥ
  substVal σ zeroᵥ = zeroᵥ
  substVal σ sucᵥ = sucᵥ
  substVal σ starᵥ = starᵥ
  substVal σ prodᵥ = prodᵥ
  substVal σ rflᵥ = rflᵥ
  substVal σ Uᵥ = Uᵥ
  substVal σ ΠΣᵥ = ΠΣᵥ
  substVal σ ℕᵥ = ℕᵥ
  substVal σ Unitᵥ = Unitᵥ
  substVal σ Emptyᵥ = Emptyᵥ
  substVal σ Idᵥ = Idᵥ

opaque

  -- Values are non-neutrals in whnf

  Val→Whnf : Val t → Whnf t × ¬ Neutral t
  Val→Whnf lamᵥ = lamₙ , (λ ())
  Val→Whnf zeroᵥ = zeroₙ , λ ()
  Val→Whnf sucᵥ = sucₙ , λ ()
  Val→Whnf starᵥ = starₙ , λ ()
  Val→Whnf prodᵥ = prodₙ , λ ()
  Val→Whnf rflᵥ = rflₙ , λ ()
  Val→Whnf Uᵥ = Uₙ , λ ()
  Val→Whnf ΠΣᵥ = ΠΣₙ , λ ()
  Val→Whnf ℕᵥ = ℕₙ , λ ()
  Val→Whnf Unitᵥ = Unitₙ , λ ()
  Val→Whnf Emptyᵥ = Emptyₙ , λ ()
  Val→Whnf Idᵥ = Idₙ , λ ()

-- opaque

--   -- Non-neutrals in whnf are values

--   Whnf→Val : ⦃ ¬ℕ-Fullred ⦄ → Whnf t → ¬ Neutral t → Val t
--   Whnf→Val Uₙ ¬ne = Uᵥ
--   Whnf→Val ΠΣₙ ¬ne = ΠΣᵥ
--   Whnf→Val ℕₙ ¬ne = ℕᵥ
--   Whnf→Val Unitₙ ¬ne = Unitᵥ
--   Whnf→Val Emptyₙ ¬ne = Emptyᵥ
--   Whnf→Val Idₙ ¬ne = Idᵥ
--   Whnf→Val lamₙ ¬ne = lamᵥ
--   Whnf→Val zeroₙ ¬ne = zeroᵥ
--   Whnf→Val sucₙ ¬ne = sucᵥ
--   Whnf→Val starₙ ¬ne = starᵥ
--   Whnf→Val prodₙ ¬ne = prodᵥ
--   Whnf→Val rflₙ ¬ne = rflᵥ
--   Whnf→Val (ne x) ¬ne = ⊥-elim (¬ne x)

-- opaque

--   -- Val t is decidable

--   dec-Val : (t : Term n) → Dec (Val t)
--   dec-Val (lam p t) = yes lamᵥ
--   dec-Val (prod s p t u) = yes prodᵥ
--   dec-Val zero = yes zeroᵥ
--   dec-Val (suc t) = yes {!!}
--   dec-Val (star s) = yes starᵥ
--   dec-Val rfl = yes rflᵥ
--   dec-Val U = yes Uᵥ
--   dec-Val (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) = yes ΠΣᵥ
--   dec-Val ℕ = yes ℕᵥ
--   dec-Val (Unit s) = yes Unitᵥ
--   dec-Val Empty = yes Emptyᵥ
--   dec-Val (Id A t u) = yes Idᵥ
--   dec-Val (var x) = no (λ ())
--   dec-Val (t ∘ u) = no (λ ())
--   dec-Val (unitrec p q A t u) = no (λ ())
--   dec-Val (emptyrec p A t) = no (λ ())
--   dec-Val (prodrec r p q A t u) = no (λ ())
--   dec-Val (natrec p q r A z s n) = no (λ ())
--   dec-Val (fst p t) = no (λ ())
--   dec-Val (snd p t) = no (λ ())
--   dec-Val (J p q A t B u v w) = no (λ ())
--   dec-Val (K p A t B u v) = no (λ ())
--   dec-Val ([]-cong s A t u v) = no (λ ())

opaque

  -- Values are not equal to non-values

  Val≢¬Val : Val t → ¬ Val u → t ≢ u
  Val≢¬Val v ¬v refl = ¬v v

------------------------------------------------------------------------
-- Properties of the lookup relations

opaque

  -- Variable lookup with heap update is deterministic.

  lookup-det : {H : Heap m} {t : Term n} {u : Term n′}
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

opaque

  -- Variable lookup without heap update is deterministic.

  lookup-det′ : {H : Heap m} {t : Term n} {u : Term n′}
             → H ⊢ y ↦ (t , E)
             → H ⊢ y ↦ (u , E′)
             → Σ (n ≡ n′) λ p → subst Term p t ≡ u × subst (Env m) p E ≡ E′
  lookup-det′ here here = refl , refl , refl
  lookup-det′ (there d) (there d′) =
    case lookup-det′ d d′ of λ {
      (refl , refl , refl) →
    refl , refl , refl }

opaque

  -- If heap lookup with update succeeds lookup without heap update
  -- succeeds with the same result.

  ↦[]→↦ : H ⊢ y ↦[ q ] c ⨾ H′ → H ⊢ y ↦ c
  ↦[]→↦ (here x) = here
  ↦[]→↦ (there d) = there (↦[]→↦ d)

opaque

  -- Heap lookups match the corresponding substitution.

  heapSubstVar : H ⊢ y ↦[ q ] t , E ⨾ H′ → toSubstₕ H y ≡ wk E t [ H ]ₕ
  heapSubstVar {t} (here _) =
    sym (step-consSubst t)
  heapSubstVar {t} (there d) =
    trans (heapSubstVar d) (sym (step-consSubst t))

opaque

  -- Heap lookups match the corresponding substitution.

  heapSubstVar′ : H ⊢ y ↦ (t , E) → toSubstₕ H y ≡ wk E t [ H ]ₕ
  heapSubstVar′ {t} here =
    sym (step-consSubst t)
  heapSubstVar′ {t} (there d) =
    trans (heapSubstVar′ d) (sym (step-consSubst t))

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

  ⦅⦆-sgSubst : ∀ S → ⦅ S ⦆ (t [ u ]₀) ≡ ⦅ wk1ˢ S ⦆ t [ u ]₀
  ⦅⦆-sgSubst ε = refl
  ⦅⦆-sgSubst {t} {u} (e ∙ S) = begin
   ⦅ e ∙ S ⦆ (t [ u ]₀)              ≡⟨⟩
   ⦅ S ⦆ (⦅ e ⦆ᵉ (t [ u ]₀))          ≡⟨ cong ⦅ S ⦆ (⦅⦆ᵉ-sgSubst e) ⟩
   ⦅ S ⦆ (⦅ wk1ᵉ e ⦆ᵉ t [ u ]₀)       ≡⟨ ⦅⦆-sgSubst S ⟩
   ⦅ wk1ˢ S ⦆ (⦅ wk1ᵉ e ⦆ᵉ t) [ u ]₀  ≡⟨⟩
   ⦅ wk1ˢ (e ∙ S) ⦆ t [ u ]₀         ∎

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

  ⦅⦆-[,] : ∀ S → ⦅ S ⦆ (t [ u , v ]₁₀) ≡ ⦅ wk2ˢ S ⦆ t [ u , v ]₁₀
  ⦅⦆-[,] ε = refl
  ⦅⦆-[,] {t} {u} {v} (e ∙ S) = begin
    ⦅ e ∙ S ⦆ (t [ u , v ]₁₀)             ≡⟨⟩
    ⦅ S ⦆ (⦅ e ⦆ᵉ (t [ u , v ]₁₀))         ≡⟨ cong ⦅ S ⦆ (⦅⦆ᵉ-[,] e) ⟩
    ⦅ S ⦆ (⦅ wk2ᵉ e ⦆ᵉ t [ u , v ]₁₀)      ≡⟨ ⦅⦆-[,] S ⟩
    ⦅ wk2ˢ S ⦆ (⦅ wk2ᵉ e ⦆ᵉ t) [ u , v ]₁₀ ≡⟨⟩
    ⦅ wk2ˢ (e ∙ S) ⦆ t [ u , v ]₁₀        ∎

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

  ⦅⦆-cong : ∀ S → t [ σ ] ≡ u [ σ ]
         → ⦅ S ⦆ t [ σ ] ≡ ⦅ S ⦆ u [ σ ]
  ⦅⦆-cong ε t≡u = t≡u
  ⦅⦆-cong (e ∙ S) t≡u = ⦅⦆-cong S (⦅⦆ᵉ-cong e t≡u)

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

  -- Multiplicity of sucₛ k

  ∣sucₛ∣≡𝟙 : ⦃ _ : Has-nr M semiring-with-meet ⦄
           → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
           → ∀ k → ∣ sucₛ {m} k ∣ ≡ 𝟙
  ∣sucₛ∣≡𝟙 0 = refl
  ∣sucₛ∣≡𝟙 (1+ k) = trans (·-identityʳ _) (∣sucₛ∣≡𝟙 k)

opaque

  -- Multiplicity of the stack S ++ sucₛ k

  ∣S++sucₛ∣≡∣S∣ :  ⦃ _ : Has-nr M semiring-with-meet ⦄
                → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
                → (S : Stack m) → ∣ S ++ sucₛ k ∣ ≡ ∣ S ∣
  ∣S++sucₛ∣≡∣S∣ {k} ε = ∣sucₛ∣≡𝟙 k
  ∣S++sucₛ∣≡∣S∣ (e ∙ S) = ·-congʳ (∣S++sucₛ∣≡∣S∣ S)

opaque

  -- Stack concatenation

  ⦅⦆++ : ∀ S S′ → ⦅ S ++ S′ ⦆ t ≡ ⦅ S′ ⦆ (⦅ S ⦆ t)
  ⦅⦆++ ε S′ = refl
  ⦅⦆++ (e ∙ S) S′ = ⦅⦆++ S S′

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

opaque

  -- Heap equality is symmetric

  ~ʰ-sym : H ~ʰ H′ → H′ ~ʰ H
  ~ʰ-sym ε = ε
  ~ʰ-sym (H~H′ ∙ c) = ~ʰ-sym H~H′ ∙ c

opaque

  -- Heap equality is transitive

  ~ʰ-trans : H ~ʰ H′ → H′ ~ʰ H″ → H ~ʰ H″
  ~ʰ-trans ε ε = ε
  ~ʰ-trans (H~H′ ∙ c) (H′~H″ ∙ .c) = ~ʰ-trans H~H′ H′~H″ ∙ c

opaque

  -- Heap lookup without update behaves the same on equal heaps

  ~ʰ-lookup : H ~ʰ H′ → H ⊢ y ↦ c → H′ ⊢ y ↦ c
  ~ʰ-lookup (H~H′ ∙ _) here = here
  ~ʰ-lookup (H~H′ ∙ _) (there d) = there (~ʰ-lookup H~H′ d)

opaque

  -- Equal heaps are equal as substitutions

  ~ʰ-subst : H ~ʰ H′ → toSubstₕ H ≡ toSubstₕ H′
  ~ʰ-subst ε = refl
  ~ʰ-subst (H~H′ ∙ (t , E)) =
    case ~ʰ-subst H~H′ of λ
      H≡H′ →
    cong₂ consSubst H≡H′ (cong (wk E t [_]) H≡H′)

opaque

  -- An updated heap is equal to the original one (up to grades)

  update-~ʰ : H ⊢ y ↦[ q ] c ⨾ H′ → H ~ʰ H′
  update-~ʰ (here _) = ~ʰ-refl ∙ _
  update-~ʰ (there d) = update-~ʰ d ∙ _

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
