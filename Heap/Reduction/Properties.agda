------------------------------------------------------------------------
-- Properties of the heap reduction relation.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Tools.Bool
open import Heap.Options
open import Definition.Typed.Variant

module Heap.Reduction.Properties
  {a} {M : Set a} (𝕄 : Modality M)
  (type-variant : Type-variant)
  (opts : Options)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+; Nat-set)
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Relation

open import Definition.Untyped M
open import Graded.Modality.Nr-instances

open import Heap.Untyped 𝕄
open import Heap.Untyped.Properties 𝕄 type-variant
open import Heap.Reduction 𝕄 opts

open Options opts

private variable
  m n m′ n′ m″ n″ k : Nat
  t t′ u A : Term _
  H H′ H″ H‴ : Heap _
  E E′ E″ : Env _ _
  S S′ : Stack _
  p p′ q r r′ : M
  s s′ s″ : State _ _
  c : Closureₘ _ _
  x x′ : Fin _

opaque

  -- Concatenation of reduction

  _⇨*_ : s ⇒* s′ → s′ ⇒* s″ → s ⇒* s″
  id ⇨* d′ = d′
  (x ⇨ d) ⇨* d′ = x ⇨ (d ⇨* d′)

opaque

  -- Lifting normalising reduction to main reduction

  ⇒ₙ*_ : s ⇒ₙ* s′ → s ⇒* s′
  ⇒ₙ* id = id
  ⇒ₙ* (x ⇨ d) = (⇒ₙ x) ⇨ (⇒ₙ* d)

------------------------------------------------------------------------
-- The heap semantics are deterministic

opaque

  -- The normalising reduction relation is deterministic

  ⇒ₙ-det : {s′ : State m n} {s″ : State m n′}
         → (d : s ⇒ₙ s′) (d′ : s ⇒ₙ s″)
         → Σ (n ≡ n′) λ n≡n′ →
            subst (State m) n≡n′ s′ ≡ s″
  ⇒ₙ-det (varₕ d) (varₕ d′) =
    case lookup-det d d′ of λ {
      (refl , refl , refl , refl) →
    refl , refl }
  ⇒ₙ-det (varₕ′ d) (varₕ′ d′) =
    case lookup-det′ d d′ of λ {
      (refl , refl , refl) →
    refl , refl }
  ⇒ₙ-det (varₕ d) (varₕ′ d′) = ⊥-elim not-tracking-and-no-tracking
  ⇒ₙ-det (varₕ′ d) (varₕ d′) = ⊥-elim not-tracking-and-no-tracking
  ⇒ₙ-det appₕ appₕ = refl , refl
  ⇒ₙ-det fstₕ fstₕ = refl , refl
  ⇒ₙ-det sndₕ sndₕ = refl , refl
  ⇒ₙ-det prodrecₕ prodrecₕ = refl , refl
  ⇒ₙ-det natrecₕ natrecₕ = refl , refl
  ⇒ₙ-det unitrecₕ unitrecₕ = refl , refl
  ⇒ₙ-det Jₕ Jₕ = refl , refl
  ⇒ₙ-det Kₕ Kₕ = refl , refl
  ⇒ₙ-det []-congₕ []-congₕ = refl , refl

opaque

  -- The reduction relation for values is deterministic

  ⇒ᵥ-det : {s′ : State m n} {s″ : State m′ n′}
         → (d : s ⇒ᵥ s′) (d′ : s ⇒ᵥ s″)
         → Σ (m ≡ m′) λ m≡m′ → Σ (n ≡ n′) λ n≡n′ →
            subst₂ State m≡m′ n≡n′ s′ ≡ s″
  ⇒ᵥ-det lamₕ d′ = lemma d′
    where
    lemma : {H : Heap m} {t : Term (1+ n)} {s : State m′ n′}
          → ⟨ H , lam p t , E , ∘ₑ p′ u E′ ∙ S ⟩ ⇒ᵥ s
          → Σ (1+ m ≡ m′) λ m≡m′ → Σ (1+ n ≡ n′) λ n≡n′ →
            subst₂ State m≡m′ n≡n′ ⟨ H ∙ (∣ S ∣ · p , u , E′) , t , lift E , wk1ˢ S ⟩ ≡ s
    lemma lamₕ = refl , refl , refl
  ⇒ᵥ-det prodˢₕ₁ d′ = lemma d′
    where
    lemma : {H : Heap m} {t : Term n} {s : State m′ n′}
          → ⟨ H , prodˢ p t u , E , fstₑ p′ ∙ S ⟩ ⇒ᵥ s
          → Σ (m ≡ m′) λ m≡m′ → Σ (n ≡ n′) λ n≡n′ →
            subst₂ State m≡m′ n≡n′ ⟨ H , t , E , S ⟩ ≡ s
    lemma prodˢₕ₁ = refl , refl , refl
  ⇒ᵥ-det prodˢₕ₂ d′ = lemma d′
    where
    lemma : {H : Heap m} {t : Term n} {s : State m′ n′}
          → ⟨ H , prodˢ p t u , E , sndₑ p′ ∙ S ⟩ ⇒ᵥ s
          → Σ (m ≡ m′) λ m≡m′ → Σ (n ≡ n′) λ n≡n′ →
            subst₂ State m≡m′ n≡n′ ⟨ H , u , E , S ⟩ ≡ s
    lemma prodˢₕ₂ = refl , refl , refl
  ⇒ᵥ-det prodʷₕ d′ = lemma d′
    where
    lemma : {H : Heap m} {t₁ t₂ : Term n″} {u : Term (2+ n)} {s : State m′ n′}
          → ⟨ H , prodʷ p′ t₁ t₂ , E , prodrecₑ r p q A u E′ ∙ S ⟩ ⇒ᵥ s
          → Σ (2+ m ≡ m′) λ m≡m′ → Σ (2+ n ≡ n′) λ n≡n′
            → subst₂ State m≡m′ n≡n′
                ⟨ H ∙ (∣ S ∣ · r · p , t₁ , E) ∙ (∣ S ∣ · r , t₂ , step E)
                   , u , liftn E′ 2 , wk2ˢ S ⟩ ≡ s
    lemma prodʷₕ = refl , refl , refl
  ⇒ᵥ-det zeroₕ zeroₕ = refl , refl , refl
  ⇒ᵥ-det sucₕ sucₕ = refl , refl , refl
  ⇒ᵥ-det starʷₕ starʷₕ = refl , refl , refl
  ⇒ᵥ-det rflₕⱼ rflₕⱼ = refl , refl , refl
  ⇒ᵥ-det rflₕₖ rflₕₖ = refl , refl , refl
  ⇒ᵥ-det rflₕₑ rflₕₑ = refl , refl , refl

opaque

  -- The reduction relation for reducing to numerals is deterministic

  ⇒ₛ-det : {s′ : State m n} {s″ : State m n}
         → (d : s ⇒ₛ s′) (d′ : s ⇒ₛ s″)
         → s′ ≡ s″
  ⇒ₛ-det (sucₕ x) d′ = lemma d′ refl x
    where
    lemma : {H : Heap m} {t : Term n} {s : State m n}
          → ⟨ H , suc t , E , S ⟩ ⇒ₛ s
          → S ≡ sucₛ k
          → ¬ Numeral t
          → ⟨ H , t , E , sucₑ ∙ sucₛ k ⟩ ≡ s
    lemma (sucₕ x) S≡ ¬n rewrite sucₛ-injective S≡ = refl
    lemma (numₕ (sucₙ n)) S≡ ¬n = ⊥-elim (¬n n)
  ⇒ₛ-det (numₕ x) d′ = lemma d′ refl x
    where
    lemma : {H : Heap m} {t : Term n} {s : State m n}
          → ⟨ H , t , E , S ⟩ ⇒ₛ s
          → S ≡ sucₑ ∙ S′
          → Numeral t
          → ⟨ H , suc t , E , S′ ⟩ ≡ s
    lemma (sucₕ ¬n) S≡ (sucₙ n) = ⊥-elim (¬n n)
    lemma (numₕ x) S≡ n rewrite stack-injective S≡ .proj₂ = refl


opaque

  -- A state cannot reduce in both ⇒ᵥ and ⇒ₙ

  not-⇒ᵥ-and-⇒ₙ : s ⇒ᵥ s′ → s ⇒ₙ s″ → ⊥
  not-⇒ᵥ-and-⇒ₙ lamₕ ()
  not-⇒ᵥ-and-⇒ₙ prodˢₕ₁ ()
  not-⇒ᵥ-and-⇒ₙ prodˢₕ₂ ()
  not-⇒ᵥ-and-⇒ₙ prodʷₕ ()
  not-⇒ᵥ-and-⇒ₙ zeroₕ ()
  not-⇒ᵥ-and-⇒ₙ sucₕ ()
  not-⇒ᵥ-and-⇒ₙ starʷₕ ()
  not-⇒ᵥ-and-⇒ₙ rflₕⱼ ()
  not-⇒ᵥ-and-⇒ₙ rflₕₖ ()
  not-⇒ᵥ-and-⇒ₙ rflₕₑ ()

opaque

  -- A state cannot reduce in both ⇒ₛ and ⇒ᵥ

  not-⇒ₛ-and-⇒ᵥ : s ⇒ₛ s′ → s ⇒ᵥ s″ → ⊥
  not-⇒ₛ-and-⇒ᵥ (sucₕ {k = 0} x) ()
  not-⇒ₛ-and-⇒ᵥ (sucₕ {k = 1+ k} x) ()
  not-⇒ₛ-and-⇒ᵥ (numₕ x) ()

opaque

  -- A state cannot reduce in both ⇒ₛ and ⇒ₙ

  not-⇒ₛ-and-⇒ₙ : s ⇒ₛ s′ → s ⇒ₙ s″ → ⊥
  not-⇒ₛ-and-⇒ₙ (sucₕ x) ()
  not-⇒ₛ-and-⇒ₙ (numₕ zeroₙ) ()
  not-⇒ₛ-and-⇒ₙ (numₕ (sucₙ x)) ()

opaque

  -- The small-step heap semantics is deterministic.

  ⇒-det : {s′ : State m n} {s″ : State m′ n′}
        → (d : s ⇒ s′) (d′ : s ⇒ s″)
        → Σ (m ≡ m′) λ m≡m′ →
          Σ (n ≡ n′) λ n≡n′ →
            subst₂ State m≡m′ n≡n′ s′ ≡ s″
  ⇒-det (⇒ᵥ d) (⇒ᵥ d′) =
    ⇒ᵥ-det d d′
  ⇒-det (⇒ₙ d) (⇒ₙ d′) =
    case ⇒ₙ-det d d′ of λ {
      (refl , refl) →
    refl , refl , refl }
  ⇒-det (⇒ₛ d) (⇒ₛ d′) =
    refl , refl , ⇒ₛ-det d d′
  ⇒-det (⇒ₙ d) (⇒ᵥ d′) = ⊥-elim (not-⇒ᵥ-and-⇒ₙ d′ d)
  ⇒-det (⇒ₙ d) (⇒ₛ d′) = ⊥-elim (not-⇒ₛ-and-⇒ₙ d′ d)
  ⇒-det (⇒ᵥ d) (⇒ₙ d′) = ⊥-elim (not-⇒ᵥ-and-⇒ₙ d d′)
  ⇒-det (⇒ᵥ d) (⇒ₛ d′) = ⊥-elim (not-⇒ₛ-and-⇒ᵥ d′ d)
  ⇒-det (⇒ₛ d) (⇒ₙ d′) = ⊥-elim (not-⇒ₛ-and-⇒ₙ d d′)
  ⇒-det (⇒ₛ d) (⇒ᵥ d′) = ⊥-elim (not-⇒ₛ-and-⇒ᵥ d d′)

opaque

  -- The normalising reduction preserves equality
  -- in a certain way

  ⇒ₙ-norm-≡ : s ⇒ₙ s′ → norm s ≡ norm s′
  ⇒ₙ-norm-≡ {s = ⟨ _ , _ , _ , S ⟩} (varₕ d) =
    trans (⦅⦆-cong S (heapSubstVar d))
      (cong (λ x → ⦅ S ⦆ _ [ x ]) (heapUpdateSubst d))
  ⇒ₙ-norm-≡ {s = ⟨ _ , _ , _ , S ⟩} (varₕ′ d) =
    ⦅⦆-cong S (heapSubstVar′ d)
  ⇒ₙ-norm-≡ appₕ = refl
  ⇒ₙ-norm-≡ fstₕ = refl
  ⇒ₙ-norm-≡ sndₕ = refl
  ⇒ₙ-norm-≡ prodrecₕ = refl
  ⇒ₙ-norm-≡ natrecₕ = refl
  ⇒ₙ-norm-≡ unitrecₕ = refl
  ⇒ₙ-norm-≡ Jₕ = refl
  ⇒ₙ-norm-≡ Kₕ = refl
  ⇒ₙ-norm-≡ []-congₕ = refl

opaque

  ⇒ₙ*-norm-≡ : s ⇒ₙ* s′ → norm s ≡ norm s′
  ⇒ₙ*-norm-≡ id = refl
  ⇒ₙ*-norm-≡ (x ⇨ d) = trans (⇒ₙ-norm-≡ x) (⇒ₙ*-norm-≡ d)


opaque

  -- The reduction evaluating numerals preserves equality
  -- in a certain way

  ⇒ₛ-norm-≡ : s ⇒ₛ s′ → norm s ≡ norm s′
  ⇒ₛ-norm-≡ (sucₕ x) = refl
  ⇒ₛ-norm-≡ (numₕ x) = refl

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇒ₙ : ⟨ H , t , E , S ⟩ ⇒ₙ ⟨ H′ , t′ , E′ , S′ ⟩
        → ⟨ H ∙ c , t , step E , wk1ˢ S ⟩ ⇒ₙ ⟨ H′ ∙ c , t′ , step E′ , wk1ˢ S′ ⟩
  wk1-⇒ₙ (varₕ {S} d) =
    varₕ (subst (_ ⊢ _ ↦[_] _ ⨾ _) (wk-∣S∣ (step id) S) (there d))
  wk1-⇒ₙ (varₕ′ d) =
    varₕ′ (there d)
  wk1-⇒ₙ appₕ = appₕ
  wk1-⇒ₙ fstₕ = fstₕ
  wk1-⇒ₙ sndₕ = sndₕ
  wk1-⇒ₙ prodrecₕ = prodrecₕ
  wk1-⇒ₙ natrecₕ = natrecₕ
  wk1-⇒ₙ unitrecₕ = unitrecₕ
  wk1-⇒ₙ Jₕ = Jₕ
  wk1-⇒ₙ Kₕ = Kₕ
  wk1-⇒ₙ []-congₕ = []-congₕ

opaque

  -- Lifting a normalising reduction to a larger heap

  wk1-⇒ₙ* : (d : ⟨ H , t , E , S ⟩ ⇒ₙ* ⟨ H′ , t′ , E′ , S′ ⟩)
          → ⟨ H ∙ c , t , step E , wk1ˢ S ⟩ ⇒ₙ* ⟨ H′ ∙ c , t′ , step E′ , wk1ˢ S′ ⟩
  wk1-⇒ₙ* id = id
  wk1-⇒ₙ* (x ⇨ d) = wk1-⇒ₙ x ⇨ wk1-⇒ₙ* d

opaque

  -- Replacing a variable and environment in a state

  var-env-⇒ₙ : ⟨ H , var x , E , S ⟩ ⇒ₙ s
            → wkVar E x ≡ wkVar E′ x′
            → ⟨ H , var x′ , E′ , S ⟩ ⇒ₙ s
  var-env-⇒ₙ (varₕ d) eq =
    varₕ (subst (_ ⊢_↦[ _ ] _ ⨾ _) eq d)
  var-env-⇒ₙ (varₕ′ d) eq =
    varₕ′ (subst (_ ⊢_↦ _) eq d)

opaque

  -- Replacing a variable and environment in a state

  var-env-⇒ₙ* : ⟨ H , var x , E , S ⟩ ⇒ₙ* ⟨ H′ , t , E″ , S′ ⟩
             → wkVar E x ≡ wkVar E′ x′ → Normal t
             → ⟨ H , var x′ , E′ , S ⟩ ⇒ₙ* ⟨ H′ , t , E″ , S′ ⟩
  var-env-⇒ₙ* id eq (val ())
  var-env-⇒ₙ* (x ⇨ d) eq _ = var-env-⇒ₙ x eq ⇨ d

opaque

  -- Extending the stack of a reduction

  ++-⇒ₙ : ⦃ ¬Track-resources ⦄
        → ∀ S₀ → ⟨ H , t , E , S ⟩ ⇒ₙ ⟨ H′ , t′ , E′ , S′ ⟩
        → ⟨ H , t , E , S ++ S₀ ⟩ ⇒ₙ ⟨ H′ , t′ , E′ , S′ ++ S₀ ⟩
  ++-⇒ₙ S₀ (varₕ x) = ⊥-elim not-tracking-and-no-tracking
  ++-⇒ₙ S₀ (varₕ′ ⦃ (nt) ⦄ x) = varₕ′ ⦃ tr = nt ⦄ x
  ++-⇒ₙ S₀ appₕ = appₕ
  ++-⇒ₙ S₀ fstₕ = fstₕ
  ++-⇒ₙ S₀ sndₕ = sndₕ
  ++-⇒ₙ S₀ prodrecₕ = prodrecₕ
  ++-⇒ₙ S₀ natrecₕ = natrecₕ
  ++-⇒ₙ S₀ unitrecₕ = unitrecₕ
  ++-⇒ₙ S₀ Jₕ = Jₕ
  ++-⇒ₙ S₀ Kₕ = Kₕ
  ++-⇒ₙ S₀ []-congₕ = []-congₕ

opaque

  -- Extending the stack of a reduction

  ++-⇒ₙ* : ⦃ ¬Track-resources ⦄
         → ∀ S₀ → (d : ⟨ H , t , E , S ⟩ ⇒ₙ* ⟨ H′ , t′ , E′ , S′ ⟩)
         → ⟨ H , t , E , S ++ S₀ ⟩ ⇒ₙ* ⟨ H′ , t′ , E′ , S′ ++ S₀ ⟩
  ++-⇒ₙ* S₀ id = id
  ++-⇒ₙ* S₀ (x ⇨ d) = ++-⇒ₙ S₀ x ⇨ ++-⇒ₙ* S₀ d

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ₙ : (d : ⟨ H , t , E , S ⟩ ⇒ₙ ⟨ H′ , t′ , E′ , S′ ⟩)
            → ⟨ H , t , E , S ++ sucₛ k ⟩ ⇒ₙ ⟨ H′ , t′ , E′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ₙ {S} (varₕ x) =
    varₕ (subst (_ ⊢ _ ↦[_] _ ⨾ _) (sym (∣S++sucₛ∣≡∣S∣ S)) x)
  ++sucₛ-⇒ₙ (varₕ′ x) = varₕ′ x
  ++sucₛ-⇒ₙ appₕ = appₕ
  ++sucₛ-⇒ₙ fstₕ = fstₕ
  ++sucₛ-⇒ₙ sndₕ = sndₕ
  ++sucₛ-⇒ₙ prodrecₕ = prodrecₕ
  ++sucₛ-⇒ₙ natrecₕ = natrecₕ
  ++sucₛ-⇒ₙ unitrecₕ = unitrecₕ
  ++sucₛ-⇒ₙ Jₕ = Jₕ
  ++sucₛ-⇒ₙ Kₕ = Kₕ
  ++sucₛ-⇒ₙ []-congₕ = []-congₕ

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ᵥ : (d : ⟨ H , t , E , S ⟩ ⇒ᵥ ⟨ H′ , t′ , E′ , S′ ⟩)
            → ⟨ H , t , E , S ++ sucₛ k ⟩ ⇒ᵥ ⟨ H′ , t′ , E′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ᵥ {k} (lamₕ {H} {p} {t} {E} {u} {E′} {S}) =
    subst₂
      (λ x y →
         ⟨ H , lam p t , E , (∘ₑ p u E′ ∙ S) ++ sucₛ k ⟩ ⇒ᵥ
         ⟨ H ∙ (x · p , u , E′) , t , lift E , y ⟩)
      (∣S++sucₛ∣≡∣S∣ S) (wk-++sucₛ (step id) S) lamₕ
  ++sucₛ-⇒ᵥ prodˢₕ₁ = prodˢₕ₁
  ++sucₛ-⇒ᵥ prodˢₕ₂ = prodˢₕ₂
  ++sucₛ-⇒ᵥ {k} (prodʷₕ {H} {p} {t₁} {t₂} {E} {r} {q} {A} {u} {E′} {S}) =
    subst₂
      (λ x y →
         ⟨ H , prodʷ p t₁ t₂ , E , (prodrecₑ r p q A u E′ ∙ S) ++ sucₛ k ⟩ ⇒ᵥ
         ⟨ H ∙ (x · r · p , t₁ , E) ∙ (x · r , t₂ , step E) , u , liftn E′ 2 , y ⟩)
      (∣S++sucₛ∣≡∣S∣ S) (wk-++sucₛ (step (step id)) S) prodʷₕ
  ++sucₛ-⇒ᵥ zeroₕ = zeroₕ
  ++sucₛ-⇒ᵥ {k} (sucₕ {H} {t} {E} {p} {q} {r} {A} {z} {s} {E′} {S}) =
    subst₂
      (λ x y →
        ⟨ H , suc t , E , natrecₑ p q r A z s E′ ∙ S ++ sucₛ k ⟩ ⇒ᵥ
        ⟨ H ∙ (x · nr₂ p r , t , E) ∙ (x · r , _ , lift E′) , s , liftn E′ 2 , y ⟩)
      (∣S++sucₛ∣≡∣S∣ S) (wk-++sucₛ (step (step id)) S) sucₕ
  ++sucₛ-⇒ᵥ starʷₕ = starʷₕ
  ++sucₛ-⇒ᵥ rflₕⱼ = rflₕⱼ
  ++sucₛ-⇒ᵥ rflₕₖ = rflₕₖ
  ++sucₛ-⇒ᵥ rflₕₑ = rflₕₑ

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ₛ : (d : ⟨ H , t , E , S ⟩ ⇒ₛ ⟨ H′ , t′ , E′ , S′ ⟩)
            → ⟨ H , t , E , S ++ sucₛ k ⟩ ⇒ₛ ⟨ H′ , t′ , E′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ₛ {k = k′} (sucₕ {t} {H} {E} {k} x) =
    subst (λ x → ⟨ H , suc t , E , x ⟩ ⇒ₛ ⟨ H , t , E , sucₑ ∙ x ⟩)
      (sym (sucₛ++sucₛ k k′)) (sucₕ x)
  ++sucₛ-⇒ₛ (numₕ x) = numₕ x

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒ : (d : ⟨ H , t , E , S ⟩ ⇒ ⟨ H′ , t′ , E′ , S′ ⟩)
           → ⟨ H , t , E , S ++ sucₛ k ⟩ ⇒ ⟨ H′ , t′ , E′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒ (⇒ₙ d) = ⇒ₙ (++sucₛ-⇒ₙ d)
  ++sucₛ-⇒ (⇒ᵥ d) = ⇒ᵥ (++sucₛ-⇒ᵥ d)
  ++sucₛ-⇒ (⇒ₛ d) = ⇒ₛ (++sucₛ-⇒ₛ d)

opaque

  -- Extending the stack of a reduction with sucₛ

  ++sucₛ-⇒* : (d : ⟨ H , t , E , S ⟩ ⇒* ⟨ H′ , t′ , E′ , S′ ⟩)
            → ⟨ H , t , E , S ++ sucₛ k ⟩ ⇒* ⟨ H′ , t′ , E′ , S′ ++ sucₛ k ⟩
  ++sucₛ-⇒* id = id
  ++sucₛ-⇒* (x ⇨ d) = ++sucₛ-⇒ x ⇨ ++sucₛ-⇒* d

opaque

  ~ʰ-⇒ᵥ : ⟨ H , t , E , S ⟩ ⇒ᵥ ⟨ H′ , t′ , E′ , S′ ⟩ → H ~ʰ H″
        → ∃ λ H‴ → ⟨ H″ , t , E , S ⟩ ⇒ᵥ ⟨ H‴ , t′ , E′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒ᵥ lamₕ H~H″   = _ , lamₕ , H~H″ ∙ _
  ~ʰ-⇒ᵥ prodˢₕ₁ H~H″ = _ , prodˢₕ₁ , H~H″
  ~ʰ-⇒ᵥ prodˢₕ₂ H~H″ = _ , prodˢₕ₂ , H~H″
  ~ʰ-⇒ᵥ prodʷₕ H~H″ = _ , prodʷₕ , H~H″ ∙ _ ∙ _
  ~ʰ-⇒ᵥ zeroₕ H~H″  = _ , zeroₕ , H~H″
  ~ʰ-⇒ᵥ sucₕ H~H″   = _ , sucₕ , H~H″ ∙ _ ∙ _
  ~ʰ-⇒ᵥ starʷₕ H~H″ = _ , starʷₕ , H~H″
  ~ʰ-⇒ᵥ rflₕⱼ H~H″  = _ , rflₕⱼ , H~H″
  ~ʰ-⇒ᵥ rflₕₖ H~H″  = _ , rflₕₖ , H~H″
  ~ʰ-⇒ᵥ rflₕₑ H~H″  = _ , rflₕₑ , H~H″

opaque

  ~ʰ-⇒ₙ : ⦃ ¬Track-resources ⦄
        → ⟨ H , t , E , S ⟩ ⇒ₙ ⟨ H′ , t′ , E′ , S′ ⟩ → H ~ʰ H″
        → ∃ λ H‴ → ⟨ H″ , t , E , S ⟩ ⇒ₙ ⟨ H‴ , t′ , E′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒ₙ (varₕ d) H~H″  = ⊥-elim not-tracking-and-no-tracking
  ~ʰ-⇒ₙ (varₕ′ ⦃ tr = tr ⦄ d) H~H″ = _ , varₕ′ ⦃ tr = tr ⦄ (~ʰ-lookup H~H″ d) , H~H″
  ~ʰ-⇒ₙ appₕ H~H″      = _ , appₕ , H~H″
  ~ʰ-⇒ₙ fstₕ H~H″      = _ , fstₕ , H~H″
  ~ʰ-⇒ₙ sndₕ H~H″      = _ , sndₕ , H~H″
  ~ʰ-⇒ₙ prodrecₕ H~H″  = _ , prodrecₕ , H~H″
  ~ʰ-⇒ₙ natrecₕ H~H″   = _ , natrecₕ , H~H″
  ~ʰ-⇒ₙ unitrecₕ H~H″  = _ , unitrecₕ , H~H″
  ~ʰ-⇒ₙ Jₕ H~H″        = _ , Jₕ , H~H″
  ~ʰ-⇒ₙ Kₕ H~H″        = _ , Kₕ , H~H″
  ~ʰ-⇒ₙ []-congₕ H~H″  = _ , []-congₕ , H~H″

opaque

  ~ʰ-⇒ₛ : ⟨ H , t , E , S ⟩ ⇒ₛ ⟨ H′ , t′ , E′ , S′ ⟩ → H ~ʰ H″
        → ∃ λ H‴ → ⟨ H″ , t , E , S ⟩ ⇒ₛ ⟨ H‴ , t′ , E′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒ₛ (sucₕ x) H~H″ = _ , sucₕ x , H~H″
  ~ʰ-⇒ₛ (numₕ x) H~H″ = _ , numₕ x , H~H″

opaque

  -- The non resource tracking reduction behaves the same on equal heaps

  ~ʰ-⇒ : ⦃ ¬Track-resources ⦄
       → ⟨ H , t , E , S ⟩ ⇒ ⟨ H′ , t′ , E′ , S′ ⟩ → H ~ʰ H″
       → ∃ λ H‴ → ⟨ H″ , t , E , S ⟩ ⇒ ⟨ H‴ , t′ , E′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒ (⇒ₙ d) H~H″ =
    case ~ʰ-⇒ₙ d H~H″ of λ
      (_ , d′ , H′~H‴) →
    _ , ⇒ₙ d′ , H′~H‴
  ~ʰ-⇒ (⇒ᵥ d) H~H″ =
    case ~ʰ-⇒ᵥ d H~H″ of λ
      (_ , d′ , H′~H‴) →
    _ , ⇒ᵥ d′ , H′~H‴
  ~ʰ-⇒ (⇒ₛ d) H~H″ =
    case ~ʰ-⇒ₛ d H~H″ of λ
      (_ , d′ , H′~H‴) →
    _ , ⇒ₛ d′ , H′~H‴

opaque

  -- The non resource tracking reduction behaves the same on equal heaps

  ~ʰ-⇒* :  ⦃ ¬tr : ¬Track-resources ⦄
        → ⟨ H , t , E , S ⟩ ⇒* ⟨ H′ , t′ , E′ , S′ ⟩ → H ~ʰ H″
        → ∃ λ H‴ → ⟨ H″ , t , E , S ⟩ ⇒* ⟨ H‴ , t′ , E′ , S′ ⟩ × H′ ~ʰ H‴
  ~ʰ-⇒* id H~H′ =
    _ , id , H~H′
  ~ʰ-⇒* (x ⇨ d) H~H′ =
    case ~ʰ-⇒ x H~H′ of λ
      (_ , x′ , H~H″) →
    case ~ʰ-⇒* d H~H″ of λ
      (_ , d′ , H~H‴) →
    _ , (x′ ⇨ d′) , H~H‴
