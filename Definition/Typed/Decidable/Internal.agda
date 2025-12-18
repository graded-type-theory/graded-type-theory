------------------------------------------------------------------------
-- A type-checker that is internal in the sense that it is intended to
-- be used to prove some of the formalisation's lemmas (not in the
-- sense that it is implemented inside the object theory)
------------------------------------------------------------------------

-- This type-checker should work even if the Type-restrictions record,
-- and perhaps also some other things, are variables. The type-checker
-- uses terms defined in Definition.Typed.Decidable.Internal.Term. See
-- Definition.Typed.Decidable.Internal.Examples for some examples of
-- how the type-checker can be used.

{-# OPTIONS --no-occurrence-analysis #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Typed TR hiding (Trans)
open import Definition.Typed.Decidable.Internal.Constraints 𝕄
open import Definition.Typed.Decidable.Internal.Context TR
open import Definition.Typed.Decidable.Internal.Monad 𝕄
open import Definition.Typed.Decidable.Internal.Substitution 𝕄
open import Definition.Typed.Decidable.Internal.Term 𝕄
open import Definition.Typed.Decidable.Internal.Tests 𝕄
open import Definition.Typed.Decidable.Internal.Weakening 𝕄
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties.Admissible.Equality TR
open import Definition.Typed.Properties.Admissible.Erased TR
open import Definition.Typed.Properties.Admissible.Identity.Primitive TR
open import Definition.Typed.Properties.Admissible.Pi TR
open import Definition.Typed.Properties.Admissible.Sigma TR
open import Definition.Typed.Properties.Admissible.Unit TR
open import Definition.Typed.Properties.Admissible.Var TR
open import Definition.Typed.Properties.Reduction TR
open import Definition.Typed.Properties.Transparentisation TR
open import Definition.Typed.Properties.Well-formed TR
import Definition.Typed.Reasoning.Term TR as TmR
import Definition.Typed.Reasoning.Type TR as TyR
open import Definition.Typed.Stability TR
open import Definition.Typed.Substitution.Primitive TR
open import Definition.Typed.Variant
import Definition.Typed.Weakening TR as W
open import Definition.Typed.Well-formed TR

open import Definition.Untyped M as U using (_or-empty_; _»_)
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open U.Con
open U.Context-pair
open U.Opacity
open U.Strength
open U.Wk
open _or-empty_

open import Tools.Fin
open import Tools.Function hiding (ext)
import Tools.Level as L
open import Tools.Maybe as M
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

private variable
  m n n₁ n₂ n₃                              : Nat
  c                                         : Constants
  γ                                         : Contexts _
  ∇                                         : DCon _ _
  Δ Δ′ Δ₁ Δ₂ Η₁ Η₂                          : Con _ _
  Γ Γ′                                      : Cons _ _ _
  A A′ A₁ A₁′ A₂ A₂′ B t t′ t₁ t₁′ t₂ t₂′ u : Term _ _
  l                                         : Termˡ _
  σ′ σ₁ σ₂                                  : Subst _ _ _
  Cs                                        : Constraints _

------------------------------------------------------------------------
-- A lemma

private opaque

  -- A lemma used below.

  ⊢1,0 :
    ∀ {Γ : U.Cons m n} {A₁ A₂ p q} →
    Γ ⊢ U.Σʷ p , q ▷ A₁ ▹ A₂ →
    Γ U.»∙ A₁ U.»∙ A₂ ⊢ U.prod 𝕨 p (U.var x1) (U.var x0) ∷
      U.wk[ 2 ] (U.Σʷ p , q ▷ A₁ ▹ A₂)
  ⊢1,0 {A₂} ⊢Σ =
    let ⊢A₁ , ⊢A₂ , Σ-ok = inversion-ΠΣ ⊢Σ in
    prodⱼ
      (PE.subst (_⊢_ _) (PE.sym (wk-comp _ _ _)) $
       W.wk
         (PE.subst (flip (W._»_∷ʷ_⊇_ _ _) _)
            (PE.cong (_∙_ _) (PE.sym wk[]≡wk[]′)) $
          W.liftʷ W.⊇-drop $
          W.wk (W.ʷ⊇-drop (∙ ⊢A₂)) ⊢A₁)
         ⊢A₂)
      (var₁ ⊢A₂)
      (PE.subst (_⊢_∷_ _ _)
         (U.wk1 A₂                                                  ≡⟨ wk≡subst _ _ ⟩

          A₂ U.[ U.toSubst (step id) ]                              ≡⟨ (flip substVar-to-subst A₂ λ where
                                                                          x0     → PE.refl
                                                                          (_ +1) → PE.refl) ⟩
          A₂ U.[ U.sgSubst (U.var x1) U.ₛ• lift (step (step id)) ]  ≡˘⟨ subst-wk A₂ ⟩

          U.wk (lift (step (step id))) A₂ U.[ U.var x1 ]₀           ≡˘⟨ PE.cong U._[ _ ]₀ (wk-comp _ _ A₂) ⟩

          U.wk (lift (step id)) (U.wk (lift (step id)) A₂)
            U.[ U.var x1 ]₀                                         ∎) $
       var₀ ⊢A₂)
      Σ-ok

------------------------------------------------------------------------
-- Fuel

-- The type of "fuel" used to ensure termination of some definitions
-- below.

Fuel : Set
Fuel = Nat

------------------------------------------------------------------------
-- Reduction and type and equality checking

private

  -- A helper function used in the implementations of equal-sub and
  -- equal-sub′.

  equal-sub″ :
    ∀ k → Con c (k N.+ c .base-con-size) → Check c ⊤
  equal-sub″ 0 Γ = do
    is-base Γ
    return tt
  equal-sub″ (1+ k) Γ = do
    Γ , _ ← is-∙ Γ
    equal-sub″ k Γ

-- Removes top-level weaken and subst constructors.

remove-weaken-subst : Fuel → Term c n → Check c (Term c n)
remove-weaken-subst 0 _ =
  fail "No fuel left."
remove-weaken-subst (1+ n) t =
  case is-weaken-subst? t of λ where
    (just (weaken ρ t)) → remove-weaken-subst n (wk ρ t)
    (just (subst t σ))  → remove-weaken-subst n (t [ σ ])
    nothing             → return t

-- Checks that the meta-variable refers to a term. In that case the
-- term's variable context and type are returned.

is-term : Meta-var c n → Check c (Con c n × Term c n)
is-term x = do
  Μ ← ask
  case Μ .bindings x of λ where
    (_ , type _) →
      fail "Expected a term."
    (Δ , term _ A) → do
      return (Δ , A)

mutual

  -- A mutually recursive definition of reduction, type-checking and
  -- equality checking.
  --
  -- Inputs that are not checked (or for which a type is infered) are
  -- assumed to be well-formed, unless otherwise noted.
  --
  -- Things are well-formed/equal if the computation succeeds and the
  -- returned constraints are satisfiable.
  --
  -- Why is reduction defined mutually with type-checking? The
  -- implementation of reduction makes use of type-checking to avoid
  -- uses of injectivity lemmas (which do not hold unconditionally in
  -- the presence of equality reflection) in the soundness proof.
  --
  -- Some of the procedures return terms that are possibly more
  -- annotated versions of the inputs. This approach was taken because
  -- it made it possible to omit some annotations.

  -- Checks that the meta-variable refers to a type. In that case the
  -- type's variable context is returned.

  is-type :
    Fuel → DCon c m → Meta-var c n → Check c (Con c n)
  is-type n ∇ x = do
    Μ ← ask
    case Μ .bindings x of λ where
      (Δ , type _) →
        return Δ
      (Δ , term _ A) → do
        A ← red-ty n (∇ » Δ) A
        is-U A
        return Δ

  -- Reduction for types.

  red-ty : Fuel → Cons c m n → Term c n → Check c (Term c n)
  red-ty 0      _ _ = fail "No fuel left."
  red-ty (1+ n) Γ A = do
    A ← remove-weaken-subst n A
    case is-type-constructor? A of λ where
      (just _) → return A
      nothing  → do
        B ← infer-red n Γ A
        is-U B
        red-tm n Γ A B

  -- Reduction for a term with a given type.
  --
  -- Note that if the definition context's length is not a literal
  -- natural number, then the code can get stuck, due to the use of de
  -- Bruijn levels.

  -- Reduction for a term with a given type.

  red-tm : Fuel → Cons c m n → (t A : Term c n) → Check c (Term c n)
  red-tm 0      _ _ _ = fail "No fuel left."
  red-tm (1+ n) Γ t A = red-tm′ n Γ t A

  private

    -- A helper function.

    red-tm′ : Fuel → Cons c m n → (t A : Term c n) → Check c (Term c n)
    red-tm′ _ _ (meta-var x σ) _ =
      return (meta-var x σ)
    red-tm′ n Γ (weaken ρ t) A =
      red-tm n Γ (wk ρ t) A
    red-tm′ n Γ (subst t σ) A =
      red-tm n Γ (t [ σ ]) A
    red-tm′ _ _ (var x) _ =
      return (var x)
    red-tm′ n Γ (defn α) _ = do
      t , B ← definition-of (Γ .defs) α
      t     ← red-tm n (Γ .defs » ε) t B
      return (wk U.wk₀ t)
    red-tm′ _ _ (U l) _ =
      return (U l)
    red-tm′ _ _ Empty _ =
      return Empty
    red-tm′ n Γ (emptyrec p A t) _ = do
      t ← red-tm n Γ t Empty
      return (emptyrec p A t)
    red-tm′ _ _ (Unit s l) _ =
      return (Unit s l)
    red-tm′ _ _ (star s l) _ =
      return (star s l)
    red-tm′ n Γ (unitrec l p q A t₁ t₂) _ = do
      t₁ ← red-tm n Γ t₁ (Unit 𝕨 l)
      case is-star? 𝕨 l t₁ of λ where
        (just _) → red-tm n Γ t₂ (subst A (sgSubst (star 𝕨 l)))
        nothing  → return (unitrec l p q A t₁ t₂)
    red-tm′ _ _ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂) _ =
      return (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
    red-tm′ _ _ (lam p qA t) _ =
      return (lam p qA t)
    red-tm′ n Γ (t₁ ∘⟨ p ⟩ t₂) A = do
      B               ← infer-red n Γ t₁
      q , B₁ , B₂ , _ ← is-ΠΣ BMΠ p B
      t₂              ← check n Γ t₂ B₁
      equal-ty n Γ A (subst B₂ (sgSubst t₂))
      t₁ ← red-tm n Γ t₁ (ΠΣ⟨ BMΠ ⟩ p , q ▷ B₁ ▹ B₂)
      case is-lam? p t₁ of λ where
        nothing              → return (t₁ ∘⟨ p ⟩ t₂)
        (just (_ , t₁′ , _)) → do
          t₁′ ← check n (Γ »∙ B₁) t₁′ B₂
          red-tm n Γ (t₁′ [ sgSubst t₂ ]) (subst B₂ (sgSubst t₂))
    red-tm′ _ _ (prod s p qA₂ t₁ t₂) _ =
      return (prod s p qA₂ t₁ t₂)
    red-tm′ n Γ (fst p t) A = do
      B               ← infer-red n Γ t
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ 𝕤) p B
      equal-ty n Γ A B₁
      t ← red-tm n Γ t (ΠΣ⟨ BMΣ 𝕤 ⟩ p , q ▷ B₁ ▹ B₂)
      case is-prod? 𝕤 p t of λ where
        nothing                  → return (fst p t)
        (just (_ , t₁ , t₂ , _)) → do
          t₁ ← check n Γ t₁ B₁
          check n Γ t₂ (subst B₂ (sgSubst t₁))
          red-tm n Γ t₁ B₁
    red-tm′ n Γ (snd p t) A = do
      B               ← infer-red n Γ t
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ 𝕤) p B
      equal-ty n Γ A (subst B₂ (sgSubst (fst p t)))
      t ← red-tm n Γ t (ΠΣ⟨ BMΣ 𝕤 ⟩ p , q ▷ B₁ ▹ B₂)
      case is-prod? 𝕤 p t of λ where
        nothing                  → return (snd p t)
        (just (_ , t₁ , t₂ , _)) → do
          t₁ ← check n Γ t₁ B₁
          t₂ ← check n Γ t₂ (subst B₂ (sgSubst t₁))
          red-tm n Γ t₂ (subst B₂ (sgSubst t₁))
    red-tm′ n Γ (prodrec r p q B t₁ t₂) A = do
      C                ← infer-red n Γ t₁
      q′ , C₁ , C₂ , _ ← is-ΠΣ (BMΣ 𝕨) p C
      B  ← check-type n (Γ »∙ Σʷ p , q′ ▷ C₁ ▹ C₂) B
      t₁ ← red-tm n Γ t₁ (Σʷ p , q′ ▷ C₁ ▹ C₂)
      equal-ty n Γ A (subst B (sgSubst t₁))
      t₂ ←
        check n (Γ »∙ C₁ »∙ C₂) t₂
          (Term.subst B $
           cons (wkSubst 2 id)
             (prod 𝕨 p (just (q′ , weaken (lift (U.stepn id 2)) C₂))
                (var x1) (var x0)))
      case is-prod? 𝕨 p t₁ of λ where
        (just (_ , t₁₁ , t₁₂ , _)) → do
          t₁₁ ← check n Γ t₁₁ C₁
          t₁₂ ← check n Γ t₁₂ (subst C₂ (sgSubst t₁₁))
          red-tm n Γ (subst t₂ (cons (sgSubst t₁₁) t₁₂))
            (subst B (sgSubst (prod 𝕨 p (just (q′ , C₂)) t₁₁ t₁₂)))
        nothing →
          return (prodrec r p q B t₁ t₂)
    red-tm′ _ _ ℕ _ =
      return ℕ
    red-tm′ _ _ zero _ =
      return zero
    red-tm′ _ _ (suc t) _ =
      return (suc t)
    red-tm′ n Γ (natrec p q r A t₁ t₂ t₃) _ = do
      t₃ ← red-tm n Γ t₃ ℕ
      case is-zero-or-suc? t₃ of λ where
        (just (inj₁ _)) →
          red-tm n Γ t₁ (subst A (sgSubst zero))
        (just (inj₂ (t₃′ , _))) →
          red-tm n Γ
            (subst t₂ (cons (sgSubst t₃′) (natrec p q r A t₁ t₂ t₃′)))
            (subst A (sgSubst (suc t₃′)))
        nothing →
          return (natrec p q r A t₁ t₂ t₃)
    red-tm′ _ _ (Id A t₁ t₂) _ =
      return (Id A t₁ t₂)
    red-tm′ _ _ (rfl t) _ =
      return (rfl t)
    red-tm′ n Γ (J p q A₁ t₁ A₂ t₂ t₃ t₄) _ = do
      t₄ ← red-tm n Γ t₄ (Id A₁ t₁ t₃)
      case is-rfl? t₄ of λ where
        nothing  → return (J p q A₁ t₁ A₂ t₂ t₃ t₄)
        (just _) → do
          equal-tm n Γ t₁ t₃ A₁
          red-tm n Γ t₂ (subst A₂ (cons (sgSubst t₁) (rfl (just t₁))))
    red-tm′ n Γ (K p A₁ t₁ A₂ t₂ t₃) _ = do
      t₃ ← red-tm n Γ t₃ (Id A₁ t₁ t₁)
      case is-rfl? t₃ of λ where
        (just _) → red-tm n Γ t₂ (subst A₂ (sgSubst (rfl (just t₁))))
        nothing  → return (K p A₁ t₁ A₂ t₂ t₃)
    red-tm′ n Γ ([]-cong s A t₁ t₂ t₃) _ = do
      t₃ ← red-tm n Γ t₃ (Id A t₁ t₂)
      case is-rfl? t₃ of λ where
        nothing  → return ([]-cong s A t₁ t₂ t₃)
        (just _) → do
          equal-tm n Γ t₁ t₂ A
          return (rfl (just t₁))

  -- A type-checker for types.
  --
  -- The returned type is a possibly more annotated version of the
  -- input.

  check-type : Fuel → Cons c m n → Term c n → Check c (Term c n)
  check-type 0 _ _ =
    fail "No fuel left."
  check-type (1+ n) Γ A = do
    A ← remove-weaken-subst n A
    check-type′ n Γ (is-type-constructor? A)

  private

    -- A helper function.

    check-type′ :
      {A : Term c n} →
      Fuel → Cons c m n → Maybe (Is-type-constructor A) →
      Check c (Term c n)
    check-type′ n Γ (just (meta-var x σ)) = do
      Δ ← is-type n (Γ .defs) x
      σ ← check-sub n (Γ .defs) (Γ .vars) σ Δ
      return (meta-var x σ)
    check-type′ _ _ (just (U l)) =
      return (U l)
    check-type′ _ _ (just Empty) =
      return Empty
    check-type′ _ _ (just (Unit s l)) = do
      require (λ γ → Unit-allowed (⟦ s ⟧ˢ γ))
      return (Unit s l)
    check-type′ n Γ (just (ΠΣ b p q A₁ A₂)) = do
      A₁ ← check-type n Γ A₁
      A₂ ← check-type n (Γ »∙ A₁) A₂
      require (λ γ → ΠΣ-allowed (⟦ b ⟧ᵇᵐ γ) (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ))
      return (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
    check-type′ _ _ (just ℕ) =
      return ℕ
    check-type′ n Γ (just (Id A t₁ t₂)) = do
      A ← check-type n Γ A
      t₁ ← check n Γ t₁ A
      t₂ ← check n Γ t₂ A
      return (Id A t₁ t₂)
    check-type′ {A} n Γ nothing = do
      B ← infer-red n Γ A
      is-U B
      return A

  -- A type-checker for terms.
  --
  -- The returned term is a possibly more annotated version of the
  -- input.

  check : Fuel → Cons c m n → Term c n → Term c n → Check c (Term c n)
  check 0 _ _ _ =
    fail "No fuel left."
  check (1+ n) Γ t A = do
    t ← remove-weaken-subst n t
    case checkable? t of λ where
      nothing → do
        B ← infer n Γ t
        equal-ty n Γ B A
        return t
      (just t) → do
        A ← red-ty n Γ A
        check′ n Γ t A

  private

    -- A helper function.

    check′ :
      {t : Term c n} →
      Fuel → Cons c m n → Checkable t → Term c n → Check c (Term c n)
    check′ n Γ (lam p t) A = do
      q , B₁ , B₂ , _ ← is-ΠΣ BMΠ p A
      t ← check n (Γ »∙ B₁) t B₂
      return (lam p (just (q , B₁)) t)
    check′ n Γ (prod s p t₁ t₂) A = do
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ s) p A
      t₁              ← check n Γ t₁ B₁
      t₂              ← check n Γ t₂ (subst B₂ (sgSubst t₁))
      return (prod s p (just (q , B₂)) t₁ t₂)
    check′ n Γ rfl A = do
      B , t₁ , t₂ , _ ← is-Id A
      equal-tm n Γ t₁ t₂ B
      return (rfl (just t₁))

  -- Type inference.
  --
  -- The returned type is reduced.

  infer-red : Fuel → Cons c m n → Term c n → Check c (Term c n)
  infer-red n Γ t = do
    A ← infer n Γ t
    red-ty n Γ A

  -- Type inference.
  --
  -- The returned type is not guaranteed to be reduced.

  infer : Fuel → Cons c m n → Term c n → Check c (Term c n)
  infer 0 _ _ =
    fail "No fuel left."
  infer (1+ n) Γ t = do
    t   ← remove-weaken-subst n t
    inf ← inferable t
    infer′ n Γ inf

  private

    -- A helper function.

    infer′ :
      {t : Term c n} →
      Fuel → Cons c m n → Inferable t → Check c (Term c n)
    infer′ n Γ (meta-var x σ) = do
      Δ , A ← is-term x
      σ     ← check-sub n (Γ .defs) (Γ .vars) σ Δ
      return (subst A σ)
    infer′ _ Γ (var x) =
      index (Γ .vars) x
    infer′ _ Γ (defn α) = do
      A ← type-of (Γ .defs) α
      return (weaken U.wk₀ A)
    infer′ _ _ (U l) =
      return (U (suc l))
    infer′ _ _ (Unit s l) = do
      require (λ γ → Unit-allowed (⟦ s ⟧ˢ γ))
      return (U l)
    infer′ _ _ (star s l) = do
      require (λ γ → Unit-allowed (⟦ s ⟧ˢ γ))
      return (Unit s l)
    infer′ n Γ (unitrec l A t₁ t₂) = do
      A  ← check-type n (Γ »∙ Unit 𝕨 l) A
      t₁ ← check n Γ t₁ (Unit 𝕨 l)
      check n Γ t₂ (subst A (sgSubst (star 𝕨 l)))
      require (λ _ → Unit-allowed 𝕨)
      return (subst A (sgSubst t₁))
    infer′ _ _ Empty =
      return (U zero)
    infer′ n Γ (emptyrec A t) = do
      A ← check-type n Γ A
      check n Γ t Empty
      return A
    infer′ n Γ (ΠΣ b p q A₁ A₂) = do
      B₁     ← infer-red n Γ A₁
      l₁ , _ ← is-U B₁
      B₂     ← infer-red n (Γ »∙ A₁) A₂
      l₂ , _ ← is-U B₂
      require (λ γ → ΠΣ-allowed (⟦ b ⟧ᵇᵐ γ) (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ))
      return (U (l₁ ⊔ᵘ l₂))
    infer′ n Γ (lam p q A₁ t) = do
      A₁ ← check-type n Γ A₁
      A₂ ← infer n (Γ »∙ A₁) t
      require (λ γ → Π-allowed (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ))
      return (Π p , q ▷ A₁ ▹ A₂)
    infer′ n Γ (app t₁ p t₂) = do
      A               ← infer-red n Γ t₁
      _ , A₁ , A₂ , _ ← is-ΠΣ BMΠ p A
      t₂ ← check n Γ t₂ A₁
      return (subst A₂ (sgSubst t₂))
    infer′ n Γ (prod s p q A₂ t₁ t₂) = do
      A₁ ← infer n Γ t₁
      A₂ ← check-type n (Γ »∙ A₁) A₂
      check n Γ t₂ (subst A₂ (sgSubst t₁))
      require (λ γ → Σ-allowed (⟦ s ⟧ˢ γ) (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ))
      return (ΠΣ⟨ BMΣ s ⟩ p , q ▷ A₁ ▹ A₂)
    infer′ n Γ (fst p t) = do
      A          ← infer-red n Γ t
      _ , A₁ , _ ← is-ΠΣ (BMΣ 𝕤) p A
      return A₁
    infer′ n Γ (snd p t) = do
      A              ← infer-red n Γ t
      _ , _ , A₂ , _ ← is-ΠΣ (BMΣ 𝕤) p A
      return (subst A₂ (sgSubst (fst p t)))
    infer′ n Γ (prodrec p A t₁ t₂) = do
      B               ← infer-red n Γ t₁
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ 𝕨) p B
      A               ← check-type n (Γ »∙ Σʷ p , q ▷ B₁ ▹ B₂) A
      check n (Γ »∙ B₁ »∙ B₂) t₂
        (Term.subst A $
         cons (wkSubst 2 id)
           (prod 𝕨 p (just (q , weaken (lift (U.stepn id 2)) B₂))
              (var x1) (var x0)))
      return (subst A (sgSubst t₁))
    infer′ _ _ ℕ =
      return (U zero)
    infer′ _ _ zero =
      return ℕ
    infer′ n Γ (suc t) = do
      check n Γ t ℕ
      return ℕ
    infer′ n Γ (natrec A t₁ t₂ t₃) = do
      A ← check-type n (Γ »∙ ℕ) A
      check n Γ t₁ (subst A (sgSubst zero))
      check n (Γ »∙ ℕ »∙ A) t₂
        (subst A (cons (wkSubst 2 id) (suc (var x1))))
      t₃ ← check n Γ t₃ ℕ
      return (subst A (sgSubst t₃))
    infer′ n Γ (Id A t₁ t₂) = do
      B     ← infer-red n Γ A
      l , _ ← is-U B
      check n Γ t₁ A
      check n Γ t₂ A
      return (U l)
    infer′ n Γ (rfl t) = do
      A ← infer n Γ t
      return (Id A t t)
    infer′ n Γ (J A₁ t₁ A₂ t₂ t₃ t₄) = do
      A₁ ← check-type n Γ A₁
      t₁ ← check n Γ t₁ A₁
      A₂ ←
        check-type n (Γ »∙ A₁ »∙ Id (wk[ 1 ] A₁) (wk[ 1 ] t₁) (var x0))
          A₂
      check n Γ t₂ (subst A₂ (cons (sgSubst t₁) (rfl (just t₁))))
      t₃ ← check n Γ t₃ A₁
      t₄ ← check n Γ t₄ (Id A₁ t₁ t₃)
      return (subst A₂ (cons (sgSubst t₃) t₄))
    infer′ n Γ (K A₁ t₁ A₂ t₂ t₃) = do
      A₁ ← check-type n Γ A₁
      t₁ ← check n Γ t₁ A₁
      A₂ ← check-type n (Γ »∙ Id A₁ t₁ t₁) A₂
      check n Γ t₂ (subst A₂ (sgSubst (rfl (just t₁))))
      t₃ ← check n Γ t₃ (Id A₁ t₁ t₁)
      require (λ _ → K-allowed)
      return (subst A₂ (sgSubst t₃))
    infer′ n Γ ([]-cong s A t₁ t₂ t₃) = do
      A  ← check-type n Γ A
      t₁ ← check n Γ t₁ A
      t₂ ← check n Γ t₂ A
      check n Γ t₃ (Id A t₁ t₂)
      require (λ γ → []-cong-allowed (⟦ s ⟧ˢ γ))
      return (Id (Erased s A) (box s t₁) (box s t₂))

  -- A variant of infer that checks that the inferred type is U l for
  -- some universe level l. The level is returned.

  infer-U : Fuel → Cons c m n → Term c n → Check c (Termˡ (c .ls))
  infer-U n Γ A = do
    B     ← infer-red n Γ A
    l , _ ← is-U B
    return l

  -- An equality checker for variable contexts.

  equal-con : Fuel → Cons c m n → Con c n → Check c ⊤
  equal-con n Γ Δ = do
    eq ← equal-con-constructors⁼ (Γ .vars) Δ
    equal-con′ n (Γ .defs) eq

  private

    -- A helper function.

    equal-con′ :
      {Δ₁ Δ₂ : Con c n} →
      Fuel → DCon c m → Equal-con-constructors⁼ Δ₁ Δ₂ → Check c ⊤
    equal-con′ _ _ (base _) =
      return tt
    equal-con′ _ _ ε =
      return tt
    equal-con′ n ∇ (ext Δ₁ A₁ Δ₂ A₂) = do
      equal-con n (∇ » Δ₁) Δ₂
      equal-ty n (∇ » Δ₁) A₁ A₂

  -- A type-checker for substitutions.
  --
  -- The returned substitution is a possibly more annotated version of
  -- the input.

  check-sub :
    Fuel → DCon c m → Con c n₂ → Subst c n₂ n₁ → Con c n₁ →
    Check c (Subst c n₂ n₁)
  check-sub n ∇ Δ₂ id Δ₁ = do
    equal-con n (∇ » Δ₂) Δ₁
    return id
  check-sub n ∇ Δ₂ (wk1 σ) Δ₁ = do
    Δ₂ , _ ← is-∙ Δ₂
    σ      ← check-sub n ∇ Δ₂ σ Δ₁
    return (wk1 σ)
  check-sub n ∇ Δ₂ (σ ⇑) Δ₁ = do
    Δ₂ , A , _ ← is-∙ Δ₂
    Δ₁ , B , _ ← is-∙ Δ₁
    σ          ← check-sub n ∇ Δ₂ σ Δ₁
    equal-ty n (∇ » Δ₂) A (subst B σ)
    return (σ ⇑)
  check-sub n ∇ Δ₂ (cons σ t) Δ₁ = do
    Δ₁ , B , _ ← is-∙ Δ₁
    σ          ← check-sub n ∇ Δ₂ σ Δ₁
    t          ← check n (∇ » Δ₂) t (subst B σ)
    return (cons σ t)

  -- Are the two terms equal at the given type?

  equal-tm : Fuel → Cons c m n → (t₁ t₂ A : Term c n) → Check c ⊤
  equal-tm 0 _ _ _ _ =
    fail "No fuel left."
  equal-tm (1+ n) Γ t₁ t₂ A = do
    t₁ ← red-tm n Γ t₁ A
    t₂ ← red-tm n Γ t₂ A
    A  ← red-ty n Γ A
    equal-tm-red n Γ t₁ t₂ A

  -- Are the two reduced terms equal at the given reduced type?

  equal-tm-red : Fuel → Cons c m n → (t₁ t₂ A : Term c n) → Check c ⊤
  equal-tm-red n Γ t₁ t₂ A with is-type-constructorˡ? A
  … | just (meta-var _ _) =
    equal-ne-red n Γ t₁ t₂ A
  … | just (U l) =
    equal-ty-red-U n Γ t₁ t₂ l
  … | just Empty =
    equal-ne-red n Γ t₁ t₂ A
  … | just (Unit s l) =
    case s ≟ˢ 𝕤 of λ where
      (just _) → return tt
      nothing  →
        case are-star? s l t₁ t₂ of λ where
          (just _) → return tt
          nothing  →
            equal-ne-red n Γ t₁ t₂ A
              catch
            require (λ γ → L.Lift _ (Unit-with-η (⟦ s ⟧ˢ γ)))
  … | just ℕ =
    case are-zero-or-suc? t₁ t₂ of λ where
      (just (inj₁ _))             → return tt
      (just (inj₂ (t₁ , t₂ , _))) → equal-tm n Γ t₁ t₂ ℕ
      nothing                     → equal-ne-red n Γ t₁ t₂ A
  … | just (ΠΣ BMΠ p _ A₁ A₂) =
    equal-tm n (Γ »∙ A₁) (wk[ 1 ] t₁ ∘⟨ p ⟩ var x0)
      (wk[ 1 ] t₂ ∘⟨ p ⟩ var x0) A₂
  … | just (ΠΣ BMΣ-𝕤 p _ A₁ A₂) = do
    equal-tm n Γ (fst p t₁) (fst p t₂) A₁
    equal-tm n Γ (snd p t₁) (snd p t₂)
      (subst A₂ (sgSubst (fst p t₁)))
  … | just (ΠΣ BMΣ-𝕨 p _ A₁ A₂) =
    case are-prodʷ? p t₁ t₂ of λ where
      (just (_ , t₁₁ , t₁₂ , _ , t₂₁ , t₂₂ , _)) → do
        -- Here check-and-equal-tm is used instead of equal-tm to
        -- avoid uses of injectivity lemmas.
        t₁ ← check-and-equal-tm n Γ t₁₁ t₂₁ A₁
        check-and-equal-tm n Γ t₁₂ t₂₂ (subst A₂ (sgSubst t₁))
        return tt
      nothing →
        equal-ne-red n Γ t₁ t₂ A
  … | just (Id _ _ _) =
    case are-rfl? t₁ t₂ of λ where
      (just _) → return tt
      nothing  → equal-ne-red n Γ t₁ t₂ A
  … | nothing =
    equal-ne-red n Γ t₁ t₂ A

  -- Are the two possibly neutral terms equal at the given type? The
  -- terms are not assumed to be well-typed (see equal-ne-inf below
  -- for some motivation).

  equal-ne : Fuel → (Γ : Cons c m n) (t₁ t₂ A : Term c n) → Check c ⊤
  equal-ne n Γ t₁ t₂ A = do
    A′ ← equal-ne-inf n Γ t₁ t₂
    equal-ty n Γ A′ A

  -- Are the two possibly neutral terms equal at the given reduced
  -- type? The terms are not assumed to be well-typed (see
  -- equal-ne-inf below for some motivation).

  equal-ne-red :
    Fuel → (Γ : Cons c m n) (t₁ t₂ A : Term c n) → Check c ⊤
  equal-ne-red n Γ t₁ t₂ A = do
    A′ ← equal-ne-inf-red n Γ t₁ t₂
    equal-ty-red n Γ A′ A

  -- Are the two possibly neutral terms equal? In that case an
  -- inferred, reduced type is returned. The terms are not assumed to
  -- be well-typed (see equal-ne-inf below for some motivation).

  equal-ne-inf-red :
    Fuel → (Γ : Cons c m n) (t₁ t₂ : Term c n) → Check c (Term c n)
  equal-ne-inf-red n Γ t₁ t₂ = do
    A ← equal-ne-inf n Γ t₁ t₂
    red-ty n Γ A

  -- Are the two possibly neutral terms equal? In that case an
  -- inferred type is returned.
  --
  -- The test fails for (equal) variables if no inferred type is
  -- produced because the variables point to the base context.
  --
  -- The terms are not assumed to be well-typed. Instead they are
  -- checked to be well-typed. For a variant of the code without these
  -- checks (also without the check in equal-ne), and without the case
  -- for meta-variables in equal-ne-inf, it is possible to prove the
  -- following soundness result:
  --
  --   equal-ne-inf-sound :
  --     ⦃ ok : No-equality-reflection ⦄ →
  --     ∀ {B₁ B₂} n →
  --     OK (equal-ne-inf n Γ t₁ t₂) A γ →
  --     Meta-con-wf (Γ .defs) γ →
  --     ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ B₁ →
  --     ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ B₂ →
  --     (⌜ Γ ⌝ᶜ γ ⊢ B₁ ≡ ⌜ A ⌝ γ) ×
  --     (⌜ Γ ⌝ᶜ γ ⊢ B₂ ≡ ⌜ A ⌝ γ) ×
  --     ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  --
  -- However, meta-variables might not have unique types. A
  -- meta-variable that refers to the term rfl could for instance have
  -- many different types. They are treated somewhat like neutral
  -- terms in this code, but after translation they might not be
  -- neutral.
  --
  -- Having extra checks could be detrimental to performance. A way to
  -- avoid this problem might be to replace meta-variables by opaque
  -- definitions, which are neutral. However, meta-variables can refer
  -- to open terms, and at the time of writing opaque definitions
  -- cannot. Furthermore the use of de Bruijn levels can be
  -- problematic if one wants to leave a prefix of the context
  -- unspecified.
  --
  -- One aspect of the present structure of the code is that the
  -- soundness proof equal-ne-inf-sound does not use injectivity
  -- lemmas, unlike the lemma mentioned above: those lemmas are
  -- restricted in a setting with equality reflection.

  equal-ne-inf :
    Fuel → (Γ : Cons c m n) (t₁ t₂ : Term c n) → Check c (Term c n)
  equal-ne-inf              0      _ _  _  = fail "No fuel left."
  equal-ne-inf {c} {n = n′} (1+ n) Γ t₁ t₂ = do
    equal ← are-equal-eliminators t₁ t₂
    equal-ne-inf′ equal
    where
    equal-ne-inf′ : Are-equal-eliminators t₁ t₂ → Check c (Term c n′)
    equal-ne-inf′ (meta-var x₁ σ₁ x₂ σ₂ _) = do
      Δ₁ , _  ← is-term x₁
      Δ₂ , A  ← is-term x₂
      PE.refl ← equal-sub′ n Γ σ₁ Δ₁ σ₂ Δ₂
      are-equal-meta-vars x₁ x₂
      return (subst A σ₁)
    equal-ne-inf′ (var x _) =
      index (Γ .vars) x
    equal-ne-inf′ (defn α _) = do
      A ← type-of (Γ .defs) α
      return (weaken U.wk₀ A)
    equal-ne-inf′ (emptyrec A₁ t₁ A₂ t₂ _) = do
      A ← check-and-equal-ty n Γ A₁ A₂
      equal-ne-red n Γ t₁ t₂ Empty
      return A
    equal-ne-inf′ (unitrec l A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ _) = do
      A ← check-and-equal-ty n (Γ »∙ Unit 𝕨 l) A₁ A₂
      equal-ne-red n Γ t₁₁ t₂₁ (Unit 𝕨 l)
      check-and-equal-tm n Γ t₁₂ t₂₂ (subst A (sgSubst (star 𝕨 l)))
      require (λ _ → Unit-allowed 𝕨)
      return (subst A (sgSubst t₁₁))
    equal-ne-inf′ (app p t₁₁ t₁₂ t₂₁ t₂₂ _) = do
      A               ← equal-ne-inf-red n Γ t₁₁ t₂₁
      _ , A₁ , A₂ , _ ← is-ΠΣ BMΠ p A
      t₂              ← check-and-equal-tm n Γ t₁₂ t₂₂ A₁
      return (subst A₂ (sgSubst t₂))
    equal-ne-inf′ (fst p t₁′ t₂′ _) = do
      A          ← equal-ne-inf-red n Γ t₁′ t₂′
      _ , A₁ , _ ← is-ΠΣ (BMΣ 𝕤) p A
      return A₁
    equal-ne-inf′ (snd p t₁′ t₂′ _) = do
      A              ← equal-ne-inf-red n Γ t₁′ t₂′
      _ , _ , A₂ , _ ← is-ΠΣ (BMΣ 𝕤) p A
      return (subst A₂ (sgSubst (fst p t₁′)))
    equal-ne-inf′ (prodrec p A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ _) = do
      B               ← equal-ne-inf-red n Γ t₁₁ t₂₁
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ 𝕨) p B
      A ← check-and-equal-ty n (Γ »∙ Σʷ p , q ▷ B₁ ▹ B₂) A₁ A₂
      check-and-equal-tm n (Γ »∙ B₁ »∙ B₂) t₁₂ t₂₂
        (subst A
           (cons (wkSubst 2 id)
              (prod 𝕨 p (just (q , weaken (lift (U.stepn id 2)) B₂))
                 (var x1) (var x0))))
      return (subst A (sgSubst t₁₁))
    equal-ne-inf′ (natrec A₁ t₁₁ t₁₂ t₁₃ A₂ t₂₁ t₂₂ t₂₃ _) = do
      A ← check-and-equal-ty n (Γ »∙ ℕ) A₁ A₂
      check-and-equal-tm n Γ t₁₁ t₂₁ (subst A (sgSubst zero))
      check-and-equal-tm n (Γ »∙ ℕ »∙ A) t₁₂ t₂₂
        (subst A (cons (wkSubst 2 id) (suc (var x1))))
      equal-ne-red n Γ t₁₃ t₂₃ ℕ
      return (subst A (sgSubst t₁₃))
    equal-ne-inf′
      (J A₁₁ t₁₁ A₁₂ t₁₂ t₁₃ t₁₄ A₂₁ t₂₁ A₂₂ t₂₂ t₂₃ t₂₄ _) = do
      A₁ ← check-and-equal-ty n Γ A₁₁ A₂₁
      t₁ ← check-and-equal-tm n Γ t₁₁ t₂₁ A₁
      A₂ ←
        check-and-equal-ty n
          (Γ »∙ A₁ »∙ Id (wk[ 1 ] A₁) (wk[ 1 ] t₁) (var x0)) A₁₂ A₂₂
      check-and-equal-tm n Γ t₁₂ t₂₂
        (subst A₂ (cons (sgSubst t₁) (rfl (just t₁))))
      t₃ ← check-and-equal-tm n Γ t₁₃ t₂₃ A₁
      equal-ne-red n Γ t₁₄ t₂₄ (Id A₁ t₁ t₃)
      return (subst A₂ (cons (sgSubst t₃) t₁₄))
    equal-ne-inf′ (K A₁₁ t₁₁ A₁₂ t₁₂ t₁₃ A₂₁ t₂₁ A₂₂ t₂₂ t₂₃ _) = do
      A₁ ← check-and-equal-ty n Γ A₁₁ A₂₁
      t₁ ← check-and-equal-tm n Γ t₁₁ t₂₁ A₁
      A₂ ← check-and-equal-ty n (Γ »∙ Id A₁ t₁ t₁) A₁₂ A₂₂
      check-and-equal-tm n Γ t₁₂ t₂₂
        (subst A₂ (sgSubst (rfl (just t₁))))
      equal-ne-red n Γ t₁₃ t₂₃ (Id A₁ t₁ t₁)
      require (λ _ → K-allowed)
      return (subst A₂ (sgSubst t₁₃))
    equal-ne-inf′ ([]-cong s A₁ t₁₁ t₁₂ t₁₃ A₂ t₂₁ t₂₂ t₂₃ _) = do
      A  ← check-and-equal-ty n Γ A₁ A₂
      t₁ ← check-and-equal-tm n Γ t₁₁ t₂₁ A
      t₂ ← check-and-equal-tm n Γ t₁₂ t₂₂ A
      equal-ne-red n Γ t₁₃ t₂₃ (Id A t₁ t₂)
      require (λ γ → []-cong-allowed (⟦ s ⟧ˢ γ))
      return (Id (Erased s A) (box s t₁) (box s t₂))

  -- Are the two types equal?

  equal-ty : Fuel → (Γ : Cons c m n) (A₁ A₂ : Term c n) → Check c ⊤
  equal-ty 0 _ _ _ =
    fail "No fuel left."
  equal-ty (1+ n) Γ A₁ A₂ = do
    A₁ ← red-ty n Γ A₁
    A₂ ← red-ty n Γ A₂
    equal-ty-red n Γ A₁ A₂

  -- Are the two reduced types equal?

  equal-ty-red :
    Fuel → (Γ : Cons c m n) (A₁ A₂ : Term c n) → Check c ⊤
  equal-ty-red n Γ A₁ A₂ with are-equal-type-constructors? A₁ A₂
  … | just (meta-var x₁ σ₁ x₂ σ₂ _) = do
    Δ₁ ← is-type n (Γ .defs) x₁
    Δ₂ ← is-type n (Γ .defs) x₂
    PE.refl ← equal-sub′ n Γ σ₁ Δ₁ σ₂ Δ₂
    are-equal-meta-vars x₁ x₂
    return tt
  … | just (U _) =
    return tt
  … | just (Empty _) =
    return tt
  … | just (Unit _) =
    return tt
  … | just (ΠΣ A₁₁ A₁₂ A₂₁ A₂₂ _) = do
    equal-ty n Γ A₁₁ A₂₁
    equal-ty n (Γ »∙ A₁₁) A₁₂ A₂₂
  … | just (ℕ _) =
    return tt
  … | just (Id A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ _) = do
    equal-ty n Γ A₁ A₂
    equal-tm n Γ t₁₁ t₂₁ A₁
    equal-tm n Γ t₁₂ t₂₂ A₁
  … | nothing = do
    B ← equal-ne-inf-red n Γ A₁ A₂
    is-U B
    return tt

  -- Are the two reduced terms of type U l equal?
  --
  -- If equality reflection is disallowed, then it suffices to check
  -- that the terms are equal as types (see
  -- Definition.Conversion.Consequences.InverseUniv.inverseUnivEq),
  -- but that assumption is not made here.

  equal-ty-red-U :
    Fuel → (Γ : Cons c m n) (A₁ A₂ : Term c n) → Termˡ (c .ls) →
    Check c ⊤
  equal-ty-red-U n Γ A₁ A₂ l with are-equal-type-constructors? A₁ A₂
  … | just (meta-var x₁ σ₁ x₂ σ₂ _) = do
    Δ₁ , _ ← is-term x₁
    Δ₂ , A ← is-term x₂
    A      ← red-ty n (Γ .defs » Δ₂) A
    is-U[ l ] A
    PE.refl ← equal-sub′ n Γ σ₁ Δ₁ σ₂ Δ₂
    are-equal-meta-vars x₁ x₂
    return tt
  … | just (U _) =
    return tt
  … | just (Empty _) =
    return tt
  … | just (Unit _) =
    return tt
  … | just (ΠΣ A₁₁ A₁₂ A₂₁ A₂₂ _) = do
    l₁ ← infer-U n Γ A₁₁
    l₂ ← infer-U n (Γ »∙ A₁₁) A₁₂
    [ l₁ ⊔ᵘ l₂ ≟ˡ l ]with-message "Expected equal levels."
    A₂₁ ← check n Γ A₂₁ (U l₁)
    A₂₂ ← check n (Γ »∙ A₁₁) A₂₂ (U l₂)
    equal-tm n Γ A₁₁ A₂₁ (U l₁)
    equal-tm n (Γ »∙ A₁₁) A₁₂ A₂₂ (U l₂)
  … | just (ℕ _) =
    return tt
  … | just (Id A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ _) = do
    equal-tm n Γ A₁ A₂ (U l)
    equal-tm n Γ t₁₁ t₂₁ A₁
    equal-tm n Γ t₁₂ t₂₂ A₁
  … | nothing = do
    B ← equal-ne-inf-red n Γ A₁ A₂
    is-U[ l ] B
    return tt

  -- An equality checker for substitutions. This variant, unlike
  -- equal-sub below, is supposed to work for (at least some)
  -- substitutions that are not already known to be type-correct. It
  -- does this by invoking the type-checker.
  --
  -- This procedure is used by equal-ty-red and equal-ne-inf in the
  -- cases for meta-variables. Note that, even though x, x[σ₁] and
  -- x[σ₂] are well-typed, it might not be the case that σ₁ and σ₂
  -- are. This procedure addresses this by checking if σ₁ and σ₂ are
  -- well-typed.
  --
  -- Another approach might be to use a dedicated type-system in which
  -- x[σ] is only well-typed if both x and σ are. That would however
  -- lead to a fair amount of code that is very similar to existing
  -- code (a type system, inversion lemmas, possibly well-formedness
  -- lemmas, and maybe other things). If the main type system already
  -- had (perhaps optional) support for explicit substitutions, then
  -- this approach might not be so bad, though.
  --
  -- Another complication addressed by this procedure is that if n is
  -- not known, then code that checks if x₁ : Fin n and x₂ : Fin n are
  -- equal can get stuck. For that reason this code takes two "source"
  -- variable contexts, and the substitutions are allowed to have
  -- different "source" indices. If the code succeeds, then a proof of
  -- equality between the indices is returned.
  --
  -- The test compares the "source" contexts:
  --
  -- * If they are both empty, then the substitutions are equal.
  --
  -- * If they are both the base context, then it is checked that both
  --   substitutions are equal to the same number of applications of
  --   wk1 to id. The base context's size might be a meta-level
  --   variable, so no attempt is made to handle the substitution
  --   constructors _⇑ and cons, for which the source size is
  --   1+ something.
  --
  -- * If they are both non-empty, then the tails of the substitutions
  --   are compared recursively. Furthermore it is checked that the
  --   heads are type-correct and equal (the test of type-correctness
  --   would not be required if the substitutions were known to be
  --   type-correct).
  --
  --   Note that the tail operation does not add new _⇑ or cons
  --   constructors to a substitution.

  equal-sub′ :
    Fuel → Cons c m n₃ → Subst c n₃ n₁ → Con c n₁ → Subst c n₃ n₂ →
    Con c n₂ → Check c (n₁ PE.≡ n₂)
  equal-sub′ n Γ σ₁ Δ₁ σ₂ Δ₂ = do
    eq ← equal-con-constructors Δ₁ Δ₂
    case eq of λ where
      ε →
        return PE.refl
      (ext Δ₁ _ Δ₂ A) → do
        σ₁₊     ← return (tailₛ σ₁)
        PE.refl ← equal-sub′ n Γ σ₁₊ Δ₁ (tailₛ σ₂) Δ₂
        check-and-equal-tm n Γ (headₛ σ₁) (headₛ σ₂) (subst A σ₁₊)
        return PE.refl
      base → do
        both k _ ← both-wk1-id σ₁ σ₂
        equal-sub″ k (Γ .vars)
        return PE.refl

  -- A procedure that checks two types and then checks that they are
  -- equal.
  --
  -- The returned type is a possibly more annotated version of the
  -- input.

  check-and-equal-ty :
    Fuel → Cons c m n → Term c n → Term c n → Check c (Term c n)
  check-and-equal-ty n Γ A₁ A₂ = do
    A₁ ← check-type n Γ A₁
    A₂ ← check-type n Γ A₂
    equal-ty n Γ A₁ A₂
    return A₁

  -- A procedure that checks two terms of type A and then checks that
  -- the terms are equal at type A. The type is assumed to be
  -- well-formed.
  --
  -- The returned term is a possibly more annotated version of the
  -- input.

  check-and-equal-tm :
    Fuel → Cons c m n → Term c n → Term c n → Term c n →
    Check c (Term c n)
  check-and-equal-tm n Γ t₁ t₂ A = do
    t₁ ← check n Γ t₁ A
    t₂ ← check n Γ t₂ A
    equal-tm n Γ t₁ t₂ A
    return t₁

-- A procedure that checks a type and a term of the given type.
--
-- The returned term and type are possibly more annotated versions of
-- the inputs.

check-type-and-term :
  Fuel → Cons c m n → Term c n → Term c n →
  Check c (Term c n × Term c n)
check-type-and-term n Γ t A = do
  A ← check-type n Γ A
  t ← check n Γ t A
  return (t , A)

-- A procedure that checks a type and two terms, and checks that the
-- two terms are equal.

check-and-equal-type-and-terms :
  Fuel → Cons c m n → Term c n → Term c n → Term c n → Check c ⊤
check-and-equal-type-and-terms n Γ t₁ t₂ A = do
  A ← check-type n Γ A
  check-and-equal-tm n Γ t₁ t₂ A
  return tt

-- An equality checker for substitutions. This variant, unlike
-- equal-sub′, is only supposed to work for substitutions that are
-- already known to be type-correct and that have equal indices.

equal-sub :
  Fuel → Cons c m n₂ → Subst c n₂ n₁ → Subst c n₂ n₁ → Con c n₁ →
  Check c ⊤
equal-sub _ _ _ _ ε =
  return tt
equal-sub n Γ σ₁ σ₂ (Δ ∙ B) = do
  equal-sub n Γ σ₁₊ (tailₛ σ₂) Δ
  equal-tm n Γ (headₛ σ₁) (headₛ σ₂) (subst B σ₁₊)
  where
  σ₁₊ = tailₛ σ₁
equal-sub _ Γ σ₁ σ₂ base = do
  both k _ ← both-wk1-id σ₁ σ₂
  equal-sub″ k (Γ .vars)

-- A procedure that checks a variable context.
--
-- The returned context is a possibly more annotated version of the
-- input.

check-con : Fuel → DCon c m → Con c n → Check c (Con c n)
check-con _ _ (base {b}) =
  return (base {b = b})
check-con _ _ ε =
  return ε
check-con n ∇ (Δ ∙ A) = do
  Δ ← check-con n ∇ Δ
  A ← check-type n (∇ » Δ) A
  return (Δ ∙ A)

-- A procedure that checks a definition context.
--
-- The unfolding mode is required to be transitive if any opaque
-- definition is encountered (or if base (opa something) is
-- encountered).
--
-- The meta-variable context is required to be empty if a context
-- extension is encountered. An alternative might be to check that
-- meta-variables that are used in a definition do not make use of
-- that definition or any later definitions.

check-dcon : Fuel → DCon c m → Check c ⊤
check-dcon _ (base nothing) =
  return tt
check-dcon _ (base (just _)) =
  require (λ _ → L.Lift _ (unfolding-mode PE.≡ transitive))
check-dcon _ ε =
  return tt
check-dcon {c} n (∇ ∙⟨ tra ⟩[ t ∷ A ]) = do
  check-meta-con-empty
  check-dcon n ∇
  check-type-and-term n (∇ » ε) t A
  return tt
check-dcon {c} n (∇ ∙⟨ opa o ⟩[ t ∷ A ]) = do
  check-meta-con-empty
  check-dcon n ∇
  check-type n (∇ » ε) A
  check n (Trans o ∇ » ε) t A
  require (λ _ → Opacity-allowed × unfolding-mode PE.≡ transitive)

-- A procedure that checks a context pair.
--
-- The returned context pair is a possibly more annotated version of
-- the input.

check-cons : Fuel → Cons c m n → Check c (Cons c m n)
check-cons n (∇ » Γ) = do
  check-dcon n ∇
  Γ ← check-con n ∇ Γ
  return (∇ » Γ)

-- A procedure that checks a context pair, a type and a term.

check-cons-type-and-term :
  Fuel → Cons c m n → Term c n → Term c n → Check c ⊤
check-cons-type-and-term n Γ t A = do
  Γ ← check-cons n Γ
  check-type-and-term n Γ t A
  return tt

-- A procedure that checks a context pair, a type and two terms, and
-- checks that the two terms are equal.

check-and-equal-cons-type-and-terms :
  Fuel → Cons c m n → Term c n → Term c n → Term c n → Check c ⊤
check-and-equal-cons-type-and-terms n Γ t₁ t₂ A = do
  Γ ← check-cons n Γ
  check-and-equal-type-and-terms n Γ t₁ t₂ A

------------------------------------------------------------------------
-- Some observations

opaque

  -- If equality reflection is allowed, then red-tm can succeed in
  -- reducing a well-typed term without returning a WHNF.

  successful-reduction-without-WHNF :
    Equality-reflection →
    let n = 3 N.+ n
        Γ = record { defs = ε; vars = ε ∙ Empty }
        t = emptyrec ω ℕ zero
        u = t
        A = ℕ
    in
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ×
    OK (red-tm n Γ t A) u γ ×
    ¬ Whnf (⌜ Γ ⌝ᶜ γ .defs) (⌜ u ⌝ γ)
  successful-reduction-without-WHNF okᵉ =
    let ⊢Γ = ∙ Emptyⱼ εε in
    emptyrecⱼ (ℕⱼ ⊢Γ)
      (_⊢_∷_.conv (zeroⱼ ⊢Γ) $
       univ (⊢∷Empty→⊢≡∷ okᵉ (var₀ (Emptyⱼ εε)) (ℕⱼ ⊢Γ) (Emptyⱼ ⊢Γ))) ,
    ok PE.refl _ ,
    (λ { (ne (emptyrecₙ ())) })

opaque

  -- If weak unit types are allowed and Unitʷ-η holds, then the
  -- function red-tm can return a term that is not a WHNF, and that is
  -- not the result of reducing the initial term.
  --
  -- This problem could presumably be averted by checking if Unitʷ-η
  -- holds or not, but that check might get stuck at compile-time: the
  -- idea is that red should work even if the Type-restrictions record
  -- is a variable.

  successful-reduction-without-reduction-sequence :
    Unitʷ-allowed →
    Unitʷ-η →
    let n = 4 N.+ n
        Γ = emptyᶜ »∙ Unit 𝕨 zero
        t = unitrec zero ω ω ℕ
              (unitrec zero ω ω (Unit 𝕨 zero) (star 𝕨 zero) (var x0))
              zero
        u = unitrec zero ω ω ℕ (var x0) zero
        A = ℕ
    in
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ×
    OK (red-tm n Γ t A) u γ ×
    ¬ Whnf (⌜ Γ ⌝ᶜ γ .defs) (⌜ u ⌝ γ) ×
    ¬ ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ⇒* ⌜ u ⌝ γ ∷ ⌜ A ⌝ γ
  successful-reduction-without-reduction-sequence okᵘ η =
    let ⊢Unit  = Unitⱼ εε okᵘ
        ⊢Unit′ = Unitⱼ (∙ ⊢Unit) okᵘ
        ⊢ℕ     = ℕⱼ (∙ ⊢Unit′)
        ⊢ur    = unitrecⱼ′ (Unitⱼ (∙ ⊢Unit′) okᵘ) (starⱼ (∙ ⊢Unit) okᵘ)
                   (var₀ ⊢Unit)
        ⊢0     = zeroⱼ (∙ ⊢Unit)
    in
    unitrecⱼ′ ⊢ℕ ⊢ur ⊢0 ,
    ok PE.refl _ ,
    (λ { (ne (unitrecₙ no-η _)) → no-η η }) ,
    (λ where
       (t⇒u ⇨ u⇒*v) →
         case whrDetTerm t⇒u (unitrec-β-η ⊢ℕ ⊢ur ⊢0 okᵘ η) of λ {
           PE.refl →
         case whnfRed*Term u⇒*v zeroₙ of λ () })

------------------------------------------------------------------------
-- Soundness proofs

private opaque

  -- Soundness for equal-sub″.

  equal-sub″-sound :
    ∀ {k} {Δ : Con c (k N.+ c .base-con-size)} (∇ : DCon c m) →
    OK (equal-sub″ k Δ) tt γ →
    ⊢ ⌜ ∇ » Δ ⌝ᶜ γ →
    ⌜ ∇ » Δ ⌝ᶜ γ ⊢ˢʷ ⌜ wkSubst k id ⌝ˢ γ ∷ γ .⌜base⌝ .vars
  equal-sub″-sound {k = 0} _ eq ⊢base
    with inv->>= eq
  … | inv (_ , PE.refl) _ ok! =
    ⊢ˢʷ∷-idSubst ⊢base
  equal-sub″-sound {k = 1+ _} ∇ eq ⊢Γ
    with inv->>= eq
  … | inv (_ , _ , PE.refl) _ eq =
    let ⊢A = ⊢∙→⊢ ⊢Γ in
    ⊢ˢʷ∷-wk1Subst ⊢A (equal-sub″-sound ∇ eq (wf ⊢A))

opaque

  -- Soundness for remove-weaken-subst for types.

  remove-weaken-subst-sound-⊢ :
    ∀ {Γ : U.Cons m n} n →
    OK (remove-weaken-subst n A) B γ →
    Γ ⊢ ⌜ A ⌝ γ ⊎ Γ ⊢ ⌜ B ⌝ γ →
    Γ ⊢ ⌜ A ⌝ γ ≡ ⌜ B ⌝ γ
  remove-weaken-subst-sound-⊢     0      not-ok
  remove-weaken-subst-sound-⊢ {A} (1+ _) _      _
    with is-weaken-subst? A
  remove-weaken-subst-sound-⊢ (1+ n) eq (inj₁ ⊢A)
    | just (weaken _ A) =
    PE.subst (flip (_⊢_≡_ _) _) (⌜wk⌝ A) $
    remove-weaken-subst-sound-⊢ n eq $
    inj₁ (PE.subst (_⊢_ _) (PE.sym (⌜wk⌝ A)) ⊢A)
  remove-weaken-subst-sound-⊢ (1+ n) eq (inj₂ ⊢B)
    | just (weaken _ A) =
    PE.subst (flip (_⊢_≡_ _) _) (⌜wk⌝ A) $
    remove-weaken-subst-sound-⊢ n eq (inj₂ ⊢B)
  remove-weaken-subst-sound-⊢ (1+ n) eq (inj₁ ⊢A)
    | just (subst A _) =
    PE.subst (flip (_⊢_≡_ _) _) (⌜[]⌝ A) $
    remove-weaken-subst-sound-⊢ n eq $
    inj₁ (PE.subst (_⊢_ _) (PE.sym (⌜[]⌝ A)) ⊢A)
  remove-weaken-subst-sound-⊢ (1+ n) eq (inj₂ ⊢B)
    | just (subst A _) =
    PE.subst (flip (_⊢_≡_ _) _) (⌜[]⌝ A) $
    remove-weaken-subst-sound-⊢ n eq (inj₂ ⊢B)
  remove-weaken-subst-sound-⊢ (1+ _) ok! (inj₁ ⊢A)
    | nothing =
    refl ⊢A
  remove-weaken-subst-sound-⊢ (1+ _) ok! (inj₂ ⊢B)
    | nothing =
    refl ⊢B

opaque

  -- Soundness for remove-weaken-subst for terms.

  remove-weaken-subst-sound-⊢∷ :
    ∀ {Γ : U.Cons m n} {A} n →
    OK (remove-weaken-subst n t) u γ →
    Γ ⊢ ⌜ t ⌝ γ ∷ A ⊎ Γ ⊢ ⌜ u ⌝ γ ∷ A →
    Γ ⊢ ⌜ t ⌝ γ ≡ ⌜ u ⌝ γ ∷ A
  remove-weaken-subst-sound-⊢∷     0      not-ok
  remove-weaken-subst-sound-⊢∷ {t} (1+ _) _      _
    with is-weaken-subst? t
  remove-weaken-subst-sound-⊢∷ (1+ n) eq (inj₁ ⊢t)
    | just (weaken _ t) =
    PE.subst₃ (_⊢_≡_∷_ _) (⌜wk⌝ t) PE.refl PE.refl $
    remove-weaken-subst-sound-⊢∷ n eq $
    inj₁ (PE.subst (flip (_⊢_∷_ _) _) (PE.sym (⌜wk⌝ t)) ⊢t)
  remove-weaken-subst-sound-⊢∷ (1+ n) eq (inj₂ ⊢u)
    | just (weaken _ t) =
    PE.subst₃ (_⊢_≡_∷_ _) (⌜wk⌝ t) PE.refl PE.refl $
    remove-weaken-subst-sound-⊢∷ n eq (inj₂ ⊢u)
  remove-weaken-subst-sound-⊢∷ (1+ n) eq (inj₁ ⊢t)
    | just (subst t _) =
    PE.subst₃ (_⊢_≡_∷_ _) (⌜[]⌝ t) PE.refl PE.refl $
    remove-weaken-subst-sound-⊢∷ n eq $
    inj₁ (PE.subst (flip (_⊢_∷_ _) _) (PE.sym (⌜[]⌝ t)) ⊢t)
  remove-weaken-subst-sound-⊢∷ (1+ n) eq (inj₂ ⊢u)
    | just (subst t _) =
    PE.subst₃ (_⊢_≡_∷_ _) (⌜[]⌝ t) PE.refl PE.refl $
    remove-weaken-subst-sound-⊢∷ n eq (inj₂ ⊢u)
  remove-weaken-subst-sound-⊢∷ (1+ _) ok! (inj₁ ⊢t)
    | nothing =
    refl ⊢t
  remove-weaken-subst-sound-⊢∷ (1+ _) ok! (inj₂ ⊢u)
    | nothing =
    refl ⊢u

opaque

  -- Soundness for is-term.

  is-term-sound :
    {x : Meta-var c n} →
    OK (is-term x) (Δ , A) γ →
    Meta-con-wf ∇ γ →
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ ⌜ x ⌝ᵐ γ ∷ ⌜ A ⌝ γ
  is-term-sound {γ} {x} eq ⊢Μ
    with inv->>= eq
  … | inv _ ok! eq
    with γ .metas .bindings x | ⊢Μ .bindings-wf x | eq
  … | _ , type _   | _  | not-ok
  … | _ , term _ _ | ⊢t | ok!    = ⊢t

opaque mutual

  -- Soundness for red-ty.

  red-ty-sound :
    ∀ n → OK (red-ty n Γ A) B γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ B ⌝ γ
  red-ty-sound             0      not-ok
  red-ty-sound {A} {B} {γ} (1+ n) eq     ⊢Μ ⊢A
    with inv->>= eq
  … | inv A′ eq₁ eq
    with is-type-constructor? A′ | eq
  … | just _ | ok! =
    remove-weaken-subst-sound-⊢ n eq₁ (inj₁ ⊢A)
  … | nothing | eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv (_ , PE.refl) _ eq₃ =
    let ⊢A′ = infer-red-sound n eq₂ ⊢Μ (wf ⊢A) in
    ⌜ A  ⌝ γ  ≡⟨ remove-weaken-subst-sound-⊢ n eq₁ (inj₁ ⊢A) ⟩⊢
    ⌜ A′ ⌝ γ  ≡⟨ univ (red-tm-sound n eq₃ ⊢Μ ⊢A′) ⟩⊢∎
    ⌜ B  ⌝ γ  ∎
    where
    open TyR

  -- Soundness for red-tm.
  --
  -- It is not proved that the resulting term is a WHNF, or that the
  -- initial term reduces to the resulting term (only that the two
  -- terms are judgementally equal), see
  -- successful-reduction-without-reduction-sequence.

  red-tm-sound :
    ∀ n → OK (red-tm n Γ t A) u γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ u ⌝ γ ∷ ⌜ A ⌝ γ
  red-tm-sound     0      not-ok
  red-tm-sound {t} (1+ n) eq     = red-tm′-sound n t eq

  private

    -- Soundness for red-tm′

    red-tm′-sound :
      ∀ n t → OK (red-tm′ n Γ t A) u γ →
      Meta-con-wf (Γ .defs) γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ u ⌝ γ ∷ ⌜ A ⌝ γ
    red-tm′-sound _ (meta-var _ _) ok! _ ⊢x =
      refl ⊢x
    red-tm′-sound {u} {γ} n (weaken ρ t) eq ⊢Μ ⊢wk-ρ-t =
      let open TmR
          eq′ = PE.sym (⌜wk⌝ t)
      in
      U.wk ρ (⌜ t ⌝ γ)  ≡⟨ eq′ ⟩⊢≡
      ⌜ wk ρ t ⌝ γ      ≡⟨ red-tm-sound n eq ⊢Μ $
                           PE.subst (flip (_⊢_∷_ _) _) eq′ ⊢wk-ρ-t ⟩⊢∎
      ⌜ u ⌝ γ           ∎
    red-tm′-sound {u} {γ} n (subst t σ) eq ⊢Μ ⊢t[σ] =
      let open TmR
          eq′ = PE.sym (⌜[]⌝ t)
      in
      ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]  ≡⟨ eq′ ⟩⊢≡
      ⌜ t [ σ ] ⌝ γ           ≡⟨ red-tm-sound n eq ⊢Μ $
                                 PE.subst (flip (_⊢_∷_ _) _) eq′ ⊢t[σ] ⟩⊢∎
      ⌜ u ⌝ γ                 ∎
    red-tm′-sound _ (var _) ok! _ ⊢x =
      refl ⊢x
    red-tm′-sound {Γ} {A} {u} {γ} n (defn α) eq ⊢Μ ⊢α
      using inv (t , B) eq₁ eq ← inv->>= eq
      with inv->>= eq
    … | inv t′ eq₂ ok! =
      let ⊢Γ               = wfTerm ⊢α
          A′ , α↦A′ , A≡A′ = inversion-defn ⊢α
          α↦t∷B , B≡A′     = Σ.map idᶠ (λ hyp → hyp α↦A′) $
                             definition-of-sound (Γ .defs) eq₁
                               (defn-wf ⊢Γ)

          open TmR
      in
               ∷ ⌜ A ⌝ γ                ⟨ A≡A′ ⟩≡∷
               ∷ U.wk U.wk₀ A′         ˘⟨ W.wkEq (W.wk₀∷ʷ⊇ ⊢Γ) B≡A′ ⟩≡∷
      U.defn α ∷ U.wk U.wk₀ (⌜ B ⌝ γ)  ≡⟨ δ-red ⊢Γ α↦t∷B PE.refl PE.refl ⟩⊢∷
      U.wk U.wk₀ (⌜ t ⌝ γ)             ≡⟨ W.wkEqTerm (W.wk₀∷ʷ⊇ ⊢Γ) $
                                          red-tm-sound n eq₂ ⊢Μ $
                                          wf-↦∷∈ α↦t∷B (defn-wf ⊢Γ) ⟩⊢∎≡
      U.wk U.wk₀ (⌜ t′ ⌝ γ)            ≡˘⟨ ⌜wk⌝ t′ ⟩
      ⌜ wk U.wk₀ t′ ⌝ γ                ≡⟨⟩
      ⌜ u ⌝ γ                          ∎
    red-tm′-sound _ (U _) ok! _ ⊢U =
      refl ⊢U
    red-tm′-sound _ Empty ok! _ ⊢Empty =
      refl ⊢Empty
    red-tm′-sound n (emptyrec _ _ _) eq ⊢Μ ⊢er
      with inv->>= eq
    … | inv _ eq ok! =
      let ⊢A , ⊢t , ≡A = inversion-emptyrec ⊢er in
      conv (emptyrec-cong (refl ⊢A) (red-tm-sound n eq ⊢Μ ⊢t)) (sym ≡A)
    red-tm′-sound _ (Unit _ _) ok! _ ⊢Unit =
      refl ⊢Unit
    red-tm′-sound _ (star _ _) ok! _ ⊢star =
      refl ⊢star
    red-tm′-sound {A} {u} {γ} n (unitrec l p q B t₁ t₂) eq ⊢Μ ⊢ur
      with inv->>= eq
    … | inv t₁′ eq₁ eq₂
      using ⊢B , ⊢t₁ , ⊢t₂ , A≡ ← inversion-unitrec ⊢ur
          | t₁≡                 ← red-tm-sound n eq₁ ⊢Μ ⊢t₁
          | ur≡                 ← unitrec-cong′ (refl ⊢B) t₁≡ (refl ⊢t₂)
      with is-star? 𝕨 l t₁′ | eq₂
    … | just ≡star | eq₂ =
      let open TmR in
                                          ∷ ⌜ A ⌝ γ                    ⟨ A≡ ⟩≡∷
      ⌜ unitrec l p q B t₁         t₂ ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₁ ⌝ γ ]₀   ≡⟨ ur≡ ⟩⊢∷
      ⌜ unitrec l p q B t₁′        t₂ ⌝ γ                             ≡⟨ PE.cong (flip (U.unitrec _ _ _ _) _ ∘→ flip ⌜_⌝ _) ≡star ⟩⊢≡
                                                                       ⟨ substTypeEq (refl ⊢B) t₁≡ ⟩≡
                                          ∷ ⌜ B ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀   ⟨ PE.cong (⌜ B ⌝ _ U.[_]₀ ∘→ flip ⌜_⌝ _) ≡star ⟩≡∷≡
      ⌜ unitrec l p q B (star 𝕨 l) t₂ ⌝ γ ∷
        ⌜ B ⌝ γ U.[ U.starʷ (⟦ l ⟧ˡ γ) ]₀                             ⇒⟨ unitrec-β-⇒ ⊢B ⊢t₂ ⟩⊢∷
      ⌜ t₂ ⌝ γ                                                        ≡⟨ red-tm-sound n eq₂ ⊢Μ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                                         ∎
    … | nothing | ok! =
      let open TmR in
                                   ∷ ⌜ A ⌝ γ                   ⟨ A≡ ⟩≡∷
      ⌜ unitrec l p q B t₁  t₂ ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₁ ⌝ γ ]₀  ≡⟨ ur≡ ⟩⊢∷∎≡
      ⌜ unitrec l p q B t₁′ t₂ ⌝ γ                            ≡⟨⟩
      ⌜ u ⌝ γ                                                 ∎
    red-tm′-sound _ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) ok! _ ⊢ΠΣ =
      refl ⊢ΠΣ
    red-tm′-sound _ (lam _ _ _) ok! _ ⊢lam =
      refl ⊢lam
    red-tm′-sound {A} {u} {γ} n (t₁ ∘⟨ p ⟩ t₂) eq ⊢Μ ⊢app
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , B₂ , PE.refl) _ eq
      with inv->>= eq
    … | inv t₂′ eq₂ eq
      using inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv t₁′ eq₄ eq
      using ⊢A               ← wf-⊢∷ ⊢app
          | ⊢t₁              ← infer-red-sound n eq₁ ⊢Μ (wf ⊢A)
          | ⊢B₁ , ⊢B₂ , Π-ok ← inversion-ΠΣ (wf-⊢∷ ⊢t₁)
          | t₂≡t₂′           ← check-sound′ n eq₂ ⊢Μ ⊢B₁
          | _ , ⊢t₂ , ⊢t₂′   ← wf-⊢≡∷ t₂≡t₂′
          | A≡B₂[t₂′]        ← equal-ty-sound′ n eq₃ ⊢Μ ⊢A
                                 (substType ⊢B₂ ⊢t₂′)
          | t₁≡t₁′           ← red-tm-sound n eq₄ ⊢Μ ⊢t₁
          | t₁′∘t₂′≡t₁∘t₂    ← app-cong (sym′ t₁≡t₁′) (sym′ t₂≡t₂′)
      with is-lam? p t₁′ | eq
    … | just (qB₁ , t₁″ , ≡lam) | eq =
      let inv t₁‴ eq₅ eq₆ = inv->>= eq
          t₁″≡t₁‴         = check-sound′ n eq₅ ⊢Μ ⊢B₂
          _ , ⊢t₁″ , ⊢t₁‴ = wf-⊢≡∷ t₁″≡t₁‴

          open TmR
      in
                                     ∷ ⌜ A ⌝ γ                     ⟨ A≡B₂[t₂′] ⟩≡∷
      ⌜ t₁            ∘⟨ p ⟩ t₂  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₂′ ⌝ γ ]₀  ≡˘⟨ t₁′∘t₂′≡t₁∘t₂ ⟩⊢∷
      ⌜ t₁′           ∘⟨ p ⟩ t₂′ ⌝ γ                              ≡⟨ PE.cong (U._∘⟨ _ ⟩ _ ∘→ flip ⌜_⌝ _) ≡lam ⟩⊢≡
      ⌜ lam p qB₁ t₁″ ∘⟨ p ⟩ t₂′ ⌝ γ                              ⇒⟨ β-red-⇒ ⊢t₁″ ⊢t₂′ Π-ok ⟩⊢
      ⌜ t₁″ ⌝ γ U.[ ⌜ t₂′ ⌝ γ ]₀                                  ≡⟨ substTermEq t₁″≡t₁‴ (refl ⊢t₂′) ⟩⊢
      ⌜ t₁‴ ⌝ γ U.[ ⌜ t₂′ ⌝ γ ]₀                                  ≡˘⟨ ⌜[]⌝ t₁‴ ⟩⊢≡
      ⌜ t₁‴ [ sgSubst t₂′ ] ⌝ γ                                   ≡⟨ red-tm-sound n eq₆ ⊢Μ $
                                                                     PE.subst (flip (_⊢_∷_ _) _) (PE.sym (⌜[]⌝ t₁‴)) $
                                                                     substTerm ⊢t₁‴ ⊢t₂′ ⟩⊢∎
      ⌜ u ⌝ γ                                                     ∎
    … | nothing | ok! =
      let open TmR in
                           ∷ ⌜ A  ⌝ γ                    ⟨ A≡B₂[t₂′] ⟩≡∷
      ⌜ t₁  ∘⟨ p ⟩ t₂  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₂′ ⌝ γ ]₀  ≡˘⟨ t₁′∘t₂′≡t₁∘t₂ ⟩⊢∷∎≡
      ⌜ t₁′ ∘⟨ p ⟩ t₂′ ⌝ γ                              ≡⟨⟩
      ⌜ u ⌝ γ                                           ∎
    red-tm′-sound _ (prod _ _ _ _ _) ok! _ ⊢prod =
      refl ⊢prod
    red-tm′-sound {A} {u} {γ} n (fst p t) eq ⊢Μ ⊢fst
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , B₁ , _ , PE.refl) _ eq
      using inv _ eq₂ eq ← inv->>= eq
      with inv->>= eq
    … | inv t′ eq₃ eq
      using ⊢A               ← wf-⊢∷ ⊢fst
          | ⊢t               ← infer-red-sound n eq₁ ⊢Μ (wf ⊢A)
          | ⊢B₁ , ⊢B₂ , Σ-ok ← inversion-ΠΣ (wf-⊢∷ ⊢t)
          | A≡B₁             ← equal-ty-sound′ n eq₂ ⊢Μ ⊢A ⊢B₁
          | t≡t′             ← red-tm-sound n eq₃ ⊢Μ ⊢t
      with is-prod? 𝕤 p t′ | eq
    … | just (qB₂ , t₁ , t₂ , ≡prod) | eq =
      let inv t₁′ eq₄ eq  = inv->>= eq
          inv _   eq₅ eq₆ = inv->>= eq
          t₁≡t₁′          = check-sound′ n eq₄ ⊢Μ ⊢B₁
          _ , ⊢t₁ , ⊢t₁′  = wf-⊢≡∷ t₁≡t₁′
          _ , ⊢t₂ , _     = wf-⊢≡∷ $
                            check-sound′ n eq₅ ⊢Μ (substType ⊢B₂ ⊢t₁′)

          open TmR
      in
                                       ∷ ⌜ A ⌝ γ    ⟨ A≡B₁ ⟩≡∷
      ⌜ fst p t                    ⌝ γ ∷ ⌜ B₁ ⌝ γ  ≡⟨ fst-cong′ t≡t′ ⟩⊢∷
      ⌜ fst p t′                   ⌝ γ             ≡⟨ PE.cong (U.fst _ ∘→ flip ⌜_⌝ _) ≡prod ⟩⊢≡
      ⌜ fst p (prod 𝕤 p qB₂ t₁ t₂) ⌝ γ             ≡⟨ Σ-β₁-≡ ⊢B₂ ⊢t₁ (conv ⊢t₂ (substTypeEq (refl ⊢B₂) (sym′ t₁≡t₁′))) Σ-ok ⟩⊢
      ⌜ t₁ ⌝ γ                                     ≡⟨ t₁≡t₁′ ⟩⊢
      ⌜ t₁′ ⌝ γ                                    ≡⟨ red-tm-sound n eq₆ ⊢Μ ⊢t₁′ ⟩⊢∎
      ⌜ u  ⌝ γ                                     ∎
    … | nothing | ok! =
      let open TmR in
                     ∷ ⌜ A ⌝ γ    ⟨ A≡B₁ ⟩≡∷
      ⌜ fst p t  ⌝ γ ∷ ⌜ B₁ ⌝ γ  ≡⟨ fst-cong′ t≡t′ ⟩⊢∷∎≡
      ⌜ fst p t′ ⌝ γ             ≡⟨⟩
      ⌜ u ⌝ γ                    ∎
    red-tm′-sound {A} {u} {γ} n (snd p t) eq ⊢Μ ⊢fst
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , B₂ , PE.refl) _ eq
      using inv _ eq₂ eq ← inv->>= eq
      with inv->>= eq
    … | inv t′ eq₃ eq
      using ⊢A               ← wf-⊢∷ ⊢fst
          | ⊢t               ← infer-red-sound n eq₁ ⊢Μ (wf ⊢A)
          | ⊢B₁ , ⊢B₂ , Σ-ok ← inversion-ΠΣ (wf-⊢∷ ⊢t)
          | A≡B₂[fst-t]      ← equal-ty-sound′ n eq₂ ⊢Μ ⊢A
                                 (substType ⊢B₂ (fstⱼ′ ⊢t))
          | t≡t′             ← red-tm-sound n eq₃ ⊢Μ ⊢t
      with is-prod? 𝕤 p t′ | eq
    … | just (qB₂ , t₁ , t₂ , ≡prod) | eq =
      let inv t₁′ eq₄ eq  = inv->>= eq
          inv t₂′ eq₅ eq₆ = inv->>= eq
          t₁≡t₁′          = check-sound′ n eq₄ ⊢Μ ⊢B₁
          _ , ⊢t₁ , ⊢t₁′  = wf-⊢≡∷ t₁≡t₁′
          t₂≡t₂′          = check-sound′ n eq₅ ⊢Μ (substType ⊢B₂ ⊢t₁′)
          _ , ⊢t₂ , ⊢t₂′  = wf-⊢≡∷ t₂≡t₂′
          ⊢t₂             = conv ⊢t₂
                              (substTypeEq (refl ⊢B₂) (sym′ t₁≡t₁′))

          open TmR
      in
                                       ∷ ⌜ A ⌝ γ                          ⟨ A≡B₂[fst-t] ⟩≡∷
      ⌜ snd p t                    ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ fst p t ⌝ γ ]₀   ≡⟨ snd-cong′ t≡t′ ⟩⊢∷
                                                                          ⟨ substTypeEq (refl ⊢B₂) (fst-cong′ t≡t′) ⟩≡
      ⌜ snd p t′                   ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ fst p t′ ⌝ γ ]₀  ≡⟨ PE.cong (U.snd _ ∘→ flip ⌜_⌝ _) ≡prod ⟩⊢∷≡
                                                                          ⟨ PE.cong (⌜ B₂ ⌝ γ U.[_]₀ ∘→ flip ⌜_⌝ _ ∘→ fst p) ≡prod ⟩≡≡
      ⌜ snd p (prod 𝕤 p qB₂ t₁ t₂) ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ fst p (prod 𝕤 p qB₂ t₁ t₂) ⌝ γ ]₀                 ≡⟨ Σ-β₂-≡ ⊢B₂ ⊢t₁ ⊢t₂ Σ-ok ⟩⊢∷
                                                                          ⟨ substTypeEq (refl ⊢B₂) (Σ-β₁-≡ ⊢B₂ ⊢t₁ ⊢t₂ Σ-ok) ⟩≡
                                       ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₁  ⌝ γ ]₀        ⟨ substTypeEq (refl ⊢B₂) t₁≡t₁′ ⟩≡∷
      ⌜ t₂ ⌝ γ                         ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀       ≡⟨ t₂≡t₂′ ⟩⊢∷
      ⌜ t₂′ ⌝ γ                                                          ≡⟨ red-tm-sound n eq₆ ⊢Μ ⊢t₂′ ⟩⊢∎
      ⌜ u  ⌝ γ                                                           ∎
    … | nothing | ok! =
      let open TmR in
                     ∷ ⌜ A ⌝ γ                         ⟨ A≡B₂[fst-t] ⟩≡∷
      ⌜ snd p t  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ fst p t ⌝ γ ]₀  ≡⟨ snd-cong′ t≡t′ ⟩⊢∷∎≡
      ⌜ snd p t′ ⌝ γ                                  ≡⟨⟩
      ⌜ u ⌝ γ                                         ∎
    red-tm′-sound {A} {u} {γ} n (prodrec r p q B t₁ t₂) eq ⊢Μ ⊢pr
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv B′ eq₂ eq
      with inv->>= eq
    … | inv t₁′ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
      with inv->>= eq
    … | inv t₂′ eq₅ eq
      using ⊢t₁              ← infer-red-sound n eq₁ ⊢Μ (wfTerm ⊢pr)
          | ⊢Σ               ← wf-⊢∷ ⊢t₁
          | ⊢C₁ , ⊢C₂ , Σ-ok ← inversion-ΠΣ ⊢Σ
          | B≡B′             ← check-type-sound′ n eq₂ ⊢Μ (∙ ⊢Σ)
          | _ , ⊢B′          ← wf-⊢≡ B≡B′
          | t₁≡t₁′           ← red-tm-sound n eq₃ ⊢Μ ⊢t₁
          | _ , _ , ⊢t₁′     ← wf-⊢≡∷ t₁≡t₁′
          | A≡B′[t₁′]        ← equal-ty-sound′ n eq₄ ⊢Μ (wf-⊢∷ ⊢pr)
                                 (substType ⊢B′ ⊢t₁′)
          | t₂≡t₂′           ← check-sound′ n eq₅ ⊢Μ
                                 (subst↑²Type ⊢B′ (⊢1,0 ⊢Σ))
          | _ , _ , ⊢t₂′     ← wf-⊢≡∷ t₂≡t₂′
          | pr≡pr            ← prodrec-cong′ (sym B≡B′) (sym′ t₁≡t₁′)
                                 (sym′ t₂≡t₂′)
      with is-prod? 𝕨 p t₁′ | eq
    … | just (qC , t₁₁ , t₁₂ , ≡prod) | eq =
      let inv t₁₁′ eq₆ eq  = inv->>= eq
          inv t₁₂′ eq₇ eq₈ = inv->>= eq
          t₁₁≡t₁₁′         = check-sound′ n eq₆ ⊢Μ ⊢C₁
          _ , ⊢t₁₁ , ⊢t₁₁′ = wf-⊢≡∷ t₁₁≡t₁₁′
          t₁₂≡t₁₂′         = check-sound′ n eq₇ ⊢Μ (substType ⊢C₂ ⊢t₁₁′)
          _ , _ , ⊢t₁₂′    = wf-⊢≡∷ t₁₂≡t₁₂′
          t₁₂≡t₁₂′         = conv t₁₂≡t₁₂′
                               (substTypeEq (refl ⊢C₂) (sym′ t₁₁≡t₁₁′))
          _ , ⊢t₁₂ , _     = wf-⊢≡∷ t₁₂≡t₁₂′

          open TmR
      in
                                     ∷ ⌜ A ⌝ γ                      ⟨ A≡B′[t₁′] ⟩≡∷
      ⌜ prodrec r p q B  t₁  t₂  ⌝ γ ∷ ⌜ B′ ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀  ≡˘⟨ pr≡pr ⟩⊢∷
      ⌜ prodrec r p q B′ t₁′ t₂′ ⌝ γ                              ≡⟨ PE.cong (flip (U.prodrec _ _ _ _) _ ∘→ flip ⌜_⌝ _) ≡prod ⟩⊢≡
                                                                   ⟨ PE.cong (⌜ B′ ⌝ _ U.[_]₀ ∘→ flip ⌜_⌝ _) ≡prod ⟩≡≡
      ⌜ prodrec r p q B′ (prod 𝕨 p qC t₁₁ t₁₂) t₂′ ⌝ γ ∷
        ⌜ B′ ⌝ γ U.[ ⌜ prod 𝕨 p qC t₁₁ t₁₂ ⌝ γ ]₀                 ⇒⟨ prodrec-β-⇒ ⊢B′ ⊢t₁₁ ⊢t₁₂ ⊢t₂′ ⟩⊢∷
      ⌜ subst t₂′ (cons (sgSubst t₁₁) t₁₂) ⌝ γ                    ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) ([1,0]↑²[,] (⌜ B′ ⌝ _)) $
                                                                     substTermEq₂ (refl ⊢t₂′) t₁₁≡t₁₁′ t₁₂≡t₁₂′ ⟩⊢
                                                                   ⟨ substTypeEq (refl ⊢B′) (prod-cong ⊢C₂ t₁₁≡t₁₁′ t₁₂≡t₁₂′ Σ-ok) ⟩≡
      ⌜ subst t₂′ (cons (sgSubst t₁₁′) t₁₂′) ⌝ γ ∷
        ⌜ B′ ⌝ γ U.[ ⌜ prod 𝕨 p qC t₁₁′ t₁₂′ ⌝ γ ]₀               ≡⟨ red-tm-sound n eq₈ ⊢Μ $
                                                                     PE.subst (_⊢_∷_ _ _) ([1,0]↑²[,] (⌜ B′ ⌝ _)) $
                                                                     substTerm₂ ⊢t₂′ ⊢t₁₁′ ⊢t₁₂′ ⟩⊢∷∎
      ⌜ u ⌝ γ                                                     ∎
    … | nothing | ok! =
      let open TmR in
                                      ∷ ⌜ A ⌝ γ                      ⟨ A≡B′[t₁′] ⟩≡∷
      ⌜ prodrec r p q B  t₁  t₂  ⌝ γ  ∷ ⌜ B′ ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀  ≡˘⟨ pr≡pr ⟩⊢∷∎≡
      ⌜ prodrec r p q B′ t₁′ t₂′ ⌝ γ                               ≡⟨⟩
      ⌜ u ⌝ γ                                                      ∎
    red-tm′-sound _ ℕ ok! _ ⊢ℕ =
      refl ⊢ℕ
    red-tm′-sound _ zero ok! _ ⊢zero =
      refl ⊢zero
    red-tm′-sound _ (suc _) ok! _ ⊢suc =
      refl ⊢suc
    red-tm′-sound {A} {u} {γ} n (natrec p q r B t₁ t₂ t₃) eq ⊢Μ ⊢nr
      with inv->>= eq
    … | inv t₃′ eq₁ eq
      using ⊢B , ⊢t₁ , ⊢t₂ , ⊢t₃ , A≡ ← inversion-natrec ⊢nr
          | t₃≡t₃′                    ← red-tm-sound n eq₁ ⊢Μ ⊢t₃
      with is-zero-or-suc? t₃′ | eq
    … | just (inj₁ ≡zero) | eq₂ =
      let open TmR

          t₃≡0 =
            ⌜ t₃   ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′  ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) ≡zero ⟩
            U.zero      ∎
      in
                                      ∷ ⌜ A ⌝ γ                   ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃   ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡0 ⟩⊢∷
                                                                  ⟨ substTypeEq (refl ⊢B) t₃≡0 ⟩≡
      ⌜ natrec p q r B t₁ t₂ zero ⌝ γ ∷ ⌜ B ⌝ γ U.[ U.zero ]₀    ⇒⟨ natrec-zero ⊢t₁ ⊢t₂ ⟩⊢∷
      ⌜ t₁ ⌝ γ                                                   ≡⟨ red-tm-sound n eq₂ ⊢Μ ⊢t₁ ⟩⊢∎
      ⌜ u ⌝ γ                                                    ∎
    … | just (inj₂ (t₃″ , ≡suc)) | eq₂ =
      let open TmR

          t₃≡suc =
            ⌜ t₃      ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′     ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) ≡suc ⟩
            ⌜ suc t₃″ ⌝ γ  ∎
          ⊢t₃″ , _ =
            inversion-suc (wf-⊢≡∷ t₃≡suc .proj₂ .proj₂)
      in
                                           ∷ ⌜ A ⌝ γ                   ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃        ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡suc ⟩⊢∷
                                                                       ⟨ substTypeEq (refl ⊢B) t₃≡suc ⟩≡
      ⌜ natrec p q r B t₁ t₂ (suc t₃″) ⌝ γ ∷
        ⌜ B ⌝ γ U.[ ⌜ suc t₃″ ⌝ γ ]₀                                  ⇒⟨ natrec-suc ⊢t₁ ⊢t₂ ⊢t₃″ ⟩⊢∷
      ⌜ subst t₂ (cons (sgSubst t₃″) (natrec p q r B t₁ t₂ t₃″)) ⌝ γ  ≡⟨ red-tm-sound n eq₂ ⊢Μ $
                                                                         PE.subst (_⊢_∷_ _ _) (PE.sym $ substComp↑² (⌜ B ⌝ _) _) $
                                                                         substTerm₂ ⊢t₂ ⊢t₃″ (natrecⱼ ⊢t₁ ⊢t₂ ⊢t₃″) ⟩⊢∎
      ⌜ u ⌝ γ                                                         ∎
    … | nothing | ok! =
      let open TmR in
                                     ∷ ⌜ A ⌝ γ                    ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃  ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃  ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡t₃′ ⟩⊢∷∎≡
      ⌜ natrec p q r B t₁ t₂ t₃′ ⌝ γ                             ≡⟨⟩
      ⌜ u ⌝ γ                                                    ∎
    red-tm′-sound _ (Id _ _ _) ok! _ ⊢Id =
      refl ⊢Id
    red-tm′-sound _ (rfl _) ok! _ ⊢rfl =
      refl ⊢rfl
    red-tm′-sound {A} {u} {γ} n (J p q B₁ t₁ B₂ t₂ t₃ t₄) eq ⊢Μ ⊢J
      with inv->>= eq
    … | inv t₄′ eq₁ eq
      using ⊢B₁ , ⊢t₁ , ⊢B₂ , ⊢t₂ , ⊢t₃ , ⊢t₄ , A≡ ←
              inversion-J ⊢J
          | t₄≡t₄′ ←
              red-tm-sound n eq₁ ⊢Μ ⊢t₄
      with is-rfl? t₄′ | eq
    … | just (t₁? , ≡rfl) | eq =
      let open TmR

          inv _ eq₂ eq₃ = inv->>= eq
          t₁≡t₃         = equal-tm-sound′ n eq₂ ⊢Μ ⊢t₁ ⊢t₃
          t₄≡rfl        =
            ⌜ t₄  ⌝ γ  ≡⟨ t₄≡t₄′ ⟩⊢∎≡
            ⌜ t₄′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) ≡rfl ⟩
            U.rfl      ∎
      in
                                    ∷ ⌜ A ⌝ γ   ⟨ A≡ ⟩≡∷
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄ ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ , ⌜ t₄ ⌝ γ ]₁₀   ≡⟨ J-cong′ (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) (refl ⊢t₃) t₄≡rfl ⟩⊢∷
                                                ⟨ substTypeEq₂ (refl ⊢B₂) (sym′ t₁≡t₃) (PE.subst (_⊢_≡_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ t₄≡rfl) ⟩≡
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ (rfl t₁?) ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₁ ⌝ γ , U.rfl ]₁₀      ⇒⟨ J-β-⇒ t₁≡t₃ ⊢B₂ ⊢t₂ ⟩⊢∷
      ⌜ t₂ ⌝ γ                                 ≡⟨ red-tm-sound n eq₃ ⊢Μ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                  ∎
    … | nothing | ok! =
      let open TmR in
                                    ∷ ⌜ A ⌝ γ   ⟨ A≡ ⟩≡∷
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄ ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ , ⌜ t₄ ⌝ γ ]₁₀   ≡⟨ J-cong′ (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) (refl ⊢t₃) t₄≡t₄′ ⟩⊢∷∎≡
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄′ ⌝ γ           ≡⟨⟩
      ⌜ u ⌝ γ                                  ∎
    red-tm′-sound {A} {u} {γ} n (K p B₁ t₁ B₂ t₂ t₃) eq ⊢Μ ⊢K
      with inv->>= eq
    … | inv t₃′ eq₁ eq₂
      using ⊢B₁ , ⊢t₁ , ⊢B₂ , ⊢t₂ , ⊢t₃ , K-ok , A≡ ←
              inversion-K ⊢K
          | t₃≡t₃′ ←
              red-tm-sound n eq₁ ⊢Μ ⊢t₃
      with is-rfl? t₃′ | eq₂
    … | just (t₁? , eq₃) | eq₂ =
      let open TmR

          t₃≡rfl =
            ⌜ t₃  ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) eq₃ ⟩
            U.rfl      ∎
      in
                                      ∷ ⌜ A ⌝ γ                    ⟨ A≡ ⟩≡∷
      ⌜ K p B₁ t₁ B₂ t₂ t₃        ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ K-cong (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) t₃≡rfl K-ok ⟩⊢∷
                                                                   ⟨ substTypeEq (refl ⊢B₂) t₃≡rfl ⟩≡
      ⌜ K p B₁ t₁ B₂ t₂ (rfl t₁?) ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ U.rfl ]₀     ⇒⟨ K-β ⊢B₂ ⊢t₂ K-ok ⟩⊢∷
      ⌜ t₂ ⌝ γ                                                    ≡⟨ red-tm-sound n eq₂ ⊢Μ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                                     ∎
    … | nothing | ok! =
      let open TmR in
                                ∷ ⌜ A ⌝ γ                    ⟨ A≡ ⟩≡∷
      ⌜ K p B₁ t₁ B₂ t₂ t₃  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ K-cong (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) t₃≡t₃′ K-ok ⟩⊢∷∎≡
      ⌜ K p B₁ t₁ B₂ t₂ t₃′ ⌝ γ                             ≡⟨⟩
      ⌜ u ⌝ γ                                               ∎
    red-tm′-sound {A} {u} {γ} n ([]-cong s B t₁ t₂ t₃) eq ⊢Μ ⊢bc
      with inv->>= eq
    … | inv t₃′ eq₁ eq
      using ⊢B , ⊢t₁ , ⊢t₂ , ⊢t₃ , okᵇᶜ , A≡ ← inversion-[]-cong ⊢bc
          | t₃≡t₃′                           ← red-tm-sound n eq₁ ⊢Μ ⊢t₃
      with is-rfl? t₃′ | eq
    … | nothing | ok! =
      let open TmR
          module E = Erased (⟦ s ⟧ˢ γ)
      in
                                 ∷ ⌜ A ⌝ γ                        ⟨ A≡ ⟩≡∷
      ⌜ []-cong s B t₁ t₂ t₃ ⌝ γ ∷
        U.Id (E.Erased (⌜ B ⌝ γ)) E.[ ⌜ t₁ ⌝ γ ] E.[ ⌜ t₂ ⌝ γ ]  ≡⟨ []-cong-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡t₃′ okᵇᶜ ⟩⊢∷∎≡
      ⌜ []-cong s B t₁ t₂ t₃′ ⌝ γ                                ≡⟨⟩
      ⌜ u ⌝ γ                                                    ∎
    … | just (t₁? , ≡rfl) | eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let open TmR
          module E = Erased (⟦ s ⟧ˢ γ)

          t₁≡t₂  = equal-tm-sound′ n eq₂ ⊢Μ ⊢t₁ ⊢t₂
          t₃≡rfl =
            ⌜ t₃  ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) ≡rfl ⟩
            U.rfl      ∎
      in
                                 ∷ ⌜ A ⌝ γ                        ⟨ A≡ ⟩≡∷
      ⌜ []-cong s B t₁ t₂ t₃ ⌝ γ ∷
        U.Id (E.Erased (⌜ B ⌝ γ)) E.[ ⌜ t₁ ⌝ γ ] E.[ ⌜ t₂ ⌝ γ ]  ≡⟨ []-cong-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡rfl okᵇᶜ ⟩⊢∷
      ⌜ []-cong s B t₁ t₂ (rfl t₁?) ⌝ γ                          ≡⟨ subsetTerm ([]-cong-β-⇒ t₁≡t₂ okᵇᶜ) ⟩⊢∎≡
      U.rfl                                                      ≡⟨⟩
      ⌜ u ⌝ γ                                                    ∎

  -- Soundness for is-type.

  is-type-sound :
    ∀ {x : Meta-var c n} {n} →
    OK (is-type n ∇ x) Δ γ →
    Meta-con-wf ∇ γ →
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ ⌜ x ⌝ᵐ γ
  is-type-sound {γ} {x} {n} eq ⊢Μ
    with inv->>= eq
  … | inv _ ok! eq
    with γ .metas .bindings x | ⊢Μ .bindings-wf x | eq
  … | _ , type _   | ⊢A | ok! = ⊢A
  … | _ , term _ _ | ⊢t | eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , PE.refl) eq₂ ok! =
    univ (conv ⊢t (red-ty-sound n eq₁ ⊢Μ (wf-⊢∷ ⊢t)))

  -- Soundness for check-type.

  check-type-sound′ :
    ∀ n →
    OK (check-type n Γ A) A′ γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ A′ ⌝ γ
  check-type-sound′              0      not-ok
  check-type-sound′ {A} {A′} {γ} (1+ n) eq     ⊢Μ ⊢Γ =
    let inv A″ eq₁ eq₂ = inv->>= eq
        A″≡A′          = check-type′-sound (is-type-constructor? A″) eq₂
                           ⊢Μ ⊢Γ
        ⊢A″ , _        = wf-⊢≡ A″≡A′
    in
    ⌜ A ⌝ γ   ≡⟨ remove-weaken-subst-sound-⊢ n eq₁ (inj₂ ⊢A″) ⟩⊢
    ⌜ A″ ⌝ γ  ≡⟨ A″≡A′ ⟩⊢∎
    ⌜ A′ ⌝ γ  ∎
    where
    open TyR

  private

    -- Soundness for check-type′.

    check-type′-sound :
      (A-c : Maybe (Is-type-constructor A)) →
      OK (check-type′ n Γ A-c) A′ γ →
      Meta-con-wf (Γ .defs) γ →
      ⊢ ⌜ Γ ⌝ᶜ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ A′ ⌝ γ
    check-type′-sound {γ} (just (meta-var x σ)) eq ⊢Μ ⊢Γ
      using inv _ eq₁ eq ← inv->>= eq
      with inv->>= eq
    … | inv σ′ eq₂ ok!
      rewrite ⌜meta-var⌝ {γ = γ} {x = x} σ
            | ⌜meta-var⌝ {γ = γ} {x = x} σ′ =
      let ⊢x   = is-type-sound eq₁ ⊢Μ
          σ≡σ′ = check-sub-sound′ σ eq₂ ⊢Μ ⊢Γ (wf ⊢x)
      in
      subst-⊢≡ (refl ⊢x) σ≡σ′
    check-type′-sound (just (U _)) ok! _ ⊢Γ =
      refl (Uⱼ ⊢Γ)
    check-type′-sound (just Empty) ok! _ ⊢Γ =
      refl (Emptyⱼ ⊢Γ)
    check-type′-sound (just (Unit _ _)) (ok PE.refl Unit-ok) _ ⊢Γ =
      refl (Unitⱼ ⊢Γ Unit-ok)
    check-type′-sound {n} (just (ΠΣ _ _ _ _ _)) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ (ok PE.refl ΠΣ-ok) =
      let A₁≡A₁′   = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
          _ , ⊢A₁′ = wf-⊢≡ A₁≡A₁′
          A₂≡A₂′   = check-type-sound′ n eq₂ ⊢Μ (∙ ⊢A₁′)
      in
      sym (ΠΣ-cong (sym A₁≡A₁′) (sym A₂≡A₂′) ΠΣ-ok)
    check-type′-sound (just ℕ) ok! _ ⊢Γ =
      refl (ℕⱼ ⊢Γ)
    check-type′-sound {n} (just (Id _ _ _)) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let A≡A′    = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
          _ , ⊢A′ = wf-⊢≡ A≡A′
          t₁≡t₁′  = check-sound′ n eq₂ ⊢Μ ⊢A′
          t₂≡t₂′  = check-sound′ n eq₃ ⊢Μ ⊢A′
      in
      sym (Id-cong (sym A≡A′) (sym′ t₁≡t₁′) (sym′ t₂≡t₂′))
    check-type′-sound {n} nothing eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , PE.refl) _ ok! =
      refl (univ (infer-red-sound n eq₁ ⊢Μ ⊢Γ))

  -- Soundness for check.

  check-sound′ :
    ∀ n →
    OK (check n Γ t A) t′ γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ t′ ⌝ γ ∷ ⌜ A ⌝ γ
  check-sound′ 0      not-ok
  check-sound′ (1+ n) eq     _ ⊢A
    with inv->>= eq
  … | inv t″ eq₁ eq
    using t≡t″ ← remove-weaken-subst-sound-⊢∷ n eq₁
    with checkable? t″
  check-sound′ (1+ n) _ ⊢Μ ⊢A | inv _ eq₁ eq | nothing
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let ⊢t′ = infer-sound n eq₂ ⊢Μ (wf ⊢A)
        B≡A = equal-ty-sound′ n eq₃ ⊢Μ (wf-⊢∷ ⊢t′) ⊢A
    in
    t≡t″ (inj₂ (conv ⊢t′ B≡A))
  check-sound′ {t} {t′} {γ} (1+ n) _ ⊢Μ ⊢A | inv t″ eq₁ eq | just t″-c =
    let inv _ eq₂ eq₃ = inv->>= eq
        A≡A′          = red-ty-sound n eq₂ ⊢Μ ⊢A
        _ , ⊢A′       = wf-⊢≡ A≡A′
        t″≡t′         = check′-sound t″-c eq₃ ⊢Μ ⊢A′
        _ , ⊢t″ , _   = wf-⊢≡∷ t″≡t′
    in
    ⌜ t ⌝ γ   ≡⟨ t≡t″ (inj₂ (conv ⊢t″ (sym A≡A′))) ⟩⊢
    ⌜ t″ ⌝ γ  ≡⟨ conv t″≡t′ (sym A≡A′) ⟩⊢∎
    ⌜ t′ ⌝ γ  ∎
    where
    open TmR

  private

    -- Soundness for check′.

    check′-sound :
      (t-c : Checkable t) →
      OK (check′ n Γ t-c A) t′ γ →
      Meta-con-wf (Γ .defs) γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ t′ ⌝ γ ∷ ⌜ A ⌝ γ
    check′-sound {n} (lam p _) eq ⊢Μ ⊢A
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let _ , ⊢B₂ , Π-ok = inversion-ΠΣ ⊢A in
      lam-cong (check-sound′ n eq₁ ⊢Μ ⊢B₂) Π-ok
    check′-sound {n} (prod s p _ _) eq ⊢Μ ⊢A
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let ⊢B₁ , ⊢B₂ , Σ-ok = inversion-ΠΣ ⊢A
          t₁≡t₁′           = check-sound′ n eq₁ ⊢Μ ⊢B₁
          _ , _ , ⊢t₁′     = wf-⊢≡∷ t₁≡t₁′
          t₂≡t₂′           = check-sound′ n eq₂ ⊢Μ (substType ⊢B₂ ⊢t₁′)
      in
      sym′ (prod-cong ⊢B₂ (sym′ t₁≡t₁′) (sym′ t₂≡t₂′) Σ-ok)
    check′-sound {n} rfl eq ⊢Μ ⊢A
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let _ , ⊢t₁ , ⊢t₂ = inversion-Id ⊢A in
      refl (rflⱼ′ (equal-tm-sound′ n eq₁ ⊢Μ ⊢t₁ ⊢t₂))

  -- Soundness for infer-red.

  infer-red-sound :
    ∀ n →
    OK (infer-red n Γ t) A γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  infer-red-sound n eq ⊢Μ ⊢Γ =
    let inv _ eq₁ eq₂ = inv->>= eq
        ⊢t            = infer-sound n eq₁ ⊢Μ ⊢Γ
    in
    conv ⊢t (red-ty-sound n eq₂ ⊢Μ (wf-⊢∷ ⊢t))

  -- Soundness for infer.

  infer-sound :
    ∀ n →
    OK (infer n Γ t) A γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  infer-sound 0      not-ok
  infer-sound (1+ n) eq     ⊢Μ ⊢Γ =
    let inv _ eq₁ eq = inv->>= eq
        inv t-i _ eq = inv->>= eq
        t≡t′         = remove-weaken-subst-sound-⊢∷ n eq₁ $
                       inj₂ (infer′-sound t-i eq ⊢Μ ⊢Γ)
        _ , ⊢t , _   = wf-⊢≡∷ t≡t′
    in
    ⊢t

  private

    -- Soundness for infer′.

    infer′-sound :
      (t-i : Inferable t) →
      OK (infer′ n Γ t-i) A γ →
      Meta-con-wf (Γ .defs) γ →
      ⊢ ⌜ Γ ⌝ᶜ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
    infer′-sound {γ} (meta-var x σ) eq ⊢Μ ⊢Γ
      rewrite ⌜meta-var⌝ {γ = γ} {x = x} σ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let ⊢t   = is-term-sound eq₁ ⊢Μ
          ⊢Δ   = wfTerm ⊢t
          σ≡σ′ = check-sub-sound′ σ eq₂ ⊢Μ ⊢Γ ⊢Δ
      in
      wf-⊢≡∷ (subst-⊢≡∷ (refl ⊢t) (sym-⊢ˢʷ≡∷ ⊢Δ σ≡σ′)) .proj₂ .proj₂
    infer′-sound {Γ} (var _) eq _ ⊢Γ =
      var ⊢Γ (index-sound (Γ .vars) eq .proj₁ PE.refl)
    infer′-sound {Γ} (defn _) eq _ ⊢Γ
      with inv->>= eq
    … | inv _ eq ok! =
      defn ⊢Γ (type-of-sound (Γ .defs) eq) PE.refl
    infer′-sound (U _) ok! _ ⊢Γ =
      Uⱼ ⊢Γ
    infer′-sound (Unit _ _) (ok PE.refl Unit-ok) _ ⊢Γ =
      Unitⱼ ⊢Γ Unit-ok
    infer′-sound (star _ _) (ok PE.refl Unit-ok) _ ⊢Γ =
      starⱼ ⊢Γ Unit-ok
    infer′-sound {n} (unitrec _ A _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ (ok PE.refl Unit-ok) =
      let ⊢Unit   = Unitⱼ ⊢Γ Unit-ok
          A≡A′    = check-type-sound′ n eq₁ ⊢Μ (∙ ⊢Unit)
          _ , ⊢A′ = wf-⊢≡ A≡A′
          t₁≡t₁′  = check-sound′ n eq₂ ⊢Μ ⊢Unit
          t₂≡t₂′  = check-sound′ n eq₃ ⊢Μ $
                    substType ⊢A′ (starⱼ ⊢Γ Unit-ok)
      in
      wf-⊢≡∷ (unitrec-cong′ (sym A≡A′) (sym′ t₁≡t₁′) (sym′ t₂≡t₂′))
        .proj₂ .proj₂
    infer′-sound Empty ok! _ ⊢Γ =
      Emptyⱼ ⊢Γ
    infer′-sound {n} (emptyrec _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let A≡A′ = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
          t≡t′ = check-sound′ n eq₂ ⊢Μ (Emptyⱼ ⊢Γ)
      in
      wf-⊢≡∷ (emptyrec-cong (sym A≡A′) (sym′ t≡t′)) .proj₂ .proj₂
    infer′-sound {n} (ΠΣ _ _ _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv (_ , PE.refl) _ (ok PE.refl ΠΣ-ok) =
      let ⊢A₁ = infer-red-sound n eq₁ ⊢Μ ⊢Γ
          ⊢A₂ = infer-red-sound n eq₂ ⊢Μ (∙ univ ⊢A₁)
      in
      ΠΣⱼ ⊢A₁ ⊢A₂ ΠΣ-ok
    infer′-sound {n} (lam _ _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ (ok PE.refl Π-ok) ok! =
      let A₁≡A₁′   = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
          _ , ⊢A₁′ = wf-⊢≡ A₁≡A₁′
          ⊢t       = infer-sound n eq₂ ⊢Μ (∙ ⊢A₁′)
      in
      lamⱼ′ Π-ok ⊢t
    infer′-sound {n} (app _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , A₂ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let ⊢t₁     = infer-red-sound n eq₁ ⊢Μ ⊢Γ
          ⊢A₁ , _ = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
          t₂≡t₂′  = check-sound′ n eq₂ ⊢Μ ⊢A₁
      in
      wf-⊢≡∷ (app-cong (refl ⊢t₁) (sym′ t₂≡t₂′)) .proj₂ .proj₂
    infer′-sound {n} (prod _ _ _ _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      using inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ (ok PE.refl Σ-ok) ok! =
      let ⊢t₁      = infer-sound n eq₁ ⊢Μ ⊢Γ
          ⊢A₁      = wf-⊢∷ ⊢t₁
          A₂≡A₂′   = check-type-sound′ n eq₂ ⊢Μ (∙ ⊢A₁)
          _ , ⊢A₂′ = wf-⊢≡ A₂≡A₂′
          t₂≡t₂′   = check-sound′ n eq₃ ⊢Μ (substType ⊢A₂′ ⊢t₁)
      in
      wf-⊢≡∷ (prod-cong ⊢A₂′ (refl ⊢t₁) t₂≡t₂′ Σ-ok) .proj₂ .proj₁
    infer′-sound {n} (fst _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ ok! =
      let ⊢t = infer-red-sound n eq₁ ⊢Μ ⊢Γ in
      fstⱼ′ ⊢t
    infer′-sound {n} (snd _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ ok! =
      let ⊢t = infer-red-sound n eq₁ ⊢Μ ⊢Γ in
      sndⱼ′ ⊢t
    infer′-sound {n} (prodrec _ _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let ⊢t₁          = infer-red-sound n eq₁ ⊢Μ ⊢Γ
          ⊢ΣB₁B₂       = wf-⊢∷ ⊢t₁
          _ , _ , Σ-ok = inversion-ΠΣ ⊢ΣB₁B₂
          A≡A′         = check-type-sound′ n eq₂ ⊢Μ (∙ ⊢ΣB₁B₂)
          _ , ⊢A′      = wf-⊢≡ A≡A′
          t₂≡t₂′       = check-sound′ n eq₃ ⊢Μ $
                         subst-⊢ ⊢A′ (⊢ˢʷ∷-[][]↑ (⊢1,0 ⊢ΣB₁B₂))
      in
      wf-⊢≡∷ (prodrec-cong (sym A≡A′) (refl ⊢t₁) (sym′ t₂≡t₂′) Σ-ok)
        .proj₂ .proj₂
    infer′-sound ℕ ok! _ ⊢Γ =
      ℕⱼ ⊢Γ
    infer′-sound zero ok! _ ⊢Γ =
      zeroⱼ ⊢Γ
    infer′-sound {n} (suc _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq ok! =
      let t≡t′       = check-sound′ n eq ⊢Μ (ℕⱼ ⊢Γ)
          _ , ⊢t , _ = wf-⊢≡∷ t≡t′
      in
      sucⱼ ⊢t
    infer′-sound {n} (natrec _ _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      using inv _ eq₂ eq ← inv->>= eq
          | inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₄ ok! =
      let A≡A′    = check-type-sound′ n eq₁ ⊢Μ (∙ ℕⱼ ⊢Γ)
          _ , ⊢A′ = wf-⊢≡ A≡A′
          t₁≡t₁′  = check-sound′ n eq₂ ⊢Μ (substType ⊢A′ (zeroⱼ ⊢Γ))
          t₂≡t₂′  = check-sound′ n eq₃ ⊢Μ $
                    subst-⊢ ⊢A′ (⊢ˢʷ∷-[][]↑ (sucⱼ (var₁ ⊢A′)))
          t₃≡t₃′  = check-sound′ n eq₄ ⊢Μ (ℕⱼ ⊢Γ)
      in
      wf-⊢≡∷
        (natrec-cong (sym A≡A′) (sym′ t₁≡t₁′) (sym′ t₂≡t₂′)
           (sym′ t₃≡t₃′))
        .proj₂ .proj₂
    infer′-sound {n} (Id _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , PE.refl) _ eq
      using inv _ eq₂ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let ⊢A          = infer-red-sound n eq₁ ⊢Μ ⊢Γ
          t₁≡t₁′      = check-sound′ n eq₂ ⊢Μ (univ ⊢A)
          _ , ⊢t₁ , _ = wf-⊢≡∷ t₁≡t₁′
          t₂≡t₂′      = check-sound′ n eq₃ ⊢Μ (univ ⊢A)
          _ , ⊢t₂ , _ = wf-⊢≡∷ t₂≡t₂′
      in
      Idⱼ ⊢A ⊢t₁ ⊢t₂
    infer′-sound {n} (rfl _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ ok! =
      rflⱼ (infer-sound n eq₁ ⊢Μ ⊢Γ)
    infer′-sound {n} (J _ _ _ _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₅ eq
      with inv->>= eq
    … | inv _ eq₆ ok! =
      let A₁≡A₁′       = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
          _ , ⊢A₁′     = wf-⊢≡ A₁≡A₁′
          t₁≡t₁′       = check-sound′ n eq₂ ⊢Μ ⊢A₁′
          _ , _ , ⊢t₁′ = wf-⊢≡∷ t₁≡t₁′
          A₂≡A₂′       = check-type-sound′ n eq₃ ⊢Μ
                           (J-motive-context ⊢t₁′)
          _ , ⊢A₂′     = wf-⊢≡ A₂≡A₂′
          t₂≡t₂′       = check-sound′ n eq₄ ⊢Μ
                           (J-result ⊢A₂′ (rflⱼ ⊢t₁′))
          t₃≡t₃′       = check-sound′ n eq₅ ⊢Μ ⊢A₁′
          _ , _ , ⊢t₃′ = wf-⊢≡∷ t₃≡t₃′
          t₄≡t₄′       = check-sound′ n eq₆ ⊢Μ (Idⱼ′ ⊢t₁′ ⊢t₃′)
      in
      wf-⊢≡∷
        (J-cong′ (sym A₁≡A₁′) (sym′ t₁≡t₁′) (sym A₂≡A₂′) (sym′ t₂≡t₂′)
           (sym′ t₃≡t₃′) (sym′ t₄≡t₄′))
        .proj₂ .proj₂
    infer′-sound {n} (K _ _ _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₅ eq
      with inv->>= eq
    … | inv _ (ok PE.refl K-ok) ok! =
      let A₁≡A₁′       = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
          _ , ⊢A₁′     = wf-⊢≡ A₁≡A₁′
          t₁≡t₁′       = check-sound′ n eq₂ ⊢Μ ⊢A₁′
          _ , _ , ⊢t₁′ = wf-⊢≡∷ t₁≡t₁′
          ⊢Id          = Idⱼ′ ⊢t₁′ ⊢t₁′
          A₂≡A₂′       = check-type-sound′ n eq₃ ⊢Μ (∙ ⊢Id)
          _ , ⊢A₂′     = wf-⊢≡ A₂≡A₂′
          t₂≡t₂′       = check-sound′ n eq₄ ⊢Μ $
                         substType ⊢A₂′ (rflⱼ ⊢t₁′)
          t₃≡t₃′       = check-sound′ n eq₅ ⊢Μ ⊢Id
      in
      wf-⊢≡∷
        (K-cong (sym A₁≡A₁′) (sym′ t₁≡t₁′) (sym A₂≡A₂′) (sym′ t₂≡t₂′)
           (sym′ t₃≡t₃′) K-ok)
        .proj₂ .proj₂
    infer′-sound {n} ([]-cong _ _ _ _ _) eq ⊢Μ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ (ok PE.refl okᵇᶜ) ok! =
      let A≡A′         = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
          _ , ⊢A′      = wf-⊢≡ A≡A′
          t₁≡t₁′       = check-sound′ n eq₂ ⊢Μ ⊢A′
          _ , _ , ⊢t₁′ = wf-⊢≡∷ t₁≡t₁′
          t₂≡t₂′       = check-sound′ n eq₃ ⊢Μ ⊢A′
          _ , _ , ⊢t₂′ = wf-⊢≡∷ t₂≡t₂′
          t₃≡t₃′       = check-sound′ n eq₄ ⊢Μ (Idⱼ′ ⊢t₁′ ⊢t₂′)
      in
      wf-⊢≡∷
        ([]-cong-cong (sym A≡A′) (sym′ t₁≡t₁′) (sym′ t₂≡t₂′)
           (sym′ t₃≡t₃′) okᵇᶜ)
        .proj₂ .proj₂

  -- Soundness for infer-U.

  infer-U-sound :
    ∀ {Γ : Cons c m n} n →
    OK (infer-U n Γ t) l γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ U l ⌝ γ
  infer-U-sound n eq ⊢Μ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , PE.refl) _ ok! =
    infer-red-sound n eq₁ ⊢Μ ⊢Γ

  -- Soundness for equal-con.

  equal-con-sound′ :
    OK (equal-con n Γ Δ) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Γ ⌝ᶜ γ .vars ≡ ⌜ Δ ⌝ᶜᵛ γ
  equal-con-sound′ eq ⊢Μ ⊢Γ ⊢Δ =
    let inv Γ∼Δ _ eq = inv->>= eq in
    equal-con′-sound Γ∼Δ eq ⊢Μ ⊢Γ ⊢Δ

  private

    -- Soundness for equal-con′.

    equal-con′-sound :
      (Δ₁∼Δ₂ : Equal-con-constructors⁼ Δ₁ Δ₂) →
      OK (equal-con′ n ∇ Δ₁∼Δ₂) tt γ →
      Meta-con-wf ∇ γ →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₂ ⌝ᶜᵛ γ →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ ≡ ⌜ Δ₂ ⌝ᶜᵛ γ
    equal-con′-sound (base PE.refl) ok! _ ⊢base _ =
      reflConEq ⊢base
    equal-con′-sound ε ok! _ ⊢ε _ =
      reflConEq ⊢ε
    equal-con′-sound {n} (ext _ _ _ _) eq ⊢Μ (∙ ⊢A₁) (∙ ⊢A₂) =
      let inv _ eq₁ eq₂ = inv->>= eq
          Δ₁≡Δ₂         = equal-con-sound′ eq₁ ⊢Μ (wf ⊢A₁) (wf ⊢A₂)
      in
      Δ₁≡Δ₂ ∙
      equal-ty-sound′ n eq₂ ⊢Μ ⊢A₁ (stability (symConEq Δ₁≡Δ₂) ⊢A₂)

  -- Soundness for check-sub.

  check-sub-sound′ :
    ∀ σ →
    OK (check-sub n ∇ Δ₂ σ Δ₁) σ′ γ →
    Meta-con-wf ∇ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₂ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ₂ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ ⌝ˢ γ ≡ ⌜ σ′ ⌝ˢ γ ∷ ⌜ Δ₁ ⌝ᶜᵛ γ
  check-sub-sound′ id eq ⊢Μ ⊢Δ₂ ⊢Δ₁
    with inv->>= eq
  … | inv _ eq₁ ok! =
    let Γ≡Δ = equal-con-sound′ eq₁ ⊢Μ ⊢Δ₂ ⊢Δ₁ in
    refl-⊢ˢʷ≡∷ (stability-⊢ˢʷ∷ʳ Γ≡Δ (⊢ˢʷ∷-idSubst ⊢Δ₂))
  check-sub-sound′ (wk1 σ) eq ⊢Μ ⊢Δ₂ ⊢Δ₁
    with inv->>= eq
  … | inv (_ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ ok! =
    let ⊢A   = ⊢∙→⊢ ⊢Δ₂
        σ≡σ′ = check-sub-sound′ σ eq₁ ⊢Μ (wf ⊢A) ⊢Δ₁
    in
    ⊢ˢʷ≡∷-wk1Subst ⊢A σ≡σ′
  check-sub-sound′ {n} (σ ⇑) eq ⊢Μ ⊢Δ₂ ⊢Δ₁
    with inv->>= eq
  … | inv (_ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv (_ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let ⊢A          = ⊢∙→⊢ ⊢Δ₂
        ⊢B          = ⊢∙→⊢ ⊢Δ₁
        σ≡σ′        = check-sub-sound′ σ eq₁ ⊢Μ (wf ⊢A) (wf ⊢B)
        _ , _ , ⊢σ′ = wf-⊢ˢʷ≡∷ σ≡σ′
        A≡B[σ′]     = equal-ty-sound′ n eq₂ ⊢Μ ⊢A (subst-⊢ ⊢B ⊢σ′)
    in
    stability-⊢ˢʷ≡∷ˡ (refl-∙ (sym A≡B[σ′])) $
    sym-⊢ˢʷ≡∷ ⊢Δ₁ (⊢ˢʷ≡∷-⇑′ ⊢B (sym-⊢ˢʷ≡∷ (wf ⊢B) σ≡σ′))
  check-sub-sound′ {n} (cons σ _) eq ⊢Μ ⊢Δ₂ ⊢Δ₁
    with inv->>= eq
  … | inv (_ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let ⊢B          = ⊢∙→⊢ ⊢Δ₁
        σ≡σ′        = check-sub-sound′ σ eq₁ ⊢Μ ⊢Δ₂ (wf ⊢B)
        _ , _ , ⊢σ′ = wf-⊢ˢʷ≡∷ σ≡σ′
        t≡t′        = check-sound′ n eq₂ ⊢Μ (subst-⊢ ⊢B ⊢σ′)
    in
    sym-⊢ˢʷ≡∷ ⊢Δ₁ (→⊢ˢʷ≡∷∙ ⊢B (sym-⊢ˢʷ≡∷ (wf ⊢B) σ≡σ′) (sym′ t≡t′))

  -- Soundness for equal-tm.

  equal-tm-sound′ :
    ∀ n →
    OK (equal-tm n Γ t₁ t₂ A) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-tm-sound′                   0      not-ok _
  equal-tm-sound′ {t₁} {t₂} {A} {γ} (1+ n) eq     ⊢Μ ⊢t₁ ⊢t₂ =
    let open TmR

        inv t₁′ eq₁ eq  = inv->>= eq
        inv t₂′ eq₂ eq  = inv->>= eq
        inv A′  eq₃ eq₄ = inv->>= eq

        t₁≡t₁′ = red-tm-sound n eq₁ ⊢Μ ⊢t₁
        t₂≡t₂′ = red-tm-sound n eq₂ ⊢Μ ⊢t₂
        A≡A′   = red-ty-sound n eq₃ ⊢Μ (wf-⊢∷ ⊢t₁)
    in
    ⌜ t₁ ⌝ γ   ≡⟨ t₁≡t₁′ ⟩⊢
    ⌜ t₁′ ⌝ γ  ≡⟨ flip _⊢_≡_∷_.conv (sym A≡A′) $
                  equal-tm-red-sound n A′ eq₄ ⊢Μ
                    (conv (wf-⊢≡∷ t₁≡t₁′ .proj₂ .proj₂) A≡A′)
                    (conv (wf-⊢≡∷ t₂≡t₂′ .proj₂ .proj₂) A≡A′) ⟩⊢
    ⌜ t₂′ ⌝ γ  ≡˘⟨ t₂≡t₂′ ⟩⊢∎
    ⌜ t₂ ⌝ γ   ∎

  -- Soundness for equal-tm-red.

  equal-tm-red-sound :
    ∀ n A →
    OK (equal-tm-red n Γ t₁ t₂ A) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-tm-red-sound _ A _ _ _ _
    with is-type-constructorˡ? A
  equal-tm-red-sound n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just (meta-var _ _) =
    equal-ne-red-sound n eq ⊢Μ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound {t₁} {t₂} n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just (U _) =
    equal-ty-red-U-sound t₁ eq ⊢Μ ⊢t₁ ⊢t₂
  equal-tm-red-sound n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just Empty =
    equal-ne-red-sound n eq ⊢Μ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound {Γ} {t₁} {t₂} n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just (Unit s l)
    with s ≟ˢ 𝕤
  … | just PE.refl =
    η-unit ⊢t₁ ⊢t₂ (inj₁ PE.refl)
  … | nothing
    with are-star? s l t₁ t₂
  … | just (PE.refl , PE.refl) =
    refl ⊢t₁
  … | nothing
    with inv-catch eq
  … | inj₁ eq =
    equal-ne-red-sound n eq ⊢Μ (wf-⊢∷ ⊢t₁)
  … | inj₂ (ok PE.refl (L.lift η)) =
    η-unit ⊢t₁ ⊢t₂ η
  equal-tm-red-sound {t₁} {t₂} n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just ℕ
    with are-zero-or-suc? t₁ t₂
  … | just (inj₁ (PE.refl , PE.refl)) =
    refl ⊢t₁
  … | just (inj₂ (_ , _ , PE.refl , PE.refl)) =
    suc-cong $
    equal-tm-sound′ n eq ⊢Μ (inversion-suc ⊢t₁ .proj₁)
      (inversion-suc ⊢t₂ .proj₁)
  … | nothing =
    equal-ne-red-sound n eq ⊢Μ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just (ΠΣ BMΠ _ _ _ _) =
    let ⊢A₁ , _     = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
        t₁∘x0≡t₂∘x0 =
          equal-tm-sound′ n eq ⊢Μ
            (PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) $
             W.wkTerm₁ ⊢A₁ ⊢t₁ ∘ⱼ var₀ ⊢A₁)
            (PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) $
             W.wkTerm₁ ⊢A₁ ⊢t₂ ∘ⱼ var₀ ⊢A₁)
    in
    η-eq′ ⊢t₁ ⊢t₂ t₁∘x0≡t₂∘x0
  equal-tm-red-sound n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just (ΠΣ BMΣ-𝕤 _ _ _ A₂) =
    let inv _ eq₁ eq₂ = inv->>= eq
        _ , ⊢A₂ , _   = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
        fst-t₁≡fst-t₂ =
          equal-tm-sound′ n eq₁ ⊢Μ (fstⱼ′ ⊢t₁) (fstⱼ′ ⊢t₂)
    in
    Σ-η′ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂
      (equal-tm-sound′ n eq₂ ⊢Μ (sndⱼ′ ⊢t₁)
         (conv (sndⱼ′ ⊢t₂) $
          substTypeEq (refl ⊢A₂) (sym′ fst-t₁≡fst-t₂)))
  equal-tm-red-sound {t₁} {t₂} n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just (ΠΣ BMΣ-𝕨 p _ _ A₂)
    with are-prodʷ? p t₁ t₂
  … | nothing =
    equal-ne-red-sound n eq ⊢Μ (wf-⊢∷ ⊢t₁)
  … | just (_ , _ , _ , _ , _ , _ , PE.refl , PE.refl)
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let ⊢A₁ , ⊢A₂ , Σ-ok = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
        t₁₁≡t₁ , t₁₁≡t₂₁ = check-and-equal-tm-sound′ n eq₁ ⊢Μ ⊢A₁
        _ , _ , ⊢t₁      = wf-⊢≡∷ t₁₁≡t₁
        _ , t₁₂≡t₂₂      = check-and-equal-tm-sound′ n eq₂ ⊢Μ
                             (substType ⊢A₂ ⊢t₁)
        t₁₂≡t₂₂          = conv t₁₂≡t₂₂ $
                           substTypeEq (refl ⊢A₂) (sym′ t₁₁≡t₁)
    in
    prod-cong ⊢A₂ t₁₁≡t₂₁ t₁₂≡t₂₂ Σ-ok
  equal-tm-red-sound {t₁} {t₂} n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | just (Id _ _ _)
    with are-rfl? t₁ t₂
  … | just (_ , _ , PE.refl , PE.refl) =
    refl ⊢t₁
  … | nothing =
    equal-ne-red-sound n eq ⊢Μ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound n _ eq ⊢Μ ⊢t₁ ⊢t₂
    | nothing =
    equal-ne-red-sound n eq ⊢Μ (wf-⊢∷ ⊢t₁)

  -- Soundness for equal-ne.

  equal-ne-sound :
    ∀ n →
    OK (equal-ne n Γ t₁ t₂ A) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-ne-sound n eq ⊢Μ ⊢A =
    let inv _ eq₁ eq₂ = inv->>= eq
        t₁≡t₂         = equal-ne-inf-sound n eq₁ ⊢Μ (wf ⊢A)
        ⊢A′ , _       = wf-⊢≡∷ t₁≡t₂
    in
    conv t₁≡t₂ (equal-ty-sound′ n eq₂ ⊢Μ ⊢A′ ⊢A)

  -- Soundness for equal-ne-red.

  equal-ne-red-sound :
    ∀ n →
    OK (equal-ne-red n Γ t₁ t₂ A) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-ne-red-sound {A} n eq ⊢Μ ⊢A =
    let inv A′ eq₁ eq₂ = inv->>= eq
        t₁≡t₂          = equal-ne-inf-red-sound n eq₁ ⊢Μ (wf ⊢A)
        ⊢A′ , _        = wf-⊢≡∷ t₁≡t₂
    in
    conv t₁≡t₂ (equal-ty-red-sound n A′ A eq₂ ⊢Μ ⊢A′ ⊢A)

  -- Soundness for equal-ne-inf-red.

  equal-ne-inf-red-sound :
    ∀ n →
    OK (equal-ne-inf-red n Γ t₁ t₂) A γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-ne-inf-red-sound n eq ⊢Μ ⊢Γ =
    let inv _ eq₁ eq₂ = inv->>= eq
        t₁≡t₂         = equal-ne-inf-sound n eq₁ ⊢Μ ⊢Γ
        ⊢A , _        = wf-⊢≡∷ t₁≡t₂
    in
    conv t₁≡t₂ (red-ty-sound n eq₂ ⊢Μ ⊢A)

  -- Soundness for equal-ne-inf.

  equal-ne-inf-sound :
    ∀ n →
    OK (equal-ne-inf n Γ t₁ t₂) A γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-ne-inf-sound 0      not-ok
  equal-ne-inf-sound (1+ _) eq     _ _
    with inv->>= eq
  equal-ne-inf-sound {γ} _ _ ⊢Μ ⊢Γ
    | inv (meta-var x₁ σ₁ x₂ σ₂ PE.refl) _ eq
    rewrite ⌜meta-var⌝ {γ = γ} {x = x₁} σ₁
          | ⌜meta-var⌝ {γ = γ} {x = x₂} σ₂
    using inv _ _ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv PE.refl eq₂ eq
    with inv->>= eq
  … | inv PE.refl _ ok! =
    let ⊢t    = is-term-sound eq₁ ⊢Μ
        σ₁≡σ₂ = equal-sub′-sound eq₂ ⊢Μ ⊢Γ (wfTerm ⊢t)
    in
    subst-⊢≡∷ (refl ⊢t) σ₁≡σ₂
  equal-ne-inf-sound {Γ} _ _ _ ⊢Γ
    | inv (var _ PE.refl) _ eq =
    refl (var ⊢Γ (index-sound (Γ .vars) eq .proj₁ PE.refl))
  equal-ne-inf-sound {Γ} _ _ _ ⊢Γ
    | inv (defn _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq ok! =
    refl (defn ⊢Γ (type-of-sound (Γ .defs) eq) PE.refl)
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (emptyrec _ _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let A₁≡A , A₁≡A₂ = check-and-equal-ty-sound′ n eq₁ ⊢Μ ⊢Γ
        t₁≡t₂        = equal-ne-red-sound n eq₂ ⊢Μ (Emptyⱼ ⊢Γ)
    in
    conv (emptyrec-cong A₁≡A₂ t₁≡t₂) A₁≡A
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (unitrec _ _ _ _ _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    using inv _ eq₂ eq ← inv->>= eq
        | inv _ eq₃ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ (ok PE.refl Unit-ok) ok! =
    let ⊢Unit        = Unitⱼ ⊢Γ Unit-ok
        ⊢⋆           = starⱼ ⊢Γ Unit-ok
        A₁≡A , A₁≡A₂ = check-and-equal-ty-sound′ n eq₁ ⊢Μ (∙ ⊢Unit)
        _ , ⊢A       = wf-⊢≡ A₁≡A
        t₁₁≡t₂₁      = equal-ne-red-sound n eq₂ ⊢Μ ⊢Unit
        _ , ⊢t₁₁ , _ = wf-⊢≡∷ t₁₁≡t₂₁
        _ , t₁₂≡t₂₂  = check-and-equal-tm-sound′ n eq₃ ⊢Μ
                         (substType ⊢A ⊢⋆)
        t₁₂≡t₂₂      = conv t₁₂≡t₂₂ (substTypeEq (sym A₁≡A) (refl ⊢⋆))
    in
    conv (unitrec-cong′ A₁≡A₂ t₁₁≡t₂₁ t₁₂≡t₂₂)
      (substTypeEq A₁≡A (refl ⊢t₁₁))
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (app _ _ _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , _ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let t₁₁≡t₂₁          = equal-ne-inf-red-sound n eq₁ ⊢Μ ⊢Γ
        ⊢Π , _           = wf-⊢≡∷ t₁₁≡t₂₁
        ⊢A₁ , ⊢A₂ , _    = inversion-ΠΣ ⊢Π
        t₁₂≡t₂ , t₁₂≡t₂₂ = check-and-equal-tm-sound′ n eq₂ ⊢Μ ⊢A₁
    in
    conv (app-cong t₁₁≡t₂₁ t₁₂≡t₂₂) (substTypeEq (refl ⊢A₂) t₁₂≡t₂)
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (fst _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , _ , _ , PE.refl) _ ok! =
    fst-cong′ (equal-ne-inf-red-sound n eq₁ ⊢Μ ⊢Γ)
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (snd _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , _ , _ , PE.refl) _ ok! =
    snd-cong′ (equal-ne-inf-red-sound n eq₁ ⊢Μ ⊢Γ)
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (prodrec _ _ _ _ _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , _ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let t₁₁≡t₂₁      = equal-ne-inf-red-sound n eq₁ ⊢Μ ⊢Γ
        _ , ⊢t₁₁ , _ = wf-⊢≡∷ t₁₁≡t₂₁
        ⊢Σ , _       = wf-⊢≡∷ t₁₁≡t₂₁
        A₁≡A , A₁≡A₂ = check-and-equal-ty-sound′ n eq₂ ⊢Μ (∙ ⊢Σ)
        _ , ⊢A       = wf-⊢≡ A₁≡A
        _ , t₁₂≡t₂₂  = check-and-equal-tm-sound′ n eq₃ ⊢Μ
                         (subst↑²Type ⊢A (⊢1,0 ⊢Σ))
        t₁₂≡t₂₂      = conv t₁₂≡t₂₂ $
                       subst↑²TypeEq (sym A₁≡A) (refl (⊢1,0 ⊢Σ))
    in
    conv (prodrec-cong′ A₁≡A₂ t₁₁≡t₂₁ t₁₂≡t₂₂)
      (substTypeEq A₁≡A (refl ⊢t₁₁))
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (natrec _ _ _ _ _ _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    using inv _ eq₂ eq ← inv->>= eq
        | inv _ eq₃ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ eq₄ ok! =
    let A₁≡A , A₁≡A₂ = check-and-equal-ty-sound′ n eq₁ ⊢Μ (∙ ℕⱼ ⊢Γ)
        _ , ⊢A       = wf-⊢≡ A₁≡A
        ⊢0           = zeroⱼ ⊢Γ
        ⊢suc-1       = sucⱼ (var₁ ⊢A)
        _ , t₁₁≡t₂₁  = check-and-equal-tm-sound′ n eq₂ ⊢Μ
                         (substType ⊢A ⊢0)
        t₁₁≡t₂₁      = conv t₁₁≡t₂₁ (substTypeEq (sym A₁≡A) (refl ⊢0))
        _ , t₁₂≡t₂₂  = check-and-equal-tm-sound′ n eq₃ ⊢Μ
                         (subst↑²Type ⊢A ⊢suc-1)
        t₁₂≡t₂₂      = stabilityEqTerm (refl-∙ (sym A₁≡A)) $
                       conv t₁₂≡t₂₂ $
                       subst↑²TypeEq (sym A₁≡A) (refl ⊢suc-1)
        t₁₃≡t₂₃      = equal-ne-red-sound n eq₄ ⊢Μ (ℕⱼ ⊢Γ)
        _ , ⊢t₁₃ , _ = wf-⊢≡∷ t₁₃≡t₂₃
    in
    conv (natrec-cong A₁≡A₂ t₁₁≡t₂₁ t₁₂≡t₂₂ t₁₃≡t₂₃)
      (substTypeEq A₁≡A (refl ⊢t₁₃))
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (J _ _ _ _ _ _ _ _ _ _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ eq
    using inv _ eq₄ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ eq₅ eq
    with inv->>= eq
  … | inv _ eq₆ ok! =
    let A₁₁≡A₁ , A₁₁≡A₂₁ = check-and-equal-ty-sound′ n eq₁ ⊢Μ ⊢Γ
        _ , ⊢A₁          = wf-⊢≡ A₁₁≡A₁
        t₁₁≡t₁ , t₁₁≡t₂₁ = check-and-equal-tm-sound′ n eq₂ ⊢Μ ⊢A₁
        _ , _ , ⊢t₁      = wf-⊢≡∷ t₁₁≡t₁
        t₁₁≡t₂₁          = conv t₁₁≡t₂₁ (sym A₁₁≡A₁)
        A₁₂≡A₂ , A₁₂≡A₂₂ = check-and-equal-ty-sound′ n eq₃ ⊢Μ
                             (J-motive-context ⊢t₁)
        _ , ⊢A₂          = wf-⊢≡ A₁₂≡A₂
        A₁₂≡A₂₂          = stabilityEq
                             (J-motive-context-cong′ (sym A₁₁≡A₁)
                                (sym′ t₁₁≡t₁))
                             A₁₂≡A₂₂
        _ , t₁₂≡t₂₂      = check-and-equal-tm-sound′ n eq₄ ⊢Μ
                             (J-result ⊢A₂ (rflⱼ ⊢t₁))
        t₁₂≡t₂₂          = conv t₁₂≡t₂₂ $
                           J-motive-rfl-cong (sym A₁₂≡A₂) (sym′ t₁₁≡t₁)
        t₁₃≡t₃ , t₁₃≡t₂₃ = check-and-equal-tm-sound′ n eq₅ ⊢Μ ⊢A₁
        _ , _ , ⊢t₃      = wf-⊢≡∷ t₁₃≡t₃
        t₁₃≡t₂₃          = conv t₁₃≡t₂₃ (sym A₁₁≡A₁)
        t₁₄≡t₂₄          = equal-ne-red-sound n eq₆ ⊢Μ (Idⱼ′ ⊢t₁ ⊢t₃)
        _ , ⊢t₁₄ , _     = wf-⊢≡∷ t₁₄≡t₂₄
        t₁₄≡t₂₄          = conv t₁₄≡t₂₄ $
                           Id-cong (sym A₁₁≡A₁) (sym′ t₁₁≡t₁)
                             (sym′ t₁₃≡t₃)
    in
    conv (J-cong′ A₁₁≡A₂₁ t₁₁≡t₂₁ A₁₂≡A₂₂ t₁₂≡t₂₂ t₁₃≡t₂₃ t₁₄≡t₂₄)
      (sym (J-result-cong (sym A₁₂≡A₂) (sym′ t₁₃≡t₃) (refl ⊢t₁₄)))
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv (K _ _ _ _ _ _ _ _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ eq
    using inv _ eq₄ eq ← inv->>= eq
        | inv _ eq₅ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ (ok PE.refl K-ok) ok! =
    let A₁₁≡A₁ , A₁₁≡A₂₁ = check-and-equal-ty-sound′ n eq₁ ⊢Μ ⊢Γ
        _ , ⊢A₁          = wf-⊢≡ A₁₁≡A₁
        t₁₁≡t₁ , t₁₁≡t₂₁ = check-and-equal-tm-sound′ n eq₂ ⊢Μ ⊢A₁
        _ , _ , ⊢t₁      = wf-⊢≡∷ t₁₁≡t₁
        t₁₁≡t₂₁          = conv t₁₁≡t₂₁ (sym A₁₁≡A₁)
        Id≡Id            = Id-cong (sym A₁₁≡A₁) (sym′ t₁₁≡t₁)
                             (sym′ t₁₁≡t₁)
        ⊢Id , _          = wf-⊢≡ Id≡Id
        A₁₂≡A₂ , A₁₂≡A₂₂ = check-and-equal-ty-sound′ n eq₃ ⊢Μ (∙ ⊢Id)
        _ , ⊢A₂          = wf-⊢≡ A₁₂≡A₂
        A₁₂≡A₂₂          = stabilityEq (refl-∙ Id≡Id) A₁₂≡A₂₂
        _ , t₁₂≡t₂₂      = check-and-equal-tm-sound′ n eq₄ ⊢Μ $
                           substType ⊢A₂ (rflⱼ ⊢t₁)
        t₁₂≡t₂₂          = conv t₁₂≡t₂₂ $
                           substTypeEq (sym A₁₂≡A₂) (refl (rflⱼ ⊢t₁))
        t₁₃≡t₂₃          = equal-ne-red-sound n eq₅ ⊢Μ ⊢Id
        _ , ⊢t₁₃ , _     = wf-⊢≡∷ t₁₃≡t₂₃
        t₁₃≡t₂₃          = conv t₁₃≡t₂₃ Id≡Id
    in
    conv (K-cong A₁₁≡A₂₁ t₁₁≡t₂₁ A₁₂≡A₂₂ t₁₂≡t₂₂ t₁₃≡t₂₃ K-ok)
      (substTypeEq A₁₂≡A₂ (refl ⊢t₁₃))
  equal-ne-inf-sound (1+ n) _ ⊢Μ ⊢Γ
    | inv ([]-cong _ _ _ _ _ _ _ _ _ PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ eq
    using inv _ eq₄ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ (ok PE.refl okᵇᶜ) ok! =
    let A₁≡A , A₁≡A₂     = check-and-equal-ty-sound′ n eq₁ ⊢Μ ⊢Γ
        _ , ⊢A           = wf-⊢≡ A₁≡A
        t₁₁≡t₁ , t₁₁≡t₂₁ = check-and-equal-tm-sound′ n eq₂ ⊢Μ ⊢A
        _ , _ , ⊢t₁      = wf-⊢≡∷ t₁₁≡t₁
        t₁₁≡t₂₁          = conv t₁₁≡t₂₁ (sym A₁≡A)
        t₁₂≡t₂ , t₁₂≡t₂₂ = check-and-equal-tm-sound′ n eq₃ ⊢Μ ⊢A
        _ , _ , ⊢t₂      = wf-⊢≡∷ t₁₂≡t₂
        t₁₂≡t₂₂          = conv t₁₂≡t₂₂ (sym A₁≡A)
        t₁₃≡t₂₃          = equal-ne-red-sound n eq₄ ⊢Μ (Idⱼ′ ⊢t₁ ⊢t₂)
        t₁₃≡t₂₃          = conv t₁₃≡t₂₃ $
                           Id-cong (sym A₁≡A) (sym′ t₁₁≡t₁)
                             (sym′ t₁₂≡t₂)
        okᴱ              = []-cong→Erased okᵇᶜ
    in
    _⊢_≡_∷_.conv ([]-cong-cong A₁≡A₂ t₁₁≡t₂₁ t₁₂≡t₂₂ t₁₃≡t₂₃ okᵇᶜ) $
    _⊢_≡_.sym $
    Id-cong (sym (Erased-cong okᴱ A₁≡A)) (sym′ ([]-cong′ okᴱ t₁₁≡t₁))
      (sym′ ([]-cong′ okᴱ t₁₂≡t₂))

  -- Soundness for equal-ty.

  equal-ty-sound′ :
    ∀ n →
    OK (equal-ty n Γ A₁ A₂) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  equal-ty-sound′               0      not-ok
  equal-ty-sound′ {A₁} {A₂} {γ} (1+ n) eq     ⊢Μ ⊢A₁ ⊢A₂ =
    let open TyR

        inv A₁′ eq₁ eq  = inv->>= eq
        inv A₂′ eq₂ eq₃ = inv->>= eq

        A₁≡A₁′ = red-ty-sound n eq₁ ⊢Μ ⊢A₁
        A₂≡A₂′ = red-ty-sound n eq₂ ⊢Μ ⊢A₂
    in
    ⌜ A₁ ⌝ γ   ≡⟨ A₁≡A₁′ ⟩⊢
    ⌜ A₁′ ⌝ γ  ≡⟨ equal-ty-red-sound n A₁′ A₂′ eq₃ ⊢Μ
                    (wf-⊢≡ A₁≡A₁′ .proj₂) (wf-⊢≡ A₂≡A₂′ .proj₂) ⟩⊢
    ⌜ A₂′ ⌝ γ  ≡˘⟨ A₂≡A₂′ ⟩⊢∎
    ⌜ A₂ ⌝ γ   ∎

  -- Soundness for equal-ty-red.

  equal-ty-red-sound :
    ∀ n A₁ A₂ →
    OK (equal-ty-red n Γ A₁ A₂) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  equal-ty-red-sound _ A₁ A₂ _ _ _ _
    with are-equal-type-constructors? A₁ A₂
  equal-ty-red-sound {γ} _ _ _ eq ⊢Μ ⊢x₁ _
    | just (meta-var x₁ σ₁ x₂ σ₂ PE.refl)
    rewrite ⌜meta-var⌝ {γ = γ} {x = x₁} σ₁
          | ⌜meta-var⌝ {γ = γ} {x = x₂} σ₂
    with inv->>= eq
  … | inv _ _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv PE.refl eq₂ eq
    with inv->>= eq
  … | inv PE.refl _ ok! =
    let ⊢x    = is-type-sound eq₁ ⊢Μ
        σ₁≡σ₂ = equal-sub′-sound eq₂ ⊢Μ (wf ⊢x₁) (wf ⊢x)
    in
    subst-⊢≡ (refl ⊢x) σ₁≡σ₂
  equal-ty-red-sound _ _ _ _ _ ⊢A₁ _ | just (U PE.refl) =
    refl ⊢A₁
  equal-ty-red-sound _ _ _ _ _ ⊢A₁ _ | just (Empty PE.refl) =
    refl ⊢A₁
  equal-ty-red-sound _ _ _ _ _ ⊢A₁ _ | just (Unit PE.refl) =
    refl ⊢A₁
  equal-ty-red-sound n _ _ eq ⊢Μ ⊢A₁ ⊢A₂ | just (ΠΣ _ _ _ _ PE.refl) =
    let inv _ eq₁ eq₂       = inv->>= eq
        ⊢A₁₁ , ⊢A₁₂ , ΠΣ-ok = inversion-ΠΣ ⊢A₁
        ⊢A₂₁ , ⊢A₂₂ , _     = inversion-ΠΣ ⊢A₂
        A₁₁≡A₂₁             = equal-ty-sound′ n eq₁ ⊢Μ ⊢A₁₁ ⊢A₂₁
    in
    ΠΣ-cong A₁₁≡A₂₁
      (equal-ty-sound′ n eq₂ ⊢Μ ⊢A₁₂
         (stability (refl-∙ (sym A₁₁≡A₂₁)) ⊢A₂₂))
      ΠΣ-ok
  equal-ty-red-sound _ _ _ _ _ ⊢A₁ _ | just (ℕ PE.refl) =
    refl ⊢A₁
  equal-ty-red-sound n _ _ eq ⊢Μ ⊢A₁ ⊢A₂
    | just (Id _ _ _ _ _ _ PE.refl) =
    let inv _ eq₁ eq      = inv->>= eq
        inv _ eq₂ eq₃     = inv->>= eq
        ⊢A₁ , ⊢t₁₁ , ⊢t₁₂ = inversion-Id ⊢A₁
        ⊢A₂ , ⊢t₂₁ , ⊢t₂₂ = inversion-Id ⊢A₂
        A₁≡A₂             = equal-ty-sound′ n eq₁ ⊢Μ ⊢A₁ ⊢A₂
    in
    Id-cong A₁≡A₂
      (equal-tm-sound′ n eq₂ ⊢Μ ⊢t₁₁ (conv ⊢t₂₁ (sym A₁≡A₂)))
      (equal-tm-sound′ n eq₃ ⊢Μ ⊢t₁₂ (conv ⊢t₂₂ (sym A₁≡A₂)))
  equal-ty-red-sound n _ _ eq ⊢Μ ⊢A₁ ⊢A₂ | nothing
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , PE.refl) _ ok! =
    univ (equal-ne-inf-red-sound n eq₁ ⊢Μ (wf ⊢A₁))

  -- Soundness for equal-ty-red-U.

  equal-ty-red-U-sound :
    ∀ {Γ : Cons c m n} A₁ {n} →
    OK (equal-ty-red-U n Γ A₁ A₂ l) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ∷ ⌜ U l ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ ∷ ⌜ U l ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ ∷ ⌜ U l ⌝ γ
  equal-ty-red-U-sound {A₂} A₁ _ _ _ _
    with are-equal-type-constructors? A₁ A₂
  equal-ty-red-U-sound {γ} _ {n} eq ⊢Μ ⊢x₁ _
    | just (meta-var x₁ σ₁ x₂ σ₂ PE.refl)
    rewrite ⌜meta-var⌝ {γ = γ} {x = x₁} σ₁
          | ⌜meta-var⌝ {γ = γ} {x = x₂} σ₂
    with inv->>= eq
  … | inv _ _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv PE.refl _ eq
    with inv->>= eq
  … | inv PE.refl eq₃ eq
    with inv->>= eq
  … | inv PE.refl _ _ =
    let ⊢x₂   = is-term-sound eq₁ ⊢Μ
        ≡U    = red-ty-sound n eq₂ ⊢Μ (wf-⊢∷ ⊢x₂)
        σ₁≡σ₂ = equal-sub′-sound eq₃ ⊢Μ (wfTerm ⊢x₁) (wfTerm ⊢x₂)
    in
    subst-⊢≡∷ (conv (refl ⊢x₂) ≡U) σ₁≡σ₂
  equal-ty-red-U-sound _ _ _ ⊢A₁ _ | just (U PE.refl) =
    refl ⊢A₁
  equal-ty-red-U-sound _ _ _ ⊢A₁ _ | just (Empty PE.refl) =
    refl ⊢A₁
  equal-ty-red-U-sound _ _ _ ⊢A₁ _ | just (Unit PE.refl) =
    refl ⊢A₁
  equal-ty-red-U-sound _ {n} eq ⊢Μ ⊢A₁ ⊢A₂ | just (ΠΣ _ _ _ _ PE.refl)
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv PE.refl _ eq =
    let inv _ eq₃ eq  = inv->>= eq
        inv _ eq₄ eq  = inv->>= eq
        inv _ eq₅ eq₆ = inv->>= eq

        _ , _ , _ , _ , _ , ΠΣ-ok = inversion-ΠΣ-U ⊢A₁

        ⊢Γ            = wfTerm ⊢A₁
        ⊢A₁₁          = infer-U-sound n eq₁ ⊢Μ ⊢Γ
        ⊢A₁₂          = infer-U-sound n eq₂ ⊢Μ (∙ univ ⊢A₁₁)
        A₂₁≡A₂₁′      = check-sound′ n eq₃ ⊢Μ (Uⱼ ⊢Γ)
        _ , _ , ⊢A₂₁′ = wf-⊢≡∷ A₂₁≡A₂₁′
        A₂₂≡A₂₂′      = check-sound′ n eq₄ ⊢Μ (Uⱼ (∙ univ ⊢A₁₁))
        _ , _ , ⊢A₂₂′ = wf-⊢≡∷ A₂₂≡A₂₂′
        A₁₁≡A₂₁′      = equal-tm-sound′ n eq₅ ⊢Μ ⊢A₁₁ ⊢A₂₁′
        A₁₂≡A₂₂′      = equal-tm-sound′ n eq₆ ⊢Μ ⊢A₁₂ ⊢A₂₂′
    in
    ΠΣ-cong (trans A₁₁≡A₂₁′ (sym′ A₂₁≡A₂₁′))
      (trans A₁₂≡A₂₂′ (sym′ A₂₂≡A₂₂′)) ΠΣ-ok
  equal-ty-red-U-sound _ _ _ ⊢A₁ _ | just (ℕ PE.refl) =
    refl ⊢A₁
  equal-ty-red-U-sound _ {n} eq ⊢Μ ⊢A₁ ⊢A₂
    | just (Id _ _ _ _ _ _ PE.refl) =
   let inv _ eq₁ eq      = inv->>= eq
       inv _ eq₂ eq₃     = inv->>= eq
       ⊢A₁ , ⊢t₁₁ , ⊢t₁₂ = inversion-Id∷U ⊢A₁
       ⊢A₂ , ⊢t₂₁ , ⊢t₂₂ = inversion-Id∷U ⊢A₂
       A₁≡A₂             = equal-tm-sound′ n eq₁ ⊢Μ ⊢A₁ ⊢A₂
       A₂≡A₁             = sym (univ A₁≡A₂)
   in
   Id-cong A₁≡A₂
     (equal-tm-sound′ n eq₂ ⊢Μ ⊢t₁₁ (conv ⊢t₂₁ A₂≡A₁))
     (equal-tm-sound′ n eq₃ ⊢Μ ⊢t₁₂ (conv ⊢t₂₂ A₂≡A₁))
  equal-ty-red-U-sound _ {n} eq ⊢Μ ⊢A₁ _ | nothing
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv PE.refl _ _ =
    equal-ne-inf-red-sound n eq₁ ⊢Μ (wfTerm ⊢A₁)

  -- Soundness for equal-sub′.

  equal-sub′-sound :
    OK (equal-sub′ n (∇ » Δ) σ₁ Η₁ σ₂ Η₂) PE.refl γ →
    Meta-con-wf ∇ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Η₂ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ≡ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Η₂ ⌝ᶜᵛ γ
  equal-sub′-sound eq = equal-sub′-sound′ PE.refl eq

  private

    -- Soundness for equal-sub′.

    equal-sub′-sound′ :
      (n₁≡n₂ : n₁ PE.≡ n₂) →
      OK (equal-sub′ n (∇ » Δ) σ₁ Η₁ σ₂ Η₂) n₁≡n₂ γ →
      Meta-con-wf ∇ γ →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Η₂ ⌝ᶜᵛ γ →
      ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ˢʷ PE.subst (U.Subst _) n₁≡n₂ (⌜ σ₁ ⌝ˢ γ) ≡
        ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Η₂ ⌝ᶜᵛ γ
    equal-sub′-sound′ _ eq _ _ _
      with inv->>= eq
    equal-sub′-sound′ _ _ _ ⊢Δ _ | inv ε _ ok! =
      ⊢ˢʷ≡∷ε⇔ .proj₂ ⊢Δ
    equal-sub′-sound′ {n} {σ₁} {σ₂} _ _ ⊢Μ ⊢Δ (∙ ⊢A)
      | inv (ext Δ₁ _ Δ₂ A) _ eq
      with inv->>= eq
    … | inv _ ok! eq
      with inv->>= eq
    … | inv PE.refl eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let σ₁₊≡σ₂₊ =
            cast-⊢ˢʷ≡∷ (⌜tailₛ⌝ˢ σ₁) (⌜tailₛ⌝ˢ σ₂) $
            equal-sub′-sound eq₁ ⊢Μ ⊢Δ (wf ⊢A)
          _ , ⊢σ₁₊ , _ =
            wf-⊢ˢʷ≡∷ σ₁₊≡σ₂₊
          A[]≡A[] = substVar-to-subst (⌜tailₛ⌝ˢ σ₁) (⌜ A ⌝ _)
      in
      ⊢ˢʷ≡∷∙⇔′ ⊢A .proj₂
        ( σ₁₊≡σ₂₊
        , PE.subst₃ (_⊢_≡_∷_ _) (⌜headₛ⌝ σ₁) (⌜headₛ⌝ σ₂) A[]≡A[]
            (check-and-equal-tm-sound′ n eq₂ ⊢Μ
               (PE.subst (_⊢_ _) (PE.sym A[]≡A[]) (subst-⊢ ⊢A ⊢σ₁₊))
               .proj₂)
        )
    equal-sub′-sound′ {∇} _ _ _ ⊢Δ _ | inv base _ eq
      with inv->>= eq
    … | inv (both _ PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq ok! =
      refl-⊢ˢʷ≡∷ (equal-sub″-sound ∇ eq ⊢Δ)

  -- Soundness for check-and-equal-ty.

  check-and-equal-ty-sound′ :
    ∀ n →
    OK (check-and-equal-ty n Γ A₁ A₂) A γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A ⌝ γ ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  check-and-equal-ty-sound′ {A₁} {A₂} {γ} n eq ⊢Μ ⊢Γ
    with inv->>= eq
  … | inv A₁′ eq₁ eq
    with inv->>= eq
  … | inv A₂′ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let A₁≡A₁′   = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
        _ , ⊢A₁′ = wf-⊢≡ A₁≡A₁′
        A₂≡A₂′   = check-type-sound′ n eq₂ ⊢Μ ⊢Γ
        _ , ⊢A₂′ = wf-⊢≡ A₂≡A₂′
        A₁′≡A₂′  = equal-ty-sound′ n eq₃ ⊢Μ ⊢A₁′ ⊢A₂′
    in
    A₁≡A₁′ ,
    (⌜ A₁ ⌝ γ   ≡⟨ A₁≡A₁′ ⟩⊢
     ⌜ A₁′ ⌝ γ  ≡⟨ A₁′≡A₂′ ⟩⊢
     ⌜ A₂′ ⌝ γ  ≡˘⟨ A₂≡A₂′ ⟩⊢∎
     ⌜ A₂ ⌝ γ   ∎)
    where
    open TyR

  -- Soundness for check-and-equal-tm.

  check-and-equal-tm-sound′ :
    ∀ n →
    OK (check-and-equal-tm n Γ t₁ t₂ A) t γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-tm-sound′ {t₁} {t₂} {γ} n eq ⊢Μ ⊢Γ
    with inv->>= eq
  … | inv t₁′ eq₁ eq
    with inv->>= eq
  … | inv t₂′ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let t₁≡t₁′       = check-sound′ n eq₁ ⊢Μ ⊢Γ
        _ , _ , ⊢t₁′ = wf-⊢≡∷ t₁≡t₁′
        t₂≡t₂′       = check-sound′ n eq₂ ⊢Μ ⊢Γ
        _ , _ , ⊢t₂′ = wf-⊢≡∷ t₂≡t₂′
        t₁′≡t₂′      = equal-tm-sound′ n eq₃ ⊢Μ ⊢t₁′ ⊢t₂′
    in
    t₁≡t₁′ ,
    (⌜ t₁ ⌝ γ   ≡⟨ t₁≡t₁′ ⟩⊢
     ⌜ t₁′ ⌝ γ  ≡⟨ t₁′≡t₂′ ⟩⊢
     ⌜ t₂′ ⌝ γ  ≡˘⟨ t₂≡t₂′ ⟩⊢∎
     ⌜ t₂ ⌝ γ   ∎)
    where
    open TmR

opaque

  -- Soundness for check-type.

  check-type-sound :
    ∀ γ (Γ : Cons c m n) A n →
    check-type n Γ A .run (γ .metas) PE.≡ inj₂ (A′ , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ
  check-type-sound {Cs} _ _ _ n eq cs ⊢Μ ⊢Γ =
    wf-⊢≡ (check-type-sound′ n (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs)) ⊢Μ ⊢Γ)
      .proj₁

opaque

  -- Soundness for check.

  check-sound :
    ∀ γ (Γ : Cons c m n) t A n →
    check n Γ t A .run (γ .metas) PE.≡ inj₂ (t′ , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  check-sound {Cs} _ _ _ _ n eq cs ⊢Μ ⊢A =
    wf-⊢≡∷ (check-sound′ n (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs)) ⊢Μ ⊢A)
      .proj₂ .proj₁

opaque

  -- Soundness for equal-con.

  equal-con-sound :
    ∀ γ (Γ : Cons c m n) Δ n →
    equal-con n Γ Δ .run (γ .metas) PE.≡ inj₂ (tt , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Γ ⌝ᶜ γ .vars ≡ ⌜ Δ ⌝ᶜᵛ γ
  equal-con-sound {Cs} _ Γ _ _ eq cs =
    equal-con-sound′ {Γ = Γ} (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs))

opaque

  -- Soundness for check-sub.

  check-sub-sound :
    ∀ γ (∇ : DCon c m) Δ₂ (σ : Subst c n₂ n₁) Δ₁ n →
    check-sub n ∇ Δ₂ σ Δ₁ .run (γ .metas) PE.≡ inj₂ (σ′ , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf ∇ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₂ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ₂ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ ⌝ˢ γ ∷ ⌜ Δ₁ ⌝ᶜᵛ γ
  check-sub-sound {Cs} _ _ _ σ _ _ eq cs ⊢Μ ⊢Δ₂ ⊢Δ₁ =
    wf-⊢ˢʷ≡∷
      (check-sub-sound′ σ (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs)) ⊢Μ ⊢Δ₂ ⊢Δ₁)
      .proj₂ .proj₁

opaque

  -- Soundness for equal-ty.

  equal-ty-sound :
    ∀ γ (Γ : Cons c m n) A₁ A₂ n →
    equal-ty n Γ A₁ A₂ .run (γ .metas) PE.≡ inj₂ (tt , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  equal-ty-sound {Cs} _ _ _ _ n eq cs =
    equal-ty-sound′ n (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs))

opaque

  -- Soundness for equal-tm.

  equal-tm-sound :
    ∀ γ (Γ : Cons c m n) t₁ t₂ A n →
    equal-tm n Γ t₁ t₂ A .run (γ .metas) PE.≡ inj₂ (tt , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-tm-sound {Cs} _ _ _ _ _ n eq cs =
    equal-tm-sound′ n (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs))

opaque

  -- Soundness for check-type-and-term.

  check-type-and-term-sound′ :
    ∀ n →
    OK (check-type-and-term n Γ t A) (t′ , A′) γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    (⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ A′ ⌝ γ) ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ t′ ⌝ γ ∷ ⌜ A ⌝ γ
  check-type-and-term-sound′ n eq ⊢Μ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let A≡A′    = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
        _ , ⊢A′ = wf-⊢≡ A≡A′
        t≡t′    = check-sound′ n eq₂ ⊢Μ ⊢A′
    in
    A≡A′ , conv t≡t′ (sym A≡A′)

opaque

  -- Soundness for check-type-and-term.

  check-type-and-term-sound :
    ∀ γ (Γ : Cons c m n) t A n →
    check-type-and-term n Γ t A .run (γ .metas) PE.≡
      inj₂ ((t′ , A′) , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  check-type-and-term-sound {Cs} _ _ _ _ n eq cs ⊢Μ ⊢Γ =
    wf-⊢≡∷
      (check-type-and-term-sound′ n (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs)) ⊢Μ ⊢Γ
         .proj₂)
      .proj₂ .proj₁

opaque

  -- Soundness for check-and-equal-ty.

  check-and-equal-ty-sound :
    ∀ γ (Γ : Cons c m n) A₁ A₂ n →
    check-and-equal-ty n Γ A₁ A₂ .run (γ .metas) PE.≡ inj₂ (A , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  check-and-equal-ty-sound {Cs} _ _ _ _ n eq cs ⊢Μ ⊢Γ =
    check-and-equal-ty-sound′ n (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs)) ⊢Μ ⊢Γ
      .proj₂

opaque

  -- Soundness for check-and-equal-tm.

  check-and-equal-tm-sound :
    ∀ γ (Γ : Cons c m n) t₁ t₂ A n →
    check-and-equal-tm n Γ t₁ t₂ A .run (γ .metas) PE.≡ inj₂ (t , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-tm-sound {Cs} _ _ _ _ _ n eq cs ⊢Μ ⊢A =
    check-and-equal-tm-sound′ n (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs)) ⊢Μ ⊢A
      .proj₂

opaque

  -- Soundness for check-and-equal-type-and-terms.

  check-and-equal-type-and-terms-sound′ :
    ∀ n →
    OK (check-and-equal-type-and-terms n Γ t₁ t₂ A) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-type-and-terms-sound′ n eq ⊢Μ ⊢Γ =
    let inv _ eq₁ eq = inv->>= eq
        inv _ eq₂ _  = inv->>= eq
        A≡A′         = check-type-sound′ n eq₁ ⊢Μ ⊢Γ
        _ , ⊢A′      = wf-⊢≡ A≡A′
        _ , t₁≡t₂    = check-and-equal-tm-sound′ n eq₂ ⊢Μ ⊢A′
    in
    conv t₁≡t₂ (sym A≡A′)

opaque

  -- Soundness for check-and-equal-type-and-terms.

  check-and-equal-type-and-terms-sound :
    ∀ γ (Γ : Cons c m n) t₁ t₂ A n →
    check-and-equal-type-and-terms n Γ t₁ t₂ A .run (γ .metas) PE.≡
      inj₂ (tt , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-type-and-terms-sound {Cs} _ _ _ _ _ n eq cs =
    check-and-equal-type-and-terms-sound′ n
      (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs))

opaque

  -- Soundness for equal-sub.

  equal-sub-sound′ :
    ∀ Δ →
    OK (equal-sub n Γ σ₁ σ₂ Δ) tt γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ≡ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ
  equal-sub-sound′ ε ok! _ _ ⊢σ₁ _ =
    ⊢ˢʷ≡∷ε⇔ .proj₂ (wf-⊢ˢʷ∷ ⊢σ₁)
  equal-sub-sound′ {n} {σ₁} {σ₂} (Δ ∙ B) eq ⊢Μ (∙ ⊢B) ⊢σ₁ ⊢σ₂ =
    let inv _ eq₁ eq₂ = inv->>= eq
        ⊢σ₁₊ , ⊢σ₁₀   = ⊢ˢʷ∷∙⇔ .proj₁ ⊢σ₁
        ⊢σ₂₊ , ⊢σ₂₀   = ⊢ˢʷ∷∙⇔ .proj₁ ⊢σ₂
        σ₁₊≡σ₂₊       =
          cast-⊢ˢʷ≡∷ (⌜tailₛ⌝ˢ σ₁) (⌜tailₛ⌝ˢ σ₂) $
          equal-sub-sound′ Δ eq₁ ⊢Μ (wf ⊢B)
            (cast-⊢ˢʷ∷ (PE.sym ∘→ ⌜tailₛ⌝ˢ σ₁) ⊢σ₁₊)
            (cast-⊢ˢʷ∷ (PE.sym ∘→ ⌜tailₛ⌝ˢ σ₂) ⊢σ₂₊)
        B[]≡B[] =
          substVar-to-subst (⌜tailₛ⌝ˢ σ₁) (⌜ B ⌝ _)
    in
    ⊢ˢʷ≡∷∙⇔′ ⊢B .proj₂
      ( σ₁₊≡σ₂₊
      , PE.subst₃ (_⊢_≡_∷_ _) (⌜headₛ⌝ σ₁) (⌜headₛ⌝ σ₂) B[]≡B[]
          (equal-tm-sound′ n eq₂ ⊢Μ
             (PE.subst₂ (_⊢_∷_ _)
                (PE.sym (⌜headₛ⌝ σ₁)) (PE.sym B[]≡B[])
                ⊢σ₁₀)
             (PE.subst₂ (_⊢_∷_ _)
                (PE.sym (⌜headₛ⌝ σ₂)) (PE.sym B[]≡B[]) $
              conv ⊢σ₂₀ (sym (subst-⊢≡ (refl ⊢B) σ₁₊≡σ₂₊))))
      )
  equal-sub-sound′ {Γ} base eq _ _ ⊢σ₁ _
    with inv->>= eq
  … | inv (both _ PE.refl) _ eq =
    refl-⊢ˢʷ≡∷ (equal-sub″-sound (Γ .defs) eq (wf-⊢ˢʷ∷ ⊢σ₁))

opaque

  -- Soundness for equal-sub.

  equal-sub-sound :
    ∀ γ (Γ : Cons c m n₂) (σ₁ σ₂ : Subst c n₂ n₁) Δ n →
    equal-sub n Γ σ₁ σ₂ Δ .run (γ .metas) PE.≡ inj₂ (tt , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ≡ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ
  equal-sub-sound {Cs} _ _ _ _ Δ _ eq cs =
    equal-sub-sound′ Δ (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs))

opaque

  -- Soundness for check-con.

  check-con-sound′ :
    ∀ (Δ : Con c n) {n} →
    OK (check-con n ∇ Δ) Δ′ γ →
    Meta-con-wf ∇ γ →
    (Base-con-allowed c → ⌜ ∇ ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    » ⌜ ∇ ⌝ᶜᵈ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ ≡ ⌜ Δ′ ⌝ᶜᵛ γ
  check-con-sound′ (base {b}) ok! _ ⊢base _ =
    reflConEq (⊢base b)
  check-con-sound′ ε ok! _ _ »∇ =
    reflConEq (ε »∇)
  check-con-sound′ (Δ ∙ _) {n} eq ⊢Μ ⊢base »∇
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let Δ≡Δ′        = check-con-sound′ Δ eq₁ ⊢Μ ⊢base »∇
        _ , ⊢Δ′ , _ = contextConvSubst Δ≡Δ′
        A≡A′        = check-type-sound′ n eq₂ ⊢Μ ⊢Δ′
    in
    Δ≡Δ′ ∙ stabilityEq (symConEq Δ≡Δ′) A≡A′

opaque

  -- Soundness for check-con.

  check-con-sound :
    ∀ γ (∇ : DCon c m) (Δ : Con c n) n →
    check-con n ∇ Δ .run (γ .metas) PE.≡ inj₂ (Δ′ , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf ∇ γ →
    (Base-con-allowed c → ⌜ ∇ ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    » ⌜ ∇ ⌝ᶜᵈ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ
  check-con-sound {Cs} _ _ Γ _ eq cs ⊢Μ ⊢base »∇ =
    contextConvSubst
      (check-con-sound′ Γ (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs)) ⊢Μ ⊢base »∇)
      .proj₁

opaque

  -- Soundness for check-dcon.

  check-dcon-sound′ :
    (∇ : DCon c m) →
    OK (check-dcon n ∇) tt γ →
    » γ .⌜base⌝ .defs →
    » ⌜ ∇ ⌝ᶜᵈ γ
  check-dcon-sound′ (base nothing) _ ⊢base =
    ⊢base
  check-dcon-sound′ (base (just _)) (ok PE.refl (L.lift eq)) ⊢base =
    Transitive.unfold-» eq ⊢base
  check-dcon-sound′ ε _ _ =
    ε
  check-dcon-sound′ {n} (∇ ∙⟨ tra ⟩[ _ ∷ _ ]) eq ⊢base =
    let inv ms≡0 _   eq  = inv->>= eq
        inv _    eq₁ eq  = inv->>= eq
        inv _    eq₂ _   = inv->>= eq
        _ , t≡t′         = check-type-and-term-sound′ n eq₂
                             (Meta-con-wf-empty ms≡0)
                             (ε (check-dcon-sound′ ∇ eq₁ ⊢base))
        _ , ⊢t , _       = wf-⊢≡∷ t≡t′
    in
    ∙ᵗ[ ⊢t ]
  check-dcon-sound′ {n} (∇ ∙⟨ opa _ ⟩[ _ ∷ _ ]) eq ⊢base
    using inv ms≡0 _   eq ← inv->>= eq
        | inv _    eq₁ eq ← inv->>= eq
        | inv _    eq₂ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ eq₃ (ok PE.refl (opacity-ok , unfolding≡trans)) =
    let »∇     = check-dcon-sound′ ∇ eq₁ ⊢base
        A≡A′   = check-type-sound′ n eq₂ (Meta-con-wf-empty ms≡0) (ε »∇)
        ⊢A , _ = wf-⊢≡ A≡A′
        ⊢t     =
          PE.subst₃ _⊢_∷_
            (PE.cong (flip U._»_ _) (⌜Trans⌝ᶜᵈ ∇)) PE.refl PE.refl $
          wf-⊢≡∷
            (check-sound′ n eq₃ (Meta-con-wf-empty ms≡0)
               (PE.subst (flip _⊢_ _)
                  (PE.cong (flip U._»_ _) (PE.sym (⌜Trans⌝ᶜᵈ ∇))) $
                Transitive.unfold-⊢ unfolding≡trans ⊢A))
            .proj₂ .proj₁
    in
    ∙ᵒ⟨ opacity-ok ⟩[ ⊢t ∷ ⊢A ]

opaque

  -- Soundness for check-dcon.

  check-dcon-sound :
    ∀ γ (∇ : DCon c m) n →
    check-dcon n ∇ .run (γ .metas) PE.≡ inj₂ (tt , Cs) →
    ⟦ Cs ⟧ γ →
    » γ .⌜base⌝ .defs →
    » ⌜ ∇ ⌝ᶜᵈ γ
  check-dcon-sound {Cs} _ ∇ _ eq cs =
    check-dcon-sound′ ∇ (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs))

opaque

  -- Soundness for check-cons.

  check-cons-sound′ :
    ∀ (Γ : Cons c m n) {n} →
    OK (check-cons n Γ) Γ′ γ →
    Meta-con-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    Γ .defs PE.≡ Γ′ .defs ×
    ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ ⌜ Γ .vars ⌝ᶜᵛ γ ≡ ⌜ Γ′ .vars ⌝ᶜᵛ γ
  check-cons-sound′ (∇ » Γ) eq ⊢Μ ⊢base₁ ⊢base₂
    using inv _ eq₁ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let »∇ = check-dcon-sound′ ∇ eq₁ ⊢base₁ in
    PE.refl , check-con-sound′ Γ eq₂ ⊢Μ ⊢base₂ »∇

opaque

  -- Soundness for check-cons.

  check-cons-sound :
    ∀ γ (Γ : Cons c m n) n →
    check-cons n Γ .run (γ .metas) PE.≡ inj₂ (Γ′ , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⊢ ⌜ Γ ⌝ᶜ γ
  check-cons-sound {Cs} _ Γ _ eq cs ⊢Μ ⊢base₁ ⊢base₂ =
    contextConvSubst
      (check-cons-sound′ Γ (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs)) ⊢Μ ⊢base₁
         ⊢base₂ .proj₂)
      .proj₁

opaque

  -- Soundness for check-cons-type-and-term.

  check-cons-type-and-term-sound′ :
    ∀ (Γ : Cons c m n) {n} →
    OK (check-cons-type-and-term n Γ t A) tt γ →
    Meta-con-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  check-cons-type-and-term-sound′ Γ {n} eq ⊢Μ ⊢base₁ ⊢base₂
    with inv->>= eq
  … | inv _ eq₁ eq
    using inv _ eq₂ _ ← inv->>= eq
    with check-cons-sound′ Γ eq₁ ⊢Μ ⊢base₁ ⊢base₂
  … | PE.refl , Δ≡Δ′ =
    let _ , ⊢Δ′ , _ = contextConvSubst Δ≡Δ′
        _ , t≡t′    = check-type-and-term-sound′ n eq₂ ⊢Μ ⊢Δ′
        _ , ⊢t , _  = wf-⊢≡∷ t≡t′
    in
    stabilityTerm (symConEq Δ≡Δ′) ⊢t

opaque

  -- Soundness for check-cons-type-and-term.

  check-cons-type-and-term-sound :
    ∀ γ (Γ : Cons c m n) t A n →
    check-cons-type-and-term n Γ t A .run (γ .metas) PE.≡
      inj₂ (tt , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  check-cons-type-and-term-sound {Cs} _ Γ _ _ _ eq cs =
    check-cons-type-and-term-sound′ Γ (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs))

opaque

  -- Soundness for check-and-equal-cons-type-and-terms.

  check-and-equal-cons-type-and-terms-sound′ :
    ∀ (Γ : Cons c m n) {n} →
    OK (check-and-equal-cons-type-and-terms n Γ t₁ t₂ A) tt γ →
    Meta-con-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-cons-type-and-terms-sound′ Γ {n} eq ⊢Μ ⊢base₁ ⊢base₂
    with inv->>= eq
  … | inv _ eq₁ eq₂
    with check-cons-sound′ Γ eq₁ ⊢Μ ⊢base₁ ⊢base₂
  … | PE.refl , Δ≡Δ′ =
    let _ , ⊢Δ′ , _ = contextConvSubst Δ≡Δ′
        t₁≡t₂       = check-and-equal-type-and-terms-sound′ n eq₂ ⊢Μ ⊢Δ′
    in
    stabilityEqTerm (symConEq Δ≡Δ′) t₁≡t₂

opaque

  -- Soundness for check-and-equal-cons-type-and-terms.

  check-and-equal-cons-type-and-terms-sound :
    ∀ γ (Γ : Cons c m n) t₁ t₂ A n →
    check-and-equal-cons-type-and-terms n Γ t₁ t₂ A .run (γ .metas) PE.≡
      inj₂ (tt , Cs) →
    ⟦ Cs ⟧ γ →
    Meta-con-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-cons-type-and-terms-sound {Cs} _ Γ _ _ _ _ eq cs =
    check-and-equal-cons-type-and-terms-sound′ Γ
      (ok eq (⟦⟧⇔⟦⟧′ Cs .proj₁ cs))
