------------------------------------------------------------------------
-- Some assumptions used to define the logical relation for erasure
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Assumptions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Graded.Erasure.Target as T using (Strictness)

open import Tools.Fin
open import Tools.Function
open import Tools.Level using (lsuc)
open import Tools.List hiding (_∷_)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum

private variable
  m n                           : Nat
  Γ                             : Cons _ _
  A B C t t₁ t₂ u v v₁ v₂ w₁ w₂ : Term _
  l                             : Lvl _
  p q q′ r                      : M

------------------------------------------------------------------------
-- Is-reduction-relation

-- An axiomatisation of "reduction" relations that can be used in the
-- logical relation. The context is fixed.

record Is-reduction-relation
         (Γ : Cons m n) (_⇛_∷_ : Term n → Term n → Term n → Set a) :
         Set (lsuc a) where
  field
    -- Conversion.

    conv-⇛ : t ⇛ u ∷ A → Γ ⊢ A ≡ B → t ⇛ u ∷ B

    -- Reduction is contained in the relation.

    ⇒*→⇛ : Γ ⊢ t ⇒* u ∷ A → t ⇛ u ∷ A

    -- The relation is contained in definitional equality.

    ⇛→⊢≡ : t ⇛ u ∷ A → Γ ⊢ t ≡ u ∷ A

    -- Transitivity.

    trans-⇛ : t ⇛ u ∷ A → u ⇛ v ∷ A → t ⇛ v ∷ A

    -- If t "reduces" to both u and v, and u is a WHNF, then v
    -- "reduces" to u.

    whnf-⇛ : t ⇛ u ∷ A → Whnf (Γ .defs) u → t ⇛ v ∷ A → v ⇛ u ∷ A

    -- Some congruence properties.

    lower-⇛ :
      t₁ ⇛ t₂ ∷ Lift l A →
      lower t₁ ⇛ lower t₂ ∷ A

    app-⇛ :
      t₁ ⇛ t₂ ∷ Π p , q ▷ A ▹ B →
      Γ ⊢ u ∷ A →
      t₁ ∘⟨ p ⟩ u ⇛ t₂ ∘⟨ p ⟩ u ∷ B [ u ]₀

    fst-⇛ :
      t₁ ⇛ t₂ ∷ Σˢ p , q ▷ A ▹ B →
      fst p t₁ ⇛ fst p t₂ ∷ A

    snd-⇛ :
      t₁ ⇛ t₂ ∷ Σˢ p , q ▷ A ▹ B →
      snd p t₁ ⇛ snd p t₂ ∷ B [ fst p t₁ ]₀

    prodrec-⇛ :
      Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
      t₁ ⇛ t₂ ∷ Σʷ p , q′ ▷ A ▹ B →
      Γ »∙ A »∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
      prodrec r p q C t₁ u ⇛ prodrec r p q C t₂ u ∷ C [ t₁ ]₀

    natrec-⇛ :
      Γ ⊢ t ∷ A [ zero ]₀ →
      Γ »∙ ℕ »∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
      v₁ ⇛ v₂ ∷ ℕ →
      natrec p q r A t u v₁ ⇛ natrec p q r A t u v₂ ∷ A [ v₁ ]₀

    J-⇛ :
      Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
      Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
      w₁ ⇛ w₂ ∷ Id A t v →
      J p q A t B u v w₁ ⇛ J p q A t B u v w₂ ∷ B [ v , w₁ ]₁₀

    K-⇛ :
      Γ »∙ Id A t t ⊢ B →
      Γ ⊢ u ∷ B [ rfl ]₀ →
      v₁ ⇛ v₂ ∷ Id A t t →
      K-allowed →
      K p A t B u v₁ ⇛ K p A t B u v₂ ∷ B [ v₁ ]₀

  opaque

    -- If t reduces to u, then t and u are well-typed.

    wf-⇛ : t ⇛ u ∷ A → Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
    wf-⇛ = proj₂ ∘→ wf-⊢ ∘→ ⇛→⊢≡

opaque instance

  -- Reduction is a "reduction" relation.

  ⇒*-is-reduction-relation : Is-reduction-relation Γ (Γ ⊢_⇒*_∷_)
  ⇒*-is-reduction-relation = record
    { conv-⇛    = conv*
    ; ⇒*→⇛      = idᶠ
    ; ⇛→⊢≡      = subset*Term
    ; trans-⇛   = _⇨∷*_
    ; whnf-⇛    = λ t⇒*u u-whnf → whrDet↘Term (t⇒*u , u-whnf)
    ; lower-⇛   = lower-subst*
    ; app-⇛     = app-subst*
    ; fst-⇛     = fst-subst*
    ; snd-⇛     = snd-subst*
    ; prodrec-⇛ = prodrec-subst*
    ; natrec-⇛  = natrec-subst*
    ; J-⇛       = J-subst*
    ; K-⇛       = K-subst*
    }

opaque instance

  -- Definitional equality is a "reduction" relation.

  ≡-is-reduction-relation : Is-reduction-relation Γ (Γ ⊢_≡_∷_)
  ≡-is-reduction-relation = record
    { conv-⇛    = conv
    ; ⇒*→⇛      = subset*Term
    ; ⇛→⊢≡      = idᶠ
    ; trans-⇛   = trans
    ; whnf-⇛    = λ t≡u _ t≡v → trans (sym′ t≡v) t≡u
    ; lower-⇛   = lower-cong
    ; app-⇛     = λ t₁≡t₂ ⊢u → app-cong t₁≡t₂ (refl ⊢u)
    ; fst-⇛     = fst-cong′
    ; snd-⇛     = snd-cong′
    ; prodrec-⇛ = λ ⊢C t₁≡t₂ ⊢u →
                    prodrec-cong′ (refl ⊢C) t₁≡t₂ (refl ⊢u)
    ; natrec-⇛  = λ ⊢t ⊢u v₁≡v₂ →
                    natrec-cong (refl (⊢∙→⊢ (wf ⊢u))) (refl ⊢t)
                      (refl ⊢u) v₁≡v₂
    ; J-⇛       = λ ⊢B ⊢u w₁≡w₂ →
                    let ⊢A , ⊢t , ⊢v =
                          inversion-Id (wf-⊢ w₁≡w₂ .proj₁)
                    in
                    J-cong′ (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u)
                      (refl ⊢v) w₁≡w₂
    ; K-⇛       = λ ⊢B ⊢u v₁≡v₂ ok →
                    let ⊢A , ⊢t , _ =
                          inversion-Id (wf-⊢ v₁≡v₂ .proj₁)
                    in
                    K-cong (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) v₁≡v₂
                      ok
    }

opaque

  -- Propositional equality is a "reduction" relation
  -- * for the empty variable context, if the definition context is
  --   transparent, or
  -- * if equality reflection is allowed.

  Id-is-reduction-relation :
    Transparent (Γ .defs) × Empty-con (Γ .vars) ⊎ Equality-reflection →
    Is-reduction-relation Γ (λ t u A → ∃ λ v → Γ ⊢ v ∷ Id A t u)
  Id-is-reduction-relation {Γ} ok = record
    { conv-⇛    = λ (_ , ⊢v) A≡B →
                    let _ , ⊢t , ⊢u = inversion-Id (wf-⊢ ⊢v) in
                    _ , conv ⊢v (Id-cong A≡B (refl ⊢t) (refl ⊢u))
    ; ⇒*→⇛      = ⊢≡→⇛ ∘→ subset*Term
    ; ⇛→⊢≡      = ⇛→⊢≡
    ; trans-⇛   = λ (_ , ⊢v₁) (_ , ⊢v₂) → _ , ⊢transitivity ⊢v₁ ⊢v₂
    ; whnf-⇛    = λ (_ , ⊢v₁) _ (_ , ⊢v₂) →
                    _ , ⊢transitivity (⊢symmetry ⊢v₂) ⊢v₁
    ; lower-⇛   = ⊢≡→⇛ ∘→ R.lower-⇛ ∘→ ⇛→⊢≡
    ; app-⇛     = λ t₁⇛t₂ ⊢u → ⊢≡→⇛ (R.app-⇛ (⇛→⊢≡ t₁⇛t₂) ⊢u)
    ; fst-⇛     = ⊢≡→⇛ ∘→ R.fst-⇛ ∘→ ⇛→⊢≡
    ; snd-⇛     = ⊢≡→⇛ ∘→ R.snd-⇛ ∘→ ⇛→⊢≡
    ; prodrec-⇛ = λ ⊢C t₁⇛t₂ ⊢u → ⊢≡→⇛ (R.prodrec-⇛ ⊢C (⇛→⊢≡ t₁⇛t₂) ⊢u)
    ; natrec-⇛  = λ ⊢A ⊢u v₁⇛v₂ → ⊢≡→⇛ (R.natrec-⇛ ⊢A ⊢u (⇛→⊢≡ v₁⇛v₂))
    ; J-⇛       = λ ⊢B ⊢u w₁⇛w₂ → ⊢≡→⇛ (R.J-⇛ ⊢B ⊢u (⇛→⊢≡ w₁⇛w₂))
    ; K-⇛       = λ ⊢B ⊢u v₁⇛v₂ ok → ⊢≡→⇛ (R.K-⇛ ⊢B ⊢u (⇛→⊢≡ v₁⇛v₂) ok)
    }
    where
    module R = Is-reduction-relation (≡-is-reduction-relation {Γ = Γ})

    ⇛→⊢≡ : (∃ λ v → Γ ⊢ v ∷ Id A t u) → Γ ⊢ t ≡ u ∷ A
    ⇛→⊢≡ (_ , ⊢v) = case ok of λ where
      (inj₁ (transparent , ε)) →
        PE.subst₄ _⊢_≡_∷_
          (PE.cong (_» _) (PE.sym transparent)) PE.refl PE.refl PE.refl
          (ε⊢∷Id→ε⊢≡∷ ⊢v)
      (inj₂ ok) →
        equality-reflection′ ok ⊢v

    ⊢≡→⇛ : Γ ⊢ t ≡ u ∷ A → ∃ λ v → Γ ⊢ v ∷ Id A t u
    ⊢≡→⇛ t≡u = rfl , rflⱼ′ t≡u

------------------------------------------------------------------------
-- Assumptions

-- Assumptions used to define the logical relation for erasure.

record Assumptions : Set (lsuc a) where
  infix 4 _⇛_∷_

  field
    -- The size of the definition context below.
    {kᵈ} : Nat

    -- The size of the context below.
    {k} : Nat

    -- A definition context.
    {ts} : DCon (Term 0) kᵈ

    -- A variable context.
    {Δ} : Con Term k

    -- A definition context for the target language.
    vs : List (T.Term 0)

    -- The source contexts are well-formed.
    ⊢Δ : ts »⊢ Δ

    instance
      -- Var-included holds or Δ is empty.
      ⦃ no-equality-reflection-or-empty ⦄ :
        No-equality-reflection or-empty Δ

    -- Should applications be extracted to strict or non-strict
    -- applications?
    str : Strictness

    -- A "reduction" relation.
    _⇛_∷_ : Term k → Term k → Term k → Set a

    -- The "reduction" relation satisfies certain properties.
    is-reduction-relation : Is-reduction-relation (ts » Δ) _⇛_∷_

  open Is-reduction-relation is-reduction-relation public
