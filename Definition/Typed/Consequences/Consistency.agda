------------------------------------------------------------------------
-- Consistency of equality of natural numbers.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Consistency
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Substitution.Introductions R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    m n : Nat
    ∇   : DCon (Term 0) m
    Γ   : Con Term n
    σ   : Subst _ _
    t u : Term n

opaque

  -- If there is some way to instantiate all the types in Γ, then Γ is
  -- consistent.

  inhabited-consistent : ∇ » ε ⊢ˢʷ σ ∷ Γ → Consistent (∇ » Γ)
  inhabited-consistent ⊢σ _ ⊢t = ¬Empty (subst-⊢∷ ⊢t ⊢σ)

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- then zero is not definitionally equal to suc t.

  zero≢suc :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ¬ ∇ » Γ ⊢ zero ≡ suc t ∷ ℕ
  zero≢suc {Γ} {∇} {t} =
    ∇ » Γ ⊢ zero ≡ suc t ∷ ℕ                 →⟨ reducible-⊩≡∷ ⟩
    (∃ λ l → ∇ » Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ)  →⟨ ⊩zero≡suc∷ℕ⇔ .proj₁ ∘→ proj₂ ⟩
    ⊥                                        □

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- then zero is not definitionally equal to one.

  zero≢one :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ¬ ∇ » Γ ⊢ zero ≡ suc zero ∷ ℕ
  zero≢one = zero≢suc

opaque

  -- If equality reflection is allowed, then there is a context for
  -- which zero is definitionally equal to one.

  zero≡one :
    Equality-reflection →
    » ∇ →
    ∃ λ (Γ : Con Term 1) → ∇ » Γ ⊢ zero ≡ suc zero ∷ ℕ
  zero≡one ok »∇ =
    ε ∙ Id ℕ zero (suc zero) ,
    equality-reflection′ ok (var₀ (Idⱼ′ (zeroⱼ (ε »∇)) (sucⱼ (zeroⱼ (ε »∇)))))

opaque

  -- A variant of zero≢suc: the identity type Id ℕ zero (suc t) is not
  -- inhabited in the empty context.

  ¬-Id-ℕ-zero-suc : ¬ ∇ » ε ⊢ u ∷ Id ℕ zero (suc t)
  ¬-Id-ℕ-zero-suc {∇} {u} {t} =
    ∇ » ε ⊢ u ∷ Id ℕ zero (suc t)      →⟨ ε⊢∷Id→ε⊢≡∷ ⟩
    glassify ∇ » ε ⊢ zero ≡ suc t ∷ ℕ  →⟨ zero≢suc ⦃ ok = ε ⦄ ⟩
    ⊥                                  □

------------------------------------------------------------------------
-- Consistency, glassification and inlining

opaque

  -- If glassify ∇ and Γ are consistent, then ∇ and Γ are consistent.

  Consistent-glassify→Consistent :
    Consistent (glassify ∇ » Γ) →
    Consistent (∇ » Γ)
  Consistent-glassify→Consistent consistent _ =
    consistent _ ∘→ glassify-⊢∷

opaque
  unfolding inline

  -- If ε and inline-Con ∇ Γ are consistent, then ∇ and Γ are
  -- consistent.

  Consistent-inline-Con→Consistent :
    Consistent (ε » inline-Con ∇ Γ) →
    Consistent (∇ » Γ)
  Consistent-inline-Con→Consistent consistent _ =
    consistent _ ∘→ ⊢inline∷

opaque
  unfolding inline inline-Con

  -- If opacity is allowed, then consistency is not preserved by
  -- glassification or inlining: there is a definition context ∇ and
  -- well-formed context Γ that are consistent, but for which
  -- glassify ∇ and Γ are not consistent.

  consistency-is-not-preserved-by-glassification-or-inlining :
    Opacity-allowed →
    ∃₄ λ m n (∇ : DCon (Term 0) m) (Γ : Con Term n) →
       ∇ »⊢ Γ ×
       Consistent (∇ » Γ) ×
       ¬ Consistent (glassify ∇ » Γ) ×
       ¬ Consistent (ε » inline-Con ∇ Γ)
  consistency-is-not-preserved-by-glassification-or-inlining ok =
    _ , _ , Opaque[ Empty ∷ U 0 ] , ε ∙ defn 0 , ∙ ⊢0 , consistent ,
    (λ hyp → hyp _ inconsistent₁) ,
    (λ hyp → hyp _ inconsistent₂)
    where
    ⊢0 : Opaque[ Empty ∷ U 0 ] » ε ⊢ defn 0
    ⊢0 = univ (defn (ε (»Opaque ok (Emptyⱼ εε))) here PE.refl)

    ⊢0′ : glassify Opaque[ Empty ∷ U 0 ] » ε ⊢ defn 0
    ⊢0′ = glassify-⊢ ⊢0

    inconsistent₁ :
      glassify Opaque[ Empty ∷ U 0 ] » ε ∙ defn 0 ⊢ var x0 ∷ Empty
    inconsistent₁ =
      conv (var₀ ⊢0′) (univ (δ-red (∙ ⊢0′) here PE.refl PE.refl))

    inconsistent₂ :
      ε » inline-Con Opaque[ Empty ∷ U 0 ] (ε ∙ defn 0) ⊢ var x0 ∷ Empty
    inconsistent₂ =
      var₀ (Emptyⱼ εε)

    consistent : Consistent (Opaque[ Empty ∷ U 0 ] » ε ∙ defn 0)
    consistent t =
      let ⊢ε = ε ∙ᵗ[ ℕⱼ εε ] in
      Opaque[ Empty ∷ U 0 ]      » ε ∙ defn 0 ⊢ t ∷ Empty  →⟨ definition-irrelevant-⊢∷ ok (ℕⱼ εε) ⟩
      Opaque[ ℕ ∷ U 0 ]          » ε ∙ defn 0 ⊢ t ∷ Empty  →⟨ glassify-⊢∷ ⟩
      glassify Opaque[ ℕ ∷ U 0 ] » ε ∙ defn 0 ⊢ t ∷ Empty  →⟨ inhabited-consistent {σ = sgSubst _}
                                                                (→⊢ˢʷ∷∙ (⊢ˢʷ∷ε⇔ .proj₂ ⊢ε)
                                                                   (conv (zeroⱼ ⊢ε) (univ (sym′ (δ-red ⊢ε here PE.refl PE.refl))))) _ ⟩
      ⊥                                                    □

opaque

  -- If opacity is allowed then it is not in general the case that, if
  -- ∇ »⊢ Γ, and ∇ and Γ are consistent, then glassify ∇ and Γ are
  -- consistent.

  ¬Consistent→Consistent-glassify :
    Opacity-allowed →
    ¬ (∀ {m n} {∇ : DCon (Term 0) m} {Γ : Con Term n} →
       ∇ »⊢ Γ →
       Consistent (∇ » Γ) →
       Consistent (glassify ∇ » Γ))
  ¬Consistent→Consistent-glassify ok hyp =
    let _ , _ , _ , _ , ⊢Γ , con , not-con , _ =
          consistency-is-not-preserved-by-glassification-or-inlining ok
    in
    not-con (hyp ⊢Γ con)

opaque

  -- If opacity is allowed then it is not in general the case that, if
  -- ∇ »⊢ Γ, and ∇ and Γ are consistent, then ε and inline-Con ∇ Γ are
  -- consistent.

  ¬Consistent→Consistent-inline-Con :
    Opacity-allowed →
    ¬ (∀ {m n} {∇ : DCon (Term 0) m} {Γ : Con Term n} →
       ∇ »⊢ Γ →
       Consistent (∇ » Γ) →
       Consistent (ε » inline-Con ∇ Γ))
  ¬Consistent→Consistent-inline-Con ok hyp =
    let _ , _ , _ , _ , ⊢Γ , con , _ , not-con =
          consistency-is-not-preserved-by-glassification-or-inlining ok
    in
    not-con (hyp ⊢Γ con)
