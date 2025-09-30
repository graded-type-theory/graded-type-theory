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

open Modality 𝕄
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Typed R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening.Definition R
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
    m n  : Nat
    ∇ ∇′ : DCon (Term 0) m
    ξ    : DExt _ _ _
    Δ Ε  : Con Term n
    Γ    : Cons m n
    σ    : Subst _ _
    t u  : Term n
    p q  : M

opaque

  -- If ∇ » Ε is consistent and there is a substitution from Δ to Ε
  -- under ∇, then ∇ » Δ is consistent.

  subst-Consistent :
    ∇ » Ε ⊢ˢʷ σ ∷ Δ → Consistent (∇ » Ε) → Consistent (∇ » Δ)
  subst-Consistent ⊢σ consistent _ ⊢t = consistent _ (subst-⊢∷ ⊢t ⊢σ)

opaque

  -- If there is some way to instantiate all the types in Δ, then Δ is
  -- consistent.

  inhabited-consistent : ∇ » ε ⊢ˢʷ σ ∷ Δ → Consistent (∇ » Δ)
  inhabited-consistent = flip subst-Consistent (λ _ → ¬Empty)

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- then zero is not definitionally equal to suc t.

  zero≢suc :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ zero ≡ suc t ∷ ℕ
  zero≢suc {Γ} {t} =
    Γ ⊢ zero ≡ suc t ∷ ℕ                 →⟨ reducible-⊩≡∷ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ)  →⟨ ⊩zero≡suc∷ℕ⇔ .proj₁ ∘→ proj₂ ⟩
    ⊥                                    □

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- then zero is not definitionally equal to one.

  zero≢one :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ zero ≡ suc zero ∷ ℕ
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
-- Consistency, glassification, inlining and context extensions

opaque

  -- If glassify ∇ and Δ are consistent, then ∇ and Δ are consistent.

  Consistent-glassify→Consistent :
    Consistent (glassify ∇ » Δ) →
    Consistent (∇ » Δ)
  Consistent-glassify→Consistent consistent _ =
    consistent _ ∘→ glassify-⊢∷

opaque
  unfolding inline

  -- If ε and inline-Con ∇ Δ are consistent, then ∇ and Δ are
  -- consistent.

  Consistent-inline-Con→Consistent :
    Consistent (ε » inline-Con ∇ Δ) →
    Consistent (∇ » Δ)
  Consistent-inline-Con→Consistent consistent _ =
    consistent _ ∘→ ⊢inline∷

opaque

  -- If ∇′ » Δ is consistent, where ∇′ is a well-formed extension of
  -- ∇, then ∇ » Δ is consistent.

  Consistent-⊇→Consistent :
    ξ » ∇′ ⊇ ∇ →
    Consistent (∇′ » Δ) →
    Consistent (∇ » Δ)
  Consistent-⊇→Consistent ∇′⊇∇ consistent _ =
    consistent _ ∘→ defn-wkTerm ∇′⊇∇

opaque
  unfolding inline inline-Con

  -- If opacity is allowed, then consistency is not preserved by
  -- glassification, inlining or context extension: there is a
  -- definition context ∇ and well-formed context Γ that are
  -- consistent, but for which glassify ∇ » Γ and ε » inline-Con ∇ Γ
  -- are not consistent, and for which there is an extended context ∇′
  -- such that ∇′ » Γ is not consistent.

  consistency-is-not-preserved :
    Opacity-allowed →
    ∃₄ λ m n (∇ : DCon (Term 0) m) (Γ : Con Term n) →
       ∇ »⊢ Γ ×
       Consistent (∇ » Γ) ×
       ¬ Consistent (glassify ∇ » Γ) ×
       ¬ Consistent (ε » inline-Con ∇ Γ) ×
       ∃₃ λ m′ ξ (∇′ : DCon (Term 0) m′) →
         ξ » ∇′ ⊇ ∇ × ¬ Consistent (∇′ » Γ)
  consistency-is-not-preserved ok =
    _ , _ , Opaque[ Empty ∷ U 0 ] , ε ∙ defn 0 , ∙ ⊢0 , consistent ,
    (λ hyp → hyp _ inconsistent₁) ,
    (λ hyp → hyp _ inconsistent₂) ,
    _ , _ , _ , ∙⊇ ,
    (λ hyp → hyp _ inconsistent₃)
    where
    ⊢ε : Opaque[ Empty ∷ U 0 ] »⊢ ε
    ⊢ε = ε (»Opaque ok (Emptyⱼ εε))

    ⊢0∷U : Opaque[ Empty ∷ U 0 ] » ε ⊢ defn 0 ∷ U 0
    ⊢0∷U = defn ⊢ε here PE.refl

    ⊢0 : Opaque[ Empty ∷ U 0 ] » ε ⊢ defn 0
    ⊢0 = univ ⊢0∷U

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

    ∙⊇ :
      step id (opa (ε ¹)) (Id (U 0) (defn 0) Empty) rfl »
      Opaque[ Empty ∷ U 0 ]
        ∙⟨ opa (ε ¹) ⟩[ rfl ∷ Id (U 0) (defn 0) Empty ] ⊇
      Opaque[ Empty ∷ U 0 ]
    ∙⊇ =
      stepᵒ₁ ok (Idⱼ′ ⊢0∷U (Emptyⱼ ⊢ε)) (ones-»↜ _)
        (rflⱼ′ (δ-red (glassify-⊢′ ⊢ε) here PE.refl PE.refl))

    ⊢0″ :
      Opaque[ Empty ∷ U 0 ]
        ∙⟨ opa (ones 1) ⟩[ rfl ∷ Id (U 0) (defn 0) Empty ] »
      ε ⊢ defn 0
    ⊢0″ = defn-wk ∙⊇ ⊢0

    inconsistent₃ :
      Opaque[ Empty ∷ U 0 ]
        ∙⟨ opa (ones 1) ⟩[ rfl ∷ Id (U 0) (defn 0) Empty ] »
      ε ∙ defn 0 ⊢
      subst 𝟙 (U 0) (var x0) (defn 0) Empty (defn 1) (var x0) ∷ Empty
    inconsistent₃ =
      ⊢subst (univ (var₀ (Uⱼ (∙ ⊢0″)))) (defn (∙ ⊢0″) here PE.refl)
        (var₀ ⊢0″)

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
          consistency-is-not-preserved ok
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
    let _ , _ , _ , _ , ⊢Γ , con , _ , not-con , _ =
          consistency-is-not-preserved ok
    in
    not-con (hyp ⊢Γ con)

opaque

  -- If opacity is allowed then it is not in general the case that, if
  -- ∇ »⊢ Γ, and ∇ and Γ are consistent, then ∇′ and Γ are consistent
  -- for every well-formed extension ∇′ of ∇.

  ¬Consistent→Consistent-⊇ :
    Opacity-allowed →
    ¬ (∀ {m m′ n} {∇ : DCon (Term 0) m} {∇′ : DCon (Term 0) m′}
         {ξ : DExt (Term 0) m′ m} {Γ : Con Term n} →
       ∇ »⊢ Γ → ξ » ∇′ ⊇ ∇ →
       Consistent (∇ » Γ) →
       Consistent (∇′ » Γ))
  ¬Consistent→Consistent-⊇ ok hyp =
    let _ , _ , _ , _ , ⊢Γ , con , _ , _ , _ , _ , _ , ∇′⊇∇ , not-con =
          consistency-is-not-preserved ok
    in
    not-con (hyp ⊢Γ ∇′⊇∇ con)
