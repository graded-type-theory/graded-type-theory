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
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
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
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Vec using (ε)

private
  variable
    m n  : Nat
    ∇ ∇′ : DCon (Term 0) m
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
  unfolding inlineᵈ

  -- If ε and inline-Conᵈ ∇ Δ are consistent, then ∇ and Δ are
  -- consistent.

  Consistent-inline-Con→Consistent :
    Consistent (ε » inline-Conᵈ ∇ Δ) →
    Consistent (∇ » Δ)
  Consistent-inline-Con→Consistent consistent _ =
    consistent _ ∘→ ⊢inlineᵈ∷

opaque

  -- If ∇′ » Δ is consistent, where ∇′ is a well-formed extension of
  -- ∇, then ∇ » Δ is consistent.

  Consistent-⊇→Consistent :
    » ∇′ ⊇ ∇ →
    Consistent (∇′ » Δ) →
    Consistent (∇ » Δ)
  Consistent-⊇→Consistent ∇′⊇∇ consistent _ =
    consistent _ ∘→ defn-wkTerm ∇′⊇∇

opaque
  unfolding Trans ones inlineᵈ

  -- If opacity is allowed, then consistency is not preserved by
  -- glassification, inlining or context extension: there is a
  -- definition context ∇ and well-formed context Γ that are
  -- consistent, but for which glassify ∇ » Γ and ε » inline-Conᵈ ∇ Γ
  -- are not consistent, and for which there is an extended context ∇′
  -- such that ∇′ » Γ is not consistent.

  consistency-is-not-preserved :
    Opacity-allowed →
    ∃₄ λ m n (∇ : DCon (Term 0) m) (Γ : Con Term n) →
       ∇ »⊢ Γ ×
       Consistent (∇ » Γ) ×
       ¬ Consistent (glassify ∇ » Γ) ×
       ¬ Consistent (ε » inline-Conᵈ ∇ Γ) ×
       ∃₂ λ m′ (∇′ : DCon (Term 0) m′) →
         » ∇′ ⊇ ∇ × ¬ Consistent (∇′ » Γ)
  consistency-is-not-preserved ok =
    _ , _ , Opaque[ Empty ∷ U 0 ] , ε ∙ defn 0 , ∙ ⊢0 , consistent ,
    (λ hyp → hyp _ inconsistent₁) ,
    (λ hyp → hyp _ inconsistent₂) ,
    _ , _ , ∙⊇ ,
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
      ε » inline-Conᵈ Opaque[ Empty ∷ U 0 ] (ε ∙ defn 0) ⊢
        var x0 ∷ Empty
    inconsistent₂ =
      var₀ (Emptyⱼ εε)

    ∙⊇ :
      » Opaque[ Empty ∷ U 0 ]
          ∙⟨ opa (ε ¹) ⟩[ rfl ∷ Id (U 0) (defn 0) Empty ] ⊇
        Opaque[ Empty ∷ U 0 ]
    ∙⊇ =
      stepᵒ₁ ok (Idⱼ′ ⊢0∷U (Emptyⱼ ⊢ε))
        (rflⱼ′ (δ-red (glassify-⊢′ ⊢ε) here PE.refl PE.refl))

    ⊢0″ :
      Opaque[ Empty ∷ U 0 ]
        ∙⟨ opa ones ⟩[ rfl ∷ Id (U 0) (defn 0) Empty ] »
      ε ⊢ defn 0
    ⊢0″ = defn-wk ∙⊇ ⊢0

    inconsistent₃ :
      Opaque[ Empty ∷ U 0 ]
        ∙⟨ opa ones ⟩[ rfl ∷ Id (U 0) (defn 0) Empty ] »
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
  -- ∇ »⊢ Γ, and ∇ and Γ are consistent, then ε and inline-Conᵈ ∇ Γ
  -- are consistent.

  ¬Consistent→Consistent-inline-Con :
    Opacity-allowed →
    ¬ (∀ {m n} {∇ : DCon (Term 0) m} {Γ : Con Term n} →
       ∇ »⊢ Γ →
       Consistent (∇ » Γ) →
       Consistent (ε » inline-Conᵈ ∇ Γ))
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
         {Γ : Con Term n} →
       ∇ »⊢ Γ → » ∇′ ⊇ ∇ →
       Consistent (∇ » Γ) →
       Consistent (∇′ » Γ))
  ¬Consistent→Consistent-⊇ ok hyp =
    let _ , _ , _ , _ , ⊢Γ , con , _ , _ , _ , _ , ∇′⊇∇ , not-con =
          consistency-is-not-preserved ok
    in
    not-con (hyp ⊢Γ ∇′⊇∇ con)

------------------------------------------------------------------------
-- An alternative notion of consistency

opaque

  -- An alternative notion of consistency, defined in response to
  -- ¬Consistent→Consistent-glassify,
  -- ¬Consistent→Consistent-inline-Con and ¬Consistent→Consistent-⊇.

  Consistentᵍ : Cons m n → Set a
  Consistentᵍ (∇ » Γ) = Consistent (glassify ∇ » Γ)

opaque
  unfolding Consistentᵍ

  -- Consistentᵍ Γ implies Consistent Γ.

  Consistentᵍ→Consistent :
    Consistentᵍ Γ → Consistent Γ
  Consistentᵍ→Consistent = Consistent-glassify→Consistent

opaque
  unfolding Consistentᵍ

  -- If opacity is allowed, then it is not necessarily the case that
  -- Consistent Γ implies Consistentᵍ Γ for every well-formed context
  -- pair Γ.

  ¬Consistent→Consistentᵍ :
    Opacity-allowed →
    ¬ (∀ {m n} {Γ : Cons m n} →
       ⊢ Γ → Consistent Γ → Consistentᵍ Γ)
  ¬Consistent→Consistentᵍ ok hyp =
    ¬Consistent→Consistent-glassify ok hyp

opaque
  unfolding Consistentᵍ

  -- If Consistentᵍ (∇ » Ε) holds and there is a substitution from Δ
  -- to Ε under ∇, then Consistentᵍ (∇ » Δ) holds.

  subst-Consistentᵍ :
    ∇ » Ε ⊢ˢʷ σ ∷ Δ → Consistentᵍ (∇ » Ε) →
    Consistentᵍ (∇ » Δ)
  subst-Consistentᵍ = subst-Consistent ∘→ glassify-⊢ˢʷ∷

opaque
  unfolding Consistentᵍ

  -- If there is some way to instantiate all the types in Δ (under ∇),
  -- then Consistentᵍ (∇ » Δ) holds.

  ⊢ˢʷ∷→Consistentᵍ :
    ∇ » ε ⊢ˢʷ σ ∷ Δ → Consistentᵍ (∇ » Δ)
  ⊢ˢʷ∷→Consistentᵍ =
    flip subst-Consistentᵍ (λ _ → ¬Empty)

opaque

  -- If ∇ is well-formed, then Consistentᵍ (∇ » ε) holds.

  Consistentᵍ-ε : » ∇ → Consistentᵍ (∇ » ε)
  Consistentᵍ-ε =
    ⊢ˢʷ∷→Consistentᵍ ∘→ ⊢ˢʷ∷-idSubst ∘→ ε

------------------------------------------------------------------------
-- Consistentᵍ, glassification, inlining and context extensions

opaque
  unfolding Consistentᵍ

  -- Consistentᵍ (glassify ∇ » Δ) is logically equivalent to
  -- Consistentᵍ (∇ » Δ).

  Consistentᵍ-glassify⇔Consistentᵍ :
    Consistentᵍ (glassify ∇ » Δ) ⇔
    Consistentᵍ (∇ » Δ)
  Consistentᵍ-glassify⇔Consistentᵍ {∇} {Δ} =
    Π-cong-⇔ λ t →
      (glassify (glassify ∇) » Δ ⊢ t ∷ Empty  ≡⟨ PE.cong₃ _⊢_∷_ (PE.cong (_» _) (glassify-idem _)) PE.refl PE.refl ⟩⇔
                 glassify ∇  » Δ ⊢ t ∷ Empty  □⇔)
      →-cong-⇔ id⇔

opaque
  unfolding Consistentᵍ inlineᵈ

  -- "Consistentᵍ (ε » inline-Conᵈ ∇ Δ) if glassify ∇ »⊢ Δ holds" is
  -- logically equivalent to Consistentᵍ (∇ » Δ).

  Consistentᵍ-inline-Con⇔Consistentᵍ :
    (glassify ∇ »⊢ Δ → Consistentᵍ (ε » inline-Conᵈ ∇ Δ)) ⇔
    Consistentᵍ (∇ » Δ)
  Consistentᵍ-inline-Con⇔Consistentᵍ =
    (λ consistent _ ⊢t →
       consistent (wfTerm ⊢t) _ $
       PE.subst₃ _⊢_∷_
         (PE.cong (_»_ _) inline-Conᵈ-glassify) PE.refl PE.refl $
       ⊢inlineᵈ∷ ⊢t) ,
    (λ consistent ⊢Δ _ →
       consistent _ ∘→
       stabilityTerm
         (PE.subst₃ _»⊢_≡_
            (glassify-idem _) inline-Conᵈ-glassify PE.refl $
          ⊢inline-Conᵈ≡ ⊢Δ) ∘→
       defn-wkTerm (»⊇ε (defn-wf ⊢Δ)))

opaque
  unfolding Consistentᵍ

  -- Consistentᵍ (∇ » Δ) holds if and only if, given that
  -- glassify ∇ »⊢ Δ holds, Consistentᵍ (∇′ » Δ) holds for all
  -- ∇′ for which » glassify ∇′ ⊇ glassify ∇ holds.
  --
  -- See also All-extensions-consistent⇔Consistentᵍ below.

  Consistentᵍ-⊇⇔Consistentᵍ :
    (∀ {n} {∇′ : DCon (Term 0) n} →
     glassify ∇ »⊢ Δ → » glassify ∇′ ⊇ glassify ∇ →
     Consistentᵍ (∇′ » Δ)) ⇔
    Consistentᵍ (∇ » Δ)
  Consistentᵍ-⊇⇔Consistentᵍ =
    (λ consistent _ ⊢t →
       consistent (wfTerm ⊢t) id⊇ _ ⊢t) ,
    (λ consistent ⊢Δ ∇′⊇∇ _ ⊢t →
       consistent _ $
       PE.subst₃ _⊢_∷_
         (PE.cong (_» _) $ glassify-idem _) PE.refl PE.refl $
       inhabited-under-glassified-context (Emptyⱼ ⊢Δ) ∇′⊇∇ ⊢t .proj₂)

------------------------------------------------------------------------
-- Another alternative notion of consistency

opaque

  -- Another alternative notion of consistency.
  --
  -- Below the terminology "all extensions of Γ are consistent" is
  -- used for All-extensions-consistent Γ, but note that it is only
  -- the definition context Γ .defs that is extended.

  All-extensions-consistent : Cons m n → Set a
  All-extensions-consistent (∇ » Γ) =
    ∀ {k} {∇′ : DCon (Term 0) k} → » ∇′ ⊇ ∇ → Consistent (∇′ » Γ)

opaque
  unfolding All-extensions-consistent Consistentᵍ

  -- If Γ is well-formed and either some Π-type is allowed or Γ .vars
  -- is empty, then All-extensions-consistent Γ is logically
  -- equivalent to Consistentᵍ Γ.

  All-extensions-consistent⇔Consistentᵍ :
    ∃₂ Π-allowed or-empty (Γ .vars) →
    ⊢ Γ →
    All-extensions-consistent Γ ⇔ Consistentᵍ Γ
  All-extensions-consistent⇔Consistentᵍ ok ⊢Γ =
    (λ consistent _ ⊢t →
       let _ , _ , _ , ∇′⊇∇ , ⊢u =
             inhabited-under-extension ok (Emptyⱼ ⊢Γ) ⊢t
       in
       consistent ∇′⊇∇ _ ⊢u) ,
    (λ consistent ∇′⊇∇ _ ⊢t →
       consistent _ $
       inhabited-under-glassified-context (Emptyⱼ ⊢Γ) ∇′⊇∇ ⊢t .proj₂)

opaque
  unfolding All-extensions-consistent

  -- If all extensions of Γ are consistent, then Γ is consistent.

  All-extensions-consistent→Consistent :
    All-extensions-consistent Γ → Consistent Γ
  All-extensions-consistent→Consistent = _$ id⊇

opaque
  unfolding All-extensions-consistent

  -- If opacity is allowed, then it is not necessarily the case that
  -- all extensions of a consistent, well-formed context pair are
  -- consistent.

  ¬Consistent→All-extensions-consistent :
    Opacity-allowed →
    ¬ (∀ {m n} {Γ : Cons m n} →
       ⊢ Γ → Consistent Γ → All-extensions-consistent Γ)
  ¬Consistent→All-extensions-consistent ok hyp =
    let _ , _ , _ , _ , ⊢Γ , con , _ , _ , _ , _ , ∇′⊇∇ , not-con =
          consistency-is-not-preserved ok
    in
    not-con (hyp ⊢Γ con ∇′⊇∇)

opaque
  unfolding All-extensions-consistent

  -- If all extensions of ∇ » Ε are consistent and there is a
  -- substitution from Δ to Ε under ∇, then all extensions of ∇ » Δ
  -- are consistent.

  subst-All-extensions-consistent :
    ∇ » Ε ⊢ˢʷ σ ∷ Δ → All-extensions-consistent (∇ » Ε) →
    All-extensions-consistent (∇ » Δ)
  subst-All-extensions-consistent ⊢σ consistent ∇′⊇∇ =
    subst-Consistent (defn-wkSubstʷ ∇′⊇∇ ⊢σ) (consistent ∇′⊇∇)

opaque
  unfolding All-extensions-consistent

  -- If there is some way to instantiate all the types in Δ (under ∇),
  -- then all extensions of ∇ » Δ are consistent.

  ⊢ˢʷ∷→All-extensions-consistent :
    ∇ » ε ⊢ˢʷ σ ∷ Δ → All-extensions-consistent (∇ » Δ)
  ⊢ˢʷ∷→All-extensions-consistent =
    flip subst-All-extensions-consistent (λ _ _ → ¬Empty)

opaque

  -- If ∇ is well-formed, then all extensions of ∇ » ε are consistent.

  All-extensions-consistent-ε : » ∇ → All-extensions-consistent (∇ » ε)
  All-extensions-consistent-ε =
    ⊢ˢʷ∷→All-extensions-consistent ∘→ ⊢ˢʷ∷-idSubst ∘→ ε
