------------------------------------------------------------------------
-- Substitution lemmas
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Substitution.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Term.Primitive R
open import Definition.Typed.Size R
open import Definition.Typed.Weakening R as W hiding (wk)

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Size
open import Tools.Size.Instances
open import Tools.Sum using (inj₂)

private variable
  m n                   : Nat
  x                     : Fin _
  Γ Δ Η                 : Con Term _
  A A₁ A₂ B t t₁ t₂ u v : Term _
  σ σ₁ σ₂ σ₃            : Subst _ _
  ρ                     : Wk _ _
  s s₂                  : Size
  p q                   : M

------------------------------------------------------------------------
-- An admissible equality rule

opaque

  -- Lambdas preserve definitional equality.
  --
  -- See also Definition.Typed.Properties.Admissible.Pi.lam-cong.

  lam-cong :
    Γ ∙ A ⊢ B →
    Γ ∙ A ⊢ t ∷ B →
    Γ ∙ A ⊢ u ∷ B →
    Γ ∙ A ⊢ t ≡ u ∷ B →
    Π-allowed p q →
    Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B
  lam-cong {Γ} {A} {B} {t} {u} {p} ⊢B ⊢t ⊢u t≡u ok =
    η-eq ⊢B (lamⱼ ⊢B ⊢t ok) (lamⱼ ⊢B ⊢u ok)
      (wk1 (lam p t) ∘⟨ p ⟩ var x0        ≡⟨ lemma ⊢t ⟩⊢
       wk (lift (step id)) t [ var x0 ]₀  ≡⟨ PE.subst₂ (_ ⊢_≡_∷ _) (PE.sym (wkSingleSubstId _)) (PE.sym (wkSingleSubstId _))
                                             t≡u ⟩⊢
       wk (lift (step id)) u [ var x0 ]₀  ≡⟨ sym ⊢B (lemma ⊢u) ⟩⊢∎
       wk1 (lam p u) ∘⟨ p ⟩ var x0        ∎)
      ok
    where
    lemma :
      Γ ∙ A ⊢ v ∷ B →
      Γ ∙ A ⊢
        wk1 (lam p v) ∘⟨ p ⟩ var x0 ≡
        wk (lift (step id)) v [ var x0 ]₀ ∷ B
    lemma ⊢v =
      let ⊢A  = ⊢∙→⊢ (wf ⊢B)
          ⊢A′ = wk₁ ⊢A ⊢A
          ρ   = liftʷ (step id) ⊢A′
      in
      PE.subst (_ ⊢ _ ≡ _ ∷_) (wkSingleSubstId _) $
      β-red (W.wk ρ ⊢B) (wkTerm ρ ⊢v) (var₀ ⊢A) PE.refl ok

------------------------------------------------------------------------
-- Well-formed substitutions

opaque

  infix 4 _⊢ˢʷ_∷_

  -- A variant of _⊢ˢ_∷_. The letter W stands for "well-formed": the
  -- target context must be well-formed.

  _⊢ˢʷ_∷_ : Con Term m → Subst m n → Con Term n → Set a
  Δ ⊢ˢʷ σ ∷ Γ = ⊢ Δ × Δ ⊢ˢ σ ∷ Γ

opaque
  unfolding _⊢ˢʷ_∷_

  -- A characterisation lemma for _⊢ˢʷ_∷_.

  ⊢ˢʷ∷⇔ : Δ ⊢ˢʷ σ ∷ Γ ⇔ (⊢ Δ × Δ ⊢ˢ σ ∷ Γ)
  ⊢ˢʷ∷⇔ = id⇔

opaque
  unfolding _⊢ˢʷ_∷_

  -- A characterisation lemma for _⊢ˢʷ_∷_.

  ⊢ˢʷ∷ε⇔ : Δ ⊢ˢʷ σ ∷ ε ⇔ ⊢ Δ
  ⊢ˢʷ∷ε⇔ = proj₁ , (_, id)

opaque
  unfolding _⊢ˢʷ_∷_

  -- A characterisation lemma for _⊢ˢʷ_∷_.

  ⊢ˢʷ∷∙⇔ :
    Δ ⊢ˢʷ σ ∷ Γ ∙ A ⇔
    (Δ ⊢ˢʷ tail σ ∷ Γ × Δ ⊢ head σ ∷ A [ tail σ ])
  ⊢ˢʷ∷∙⇔ =
    (λ { (⊢Δ , (⊢σ₊ , ⊢σ₀)) → (⊢Δ , ⊢σ₊) , ⊢σ₀ }) ,
    (λ ((⊢Δ , ⊢σ₊) , ⊢σ₀) → ⊢Δ , (⊢σ₊ , ⊢σ₀))

opaque
  unfolding _⊢ˢʷ_∷_

  -- A well-formedness lemma for _⊢ˢʷ_∷_.

  wf-⊢ˢʷ∷ : Δ ⊢ˢʷ σ ∷ Γ → ⊢ Δ
  wf-⊢ˢʷ∷ (⊢Δ , _) = ⊢Δ

------------------------------------------------------------------------
-- Well-formed equality of substitutions

opaque

  infix 4 _⊢ˢʷ_≡_∷_

  -- A variant of _⊢ˢ_≡_∷_.

  _⊢ˢʷ_≡_∷_ : Con Term m → Subst m n → Subst m n → Con Term n → Set a
  Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ =
    ⊢ Δ × Δ ⊢ˢ σ₁ ∷ Γ × Δ ⊢ˢ σ₂ ∷ Γ × Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ

opaque
  unfolding _⊢ˢʷ_≡_∷_

  -- A characterisation lemma for _⊢ˢʷ_≡_∷_.

  ⊢ˢʷ≡∷⇔ :
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ ⇔
    (⊢ Δ × Δ ⊢ˢ σ₁ ∷ Γ × Δ ⊢ˢ σ₂ ∷ Γ × Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ)
  ⊢ˢʷ≡∷⇔ = id⇔

opaque
  unfolding _⊢ˢʷ_≡_∷_

  -- A characterisation lemma for _⊢ˢʷ_≡_∷_.

  ⊢ˢʷ≡∷ε⇔ : Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ ε ⇔ ⊢ Δ
  ⊢ˢʷ≡∷ε⇔ = proj₁ , (_, (id , id , id))

opaque
  unfolding _⊢ˢʷ_≡_∷_

  -- A characterisation lemma for _⊢ˢʷ_≡_∷_.

  ⊢ˢʷ≡∷∙⇔ :
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ ∙ A ⇔
    (Δ ⊢ˢʷ tail σ₁ ≡ tail σ₂ ∷ Γ ×
     Δ ⊢ head σ₁ ∷ A [ tail σ₁ ] ×
     Δ ⊢ head σ₂ ∷ A [ tail σ₂ ] ×
     Δ ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ])
  ⊢ˢʷ≡∷∙⇔ =
    (λ { (⊢Δ , (⊢σ₁₊ , ⊢σ₁₀) , (⊢σ₂₊ , ⊢σ₂₀) , (σ₁₊≡σ₂₊ , σ₁₀≡σ₂₀)) →
         (⊢Δ , (⊢σ₁₊ , ⊢σ₂₊ , σ₁₊≡σ₂₊)) , ⊢σ₁₀ , ⊢σ₂₀ , σ₁₀≡σ₂₀ }) ,
    (λ ((⊢Δ , (⊢σ₁₊ , ⊢σ₂₊ , σ₁₊≡σ₂₊)) , ⊢σ₁₀ , ⊢σ₂₀ , σ₁₀≡σ₂₀) →
       (⊢Δ , (⊢σ₁₊ , ⊢σ₁₀) , (⊢σ₂₊ , ⊢σ₂₀) , (σ₁₊≡σ₂₊ , σ₁₀≡σ₂₀)))

opaque
  unfolding _⊢ˢʷ_∷_ _⊢ˢʷ_≡_∷_

  -- A well-formedness lemma for _⊢ˢʷ_≡_∷_.

  wf-⊢ˢʷ≡∷ :
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    ⊢ Δ × Δ ⊢ˢʷ σ₁ ∷ Γ × Δ ⊢ˢʷ σ₂ ∷ Γ
  wf-⊢ˢʷ≡∷ (⊢Δ , ⊢σ₁ , ⊢σ₂ , _) =
    ⊢Δ , (⊢Δ , ⊢σ₁) , (⊢Δ , ⊢σ₂)

------------------------------------------------------------------------
-- Some lemmas related to _⊢ˢʷ_∷_ and _⊢ˢʷ_≡_∷_

opaque

  -- Reflexivity for _⊢ˢ_≡_∷_.

  refl-⊢ˢ≡∷ :
    Δ ⊢ˢ σ ∷ Γ →
    Δ ⊢ˢ σ ≡ σ ∷ Γ
  refl-⊢ˢ≡∷ id        = id
  refl-⊢ˢ≡∷ (⊢σ , ⊢t) = refl-⊢ˢ≡∷ ⊢σ , refl ⊢t

opaque
  unfolding _⊢ˢʷ_∷_ _⊢ˢʷ_≡_∷_

  -- Reflexivity for _⊢ˢʷ_≡_∷_.
  --
  -- Symmetry and transitivity are proved below.

  refl-⊢ˢʷ≡∷ :
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ⊢ˢʷ σ ≡ σ ∷ Γ
  refl-⊢ˢʷ≡∷ (⊢Δ , ⊢σ) = ⊢Δ , ⊢σ , ⊢σ , refl-⊢ˢ≡∷ ⊢σ

opaque

  -- A lemma related to _•ₛ_.

  ⊢ˢʷ∷-•ₛ :
    ρ ∷ʷ Η ⊇ Δ →
    Δ ⊢ˢʷ σ ∷ Γ →
    Η ⊢ˢʷ ρ •ₛ σ ∷ Γ
  ⊢ˢʷ∷-•ₛ {Γ = ε} ρ⊇ _ =
    ⊢ˢʷ∷ε⇔ .proj₂ (wf-∷ʷ⊇ ρ⊇)
  ⊢ˢʷ∷-•ₛ {Γ = _ ∙ A} ρ⊇ ⊢σ =
    let ⊢σ₊ , ⊢σ₀ = ⊢ˢʷ∷∙⇔ .proj₁ ⊢σ in
    ⊢ˢʷ∷∙⇔ .proj₂
      (⊢ˢʷ∷-•ₛ ρ⊇ ⊢σ₊ ,
       PE.subst (_⊢_∷_ _ _) (wk-subst A) (wkTerm ρ⊇ ⊢σ₀))

opaque

  -- A lemma related to _•ₛ_.

  ⊢ˢʷ≡∷-•ₛ :
    ρ ∷ʷ Η ⊇ Δ →
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Η ⊢ˢʷ ρ •ₛ σ₁ ≡ ρ •ₛ σ₂ ∷ Γ
  ⊢ˢʷ≡∷-•ₛ {Γ = ε} ρ⊇ _ =
    ⊢ˢʷ≡∷ε⇔ .proj₂ (wf-∷ʷ⊇ ρ⊇)
  ⊢ˢʷ≡∷-•ₛ {Γ = _ ∙ A} ρ⊇ σ₁≡σ₂ =
    let σ₁₊≡σ₂₊ , ⊢σ₁₀ , ⊢σ₂₀ , σ₁₀≡σ₂₀ = ⊢ˢʷ≡∷∙⇔ .proj₁ σ₁≡σ₂ in
    ⊢ˢʷ≡∷∙⇔ .proj₂
      ( ⊢ˢʷ≡∷-•ₛ ρ⊇ σ₁₊≡σ₂₊
      , PE.subst (_⊢_∷_ _ _)     (wk-subst A) (wkTerm   ρ⊇ ⊢σ₁₀)
      , PE.subst (_⊢_∷_ _ _)     (wk-subst A) (wkTerm   ρ⊇ ⊢σ₂₀)
      , PE.subst (_⊢_≡_∷_ _ _ _) (wk-subst A) (wkEqTerm ρ⊇ σ₁₀≡σ₂₀)
      )

opaque

  -- A lemma related to wk1Subst.

  ⊢ˢʷ∷-wk1Subst :
    Δ ⊢ A →
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ∙ A ⊢ˢʷ wk1Subst σ ∷ Γ
  ⊢ˢʷ∷-wk1Subst ⊢A =
    ⊢ˢʷ∷-•ₛ (stepʷ id ⊢A)

opaque

  -- A lemma related to wk1Subst.

  ⊢ˢʷ≡∷-wk1Subst :
    Δ ⊢ A →
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A ⊢ˢʷ wk1Subst σ₁ ≡ wk1Subst σ₂ ∷ Γ
  ⊢ˢʷ≡∷-wk1Subst ⊢A =
    ⊢ˢʷ≡∷-•ₛ (stepʷ id ⊢A)

opaque

  -- A lemma related to idSubst.

  ⊢ˢʷ∷-idSubst :
    ⊢ Γ →
    Γ ⊢ˢʷ idSubst ∷ Γ
  ⊢ˢʷ∷-idSubst ε =
    ⊢ˢʷ∷ε⇔ .proj₂ ε
  ⊢ˢʷ∷-idSubst (∙ ⊢A) =
    ⊢ˢʷ∷∙⇔ .proj₂
      ( ⊢ˢʷ∷-wk1Subst ⊢A (⊢ˢʷ∷-idSubst (wf ⊢A))
      , PE.subst (_⊢_∷_ _ _) (wk1-tailId _) (var₀ ⊢A)
      )

opaque

  -- A lemma related to sgSubst.

  ⊢ˢʷ∷-sgSubst :
    Γ ⊢ t ∷ A →
    Γ ⊢ˢʷ sgSubst t ∷ Γ ∙ A
  ⊢ˢʷ∷-sgSubst ⊢t =
    ⊢ˢʷ∷∙⇔ .proj₂
      ( ⊢ˢʷ∷-idSubst (wfTerm ⊢t)
      , PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-id _) ⊢t
      )

opaque

  -- A lemma related to sgSubst.

  ⊢ˢʷ≡∷-sgSubst :
    Γ ⊢ t₁ ∷ A →
    Γ ⊢ t₂ ∷ A →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ˢʷ sgSubst t₁ ≡ sgSubst t₂ ∷ Γ ∙ A
  ⊢ˢʷ≡∷-sgSubst ⊢t₁ ⊢t₂ t₁≡t₂ =
    ⊢ˢʷ≡∷∙⇔ .proj₂
      ( refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-idSubst (wfEqTerm t₁≡t₂))
      , PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-id _) ⊢t₁
      , PE.subst (_⊢_∷_ _ _) (PE.sym $ subst-id _) ⊢t₂
      , PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ subst-id _) t₁≡t₂
      )

opaque

  -- A lemma related to _⇑.

  ⊢ˢʷ∷-⇑ :
    Δ ⊢ A [ σ ] →
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊢ˢʷ σ ⇑ ∷ Γ ∙ A
  ⊢ˢʷ∷-⇑ {A} ⊢A[σ] ⊢σ =
    ⊢ˢʷ∷∙⇔ .proj₂
      (⊢ˢʷ∷-wk1Subst ⊢A[σ] ⊢σ ,
       PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1Subst-wk1 A)
         (var₀ ⊢A[σ]))

opaque

  -- A lemma related to _⇑.

  ⊢ˢʷ≡∷-⇑ :
    Δ ⊢ A [ σ₁ ] →
    Δ ⊢ A [ σ₁ ] ≡ A [ σ₂ ] →
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊢ˢʷ σ₁ ⇑ ≡ σ₂ ⇑ ∷ Γ ∙ A
  ⊢ˢʷ≡∷-⇑ {A} ⊢A[σ₁] A[σ₁]≡A[σ₂] σ₁≡σ₂ =
    let ⊢0 = PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1Subst-wk1 A)
               (var₀ ⊢A[σ₁])
    in
    ⊢ˢʷ≡∷∙⇔ .proj₂
      (⊢ˢʷ≡∷-wk1Subst ⊢A[σ₁] σ₁≡σ₂ ,
       ⊢0 ,
       PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1Subst-wk1 A)
         (conv (var₀ ⊢A[σ₁]) (wkEq₁ ⊢A[σ₁] A[σ₁]≡A[σ₂])) ,
       refl ⊢0)

------------------------------------------------------------------------
-- Substitution lemmas

opaque

  -- A substitution lemma for _∷_∈_.

  subst-∷∈→⊢∷ : x ∷ A ∈ Γ → Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ σ x ∷ A [ σ ]
  subst-∷∈→⊢∷ (here {A}) ⊢σ =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-tail A) $
    ⊢ˢʷ∷∙⇔ .proj₁ ⊢σ .proj₂
  subst-∷∈→⊢∷ (there {A} x∈) ⊢σ =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-tail A) $
    subst-∷∈→⊢∷ x∈ (⊢ˢʷ∷∙⇔ .proj₁ ⊢σ .proj₁)

opaque

  -- A substitution lemma for _∷_∈_.

  subst-∷∈→⊢≡∷ :
    x ∷ A ∈ Γ → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ σ₁ x ≡ σ₂ x ∷ A [ σ₁ ]
  subst-∷∈→⊢≡∷ (here {A}) σ₁≡σ₂ =
    PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk1-tail A) $
    ⊢ˢʷ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₂ .proj₂ .proj₂
  subst-∷∈→⊢≡∷ (there {A} x∈) σ₁≡σ₂ =
    PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk1-tail A) $
    subst-∷∈→⊢≡∷ x∈ (⊢ˢʷ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₁)

private

  -- Below several properties are proved simultaneously using
  -- well-founded induction. The properties are collected in the
  -- record type P.

  record P (s : Size) : Set a where
    no-eta-equality
    field
      sym-⊢ˢʷ≡∷ :
        (⊢Γ : ⊢ Γ) →
        size-⊢′ ⊢Γ PE.≡ s →
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        Δ ⊢ˢʷ σ₂ ≡ σ₁ ∷ Γ
      subst-⊢ :
        Δ ⊢ˢʷ σ ∷ Γ →
        (⊢A : Γ ⊢ A) →
        size-⊢ ⊢A PE.≡ s →
        Δ ⊢ A [ σ ]
      subst-⊢→⊢≡ :
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        (⊢A : Γ ⊢ A) →
        size-⊢ ⊢A PE.≡ s →
        Δ ⊢ A [ σ₁ ] ≡ A [ σ₂ ]
      subst-⊢≡ :
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        (A₁≡A₂ : Γ ⊢ A₁ ≡ A₂) →
        size-⊢≡ A₁≡A₂ PE.≡ s →
        Δ ⊢ A₁ [ σ₁ ] ≡ A₂ [ σ₂ ]
      subst-⊢∷ :
        Δ ⊢ˢʷ σ ∷ Γ →
        (⊢t : Γ ⊢ t ∷ A) →
        size-⊢∷ ⊢t PE.≡ s →
        Δ ⊢ t [ σ ] ∷ A [ σ ]
      subst-⊢∷→⊢≡∷ :
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        (⊢t : Γ ⊢ t ∷ A) →
        size-⊢∷ ⊢t PE.≡ s →
        Δ ⊢ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]
      subst-⊢≡∷ :
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A) →
        size-⊢≡∷ t₁≡t₂ PE.≡ s →
        Δ ⊢ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ]

-- Variants of the fields of P, along with some derived lemmas.

private module Lemmas (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

  opaque

    -- Variants of the fields of P.

    sym-⊢ˢʷ≡∷ :
      (⊢Γ : ⊢ Γ) →
      ⦃ lt : size-⊢′ ⊢Γ <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊢ˢʷ σ₂ ≡ σ₁ ∷ Γ
    sym-⊢ˢʷ≡∷ ⊢Γ ⦃ lt ⦄ = P.sym-⊢ˢʷ≡∷ (hyp lt) ⊢Γ PE.refl

    subst-⊢ :
      (⊢A : Γ ⊢ A)
      ⦃ lt : size-⊢ ⊢A <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ A [ σ ]
    subst-⊢ ⊢A ⦃ lt ⦄ ⊢σ = P.subst-⊢ (hyp lt) ⊢σ ⊢A PE.refl

    subst-⊢→⊢≡ :
      (⊢A : Γ ⊢ A)
      ⦃ lt : size-⊢ ⊢A <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ A [ σ₁ ] ≡ A [ σ₂ ]
    subst-⊢→⊢≡ ⊢A ⦃ lt ⦄ σ₁≡σ₂ = P.subst-⊢→⊢≡ (hyp lt) σ₁≡σ₂ ⊢A PE.refl

    subst-⊢≡ :
      (A₁≡A₂ : Γ ⊢ A₁ ≡ A₂)
      ⦃ lt : size-⊢≡ A₁≡A₂ <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ A₁ [ σ₁ ] ≡ A₂ [ σ₂ ]
    subst-⊢≡ A₁≡A₂ ⦃ lt ⦄ σ₁≡σ₂ =
      P.subst-⊢≡ (hyp lt) σ₁≡σ₂ A₁≡A₂ PE.refl

    subst-⊢∷ :
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ t [ σ ] ∷ A [ σ ]
    subst-⊢∷ ⊢t ⦃ lt ⦄ ⊢σ = P.subst-⊢∷ (hyp lt) ⊢σ ⊢t PE.refl

    subst-⊢∷→⊢≡∷ :
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]
    subst-⊢∷→⊢≡∷ ⊢t ⦃ lt ⦄ σ₁≡σ₂ =
      P.subst-⊢∷→⊢≡∷ (hyp lt) σ₁≡σ₂ ⊢t PE.refl

    subst-⊢≡∷ :
      (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A)
      ⦃ lt : size-⊢≡∷ t₁≡t₂ <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊢ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ]
    subst-⊢≡∷ t₁≡t₂ ⦃ lt ⦄ σ₁≡σ₂ =
      P.subst-⊢≡∷ (hyp lt) σ₁≡σ₂ t₁≡t₂ PE.refl

  opaque

    -- Variants of some of the variants.

    sym-⊢ˢʷ≡∷-<ˢ :
      (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊢ˢʷ σ₂ ≡ σ₁ ∷ Γ
    sym-⊢ˢʷ≡∷-<ˢ (⊢Γ , lt) = sym-⊢ˢʷ≡∷ ⊢Γ ⦃ lt = <ˢ-trans lt ! ⦄

    subst-⊢-<ˢ :
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ A [ σ ]
    subst-⊢-<ˢ (⊢A , lt) = subst-⊢ ⊢A ⦃ lt = <ˢ-trans lt ! ⦄

    subst-⊢→⊢≡-<ˢ :
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ A [ σ₁ ] ≡ A [ σ₂ ]
    subst-⊢→⊢≡-<ˢ (⊢A , lt) = subst-⊢→⊢≡ ⊢A ⦃ lt = <ˢ-trans lt ! ⦄

    subst-⊢∷-<ˢ :
      (∃ λ (⊢t : Γ ⊢ t ∷ A) → size-⊢∷ ⊢t <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ t [ σ ] ∷ A [ σ ]
    subst-⊢∷-<ˢ (⊢t , lt) = subst-⊢∷ ⊢t ⦃ lt = <ˢ-trans lt ! ⦄

    subst-⊢∷→⊢≡∷-<ˢ :
      (∃ λ (⊢t : Γ ⊢ t ∷ A) → size-⊢∷ ⊢t <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]
    subst-⊢∷→⊢≡∷-<ˢ (⊢t , lt) = subst-⊢∷→⊢≡∷ ⊢t ⦃ lt = <ˢ-trans lt ! ⦄

  opaque

    -- A variant of ⊢ˢʷ∷-⇑.

    ⊢ˢʷ∷-⇑-<ˢ :
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ Γ →
      Δ ∙ A [ σ ] ⊢ˢʷ σ ⇑ ∷ Γ ∙ A
    ⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ = ⊢ˢʷ∷-⇑ (subst-⊢-<ˢ ⊢A ⊢σ) ⊢σ

  opaque

    -- A variant of ⊢ˢʷ≡∷-⇑-<ˢ.

    ⊢ˢʷ≡∷-⇑-<ˢ :
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      Δ ∙ A [ σ₁ ] ⊢ˢʷ σ₁ ⇑ ≡ σ₂ ⇑ ∷ Γ ∙ A
    ⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁≡σ₂ =
      let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
      ⊢ˢʷ≡∷-⇑ (subst-⊢-<ˢ ⊢A ⊢σ₁) (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂) σ₁≡σ₂

  opaque

    -- A lemma related to consSubst.

    ⊢ˢʷ≡∷-consSubst-[] :
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ consSubst σ₁ (t [ σ₁ ]) ≡ consSubst σ₂ (t [ σ₂ ]) ∷ Γ ∙ A
    ⊢ˢʷ≡∷-consSubst-[] σ₁≡σ₂ ⊢t =
      let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
      ⊢ˢʷ≡∷∙⇔ .proj₂
        ( σ₁≡σ₂
        , subst-⊢∷ ⊢t ⊢σ₁
        , subst-⊢∷ ⊢t ⊢σ₂
        , subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂
        )

  opaque

    -- A lemma related to J.

    J-lemma-⊢ˢʷ∷ :
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) →
      ⦃ lt₁ : s <ˢ s₂ ⦄
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt₂ : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ Γ →
      Δ ∙ A [ σ ] ∙ Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0) ⊢ˢʷ
        σ ⇑[ 2 ] ∷ Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0)
    J-lemma-⊢ˢʷ∷ {A} {t} (⊢A , lt) ⊢t ⊢σ =
      let ⊢A[σ] = subst-⊢ ⊢A ⦃ lt = <ˢ-trans lt ! ⦄ ⊢σ in
      PE.subst₃ _⊢ˢʷ_∷_
        (PE.cong (_∙_ _) $
         PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl)
        PE.refl PE.refl $
      ⊢ˢʷ∷-⇑
        (Idⱼ
           (PE.subst (_⊢_ _) (PE.sym $ wk1-liftSubst A) $
            wk₁ ⊢A[σ] ⊢A[σ])
           (PE.subst₂ (_⊢_∷_ _)
              (PE.sym $ wk1-liftSubst t)
              (PE.sym $ wk1-liftSubst A) $
            wkTerm₁ ⊢A[σ] (subst-⊢∷ ⊢t ⊢σ))
           (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-liftSubst A) $
            var₀ ⊢A[σ])) $
      ⊢ˢʷ∷-⇑ ⊢A[σ] ⊢σ

  opaque
    unfolding size-⊢

    -- A lemma related to J.

    J-lemma-⊢ˢʷ≡∷ :
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) →
      ⦃ lt₁ : s <ˢ s₂ ⦄
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt₂ : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      Δ ∙ A [ σ₁ ] ∙ Id (wk1 (A [ σ₁ ])) (wk1 (t [ σ₁ ])) (var x0) ⊢ˢʷ
        σ₁ ⇑[ 2 ] ≡ σ₂ ⇑[ 2 ] ∷ Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0)
    J-lemma-⊢ˢʷ≡∷ {A} {t} (⊢A , lt) ⊢t σ₁≡σ₂ =
      let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
          ⊢A[σ₁]        = subst-⊢ ⊢A ⦃ lt = <ˢ-trans lt ! ⦄ ⊢σ₁
          A[σ₁]≡A[σ₂]   = subst-⊢→⊢≡ ⊢A ⦃ lt = <ˢ-trans lt ! ⦄ σ₁≡σ₂
      in
      PE.subst₄ _⊢ˢʷ_≡_∷_
        (PE.cong (_∙_ _) $
         PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl)
        PE.refl PE.refl PE.refl $
      ⊢ˢʷ≡∷-⇑
        (Idⱼ
           (PE.subst (_⊢_ _) (PE.sym $ wk1-liftSubst A) $
            wk₁ ⊢A[σ₁] ⊢A[σ₁])
           (PE.subst₂ (_⊢_∷_ _)
              (PE.sym $ wk1-liftSubst t)
              (PE.sym $ wk1-liftSubst A) $
            wkTerm₁ ⊢A[σ₁] (subst-⊢∷ ⊢t ⊢σ₁))
           (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-liftSubst A) $
            var₀ ⊢A[σ₁]))
        (Id-cong
           (PE.subst₂ (_⊢_≡_ _)
              (PE.sym $ wk1-liftSubst A)
              (PE.sym $ wk1-liftSubst A) $
            wkEq₁ ⊢A[σ₁] A[σ₁]≡A[σ₂])
           (PE.subst₃ (_⊢_≡_∷_ _)
              (PE.sym $ wk1-liftSubst t)
              (PE.sym $ wk1-liftSubst t)
              (PE.sym $ wk1-liftSubst A) $
            wkEqTerm₁ ⊢A[σ₁] (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂))
           (_⊢_≡_∷_.refl $
            PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-liftSubst A) $
            var₀ ⊢A[σ₁])) $
      ⊢ˢʷ≡∷-⇑ ⊢A[σ₁] A[σ₁]≡A[σ₂] σ₁≡σ₂

-- The type P s is inhabited for every s.

private module Inhabited where

  opaque
    unfolding size-⊢′

    -- Symmetry for _⊢ˢʷ_≡_∷_.

    sym-⊢ˢʷ≡∷′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      (⊢Γ : ⊢ Γ) →
      size-⊢′ ⊢Γ PE.≡ s₂ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊢ˢʷ σ₂ ≡ σ₁ ∷ Γ
    sym-⊢ˢʷ≡∷′ {Δ} {σ₁} {σ₂} _ ε _ =
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ ε  ⇔⟨ ⊢ˢʷ≡∷ε⇔ ⟩→
      ⊢ Δ                ⇔˘⟨ ⊢ˢʷ≡∷ε⇔ ⟩→
      Δ ⊢ˢʷ σ₂ ≡ σ₁ ∷ ε  □
    sym-⊢ˢʷ≡∷′ {Γ = Γ ∙ A} {Δ} {σ₁} {σ₂} hyp (∙ ⊢A) PE.refl =
      let ⊢Γ , Γ< = wf-<ˢ ⊢A in

      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ ∙ A                    ⇔⟨ ⊢ˢʷ≡∷∙⇔ ⟩→

      (Δ ⊢ˢʷ tail σ₁ ≡ tail σ₂ ∷ Γ ×
       Δ ⊢ head σ₁ ∷ A [ tail σ₁ ] ×
       Δ ⊢ head σ₂ ∷ A [ tail σ₂ ] ×
       Δ ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ])  →⟨ (λ (σ₁₊≡σ₂₊ , ⊢σ₁₀ , ⊢σ₂₀ , σ₁₀≡σ₂₀) →
                                                     sym-⊢ˢʷ≡∷ ⊢Γ ⦃ lt = ↙ <ˢ→≤ˢ Γ< ⦄ σ₁₊≡σ₂₊ , ⊢σ₂₀ , ⊢σ₁₀ ,
                                                     conv (sym (subst-⊢ ⊢A (wf-⊢ˢʷ≡∷ σ₁₊≡σ₂₊ .proj₂ .proj₁)) σ₁₀≡σ₂₀)
                                                       (subst-⊢→⊢≡ ⊢A σ₁₊≡σ₂₊))
                                                ⟩
      (Δ ⊢ˢʷ tail σ₂ ≡ tail σ₁ ∷ Γ ×
       Δ ⊢ head σ₂ ∷ A [ tail σ₂ ] ×
       Δ ⊢ head σ₁ ∷ A [ tail σ₁ ] ×
       Δ ⊢ head σ₂ ≡ head σ₁ ∷ A [ tail σ₂ ])  ⇔˘⟨ ⊢ˢʷ≡∷∙⇔ ⟩→

      Δ ⊢ˢʷ σ₂ ≡ σ₁ ∷ Γ ∙ A                    □
      where
      open Lemmas hyp

  opaque
    unfolding size-⊢

    -- A substitution lemma for _⊢_.

    subst-⊢′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ ∷ Γ →
      (⊢A : Γ ⊢ A) →
      size-⊢ ⊢A PE.≡ s₂ →
      Δ ⊢ A [ σ ]
    subst-⊢′ hyp ⊢σ = let open Lemmas hyp in λ where
      (Levelⱼ _) _ →
        Levelⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (Uⱼ ⊢l) PE.refl →
        Uⱼ (subst-⊢∷ ⊢l ⊢σ)
      (univ ⊢A) PE.refl →
        univ (subst-⊢∷ ⊢A ⊢σ)
      (ΠΣⱼ ⊢B ok) PE.refl →
        let _ , ⊢A = ∙⊢→⊢-<ˢ ⊢B in
        ΠΣⱼ (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ)) ok
      (Emptyⱼ _) _ →
        Emptyⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (Unitⱼ ⊢l ok) PE.refl →
        Unitⱼ (subst-⊢∷ ⊢l ⊢σ) ok
      (ℕⱼ _) _ →
        ℕⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
        Idⱼ (subst-⊢ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ) (subst-⊢∷ ⊢u ⊢σ)

  opaque
    unfolding size-⊢

    -- A substitution lemma for _⊢_ and _⊢_≡_.

    subst-⊢→⊢≡′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      (⊢A : Γ ⊢ A) →
      size-⊢ ⊢A PE.≡ s₂ →
      Δ ⊢ A [ σ₁ ] ≡ A [ σ₂ ]
    subst-⊢→⊢≡′ hyp σ₁≡σ₂ = let open Lemmas hyp in λ where
      (Levelⱼ _) _ →
        refl (Levelⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (Uⱼ ⊢l) PE.refl →
        U-cong (subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂)
      (univ ⊢A) PE.refl →
        univ (subst-⊢∷→⊢≡∷ ⊢A σ₁≡σ₂)
      (ΠΣⱼ ⊢B ok) PE.refl →
        let _ , ⊢A = ∙⊢→⊢-<ˢ ⊢B in
        ΠΣ-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂)
          (subst-⊢→⊢≡ ⊢B (⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁≡σ₂)) ok
      (Emptyⱼ _) _ →
        refl (Emptyⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (Unitⱼ ⊢l ok) PE.refl →
        Unit-cong (subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂) ok
      (ℕⱼ _) _ →
        refl (ℕⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
        Id-cong (subst-⊢→⊢≡ ⊢A σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)

  opaque
    unfolding size-⊢≡

    -- A substitution lemma for _⊢_≡_.

    subst-⊢≡′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      (A₁≡A₂ : Γ ⊢ A₁ ≡ A₂) →
      size-⊢≡ A₁≡A₂ PE.≡ s₂ →
      Δ ⊢ A₁ [ σ₁ ] ≡ A₂ [ σ₂ ]
    subst-⊢≡′ hyp σ₁≡σ₂ = let open Lemmas hyp in λ where
      (univ A₁≡A₂) PE.refl →
        univ (subst-⊢≡∷ A₁≡A₂ σ₁≡σ₂)
      (refl ⊢A) PE.refl →
        subst-⊢→⊢≡ ⊢A σ₁≡σ₂
      (sym A₂≡A₁) PE.refl →
        let ⊢Γ = wfEq-<ˢ A₂≡A₁ in
        sym (subst-⊢≡ A₂≡A₁ (sym-⊢ˢʷ≡∷-<ˢ ⊢Γ σ₁≡σ₂))
      (trans A₁≡A₂ A₂≡A₃) PE.refl →
        trans (subst-⊢≡ A₁≡A₂ σ₁≡σ₂)
          (subst-⊢≡ A₂≡A₃ (refl-⊢ˢʷ≡∷ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₂)))
      (U-cong l₁≡l₂) PE.refl →
        U-cong (subst-⊢≡∷ l₁≡l₂ σ₁≡σ₂)
      (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
        let _ , ⊢A₁ = ∙⊢≡→⊢-<ˢ B₁≡B₂ in
        ΠΣ-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂)
          (subst-⊢≡ B₁≡B₂ (⊢ˢʷ≡∷-⇑-<ˢ ⊢A₁ σ₁≡σ₂)) ok
      (Unit-cong l₁≡l₂ ok) PE.refl →
        Unit-cong (subst-⊢≡∷ l₁≡l₂ σ₁≡σ₂) ok
      (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
        Id-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)

  opaque
    unfolding size-⊢∷

    -- A substitution lemma for _⊢_∷_.

    subst-⊢∷′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ ∷ Γ →
      (⊢t : Γ ⊢ t ∷ A) →
      size-⊢∷ ⊢t PE.≡ s₂ →
      Δ ⊢ t [ σ ] ∷ A [ σ ]
    subst-⊢∷′ hyp ⊢σ = let open Lemmas hyp in λ where
      (conv ⊢t B≡A) PE.refl →
        conv (subst-⊢∷ ⊢t ⊢σ)
          (subst-⊢≡ B≡A (refl-⊢ˢʷ≡∷ ⊢σ))
      (var _ x∈) _ →
        subst-∷∈→⊢∷ x∈ ⊢σ
      (zeroᵘⱼ _) _ →
        zeroᵘⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (sucᵘⱼ ⊢t) PE.refl →
        sucᵘⱼ (subst-⊢∷ ⊢t ⊢σ)
      (maxᵘⱼ ⊢t ⊢u) PE.refl →
        maxᵘⱼ (subst-⊢∷ ⊢t ⊢σ) (subst-⊢∷ ⊢u ⊢σ)
      (Uⱼ ⊢l) PE.refl →
        Uⱼ (subst-⊢∷ ⊢l ⊢σ)
      (ΠΣⱼ ⊢A ⊢B ok) PE.refl →
        let ⊢A[σ] = subst-⊢∷ ⊢A ⊢σ in
        ΠΣⱼ ⊢A[σ] (PE.subst (λ x → _ ⊢ _ ∷ U x) {! easy  !} (subst-⊢∷ ⊢B (⊢ˢʷ∷-⇑ (univ ⊢A[σ]) ⊢σ))) ok
      (lamⱼ ⊢B ⊢t ok) PE.refl →
        let _ , ⊢A = ∙⊢∷→⊢-<ˢ ⊢t
            ⊢σ⇑    = ⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ
        in
        lamⱼ (subst-⊢ ⊢B ⊢σ⇑) (subst-⊢∷ ⊢t ⊢σ⇑) ok
      (_∘ⱼ_ {G = B} ⊢t ⊢u) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift B _)
          (subst-⊢∷ ⊢t ⊢σ ∘ⱼ subst-⊢∷ ⊢u ⊢σ)
      (prodⱼ {G = B} ⊢B ⊢t ⊢u ok) PE.refl →
        let _ , ⊢A = ∙⊢→⊢-<ˢ ⊢B in
        prodⱼ (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ)) (subst-⊢∷ ⊢t ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
           subst-⊢∷ ⊢u ⊢σ)
          ok
      (fstⱼ ⊢B ⊢t) PE.refl →
        let _ , ⊢A = ∙⊢→⊢-<ˢ ⊢B in
        fstⱼ (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ)) (subst-⊢∷ ⊢t ⊢σ)
      (sndⱼ {G = B} ⊢B ⊢t) PE.refl →
        let _ , ⊢A = ∙⊢→⊢-<ˢ ⊢B in
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift B _) $
        sndⱼ (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ)) (subst-⊢∷ ⊢t ⊢σ)
      (prodrecⱼ {A = C} ⊢C ⊢t ⊢u ok) PE.refl →
        let _ , ⊢A , ⊢B = ∙∙⊢∷→⊢-<ˢ ⊢u
            ⊢σ⇑         = ⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ
        in
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift C _) $
        prodrecⱼ (subst-⊢ ⊢C (⊢ˢʷ∷-⇑ (ΠΣⱼ (subst-⊢-<ˢ ⊢B ⊢σ⇑) ok) ⊢σ))
          (subst-⊢∷ ⊢t ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C _) $
           subst-⊢∷ ⊢u (⊢ˢʷ∷-⇑-<ˢ ⊢B ⊢σ⇑))
          ok
      (Emptyⱼ _) _ →
        Emptyⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (emptyrecⱼ ⊢A ⊢t) PE.refl →
        emptyrecⱼ (subst-⊢ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (starⱼ ⊢l ok) PE.refl →
        starⱼ (subst-⊢∷ ⊢l ⊢σ) ok
      (unitrecⱼ {A} ⊢l ⊢A ⊢t ⊢u ok) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift A _) $
        unitrecⱼ
          (subst-⊢∷ ⊢l ⊢σ)
          (subst-⊢ ⊢A $
           ⊢ˢʷ∷-⇑ (Unitⱼ (subst-⊢∷ ⊢l ⊢σ) ok) ⊢σ)
          (subst-⊢∷ ⊢t ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
           subst-⊢∷ ⊢u ⊢σ)
          ok
      (Unitⱼ ⊢l ok) PE.refl →
        Unitⱼ (subst-⊢∷ ⊢l ⊢σ) ok
      (ℕⱼ _) _ →
        ℕⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (zeroⱼ _) _ →
        zeroⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (sucⱼ ⊢t) PE.refl →
        sucⱼ (subst-⊢∷ ⊢t ⊢σ)
      (natrecⱼ {A} ⊢t ⊢u ⊢v) PE.refl →
        let _ , ⊢A = ∙⊢∷→⊢-<ˢ ⊢u in
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift A _) $
        natrecⱼ
          (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
           subst-⊢∷ ⊢t ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
           subst-⊢∷ ⊢u (⊢ˢʷ∷-⇑-<ˢ ⊢A (⊢ˢʷ∷-⇑ (ℕⱼ (wf-⊢ˢʷ∷ ⊢σ)) ⊢σ)))
          (subst-⊢∷ ⊢v ⊢σ)
      (Idⱼ ⊢l ⊢A ⊢t ⊢u) PE.refl →
        Idⱼ (subst-⊢∷ ⊢l ⊢σ) (subst-⊢∷ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ) (subst-⊢∷ ⊢u ⊢σ)
      (rflⱼ ⊢t) PE.refl →
        rflⱼ (subst-⊢∷ ⊢t ⊢σ)
      (Jⱼ {B} ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
        let _ , ⊢A , _ = ∙∙⊢→⊢-<ˢ ⊢B in
        PE.subst (_⊢_∷_ _ _) (PE.sym $ [,]-[]-commute B) $
        Jⱼ (subst-⊢∷ ⊢t ⊢σ) (subst-⊢ ⊢B (J-lemma-⊢ˢʷ∷ ⊢A ⊢t ⊢σ))
          (PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) $
           subst-⊢∷ ⊢u ⊢σ)
          (subst-⊢∷ ⊢v ⊢σ) (subst-⊢∷ ⊢w ⊢σ)
      (Kⱼ {B} ⊢B ⊢u ⊢v ok) PE.refl →
        let _ , ⊢Id     = ∙⊢→⊢-<ˢ ⊢B
            ⊢A , ⊢t , _ = inversion-Id-⊢-<ˢ ⊢Id
            ⊢A[σ]       = subst-⊢-<ˢ ⊢A ⊢σ
            ⊢t[σ]       = subst-⊢∷-<ˢ ⊢t ⊢σ
        in
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift B _) $
        Kⱼ
          (subst-⊢ ⊢B $ ⊢ˢʷ∷-⇑ (Idⱼ ⊢A[σ] ⊢t[σ] ⊢t[σ]) ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
           subst-⊢∷ ⊢u ⊢σ)
          (subst-⊢∷ ⊢v ⊢σ) ok
      ([]-congⱼ ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
        []-congⱼ (subst-⊢ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ) (subst-⊢∷ ⊢u ⊢σ)
          (subst-⊢∷ ⊢v ⊢σ) ok

  opaque
    unfolding size-⊢∷

    -- A substitution lemma for _⊢_∷_ and _⊢_≡_∷_.

    subst-⊢∷→⊢≡∷′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      (⊢t : Γ ⊢ t ∷ A) →
      size-⊢∷ ⊢t PE.≡ s₂ →
      Δ ⊢ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]
    subst-⊢∷→⊢≡∷′ {σ₁} {σ₂} hyp σ₁≡σ₂ = let open Lemmas hyp in λ where
      (conv ⊢t B≡A) PE.refl →
        conv (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (subst-⊢≡ B≡A $
           refl-⊢ˢʷ≡∷ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁))
      (var _ x∈) _ →
        subst-∷∈→⊢≡∷ x∈ σ₁≡σ₂
      (zeroᵘⱼ _) _ →
        refl (zeroᵘⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (sucᵘⱼ ⊢t) PE.refl →
        sucᵘ-cong (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (maxᵘⱼ ⊢t ⊢u) PE.refl →
        {! maxᵘ-cong (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂) !}
      (Uⱼ ⊢l) PE.refl →
        U-cong (subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂)
      (ΠΣⱼ ⊢A ⊢B ok) PE.refl →
        let ⊢A[σ₁]      = _⊢_.univ $
                          subst-⊢∷ ⊢A $
                          wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁
            A[σ₁]≡A[σ₂] = subst-⊢∷→⊢≡∷ ⊢A σ₁≡σ₂
        in
        ΠΣ-cong A[σ₁]≡A[σ₂]
          (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ U x) {! easy  !} (subst-⊢∷→⊢≡∷ ⊢B $
           ⊢ˢʷ≡∷-⇑ ⊢A[σ₁] (univ A[σ₁]≡A[σ₂]) σ₁≡σ₂))
          ok
      (lamⱼ ⊢B ⊢t ok) PE.refl →
        let _ , ⊢A        = ∙⊢∷→⊢-<ˢ ⊢t
            σ₁⇑≡σ₂⇑       = ⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁≡σ₂
            _ , σ₁⇑ , σ₂⇑ = wf-⊢ˢʷ≡∷ σ₁⇑≡σ₂⇑
        in
        lam-cong (subst-⊢ ⊢B σ₁⇑) (subst-⊢∷ ⊢t σ₁⇑)
          (_⊢_∷_.conv (subst-⊢∷ ⊢t σ₂⇑) $
           _⊢_≡_.sym (subst-⊢→⊢≡ ⊢B σ₁⇑≡σ₂⇑))
          (subst-⊢∷→⊢≡∷ ⊢t σ₁⇑≡σ₂⇑) ok
      (_∘ⱼ_ {G = B} ⊢t ⊢u) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _)
          (app-cong (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂))
      (prodⱼ {G = B} ⊢B ⊢t ⊢u ok) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        prod-cong (subst-⊢ ⊢B $ ⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁)
          (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B _) $
           subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
          ok
      (fstⱼ ⊢B ⊢t) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        fst-cong (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁)) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (sndⱼ {G = B} ⊢B ⊢t) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
        snd-cong (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁)) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (prodrecⱼ {A = C} ⊢C ⊢t ⊢u ok) PE.refl →
        let _ , ⊢A , ⊢B = ∙∙⊢∷→⊢-<ˢ ⊢u
            σ₁⇑≡σ₂⇑     = ⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁≡σ₂
            _ , σ₁⇑ , _ = wf-⊢ˢʷ≡∷ σ₁⇑≡σ₂⇑
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift C _) $
        prodrec-cong
          (subst-⊢→⊢≡ ⊢C $
           ⊢ˢʷ≡∷-⇑ (ΠΣⱼ (subst-⊢-<ˢ ⊢B σ₁⇑) ok)
             (ΠΣ-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂)
                (subst-⊢→⊢≡-<ˢ ⊢B σ₁⇑≡σ₂⇑) ok)
             σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (subst-β-prodrec C _) $
           subst-⊢∷→⊢≡∷ ⊢u $
           ⊢ˢʷ≡∷-⇑-<ˢ ⊢B σ₁⇑≡σ₂⇑)
          ok
      (Emptyⱼ _) _ →
        refl (Emptyⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (emptyrecⱼ ⊢A ⊢t) PE.refl →
        emptyrec-cong (subst-⊢→⊢≡ ⊢A σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (starⱼ ⊢l ok) PE.refl →
        star-cong (subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂) ok
      (unitrecⱼ {l} {A} {t} {u} {p} {q} ⊢l ⊢A ⊢t ⊢u ok) PE.refl →
        let ⊢Δ , ⊢σ₁ , ⊢σ₂  = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢l[σ₁]          = subst-⊢∷ ⊢l ⊢σ₁
            ⊢Unit           = Unitⱼ ⊢l[σ₁] ok
            l[σ₁]≡l[σ₂]     = subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂
            Unit[σ₁]≡Unit[σ₂] = Unit-cong l[σ₁]≡l[σ₂] ok
            σ₁⇑≡σ₂⇑         = ⊢ˢʷ≡∷-⇑ ⊢Unit Unit[σ₁]≡Unit[σ₂] σ₁≡σ₂
            _ , ⊢σ₁⇑ , ⊢σ₂⇑ = wf-⊢ˢʷ≡∷ σ₁⇑≡σ₂⇑
            u[σ₁]≡u[σ₂]     = PE.subst (_⊢_≡_∷_ _ _ _)
                                (singleSubstLift A _) $
                              subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
        case Unitʷ-η? of λ where
          (no no-η) →
            unitrec-cong l[σ₁]≡l[σ₂] (subst-⊢→⊢≡ ⊢A σ₁⇑≡σ₂⇑) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
              u[σ₁]≡u[σ₂] ok no-η
          (yes η) →
            let ⊢t[σ₁] = subst-⊢∷ ⊢t ⊢σ₁ in
            unitrec p q l A t u [ σ₁ ]  ≡⟨ unitrec-β-η ⊢l[σ₁] (subst-⊢ ⊢A ⊢σ₁⇑) ⊢t[σ₁]
                                             (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                              subst-⊢∷ ⊢u ⊢σ₁)
                                             ok η ⟩⊢
            u [ σ₁ ]                    ≡⟨ _⊢_≡_∷_.conv u[σ₁]≡u[σ₂] $
                                           PE.subst₂ (_⊢_≡_ _)
                                             (PE.sym $ singleSubstComp _ _ A)
                                             (PE.sym $ singleSubstComp _ _ A) $
                                           subst-⊢→⊢≡ ⊢A $
                                           ⊢ˢʷ≡∷∙⇔ .proj₂
                                             ( refl-⊢ˢʷ≡∷ ⊢σ₁ , starⱼ ⊢l[σ₁] ok , ⊢t[σ₁]
                                             , η-unit (starⱼ ⊢l[σ₁] ok) ⊢t[σ₁] (inj₂ η)
                                             ) ⟩⊢
            u [ σ₂ ]                    ≡⟨ _⊢_≡_∷_.sym
                                             (PE.subst (_⊢_ _) (PE.sym $ singleSubstComp _ _ A) $
                                              subst-⊢ ⊢A (⊢ˢʷ∷∙⇔ .proj₂ (⊢σ₁ , ⊢t[σ₁]))) $
                                           _⊢_≡_∷_.conv
                                             {!unitrec-β-η ? (subst-⊢ ⊢A ⊢σ₂⇑) (subst-⊢∷ ⊢t ⊢σ₂)
                                                (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                                 subst-⊢∷ ⊢u ⊢σ₂)
                                                ok η!}
                                             (PE.subst₂ (_⊢_≡_ _)
                                                (PE.sym $ singleSubstComp _ _ A)
                                                (PE.sym $ singleSubstComp _ _ A) $
                                              sym (subst-⊢→⊢≡ ⊢A (⊢ˢʷ≡∷-consSubst-[] σ₁≡σ₂ ⊢t))) ⟩⊢∎
            unitrec p q l A t u [ σ₂ ]  ∎
      (Unitⱼ ⊢l ok) PE.refl →
        -- refl (Unitⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁) ok)
        {!   !}
      (ℕⱼ _) _ →
        refl (ℕⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (zeroⱼ _) _ →
        refl (zeroⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (sucⱼ ⊢t) PE.refl →
        suc-cong (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (natrecⱼ {A} ⊢t ⊢u ⊢v) PE.refl →
        let _ , ⊢A  = ∙⊢∷→⊢-<ˢ ⊢u
            ⊢Δ , _  = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            σ₁⇑≡σ₂⇑ = ⊢ˢʷ≡∷-⇑ (ℕⱼ ⊢Δ) (refl (ℕⱼ ⊢Δ)) σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
        natrec-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁⇑≡σ₂⇑)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift A _) $
           subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (natrecSucCase _ A) $
           subst-⊢∷→⊢≡∷ ⊢u $
           ⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁⇑≡σ₂⇑)
          (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂)
      (Idⱼ ⊢l ⊢A ⊢t ⊢u) PE.refl →
        Id-cong (subst-⊢∷→⊢≡∷ ⊢A σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
      (rflⱼ ⊢t) PE.refl →
        _⊢_≡_∷_.refl $
        rflⱼ (subst-⊢∷ ⊢t (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁))
      (Jⱼ {B} ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
        let _ , ⊢A , _  = ∙∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
        J-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂) (subst-⊢∷ ⊢t ⊢σ₁)
          (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (subst-⊢→⊢≡ ⊢B (J-lemma-⊢ˢʷ≡∷ ⊢A ⊢t σ₁≡σ₂))
          (PE.subst (_⊢_≡_∷_ _ _ _) ([,]-[]-commute B) $
           subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢w σ₁≡σ₂)
      (Kⱼ {B} ⊢B ⊢u ⊢v ok) PE.refl →
        let _ , ⊢Id     = ∙⊢→⊢-<ˢ ⊢B
            ⊢A , ⊢t , _ = inversion-Id-⊢-<ˢ ⊢Id
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢A[σ₁]      = subst-⊢-<ˢ ⊢A ⊢σ₁
            A[σ₁]≡A[σ₂] = subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂
            ⊢t[σ₁]      = subst-⊢∷-<ˢ ⊢t ⊢σ₁
            t[σ₁]≡t[σ₂] = subst-⊢∷→⊢≡∷-<ˢ ⊢t σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
        K-cong A[σ₁]≡A[σ₂] t[σ₁]≡t[σ₂]
          (subst-⊢→⊢≡ ⊢B $
           ⊢ˢʷ≡∷-⇑ (Idⱼ ⊢A[σ₁] ⊢t[σ₁] ⊢t[σ₁])
             (Id-cong A[σ₁]≡A[σ₂] t[σ₁]≡t[σ₂] t[σ₁]≡t[σ₂]) σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B _) $
           subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂) ok
      ([]-congⱼ ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
        []-cong-cong (subst-⊢→⊢≡ ⊢A σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂) ok

  opaque
    unfolding size-⊢≡∷

    -- A substitution lemma for _⊢_≡_∷_.

    subst-⊢≡∷′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A) →
      size-⊢≡∷ t₁≡t₂ PE.≡ s₂ →
      Δ ⊢ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ]
    subst-⊢≡∷′ {σ₁} {σ₂} hyp σ₁≡σ₂ = let open Lemmas hyp in λ where
      (refl ⊢t) PE.refl →
        subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂
      (sym ⊢A t₂≡t₁) PE.refl →
        let ⊢Γ    = wfEqTerm-<ˢ t₂≡t₁
            σ₂≡σ₁ = sym-⊢ˢʷ≡∷-<ˢ ⊢Γ σ₁≡σ₂
        in
        conv
          (sym (subst-⊢ ⊢A (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₂))
             (subst-⊢≡∷ t₂≡t₁ σ₂≡σ₁))
          (sym (subst-⊢→⊢≡ ⊢A σ₁≡σ₂))
      (trans t₁≡t₂ t₂≡t₃) PE.refl →
        trans
          (subst-⊢≡∷ t₁≡t₂ $
           refl-⊢ˢʷ≡∷ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁))
          (subst-⊢≡∷ t₂≡t₃ σ₁≡σ₂)
      (conv t₁≡t₂ B≡A) PE.refl →
        conv (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (subst-⊢≡ B≡A $
           refl-⊢ˢʷ≡∷ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁))
      (sucᵘ-cong t₁≡t₂) PE.refl →
        sucᵘ-cong (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
      (maxᵘ-cong t₁≡t₂ u₁≡u₂) PE.refl →
        maxᵘ-cong (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂) (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
      (U-cong l₁≡l₂) PE.refl →
        U-cong (subst-⊢≡∷ l₁≡l₂ σ₁≡σ₂)
      (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
        let _ , ⊢A₁ = ∙⊢≡∷→⊢-<ˢ B₁≡B₂ in
        ΠΣ-cong (subst-⊢≡∷ A₁≡A₂ σ₁≡σ₂)
          {!subst-⊢≡∷ B₁≡B₂ (⊢ˢʷ≡∷-⇑-<ˢ ⊢A₁ σ₁≡σ₂)!} ok
      (app-cong {G = B} t₁≡t₂ u₁≡u₂) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
        app-cong (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂) (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
      (β-red {G = B} {t} {a = u} {p} ⊢B ⊢t ⊢u PE.refl ok) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢σ₁⇑        = ⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁
        in
                                             ∷ B [ u ]₀ [ σ₁ ]            ⟨ singleSubstLift B _ ⟩≡∷≡
        lam p (t [ σ₁ ⇑ ]) ∘⟨ p ⟩ (u [ σ₁ ]) ∷ B [ σ₁ ⇑ ] [ u [ σ₁ ] ]₀  ≡⟨ β-red (subst-⊢ ⊢B ⊢σ₁⇑) (subst-⊢∷ ⊢t ⊢σ₁⇑)
                                                                              (subst-⊢∷ ⊢u ⊢σ₁) PE.refl ok ⟩⊢∷
        t [ σ₁ ⇑ ] [ u [ σ₁ ] ]₀                                         ≡⟨ singleSubstComp _ _ t ⟩⊢≡
                                                                          ⟨ singleSubstComp _ _ B ⟩≡≡
        t [ consSubst σ₁ (u [ σ₁ ]) ] ∷ B [ consSubst σ₁ (u [ σ₁ ]) ]    ≡⟨ subst-⊢∷→⊢≡∷ ⊢t $
                                                                            ⊢ˢʷ≡∷-consSubst-[] σ₁≡σ₂ ⊢u ⟩⊢∷∎≡
        t [ consSubst σ₂ (u [ σ₂ ]) ]                                    ≡˘⟨ PE.trans (singleSubstLift t _) (singleSubstComp _ _ t) ⟩
        t [ u ]₀ [ σ₂ ]                                                  ∎
      (η-eq {f = t₁} {g = t₂} ⊢B ⊢t₁ ⊢t₂ t₁0≡t₂0 ok) PE.refl →
        let _ , ⊢A        = ∙⊢≡∷→⊢-<ˢ t₁0≡t₂0
            _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            σ₁⇑≡σ₂⇑       = ⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁≡σ₂
            _ , ⊢σ₁⇑ , _  = wf-⊢ˢʷ≡∷ σ₁⇑≡σ₂⇑
        in
        η-eq (subst-⊢ ⊢B ⊢σ₁⇑) (subst-⊢∷ ⊢t₁ ⊢σ₁)
          (_⊢_∷_.conv (subst-⊢∷ ⊢t₂ ⊢σ₂) $
           _⊢_≡_.sym $
           ΠΣ-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂) (subst-⊢→⊢≡ ⊢B σ₁⇑≡σ₂⇑) ok)
          (PE.subst₃ (_⊢_≡_∷_ _)
             (PE.cong (_∘⟨ _ ⟩ _) (wk1-liftSubst t₁))
             (PE.cong (_∘⟨ _ ⟩ _) (wk1-liftSubst t₂))
             PE.refl $
           subst-⊢≡∷ t₁0≡t₂0 σ₁⇑≡σ₂⇑)
          ok
      (fst-cong ⊢B t₁≡t₂) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        fst-cong (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁)) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
      (snd-cong {G = B} ⊢B t₁≡t₂) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
        snd-cong (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁)) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
      (Σ-β₁ {G = B} {t} {u} {p} ⊢B ⊢t ⊢u PE.refl ok) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        fst p (prodˢ p t u) [ σ₁ ]  ≡⟨ Σ-β₁ (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁))
                                         (subst-⊢∷ ⊢t ⊢σ₁)
                                         (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
                                          subst-⊢∷ ⊢u ⊢σ₁)
                                         PE.refl ok ⟩⊢
        t [ σ₁ ]                    ≡⟨ subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂ ⟩⊢∎
        t [ σ₂ ]                    ∎
      (Σ-β₂ {G = B} {t} {u} {p} ⊢B ⊢t ⊢u PE.refl ok) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢B[σ₁⇑]     = subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁)
            ⊢t[σ₁]      = subst-⊢∷ ⊢t ⊢σ₁
            ⊢u[σ₁]      = PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
                          subst-⊢∷ ⊢u ⊢σ₁
        in
        snd p (prodˢ p t u) [ σ₁ ] ∷ B [ fst p (prodˢ p t u) ]₀ [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
                                                                           Σ-β₂ ⊢B[σ₁⇑] ⊢t[σ₁] ⊢u[σ₁] PE.refl ok ⟩⊢∷
                                                                         ⟨ PE.subst₂ (_⊢_≡_ _)
                                                                             (PE.sym $ substCompEq B) (PE.sym $ substCompEq B) $
                                                                           subst-⊢→⊢≡ ⊢B $
                                                                           ⊢ˢʷ≡∷∙⇔ .proj₂
                                                                             ( refl-⊢ˢʷ≡∷ ⊢σ₁
                                                                             , fstⱼ ⊢B[σ₁⇑] (prodⱼ ⊢B[σ₁⇑] ⊢t[σ₁] ⊢u[σ₁] ok)
                                                                             , ⊢t[σ₁]
                                                                             , Σ-β₁ ⊢B[σ₁⇑] ⊢t[σ₁] ⊢u[σ₁] PE.refl ok
                                                                             ) ⟩≡
        u [ σ₁ ] ∷ B [ t ]₀ [ σ₁ ]                                      ≡⟨ subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂ ⟩⊢∷∎
        u [ σ₂ ]                                                        ∎
      (Σ-η {G = B} ⊢B ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ ok) PE.refl →
        let _ , ⊢A        = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        Σ-η (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁)) (subst-⊢∷ ⊢t₁ ⊢σ₁)
          (_⊢_∷_.conv (subst-⊢∷ ⊢t₂ ⊢σ₂) $
           _⊢_≡_.sym $
           ΠΣ-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂)
             (subst-⊢→⊢≡ ⊢B (⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁≡σ₂)) ok)
          (subst-⊢≡∷ fst-t₁≡fst-t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B _) $
           subst-⊢≡∷ snd-t₁≡snd-t₂ σ₁≡σ₂)
          ok
      (prod-cong {G = B} ⊢B t₁≡t₂ u₁≡u₂ ok) PE.refl →
        let _ , ⊢A      = ∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        prod-cong (subst-⊢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁))
          (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B _) $
           subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          ok
      (prodrec-cong {A = C} C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) PE.refl →
        let _ , ⊢A , ⊢B = ∙∙⊢≡∷→⊢-<ˢ u₁≡u₂
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            σ₁⇑≡σ₂⇑     = ⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift C _) $
        prodrec-cong
          (subst-⊢≡ C₁≡C₂ $
           ⊢ˢʷ≡∷-⇑ (ΠΣⱼ (subst-⊢-<ˢ ⊢B (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁)) ok)
             (ΠΣ-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂)
                (subst-⊢→⊢≡-<ˢ ⊢B σ₁⇑≡σ₂⇑) ok)
             σ₁≡σ₂)
          (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (subst-β-prodrec C _) $
           subst-⊢≡∷ u₁≡u₂ (⊢ˢʷ≡∷-⇑-<ˢ ⊢B σ₁⇑≡σ₂⇑))
          ok
      (prodrec-β
         {p} {G = B} {A = C} {t} {t′ = u} {u = v} {r} {q}
         ⊢C ⊢t ⊢u ⊢v PE.refl ok)
        PE.refl →
        let _ , ⊢A , ⊢B   = ∙∙⊢∷→⊢-<ˢ ⊢v
            _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢σ₁⇑          = ⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁
        in
          ∷ C [ prodʷ p t u ]₀ [ σ₁ ]                       ⟨ singleSubstLift C _ ⟩≡∷≡

        prodrec r p q C (prodʷ p t u) v [ σ₁ ]
          ∷ C [ σ₁ ⇑ ] [ prodʷ p (t [ σ₁ ]) (u [ σ₁ ]) ]₀  ≡⟨ prodrec-β
                                                                (subst-⊢ ⊢C (⊢ˢʷ∷-⇑ (ΠΣⱼ (subst-⊢-<ˢ ⊢B ⊢σ₁⇑) ok) ⊢σ₁))
                                                                (subst-⊢∷ ⊢t ⊢σ₁)
                                                                (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
                                                                 subst-⊢∷ ⊢u ⊢σ₁)
                                                                (PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C _) $
                                                                 subst-⊢∷ ⊢v (⊢ˢʷ∷-⇑-<ˢ ⊢B ⊢σ₁⇑))
                                                                PE.refl ok ⟩⊢∷

        v [ σ₁ ⇑[ 2 ] ] [ t [ σ₁ ] , u [ σ₁ ] ]₁₀          ≡˘⟨ [,]-[]-commute v ⟩⊢≡

        v [ t , u ]₁₀ [ σ₁ ]                               ≡⟨ PE.subst₃ (_⊢_≡_∷_ _)
                                                                (PE.sym $ [,]-[]-fusion v) (PE.sym $ [,]-[]-fusion v)
                                                                (PE.sym $ substCompProdrec C _ _ _) $
                                                              subst-⊢∷→⊢≡∷ ⊢v $
                                                              ⊢ˢʷ≡∷∙⇔ .proj₂
                                                                ( ⊢ˢʷ≡∷-consSubst-[] σ₁≡σ₂ ⊢t
                                                                , PE.subst (_⊢_∷_ _ _) (PE.sym $ substConsId B)
                                                                    (subst-⊢∷ ⊢u ⊢σ₁)
                                                                , PE.subst (_⊢_∷_ _ _) (PE.sym $ substConsId B)
                                                                    (subst-⊢∷ ⊢u ⊢σ₂)
                                                                , PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ substConsId B)
                                                                    (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
                                                                ) ⟩⊢∎
        v [ t , u ]₁₀ [ σ₂ ]                               ∎
      (emptyrec-cong A₁≡A₂ t₁≡t₂) PE.refl →
        emptyrec-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
      (Unit-cong l₁≡l₂ ok) PE.refl →
        Unit-cong (subst-⊢≡∷ l₁≡l₂ σ₁≡σ₂) ok
      (star-cong l₁≡l₂ ok) PE.refl →
        star-cong (subst-⊢≡∷ l₁≡l₂ σ₁≡σ₂) ok
      (unitrec-cong {A = A₁} l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ ok no-η) PE.refl →
        let ⊢Unit = Unitⱼ {!wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁!} ok in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ _) $
        unitrec-cong
          {!   !}
          {!subst-⊢≡ A₁≡A₂ (⊢ˢʷ≡∷-⇑ ⊢Unit (refl ⊢Unit) σ₁≡σ₂)!}
          (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift A₁ _) $
           subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          ok no-η
      (unitrec-β {l} {A} {u = t} {p} {q} ⊢l ⊢A ⊢t ok no-η) PE.refl →
        let ⊢Δ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        unitrec p q l A (starʷ l) t [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
                                               unitrec-β {!   !} (subst-⊢ ⊢A (⊢ˢʷ∷-⇑ (Unitⱼ {!   !} ok) ⊢σ₁))
                                                 (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                                  subst-⊢∷ ⊢t ⊢σ₁)
                                                 ok no-η ⟩⊢
        t [ σ₁ ]                            ≡⟨ subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂ ⟩⊢∎
        t [ σ₂ ]                            ∎
      (unitrec-β-η {l} {A} {t} {u} {p} {q} ⊢l ⊢A ⊢t ⊢u ok no-η) PE.refl →
        let ⊢Δ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢t[σ₁]       = subst-⊢∷ ⊢t ⊢σ₁
        in
        unitrec p q l A t u [ σ₁ ] ∷ A [ t ]₀ [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
                                                         unitrec-β-η {!   !} (subst-⊢ ⊢A (⊢ˢʷ∷-⇑ (Unitⱼ {!   !} ok) ⊢σ₁)) ⊢t[σ₁]
                                                           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                                            subst-⊢∷ ⊢u ⊢σ₁)
                                                           ok no-η ⟩⊢∷
                                                       ⟨ PE.subst₂ (_⊢_≡_ _)
                                                           (PE.sym $ substCompEq A) (PE.sym $ substCompEq A) $
                                                         subst-⊢→⊢≡ ⊢A $
                                                         ⊢ˢʷ≡∷∙⇔ .proj₂
                                                           ( refl-⊢ˢʷ≡∷ ⊢σ₁ , ⊢t[σ₁] , starⱼ {!   !} ok
                                                           , η-unit ⊢t[σ₁] (starⱼ {!   !} ok) (inj₂ no-η)
                                                           ) ⟩≡
        u [ σ₁ ] ∷ A [ starʷ l ]₀ [ σ₁ ]              ≡⟨ subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂ ⟩⊢∷∎
        u [ σ₂ ]                                      ∎
      (η-unit ⊢t₁ ⊢t₂ η) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        η-unit (subst-⊢∷ ⊢t₁ ⊢σ₁) {!subst-⊢∷ ⊢t₂ ⊢σ₂!} η
      (suc-cong t₁≡t₂) PE.refl →
        suc-cong (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
      (natrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
        let _ , ⊢A₁      = ∙⊢≡∷→⊢-<ˢ u₁≡u₂
            ⊢Δ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            σ₁⇑≡σ₂⇑      = ⊢ˢʷ≡∷-⇑ (ℕⱼ ⊢Δ) (refl (ℕⱼ ⊢Δ)) σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ _) $
        natrec-cong (subst-⊢≡ A₁≡A₂ σ₁⇑≡σ₂⇑)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift A₁ _) $
           subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (natrecSucCase _ A₁) $
           subst-⊢≡∷ u₁≡u₂ (⊢ˢʷ≡∷-⇑-<ˢ ⊢A₁ σ₁⇑≡σ₂⇑))
          (subst-⊢≡∷ v₁≡v₂ σ₁≡σ₂)
      (natrec-zero {z = t} {A} {s = u} {p} {q} {r} ⊢t ⊢u) PE.refl →
        let _ , ⊢A       = ∙⊢∷→⊢-<ˢ ⊢u
            ⊢Δ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        natrec p q r A t u zero [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
                                           natrec-zero
                                             (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                              subst-⊢∷ ⊢t ⊢σ₁)
                                             (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
                                              subst-⊢∷ ⊢u (⊢ˢʷ∷-⇑-<ˢ ⊢A (⊢ˢʷ∷-⇑ (ℕⱼ ⊢Δ) ⊢σ₁))) ⟩⊢
        t [ σ₁ ]                        ≡⟨ subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂ ⟩⊢∎
        t [ σ₂ ]                        ∎
      (natrec-suc {z = t} {A} {s = u} {p} {q} {r} {n = v} ⊢t ⊢u ⊢v)
        PE.refl →
        let _ , ⊢A          = ∙⊢∷→⊢-<ˢ ⊢u
            ⊢Δ , ⊢σ₁ , ⊢σ₂  = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            σ₁⇑≡σ₂⇑         = ⊢ˢʷ≡∷-⇑ (ℕⱼ ⊢Δ) (refl (ℕⱼ ⊢Δ)) σ₁≡σ₂
            _ , ⊢σ₁⇑ , ⊢σ₂⇑ = wf-⊢ˢʷ≡∷ σ₁⇑≡σ₂⇑
            ⊢t[σ₁]          = PE.subst (_⊢_∷_ _ _)
                                (singleSubstLift A _) $
                              subst-⊢∷ ⊢t ⊢σ₁
            ⊢u[σ₁⇑²]        = PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
                              subst-⊢∷ ⊢u (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₁⇑)
            ⊢v[σ₁]          = subst-⊢∷ ⊢v ⊢σ₁
        in
                                          ∷ A [ suc v ]₀ [ σ₁ ]            ⟨ singleSubstLift A _ ⟩≡∷≡

        natrec p q r A t u (suc v) [ σ₁ ] ∷ A [ σ₁ ⇑ ] [ suc v [ σ₁ ] ]₀  ≡⟨ natrec-suc ⊢t[σ₁] ⊢u[σ₁⇑²] ⊢v[σ₁] ⟩⊢∷

        u [ σ₁ ⇑[ 2 ] ] [ v [ σ₁ ] , natrec p q r A t u v [ σ₁ ] ]₁₀      ≡⟨ doubleSubstComp u _ _ _ ⟩⊢≡
                                                                           ⟨ PE.trans (singleSubstComp _ _ A) (substComp↑² A _) ⟩≡≡
        u [ consSubst (consSubst σ₁ (v [ σ₁ ]))
              (natrec p q r A t u v [ σ₁ ])
          ]
          ∷ A [ suc (var x1) ]↑²
              [ consSubst (consSubst σ₁ (v [ σ₁ ]))
                  (natrec p q r A t u v [ σ₁ ]) ]                         ≡⟨ subst-⊢∷→⊢≡∷ ⊢u $
                                                                             ⊢ˢʷ≡∷∙⇔ .proj₂
                                                                               ( ⊢ˢʷ≡∷-consSubst-[] σ₁≡σ₂ ⊢v
                                                                               , PE.subst (_⊢_∷_ _ _) (singleSubstComp _ _ A)
                                                                                   (natrecⱼ ⊢t[σ₁] ⊢u[σ₁⇑²] ⊢v[σ₁])
                                                                               , PE.subst (_⊢_∷_ _ _) (singleSubstComp _ _ A)
                                                                                   (natrecⱼ
                                                                                      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                                                                       subst-⊢∷ ⊢t ⊢σ₂)
                                                                                      (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
                                                                                       subst-⊢∷ ⊢u (⊢ˢʷ∷-⇑-<ˢ ⊢A ⊢σ₂⇑))
                                                                                      (subst-⊢∷ ⊢v ⊢σ₂))
                                                                               , PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstComp _ _ A)
                                                                                   (natrec-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁⇑≡σ₂⇑)
                                                                                      (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift A _) $
                                                                                       subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
                                                                                      (PE.subst (_⊢_≡_∷_ _ _ _) (natrecSucCase _ A) $
                                                                                       subst-⊢∷→⊢≡∷ ⊢u (⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁⇑≡σ₂⇑))
                                                                                      (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂))
                                                                               ) ⟩⊢∷∎≡
        u [ consSubst (consSubst σ₂ (v [ σ₂ ]))
              (natrec p q r A t u v [ σ₂ ]) ]                             ≡˘⟨ [,]-[]-fusion u ⟩

        u [ v , natrec p q r A t u v ]₁₀ [ σ₂ ]                           ∎
      (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
        Id-cong (subst-⊢≡∷ A₁≡A₂ σ₁≡σ₂) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
      (J-cong {B₁} A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) PE.refl →
        let _ , ⊢A₁ , _ = ∙∙⊢≡→⊢-<ˢ B₁≡B₂
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ [,]-[]-commute B₁) $
        J-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂) (subst-⊢∷ ⊢t₁ ⊢σ₁)
          (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (subst-⊢≡ B₁≡B₂ (J-lemma-⊢ˢʷ≡∷ ⊢A₁ ⊢t₁ σ₁≡σ₂))
          (PE.subst (_⊢_≡_∷_ _ _ _) ([,]-[]-commute B₁) $
           subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          (subst-⊢≡∷ v₁≡v₂ σ₁≡σ₂) (subst-⊢≡∷ w₁≡w₂ σ₁≡σ₂)
      (J-β {t} {A} {B} {u} {p} {q} ⊢t ⊢B ⊢u PE.refl) PE.refl →
        let _ , ⊢A , _  = ∙∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        J p q A t B u t rfl [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
                                       J-β (subst-⊢∷ ⊢t ⊢σ₁) (subst-⊢ ⊢B (J-lemma-⊢ˢʷ∷ ⊢A ⊢t ⊢σ₁))
                                         (PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) $
                                          subst-⊢∷ ⊢u ⊢σ₁)
                                         PE.refl ⟩⊢
        u [ σ₁ ]                    ≡⟨ subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂ ⟩⊢∎
        u [ σ₂ ]                    ∎
      (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
        let _ , ⊢Id       = ∙⊢≡→⊢-<ˢ B₁≡B₂
            ⊢A₁ , ⊢t₁ , _ = inversion-Id-⊢-<ˢ ⊢Id
            _ , ⊢σ₁ , _   = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢t₁[σ₁]       = subst-⊢∷-<ˢ ⊢t₁ ⊢σ₁
            t₁[σ₁]≡t₁[σ₂] = subst-⊢∷→⊢≡∷-<ˢ ⊢t₁ σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B₁ _) $
        K-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (subst-⊢≡ B₁≡B₂ $
           ⊢ˢʷ≡∷-⇑ (Idⱼ (subst-⊢-<ˢ ⊢A₁ ⊢σ₁) ⊢t₁[σ₁] ⊢t₁[σ₁])
             (Id-cong (subst-⊢→⊢≡-<ˢ ⊢A₁ σ₁≡σ₂) t₁[σ₁]≡t₁[σ₂]
                t₁[σ₁]≡t₁[σ₂])
             σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B₁ _) $
           subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          (subst-⊢≡∷ v₁≡v₂ σ₁≡σ₂) ok
      (K-β {A} {t} {B} {u} {p} ⊢B ⊢u ok) PE.refl →
        let _ , ⊢Id     = ∙⊢→⊢-<ˢ ⊢B
            ⊢A , ⊢t , _ = inversion-Id-⊢-<ˢ ⊢Id
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢t[σ₁]      = subst-⊢∷-<ˢ ⊢t ⊢σ₁
        in
        K p A t B u rfl [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
                                   K-β
                                     (subst-⊢ ⊢B $
                                      ⊢ˢʷ∷-⇑ (Idⱼ (subst-⊢-<ˢ ⊢A ⊢σ₁) ⊢t[σ₁] ⊢t[σ₁]) ⊢σ₁)
                                     (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
                                      subst-⊢∷ ⊢u ⊢σ₁)
                                     ok ⟩⊢
        u [ σ₁ ]                ≡⟨ subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂ ⟩⊢∎
        u [ σ₂ ]                ∎
      ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
        []-cong-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂) (subst-⊢≡∷ v₁≡v₂ σ₁≡σ₂) ok
      ([]-cong-β ⊢t PE.refl ok) PE.refl →
        []-cong-β (subst-⊢∷ ⊢t (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁)) PE.refl
          ok

  opaque

    -- The type P s is inhabited for every s.

    P-inhabited : P s
    P-inhabited =
      well-founded-induction P
        (λ _ hyp →
           record
             { sym-⊢ˢʷ≡∷    = sym-⊢ˢʷ≡∷′    hyp
             ; subst-⊢      = subst-⊢′      hyp
             ; subst-⊢→⊢≡   = subst-⊢→⊢≡′   hyp
             ; subst-⊢≡     = subst-⊢≡′     hyp
             ; subst-⊢∷     = subst-⊢∷′     hyp
             ; subst-⊢∷→⊢≡∷ = subst-⊢∷→⊢≡∷′ hyp
             ; subst-⊢≡∷    = subst-⊢≡∷′    hyp
             })
        _

opaque

  -- A substitution lemma for _⊢_.

  subst-⊢ : Γ ⊢ A → Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ A [ σ ]
  subst-⊢ ⊢A ⊢σ = P.subst-⊢ Inhabited.P-inhabited ⊢σ ⊢A PE.refl

opaque

  -- A substitution lemma for _⊢_≡_.

  subst-⊢≡ : Γ ⊢ A₁ ≡ A₂ → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ A₁ [ σ₁ ] ≡ A₂ [ σ₂ ]
  subst-⊢≡ A₁≡A₂ σ₁≡σ₂ =
    P.subst-⊢≡ Inhabited.P-inhabited σ₁≡σ₂ A₁≡A₂ PE.refl

opaque

  -- A substitution lemma for _⊢_∷_.

  subst-⊢∷ : Γ ⊢ t ∷ A → Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ t [ σ ] ∷ A [ σ ]
  subst-⊢∷ ⊢t ⊢σ = P.subst-⊢∷ Inhabited.P-inhabited ⊢σ ⊢t PE.refl

opaque

  -- A substitution lemma for _⊢_≡_∷_.

  subst-⊢≡∷ :
    Γ ⊢ t₁ ≡ t₂ ∷ A → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊢ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ]
  subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂ =
    P.subst-⊢≡∷ Inhabited.P-inhabited σ₁≡σ₂ t₁≡t₂ PE.refl

------------------------------------------------------------------------
-- More lemmas related to _⊢ˢʷ_∷_ and _⊢ˢʷ_≡_∷_

opaque

  -- Symmetry for _⊢ˢʷ_≡_∷_.

  sym-⊢ˢʷ≡∷ :
    ⊢ Γ →
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊢ˢʷ σ₂ ≡ σ₁ ∷ Γ
  sym-⊢ˢʷ≡∷ ⊢Γ = P.sym-⊢ˢʷ≡∷ Inhabited.P-inhabited ⊢Γ PE.refl

opaque

  -- Transitivity for _⊢ˢʷ_≡_∷_.

  trans-⊢ˢʷ :
    ⊢ Γ →
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊢ˢʷ σ₂ ≡ σ₃ ∷ Γ →
    Δ ⊢ˢʷ σ₁ ≡ σ₃ ∷ Γ
  trans-⊢ˢʷ ε σ₁≡σ₂ _ =
    ⊢ˢʷ≡∷ε⇔ .proj₂ (⊢ˢʷ≡∷ε⇔ .proj₁ σ₁≡σ₂)
  trans-⊢ˢʷ (∙ ⊢A) σ₁≡σ₂ σ₂≡σ₃ =
    let ⊢Γ                               = wf ⊢A
        σ₁₊≡σ₂₊ , ⊢σ₁₀  , _    , σ₁₀≡σ₂₀ = ⊢ˢʷ≡∷∙⇔ .proj₁ σ₁≡σ₂
        σ₂₊≡σ₃₊ , _     , ⊢σ₃₀ , σ₂₀≡σ₃₀ = ⊢ˢʷ≡∷∙⇔ .proj₁ σ₂≡σ₃
    in
    ⊢ˢʷ≡∷∙⇔ .proj₂
      ( trans-⊢ˢʷ ⊢Γ σ₁₊≡σ₂₊ σ₂₊≡σ₃₊
      , ⊢σ₁₀
      , ⊢σ₃₀
      , trans σ₁₀≡σ₂₀
          (conv σ₂₀≡σ₃₀ (subst-⊢≡ (refl ⊢A) (sym-⊢ˢʷ≡∷ ⊢Γ σ₁₊≡σ₂₊)))
      )
