------------------------------------------------------------------------
-- Substitution lemmas
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Substitution.Primitive.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Admissible.U.Primitive R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Term.Primitive R
open import Definition.Typed.Size R
open import Definition.Typed.Weakening R as W hiding (wk)

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as E
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
  k m n                             : Nat
  x                                 : Fin _
  Γ Δ Η                             : Con Term _
  A A₁ A₂ B C D l l₁ l₂ t t₁ t₂ u v : Term _
  σ σ₁ σ₁₁ σ₁₂ σ₂ σ₂₁ σ₂₂ σ₃        : Subst _ _
  ρ                                 : Wk _ _
  s s₂                              : Size
  p q                               : M

------------------------------------------------------------------------
-- Some admissible equality rules

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

opaque

  -- lift preserves definitional equality.
  --
  -- See also Definition.Typed.Properties.Admissible.Lift.lift-cong.

  lift-cong :
    ∀ {t u A l₂} →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ A →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ A →
    Γ ⊢ t ≡ u ∷ A →
    Γ ⊢ lift t ≡ lift u ∷ Lift l₂ A
  lift-cong {t} {u} {l₂} ⊢l₂ ⊢A ⊢t ⊢u t≡u =
    Lift-η ⊢l₂ ⊢A (liftⱼ ⊢l₂ ⊢A ⊢t)
      (liftⱼ ⊢l₂ ⊢A ⊢u)
      (lower (lift t)  ≡⟨ Lift-β ⊢A ⊢t ⟩⊢
       t                  ≡⟨ t≡u ⟩⊢
       u                  ≡⟨ sym ⊢A (Lift-β ⊢A ⊢u) ⟩⊢∎
       lower (lift u) ∎)

------------------------------------------------------------------------
-- Well-formed substitutions

-- Well-formed substitutions.

data _⊢ˢ_∷_ (Δ : Con Term m) : Subst m n → Con Term n → Set a where
  id  : Δ ⊢ˢ σ ∷ ε
  _,_ : Δ ⊢ˢ tail σ ∷ Γ →
        Δ ⊢  head σ ∷ A [ tail σ ] →
        Δ ⊢ˢ σ      ∷ Γ ∙ A

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

  -- An introduction lemma for _⊢ˢʷ_∷_.

  →⊢ˢʷ∷∙ :
    Δ ⊢ˢʷ tail σ ∷ Γ → Δ ⊢ head σ ∷ A [ tail σ ] →
    Δ ⊢ˢʷ σ ∷ Γ ∙ A
  →⊢ˢʷ∷∙ ⊢σ₊ ⊢σ₀ = ⊢ˢʷ∷∙⇔ .proj₂ (⊢σ₊ , ⊢σ₀)

opaque
  unfolding _⊢ˢʷ_∷_

  -- A well-formedness lemma for _⊢ˢʷ_∷_.

  wf-⊢ˢʷ∷ : Δ ⊢ˢʷ σ ∷ Γ → ⊢ Δ
  wf-⊢ˢʷ∷ (⊢Δ , _) = ⊢Δ

------------------------------------------------------------------------
-- Well-formed equality of substitutions

-- Well-formed equality of substitutions.

data _⊢ˢ_≡_∷_ (Δ : Con Term m) :
       (_ _ : Subst m n) → Con Term n → Set a where
  id  : Δ ⊢ˢ σ₁ ≡ σ₂ ∷ ε
  _,_ : Δ ⊢ˢ tail σ₁ ≡ tail σ₂ ∷ Γ
      → Δ ⊢  head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]
      → Δ ⊢ˢ σ₁      ≡ σ₂      ∷ Γ ∙ A

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

private opaque

  -- Reflexivity for _⊢ˢ_≡_∷_.

  refl-⊢ˢ≡∷ :
    Δ ⊢ˢ σ ∷ Γ →
    Δ ⊢ˢ σ ≡ σ ∷ Γ
  refl-⊢ˢ≡∷ id        = id
  refl-⊢ˢ≡∷ (⊢σ , ⊢t) = refl-⊢ˢ≡∷ ⊢σ , refl ⊢t

opaque
  unfolding _⊢ˢʷ_∷_ _⊢ˢʷ_≡_∷_

  -- Reflexivity for _⊢ˢʷ_≡_∷_.

  refl-⊢ˢʷ≡∷ :
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ⊢ˢʷ σ ≡ σ ∷ Γ
  refl-⊢ˢʷ≡∷ (⊢Δ , ⊢σ) = ⊢Δ , ⊢σ , ⊢σ , refl-⊢ˢ≡∷ ⊢σ

opaque

  -- A lemma relating _⊢ˢʷ_∷_ and _⊢ˢʷ_≡_∷_.

  ⊢ˢʷ∷⇔⊢ˢʷ≡∷ :
    Δ ⊢ˢʷ σ ∷ Γ ⇔ Δ ⊢ˢʷ σ ≡ σ ∷ Γ
  ⊢ˢʷ∷⇔⊢ˢʷ≡∷ = refl-⊢ˢʷ≡∷ , proj₁ ∘→ proj₂ ∘→ wf-⊢ˢʷ≡∷

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

  -- A lemma related to _•ₛ_.

  ⊢ˢʷ∷-•ₛ :
    ρ ∷ʷ Η ⊇ Δ →
    Δ ⊢ˢʷ σ ∷ Γ →
    Η ⊢ˢʷ ρ •ₛ σ ∷ Γ
  ⊢ˢʷ∷-•ₛ ρ⊇ =
    ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₂ ∘→ ⊢ˢʷ≡∷-•ₛ ρ⊇ ∘→ ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₁

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

  -- A lemma related to wkSubst.

  ⊢ˢʷ≡∷-wkSubst :
    ⊢ Δ →
    drop k Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊢ˢʷ wkSubst k σ₁ ≡ wkSubst k σ₂ ∷ Γ
  ⊢ˢʷ≡∷-wkSubst {k = 0}    _      σ₁≡σ₂ = σ₁≡σ₂
  ⊢ˢʷ≡∷-wkSubst {k = 1+ _} (∙ ⊢A) σ₁≡σ₂ =
    ⊢ˢʷ≡∷-wk1Subst ⊢A (⊢ˢʷ≡∷-wkSubst (wf ⊢A) σ₁≡σ₂)

opaque

  -- A lemma related to wkSubst.

  ⊢ˢʷ∷-wkSubst :
    ⊢ Δ →
    drop k Δ ⊢ˢʷ σ ∷ Γ →
    Δ ⊢ˢʷ wkSubst k σ ∷ Γ
  ⊢ˢʷ∷-wkSubst ⊢Δ =
    ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₂ ∘→ ⊢ˢʷ≡∷-wkSubst ⊢Δ ∘→ ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₁

opaque

  -- A lemma related to idSubst.

  ⊢ˢʷ∷-idSubst :
    ⊢ Γ →
    Γ ⊢ˢʷ idSubst ∷ Γ
  ⊢ˢʷ∷-idSubst ε =
    ⊢ˢʷ∷ε⇔ .proj₂ ε
  ⊢ˢʷ∷-idSubst (∙ ⊢A) =
    →⊢ˢʷ∷∙ (⊢ˢʷ∷-wk1Subst ⊢A (⊢ˢʷ∷-idSubst (wf ⊢A)))
      (PE.subst (_⊢_∷_ _ _) (wk1-tailId _) (var₀ ⊢A))

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

  -- A lemma related to sgSubst.

  ⊢ˢʷ∷-sgSubst :
    Γ ⊢ t ∷ A →
    Γ ⊢ˢʷ sgSubst t ∷ Γ ∙ A
  ⊢ˢʷ∷-sgSubst ⊢t =
    ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₂ (⊢ˢʷ≡∷-sgSubst ⊢t ⊢t (refl ⊢t))

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

opaque

  -- A lemma related to _⇑.

  ⊢ˢʷ∷-⇑ :
    Δ ⊢ A [ σ ] →
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊢ˢʷ σ ⇑ ∷ Γ ∙ A
  ⊢ˢʷ∷-⇑ ⊢A[σ] =
    ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₂ ∘→ ⊢ˢʷ≡∷-⇑ ⊢A[σ] (refl ⊢A[σ]) ∘→
    ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₁

opaque

  -- A lemma related to _[_][_]↑.

  ⊢ˢʷ≡∷-[][]↑ :
    Γ ⊢ t₁ ∷ wk[ k ] A →
    Γ ⊢ t₂ ∷ wk[ k ] A →
    Γ ⊢ t₁ ≡ t₂ ∷ wk[ k ] A →
    Γ ⊢ˢʷ consSubst (wkSubst k idSubst) t₁ ≡
      consSubst (wkSubst k idSubst) t₂ ∷ drop k Γ ∙ A
  ⊢ˢʷ≡∷-[][]↑ {k} ⊢t₁ ⊢t₂ t₁≡t₂ =
    let ⊢Γ = wfEqTerm t₁≡t₂ in
    ⊢ˢʷ≡∷∙⇔ .proj₂
      ( refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-wkSubst ⊢Γ (⊢ˢʷ∷-idSubst (lemma k ⊢Γ)))
      , PE.subst (_⊢_∷_ _ _) (wk[]≡[] k) ⊢t₁
      , PE.subst (_⊢_∷_ _ _) (wk[]≡[] k) ⊢t₂
      , PE.subst (_⊢_≡_∷_ _ _ _) (wk[]≡[] k) t₁≡t₂
      )
    where
    lemma :
      ∀ k {Γ : Con Term (k + n)} →
      ⊢ Γ → ⊢ drop k Γ
    lemma 0      ⊢Γ     = ⊢Γ
    lemma (1+ k) (∙ ⊢A) = lemma k (wf ⊢A)

opaque

  -- A lemma related to _[_][_]↑.

  ⊢ˢʷ∷-[][]↑ :
    Γ ⊢ t ∷ wk[ k ] A →
    Γ ⊢ˢʷ consSubst (wkSubst k idSubst) t ∷ drop k Γ ∙ A
  ⊢ˢʷ∷-[][]↑ ⊢t =
    ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₂ (⊢ˢʷ≡∷-[][]↑ ⊢t ⊢t (refl ⊢t))

opaque
  unfolding replace₂

  -- A lemma related to replace₂.

  ⊢ˢʷ∷-replace₂ :
    Γ ∙ A ∙ B ⊢ t ∷ wk[ 2 ]′ C →
    Γ ∙ A ∙ B ⊢ u ∷ wk (lift (stepn id 2)) D [ t ]₀ →
    Γ ∙ A ∙ B ⊢ˢʷ replace₂ t u ∷ Γ ∙ C ∙ D
  ⊢ˢʷ∷-replace₂ {D} ⊢t ⊢u =
    let ⊢B = ⊢∙→⊢ (wfTerm ⊢t) in
    →⊢ˢʷ∷∙
      (→⊢ˢʷ∷∙
         (⊢ˢʷ∷-wkSubst (∙ ⊢B) $
          ⊢ˢʷ∷-idSubst (wf (⊢∙→⊢ (wf ⊢B))))
         (PE.subst (_⊢_∷_ _ _) (wk≡subst _ _) ⊢t))
      (PE.subst (_⊢_∷_ _ _)
         (PE.trans (subst-wk D) $
          flip substVar-to-subst D λ where
            x0     → PE.refl
            (_ +1) → PE.refl)
         ⊢u)

opaque

  -- A cast lemma for _⊢ˢʷ_≡_∷_.

  cast-⊢ˢʷ≡∷ :
    (∀ x → σ₁₁ x PE.≡ σ₂₁ x) →
    (∀ x → σ₁₂ x PE.≡ σ₂₂ x) →
    Δ ⊢ˢʷ σ₁₁ ≡ σ₁₂ ∷ Γ → Δ ⊢ˢʷ σ₂₁ ≡ σ₂₂ ∷ Γ
  cast-⊢ˢʷ≡∷ {Γ = ε} _ _ σ₁₁≡σ₁₂ =
    ⊢ˢʷ≡∷ε⇔ .proj₂ (⊢ˢʷ≡∷ε⇔ .proj₁ σ₁₁≡σ₁₂)
  cast-⊢ˢʷ≡∷ {Γ = _ ∙ A} σ₁₁≡σ₂₁ σ₁₂≡σ₂₂ σ₁₁≡σ₁₂ =
    let σ₁₁₊≡σ₁₂₊ , ⊢σ₁₁₀ , ⊢σ₁₂₀ , σ₁₁₀≡σ₁₂₀ =
          ⊢ˢʷ≡∷∙⇔ .proj₁ σ₁₁≡σ₁₂
        σ₁₁₊≡σ₂₁₊ = σ₁₁≡σ₂₁ ∘→ _+1
        σ₁₂₊≡σ₂₂₊ = σ₁₂≡σ₂₂ ∘→ _+1
        σ₂₁₊≡σ₂₂₊ = cast-⊢ˢʷ≡∷ σ₁₁₊≡σ₂₁₊ σ₁₂₊≡σ₂₂₊ σ₁₁₊≡σ₁₂₊
    in
    ⊢ˢʷ≡∷∙⇔ .proj₂
      ( σ₂₁₊≡σ₂₂₊
      , PE.subst₂ (_⊢_∷_ _) (σ₁₁≡σ₂₁ x0)
          (substVar-to-subst σ₁₁₊≡σ₂₁₊ A) ⊢σ₁₁₀
      , PE.subst₂ (_⊢_∷_ _) (σ₁₂≡σ₂₂ x0)
          (substVar-to-subst σ₁₂₊≡σ₂₂₊ A) ⊢σ₁₂₀
      , PE.subst₃ (_⊢_≡_∷_ _) (σ₁₁≡σ₂₁ x0) (σ₁₂≡σ₂₂ x0)
          (substVar-to-subst σ₁₁₊≡σ₂₁₊ A) σ₁₁₀≡σ₁₂₀
      )

opaque

  -- A cast lemma for _⊢ˢʷ_∷_.

  cast-⊢ˢʷ∷ :
    (∀ x → σ₁ x PE.≡ σ₂ x) →
    Δ ⊢ˢʷ σ₁ ∷ Γ → Δ ⊢ˢʷ σ₂ ∷ Γ
  cast-⊢ˢʷ∷ σ₁≡σ₂ =
    ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₂ ∘→ cast-⊢ˢʷ≡∷ σ₁≡σ₂ σ₁≡σ₂ ∘→ ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₁

opaque

  -- If ρ is a well-formed weakening, then toSubst ρ is a well-formed
  -- substitution.

  ⊢ˢʷ-toSubst : ρ ∷ʷ Δ ⊇ Γ → Δ ⊢ˢʷ toSubst ρ ∷ Γ
  ⊢ˢʷ-toSubst ρ⊇ = ⊢ˢʷ-toSubst′ (wf-∷ʷ⊇ ρ⊇) (∷ʷ⊇→∷⊇ ρ⊇)
    where
    ⊢ˢʷ-toSubst′ : ⊢ Δ → ρ ∷ Δ ⊇ Γ → Δ ⊢ˢʷ toSubst ρ ∷ Γ
    ⊢ˢʷ-toSubst′ ⊢Δ id =
      ⊢ˢʷ∷-idSubst ⊢Δ
    ⊢ˢʷ-toSubst′ (∙ ⊢A) (step ρ⊇) =
      ⊢ˢʷ∷-wk1Subst ⊢A (⊢ˢʷ-toSubst′ (wf ⊢A) ρ⊇)
    ⊢ˢʷ-toSubst′ (∙ ⊢A) (lift ρ⊇) =
      cast-⊢ˢʷ∷ (PE.sym ∘→ toSubst-liftn 1) $
      PE.subst₃ _⊢ˢʷ_∷_
        (PE.cong (_∙_ _) (PE.sym $ wk≡subst _ _)) PE.refl PE.refl $
      ⊢ˢʷ∷-⇑ (PE.subst (_⊢_ _) (wk≡subst _ _) ⊢A) $
      ⊢ˢʷ-toSubst′ (wf ⊢A) ρ⊇

------------------------------------------------------------------------
-- Substitution lemmas

opaque
  unfolding _supᵘₗ_

  -- A substitution lemma for _supᵘₗ_.

  supᵘₗ-[]′ :
    (¬ Level-allowed → Level-literal l₁ × Level-literal l₂) →
    l₁ supᵘₗ l₂ [ σ ] PE.≡ (l₁ [ σ ]) supᵘₗ (l₂ [ σ ])
  supᵘₗ-[]′ hyp with level-support in eq
  … | level-type _  = PE.refl
  … | only-literals =
    let l₁-lit , l₂-lit = hyp (¬Level-allowed⇔ .proj₂ eq) in
    supᵘₗ′-[] l₁-lit l₂-lit

opaque

  -- Another substitution lemma for _supᵘₗ_.

  supᵘₗ-[] :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    l₁ supᵘₗ l₂ [ σ ] PE.≡ (l₁ [ σ ]) supᵘₗ (l₂ [ σ ])
  supᵘₗ-[] ⊢l₁ ⊢l₂ =
    supᵘₗ-[]′
      (λ not-ok →
         inversion-∷Level ⊢l₁ .proj₂ not-ok .proj₂ ,
         inversion-∷Level ⊢l₂ .proj₂ not-ok .proj₂)

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
      subst-⊢∷L :
        Δ ⊢ˢʷ σ ∷ Γ →
        (⊢l : Γ ⊢ l ∷Level) →
        size-⊢∷L ⊢l PE.≡ s →
        Δ ⊢ l [ σ ] ∷Level
      subst-⊢∷→⊢≡∷ :
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        (⊢t : Γ ⊢ t ∷ A) →
        size-⊢∷ ⊢t PE.≡ s →
        Δ ⊢ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]
      subst-⊢∷L→⊢≡∷L :
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        (⊢l : Γ ⊢ l ∷Level) →
        size-⊢∷L ⊢l PE.≡ s →
        Δ ⊢ l [ σ₁ ] ≡ l [ σ₂ ] ∷Level
      subst-⊢≡∷ :
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A) →
        size-⊢≡∷ t₁≡t₂ PE.≡ s →
        Δ ⊢ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ]
      subst-⊢≡∷L :
        Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
        (l₁≡l₂ : Γ ⊢ l₁ ≡ l₂ ∷Level) →
        size-⊢≡∷L l₁≡l₂ PE.≡ s →
        Δ ⊢ l₁ [ σ₁ ] ≡ l₂ [ σ₂ ] ∷Level

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

    subst-⊢∷L :
      (⊢l : Γ ⊢ l ∷Level)
      ⦃ lt : size-⊢∷L ⊢l <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ l [ σ ] ∷Level
    subst-⊢∷L ⊢l ⦃ lt ⦄ ⊢σ = P.subst-⊢∷L (hyp lt) ⊢σ ⊢l PE.refl

    subst-⊢∷→⊢≡∷ :
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]
    subst-⊢∷→⊢≡∷ ⊢t ⦃ lt ⦄ σ₁≡σ₂ =
      P.subst-⊢∷→⊢≡∷ (hyp lt) σ₁≡σ₂ ⊢t PE.refl

    subst-⊢∷L→⊢≡∷L :
      (⊢l : Γ ⊢ l ∷Level)
      ⦃ lt : size-⊢∷L ⊢l <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ l [ σ₁ ] ≡ l [ σ₂ ] ∷Level
    subst-⊢∷L→⊢≡∷L ⊢l ⦃ lt ⦄ σ₁≡σ₂ =
      P.subst-⊢∷L→⊢≡∷L (hyp lt) σ₁≡σ₂ ⊢l PE.refl

    subst-⊢≡∷ :
      (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A)
      ⦃ lt : size-⊢≡∷ t₁≡t₂ <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊢ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ]
    subst-⊢≡∷ t₁≡t₂ ⦃ lt ⦄ σ₁≡σ₂ =
      P.subst-⊢≡∷ (hyp lt) σ₁≡σ₂ t₁≡t₂ PE.refl

    subst-⊢≡∷L :
      (l₁≡l₂ : Γ ⊢ l₁ ≡ l₂ ∷Level)
      ⦃ lt : size-⊢≡∷L l₁≡l₂ <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊢ l₁ [ σ₁ ] ≡ l₂ [ σ₂ ] ∷Level
    subst-⊢≡∷L l₁≡l₂ ⦃ lt ⦄ σ₁≡σ₂ =
      P.subst-⊢≡∷L (hyp lt) σ₁≡σ₂ l₁≡l₂ PE.refl

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
    unfolding size-⊢′

    -- A variant of ⊢ˢʷ≡∷-⇑.

    ⊢ˢʷ≡∷-⇑[]-<ˢ :
      (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ˢʷ σ₁ ⇑[ k ] ≡ σ₂ ⇑[ k ] ∷ Γ
    ⊢ˢʷ≡∷-⇑[]-<ˢ {k = 0}    (_ , _)     = idᶠ
    ⊢ˢʷ≡∷-⇑[]-<ˢ {k = 1+ _} (∙ ⊢A , lt) =
      let lt = ⊕≤ˢ→<ˢˡ (<ˢ→≤ˢ lt) in
      ⊢ˢʷ≡∷-⇑-<ˢ (⊢A , lt) ∘→
      ⊢ˢʷ≡∷-⇑[]-<ˢ (wf-<ˢ ⊢A) ⦃ lt = <ˢ-trans lt ! ⦄

  opaque

    -- A variant of ⊢ˢʷ∷-⇑.

    ⊢ˢʷ∷-⇑[]-<ˢ :
      (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ ] ⊢ˢʷ σ ⇑[ k ] ∷ Γ
    ⊢ˢʷ∷-⇑[]-<ˢ ⊢Γ =
      ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₂ ∘→ ⊢ˢʷ≡∷-⇑[]-<ˢ ⊢Γ ∘→ ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₁

  opaque

    -- Some substitution lemmas that use ⊢ˢʷ∷-⇑[]-<ˢ or ⊢ˢʷ≡∷-⇑[]-<ˢ.

    subst-⊢-⇑ :
      (⊢A : Γ ⊢ A)
      ⦃ lt : size-⊢ ⊢A <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ ] ⊢ A [ σ ⇑[ k ] ]
    subst-⊢-⇑ ⊢A = subst-⊢ ⊢A ∘→ ⊢ˢʷ∷-⇑[]-<ˢ (wf-<ˢ ⊢A)

    subst-⊢→⊢≡-⇑ :
      (⊢A : Γ ⊢ A)
      ⦃ lt : size-⊢ ⊢A <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ A [ σ₁ ⇑[ k ] ] ≡ A [ σ₂ ⇑[ k ] ]
    subst-⊢→⊢≡-⇑ ⊢A = subst-⊢→⊢≡ ⊢A ∘→ ⊢ˢʷ≡∷-⇑[]-<ˢ (wf-<ˢ ⊢A)

    subst-⊢→⊢≡-⇑-<ˢ :
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) →
      ⦃ lt : s <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ A [ σ₁ ⇑[ k ] ] ≡ A [ σ₂ ⇑[ k ] ]
    subst-⊢→⊢≡-⇑-<ˢ (⊢A , lt) = subst-⊢→⊢≡-⇑ ⊢A ⦃ lt = <ˢ-trans lt ! ⦄

    subst-⊢≡-⇑ :
      (A₁≡A₂ : Γ ⊢ A₁ ≡ A₂)
      ⦃ lt : size-⊢≡ A₁≡A₂ <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ A₁ [ σ₁ ⇑[ k ] ] ≡ A₂ [ σ₂ ⇑[ k ] ]
    subst-⊢≡-⇑ A₁≡A₂ = subst-⊢≡ A₁≡A₂ ∘→ ⊢ˢʷ≡∷-⇑[]-<ˢ (wfEq-<ˢ A₁≡A₂)

    subst-⊢∷-⇑ :
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ ] ⊢ t [ σ ⇑[ k ] ] ∷ A [ σ ⇑[ k ] ]
    subst-⊢∷-⇑ ⊢t = subst-⊢∷ ⊢t ∘→ ⊢ˢʷ∷-⇑[]-<ˢ (wfTerm-<ˢ ⊢t)

    subst-⊢∷→⊢≡∷-⇑ :
      (⊢t : Γ ⊢ t ∷ A)
      ⦃ lt : size-⊢∷ ⊢t <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ t [ σ₁ ⇑[ k ] ] ≡ t [ σ₂ ⇑[ k ] ] ∷
        A [ σ₁ ⇑[ k ] ]
    subst-⊢∷→⊢≡∷-⇑ ⊢t = subst-⊢∷→⊢≡∷ ⊢t ∘→ ⊢ˢʷ≡∷-⇑[]-<ˢ (wfTerm-<ˢ ⊢t)

    subst-⊢≡∷-⇑ :
      (t₁≡t₂ : Γ ⊢ t₁ ≡ t₂ ∷ A)
      ⦃ lt : size-⊢≡∷ t₁≡t₂ <ˢ s₂ ⦄ →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
      Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ t₁ [ σ₁ ⇑[ k ] ] ≡ t₂ [ σ₂ ⇑[ k ] ] ∷
        A [ σ₁ ⇑[ k ] ]
    subst-⊢≡∷-⇑ t₁≡t₂ =
      subst-⊢≡∷ t₁≡t₂ ∘→ ⊢ˢʷ≡∷-⇑[]-<ˢ (wfEqTerm-<ˢ t₁≡t₂)

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
      (Levelⱼ ok _) _ →
        Levelⱼ ok (wf-⊢ˢʷ∷ ⊢σ)
      (univ ⊢A) PE.refl →
        univ (subst-⊢∷ ⊢A ⊢σ)
      (Liftⱼ ⊢l ⊢A) PE.refl →
        Liftⱼ (subst-⊢∷L ⊢l ⊢σ) (subst-⊢ ⊢A ⊢σ)
      (ΠΣⱼ ⊢B ok) PE.refl →
        ΠΣⱼ (subst-⊢-⇑ ⊢B ⊢σ) ok
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
      (Levelⱼ ok _) _ →
        refl (Levelⱼ ok (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (univ ⊢A) PE.refl →
        univ (subst-⊢∷→⊢≡∷ ⊢A σ₁≡σ₂)
      (Liftⱼ ⊢l ⊢A) PE.refl →
        Lift-cong (subst-⊢∷L→⊢≡∷L ⊢l σ₁≡σ₂) (subst-⊢→⊢≡ ⊢A σ₁≡σ₂)
      (ΠΣⱼ ⊢B ok) PE.refl →
        let _ , ⊢A = ∙⊢→⊢-<ˢ ⊢B in
        ΠΣ-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂) (subst-⊢→⊢≡-⇑ ⊢B σ₁≡σ₂) ok
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
      (Lift-cong l₁≡l₂ A≡B) PE.refl →
        Lift-cong (subst-⊢≡∷L l₁≡l₂ σ₁≡σ₂) (subst-⊢≡ A≡B σ₁≡σ₂)
      (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
        ΠΣ-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂) (subst-⊢≡-⇑ B₁≡B₂ σ₁≡σ₂) ok
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
      (Levelⱼ _ ok) _ →
        Levelⱼ (wf-⊢ˢʷ∷ ⊢σ) ok
      (zeroᵘⱼ ok _) _ →
        zeroᵘⱼ ok (wf-⊢ˢʷ∷ ⊢σ)
      (sucᵘⱼ ⊢t) PE.refl →
        sucᵘⱼ (subst-⊢∷ ⊢t ⊢σ)
      (supᵘⱼ ⊢t ⊢u) PE.refl →
        supᵘⱼ (subst-⊢∷ ⊢t ⊢σ) (subst-⊢∷ ⊢u ⊢σ)
      (Uⱼ ⊢l) PE.refl →
        Uⱼ (subst-⊢∷L ⊢l ⊢σ)
      (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.cong U $ PE.sym $ supᵘₗ-[] ⊢l₁ ⊢l₂) $
        Liftⱼ (subst-⊢∷L ⊢l₁ ⊢σ) (subst-⊢∷L ⊢l₂ ⊢σ) (subst-⊢∷ ⊢A ⊢σ)
      (liftⱼ ⊢l₂ ⊢A ⊢t) PE.refl →
        liftⱼ (subst-⊢∷L ⊢l₂ ⊢σ) (subst-⊢ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (lowerⱼ x) PE.refl →
        lowerⱼ (subst-⊢∷ x ⊢σ)
      (ΠΣⱼ {l} ⊢l ⊢A ⊢B ok) PE.refl →
        let ⊢A[σ] = subst-⊢∷ ⊢A ⊢σ in
        ΠΣⱼ (subst-⊢∷L ⊢l ⊢σ) ⊢A[σ]
          (PE.subst (λ x → _ ⊢ _ ∷ U x)
            (wk1-liftSubst l)
            (subst-⊢∷-⇑ ⊢B ⊢σ))
          ok
      (lamⱼ ⊢B ⊢t ok) PE.refl →
        lamⱼ (subst-⊢-⇑ ⊢B ⊢σ) (subst-⊢∷-⇑ ⊢t ⊢σ) ok
      (_∘ⱼ_ {G = B} ⊢t ⊢u) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift B _)
          (subst-⊢∷ ⊢t ⊢σ ∘ⱼ subst-⊢∷ ⊢u ⊢σ)
      (prodⱼ {G = B} ⊢B ⊢t ⊢u ok) PE.refl →
        prodⱼ (subst-⊢-⇑ ⊢B ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
           subst-⊢∷ ⊢u ⊢σ)
          ok
      (fstⱼ ⊢B ⊢t) PE.refl →
        fstⱼ (subst-⊢-⇑ ⊢B ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (sndⱼ {G = B} ⊢B ⊢t) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift B _) $
        sndⱼ (subst-⊢-⇑ ⊢B ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (prodrecⱼ {A = C} ⊢C ⊢t ⊢u ok) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift C _) $
        prodrecⱼ (subst-⊢-⇑ ⊢C ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C _) $
           subst-⊢∷-⇑ ⊢u ⊢σ)
          ok
      (Emptyⱼ _) _ →
        Emptyⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (emptyrecⱼ ⊢A ⊢t) PE.refl →
        emptyrecⱼ (subst-⊢ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
      (starⱼ ⊢Γ ok) PE.refl →
        starⱼ (wf-⊢ˢʷ∷ ⊢σ) ok
      (unitrecⱼ {A} ⊢A ⊢t ⊢u ok) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift A _) $
        unitrecⱼ
          (subst-⊢-⇑ ⊢A ⊢σ)
          (subst-⊢∷ ⊢t ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
           subst-⊢∷ ⊢u ⊢σ)
          ok
      (Unitⱼ ⊢Γ ok) PE.refl →
        Unitⱼ (wf-⊢ˢʷ∷ ⊢σ) ok
      (ℕⱼ _) _ →
        ℕⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (zeroⱼ _) _ →
        zeroⱼ (wf-⊢ˢʷ∷ ⊢σ)
      (sucⱼ ⊢t) PE.refl →
        sucⱼ (subst-⊢∷ ⊢t ⊢σ)
      (natrecⱼ {A} ⊢t ⊢u ⊢v) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift A _) $
        natrecⱼ
          (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
           subst-⊢∷ ⊢t ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
           subst-⊢∷-⇑ ⊢u ⊢σ)
          (subst-⊢∷ ⊢v ⊢σ)
      (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
        Idⱼ (subst-⊢∷ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ) (subst-⊢∷ ⊢u ⊢σ)
      (rflⱼ ⊢t) PE.refl →
        rflⱼ (subst-⊢∷ ⊢t ⊢σ)
      (Jⱼ {t} {A} {B} ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ [,]-[]-commute B) $
        Jⱼ (subst-⊢∷ ⊢t ⊢σ)
          (PE.subst₂ _⊢_
             (PE.cong (_∙_ _) $
              PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl)
             PE.refl $
           subst-⊢-⇑ ⊢B ⊢σ)
          (PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) $
           subst-⊢∷ ⊢u ⊢σ)
          (subst-⊢∷ ⊢v ⊢σ) (subst-⊢∷ ⊢w ⊢σ)
      (Kⱼ {B} ⊢B ⊢u ⊢v ok) PE.refl →
        PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstLift B _) $
        Kⱼ (subst-⊢-⇑ ⊢B ⊢σ)
          (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
           subst-⊢∷ ⊢u ⊢σ)
          (subst-⊢∷ ⊢v ⊢σ) ok
      ([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
        PE.subst (_⊢_∷_ _ _) (E.Id-Erased-[] _) $
        []-congⱼ (subst-⊢∷L ⊢l ⊢σ) (subst-⊢ ⊢A ⊢σ) (subst-⊢∷ ⊢t ⊢σ)
          (subst-⊢∷ ⊢u ⊢σ) (subst-⊢∷ ⊢v ⊢σ) ok

  opaque
    unfolding size-⊢∷L

    -- A substitution lemma for _⊢_∷Level.

    subst-⊢∷L′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ ∷ Γ →
      (⊢l : Γ ⊢ l ∷Level) →
      size-⊢∷L ⊢l PE.≡ s₂ →
      Δ ⊢ l [ σ ] ∷Level
    subst-⊢∷L′ hyp ⊢σ = let open Lemmas hyp in λ where
      (term ok ⊢l) PE.refl →
        term ok (subst-⊢∷ ⊢l ⊢σ)
      (literal not-ok _ l-lit) _ →
        literal not-ok (wf-⊢ˢʷ∷ ⊢σ) (Level-literal-[] l-lit)

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
      (Levelⱼ _ ok) _ →
        refl (Levelⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁) ok)
      (zeroᵘⱼ ok _) _ →
        refl (zeroᵘⱼ ok (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (sucᵘⱼ ⊢t) PE.refl →
        sucᵘ-cong (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (supᵘⱼ ⊢t ⊢u) PE.refl →
        supᵘ-cong (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
      (Uⱼ ⊢l) PE.refl →
        U-cong-⊢≡∷ (subst-⊢∷L→⊢≡∷L ⊢l σ₁≡σ₂)
      (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) PE.refl →
        let ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.cong U $ PE.sym $ supᵘₗ-[] ⊢l₁ ⊢l₂) $
        Lift-cong (subst-⊢∷L ⊢l₁ ⊢σ₁) (subst-⊢∷L ⊢l₂ ⊢σ₁)
          (subst-⊢∷L→⊢≡∷L ⊢l₂ σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢A σ₁≡σ₂)
      (liftⱼ ⊢l₂ ⊢A ⊢t) PE.refl →
        let ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂
        in
        lift-cong (subst-⊢∷L ⊢l₂ ⊢σ₁) (subst-⊢ ⊢A ⊢σ₁) (subst-⊢∷ ⊢t ⊢σ₁)
          (conv (subst-⊢∷ ⊢t ⊢σ₂) (sym (subst-⊢→⊢≡ ⊢A σ₁≡σ₂)))
          (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (lowerⱼ x) PE.refl →
        lower-cong (subst-⊢∷→⊢≡∷ x σ₁≡σ₂)
      (ΠΣⱼ {l} ⊢l ⊢A ⊢B ok) PE.refl →
        let ⊢σ₁         = wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁
            ⊢A[σ₁]      = _⊢_.univ $
                          subst-⊢∷ ⊢A ⊢σ₁
            A[σ₁]≡A[σ₂] = subst-⊢∷→⊢≡∷ ⊢A σ₁≡σ₂
        in
        ΠΣ-cong (subst-⊢∷L ⊢l ⊢σ₁) A[σ₁]≡A[σ₂]
          (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ U x)
            (wk1-liftSubst l)
            (subst-⊢∷→⊢≡∷-⇑ ⊢B σ₁≡σ₂))
          ok
      (lamⱼ ⊢B ⊢t ok) PE.refl →
        let _ , ⊢A      = ∙⊢∷→⊢-<ˢ ⊢t
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            _ , _ , σ₂⇑ = wf-⊢ˢʷ≡∷ (⊢ˢʷ≡∷-⇑-<ˢ ⊢A σ₁≡σ₂)
        in
        lam-cong (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢∷-⇑ ⊢t ⊢σ₁)
          (_⊢_∷_.conv (subst-⊢∷ ⊢t σ₂⇑) $
           _⊢_≡_.sym (subst-⊢→⊢≡-⇑ ⊢B σ₁≡σ₂))
          (subst-⊢∷→⊢≡∷-⇑ ⊢t σ₁≡σ₂) ok
      (_∘ⱼ_ {G = B} ⊢t ⊢u) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _)
          (app-cong (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂))
      (prodⱼ {G = B} ⊢B ⊢t ⊢u ok) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        prod-cong (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B _) $
           subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
          ok
      (fstⱼ ⊢B ⊢t) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        fst-cong (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (sndⱼ {G = B} ⊢B ⊢t) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
        snd-cong (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (prodrecⱼ {A = C} ⊢C ⊢t ⊢u ok) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift C _) $
        prodrec-cong (subst-⊢→⊢≡-⇑ ⊢C σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (subst-β-prodrec C _) $
           subst-⊢∷→⊢≡∷-⇑ ⊢u σ₁≡σ₂)
          ok
      (Emptyⱼ _) _ →
        refl (Emptyⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (emptyrecⱼ ⊢A ⊢t) PE.refl →
        emptyrec-cong (subst-⊢→⊢≡ ⊢A σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (starⱼ ⊢l ok) PE.refl →
        refl (starⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁) ok)
      (unitrecⱼ {A} {t} {u} {p} {q} ⊢A ⊢t ⊢u ok) PE.refl →
        let ⊢Δ , ⊢σ₁ , ⊢σ₂  = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢Unit           = univ (Unitⱼ ⊢Δ ok)
            σ₁⇑≡σ₂⇑         = ⊢ˢʷ≡∷-⇑ ⊢Unit (refl ⊢Unit) σ₁≡σ₂
            _ , ⊢σ₁⇑ , ⊢σ₂⇑ = wf-⊢ˢʷ≡∷ σ₁⇑≡σ₂⇑
            u[σ₁]≡u[σ₂]     = PE.subst (_⊢_≡_∷_ _ _ _)
                                (singleSubstLift A _) $
                              subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
        case Unitʷ-η? of λ where
          (no no-η) →
            unitrec-cong (subst-⊢→⊢≡ ⊢A σ₁⇑≡σ₂⇑) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
              u[σ₁]≡u[σ₂] ok no-η
          (yes η) →
            let ⊢t[σ₁] = subst-⊢∷ ⊢t ⊢σ₁ in
            unitrec p q A t u [ σ₁ ]  ≡⟨ unitrec-β-η (subst-⊢ ⊢A ⊢σ₁⇑) ⊢t[σ₁]
                                             (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                              subst-⊢∷ ⊢u ⊢σ₁)
                                             ok η ⟩⊢
            u [ σ₁ ]                    ≡⟨ _⊢_≡_∷_.conv u[σ₁]≡u[σ₂] $
                                           PE.subst₂ (_⊢_≡_ _)
                                             (PE.sym $ singleSubstComp _ _ A)
                                             (PE.sym $ singleSubstComp _ _ A) $
                                           subst-⊢→⊢≡ ⊢A $
                                           ⊢ˢʷ≡∷∙⇔ .proj₂
                                             ( refl-⊢ˢʷ≡∷ ⊢σ₁ , starⱼ ⊢Δ ok , ⊢t[σ₁]
                                             , η-unit (starⱼ ⊢Δ ok) ⊢t[σ₁] ok (inj₂ η)
                                             ) ⟩⊢
            u [ σ₂ ]                    ≡⟨ _⊢_≡_∷_.sym
                                             (PE.subst (_⊢_ _) (PE.sym $ singleSubstComp _ _ A) $
                                              subst-⊢ ⊢A (⊢ˢʷ∷∙⇔ .proj₂ (⊢σ₁ , ⊢t[σ₁]))) $
                                           _⊢_≡_∷_.conv
                                             (unitrec-β-η
                                              (subst-⊢ ⊢A (⊢ˢʷ∷-⇑ (univ (Unitⱼ ⊢Δ ok)) ⊢σ₂))
                                              (subst-⊢∷ ⊢t ⊢σ₂)
                                              (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A _) $ subst-⊢∷ ⊢u ⊢σ₂)
                                              ok η)
                                             (PE.subst₂ (_⊢_≡_ _)
                                                (PE.sym $ singleSubstComp _ _ A)
                                                (PE.sym $ singleSubstComp _ _ A) $
                                              sym (subst-⊢→⊢≡ ⊢A (⊢ˢʷ≡∷-consSubst-[] σ₁≡σ₂ ⊢t))) ⟩⊢∎
            unitrec p q A t u [ σ₂ ]  ∎
      (Unitⱼ ⊢Γ ok) PE.refl →
        refl (Unitⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁) ok)
      (ℕⱼ _) _ →
        refl (ℕⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (zeroⱼ _) _ →
        refl (zeroⱼ (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁))
      (sucⱼ ⊢t) PE.refl →
        suc-cong (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
      (natrecⱼ {A} ⊢t ⊢u ⊢v) PE.refl →
        let _ , ⊢A = ∙⊢∷→⊢-<ˢ ⊢u in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
        natrec-cong (subst-⊢→⊢≡-⇑-<ˢ ⊢A σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift A _) $
           subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (natrecSucCase _ A) $
           subst-⊢∷→⊢≡∷-⇑ ⊢u σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂)
      (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
        Id-cong (subst-⊢∷→⊢≡∷ ⊢A σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
      (rflⱼ ⊢t) PE.refl →
        _⊢_≡_∷_.refl $
        rflⱼ (subst-⊢∷ ⊢t (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁))
      (Jⱼ {t} {A} {B} ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
        let _ , ⊢A , _  = ∙∙⊢→⊢-<ˢ ⊢B
            _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
        J-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂) (subst-⊢∷ ⊢t ⊢σ₁)
          (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
          (PE.subst₃ _⊢_≡_
             (PE.cong (_∙_ _) $
              PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl)
             PE.refl PE.refl $
           subst-⊢→⊢≡-⇑ ⊢B σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) ([,]-[]-commute B) $
           subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢w σ₁≡σ₂)
      (Kⱼ {B} ⊢B ⊢u ⊢v ok) PE.refl →
        let _ , ⊢Id     = ∙⊢→⊢-<ˢ ⊢B
            ⊢A , ⊢t , _ = inversion-Id-⊢-<ˢ ⊢Id
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
        K-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂) (subst-⊢∷→⊢≡∷-<ˢ ⊢t σ₁≡σ₂)
          (subst-⊢→⊢≡-⇑ ⊢B σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B _) $
           subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂) ok
      ([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (E.Id-Erased-[] _) $
        []-cong-cong (subst-⊢∷L→⊢≡∷L ⊢l σ₁≡σ₂) (subst-⊢→⊢≡ ⊢A σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂)
          (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂) ok

  opaque
    unfolding size-⊢∷L

    -- A substitution lemma for _⊢_∷Level and _⊢_≡_∷Level.

    subst-⊢∷L→⊢≡∷L′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      (⊢l : Γ ⊢ l ∷Level) →
      size-⊢∷L ⊢l PE.≡ s₂ →
      Δ ⊢ l [ σ₁ ] ≡ l [ σ₂ ] ∷Level
    subst-⊢∷L→⊢≡∷L′ {σ₁} {σ₂} hyp σ₁≡σ₂ =
      let open Lemmas hyp in λ where
        (term ok ⊢l) PE.refl →
          term ok (subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂)
        (literal not-ok _ l-lit) _ →
          PE.subst (_⊢_≡_∷Level _ _) (Level-literal→[]≡[] l-lit) $
          literal not-ok (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁)
            (Level-literal-[] l-lit)

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
      (supᵘ-cong t₁≡t₂ u₁≡u₂) PE.refl →
        supᵘ-cong (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂) (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
      (supᵘ-zeroˡ ⊢l) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in trans (supᵘ-zeroˡ (subst-⊢∷ ⊢l ⊢σ₁)) (subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂)
      (supᵘ-sucᵘ ⊢l₁ ⊢l₂) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in trans
          (supᵘ-sucᵘ (subst-⊢∷ ⊢l₁ ⊢σ₁) (subst-⊢∷ ⊢l₂ ⊢σ₁))
          (sucᵘ-cong (supᵘ-cong (subst-⊢∷→⊢≡∷ ⊢l₁ σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢l₂ σ₁≡σ₂)))
      (supᵘ-assoc ⊢l₁ ⊢l₂ ⊢l₃) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in trans
          (supᵘ-assoc (subst-⊢∷ ⊢l₁ ⊢σ₁) (subst-⊢∷ ⊢l₂ ⊢σ₁) (subst-⊢∷ ⊢l₃ ⊢σ₁))
          (supᵘ-cong (subst-⊢∷→⊢≡∷ ⊢l₁ σ₁≡σ₂)
            (supᵘ-cong (subst-⊢∷→⊢≡∷ ⊢l₂ σ₁≡σ₂)
              (subst-⊢∷→⊢≡∷ ⊢l₃ σ₁≡σ₂)))
      (supᵘ-comm ⊢l₁ ⊢l₂) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in trans
          (supᵘ-comm (subst-⊢∷ ⊢l₁ ⊢σ₁) (subst-⊢∷ ⊢l₂ ⊢σ₁))
          (supᵘ-cong (subst-⊢∷→⊢≡∷ ⊢l₂ σ₁≡σ₂) (subst-⊢∷→⊢≡∷ ⊢l₁ σ₁≡σ₂))
      (supᵘ-idem ⊢l) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in trans
          (supᵘ-idem (subst-⊢∷ ⊢l ⊢σ₁))
          (subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂)
      (supᵘ-sub ⊢l) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in trans
          (supᵘ-sub (subst-⊢∷ ⊢l ⊢σ₁))
          (sucᵘ-cong (subst-⊢∷→⊢≡∷ ⊢l σ₁≡σ₂))
      (U-cong l₁≡l₂) PE.refl →
        U-cong (subst-⊢≡∷ l₁≡l₂ σ₁≡σ₂)
      (Lift-cong ⊢l₁ ⊢l₂ l₂≡l₃ A≡B) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        PE.subst (_⊢_≡_∷_ _ _ _)
          (PE.cong U $ PE.sym $ supᵘₗ-[] ⊢l₁ ⊢l₂) $
        Lift-cong (subst-⊢∷L ⊢l₁ ⊢σ₁) (subst-⊢∷L ⊢l₂ ⊢σ₁)
          (subst-⊢≡∷L l₂≡l₃ σ₁≡σ₂) (subst-⊢≡∷ A≡B σ₁≡σ₂)
      (lower-cong x) PE.refl → lower-cong (subst-⊢≡∷ x σ₁≡σ₂)
      (Lift-β x₁ x₂) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in trans (Lift-β (subst-⊢ x₁ ⊢σ₁) (subst-⊢∷ x₂ ⊢σ₁)) (subst-⊢∷→⊢≡∷ x₂ σ₁≡σ₂)
      (Lift-η ⊢l ⊢A ⊢t ⊢u lower-t≡lower-u) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        Lift-η (subst-⊢∷L ⊢l ⊢σ₁) (subst-⊢ ⊢A ⊢σ₁) (subst-⊢∷ ⊢t ⊢σ₁)
          (_⊢_∷_.conv (subst-⊢∷ ⊢u ⊢σ₂) $ _⊢_≡_.sym $
           Lift-cong (subst-⊢∷L→⊢≡∷L ⊢l σ₁≡σ₂) (subst-⊢→⊢≡ ⊢A σ₁≡σ₂))
          (subst-⊢≡∷ lower-t≡lower-u σ₁≡σ₂)
      (ΠΣ-cong {l} ⊢l A₁≡A₂ B₁≡B₂ ok) PE.refl →
        let ⊢σ₁ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₂ .proj₁
            _ , ⊢A₁ = ∙⊢≡∷→⊢-<ˢ B₁≡B₂
        in
        ΠΣ-cong (subst-⊢∷L ⊢l ⊢σ₁) (subst-⊢≡∷ A₁≡A₂ σ₁≡σ₂)
          (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ U x)
            (wk1-liftSubst l)
            (subst-⊢≡∷-⇑ B₁≡B₂ σ₁≡σ₂))
          ok
      (app-cong {G = B} t₁≡t₂ u₁≡u₂) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
        app-cong (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂) (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
      (β-red {G = B} {t} {a = u} {p} ⊢B ⊢t ⊢u PE.refl ok) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
                                             ∷ B [ u ]₀ [ σ₁ ]            ⟨ singleSubstLift B _ ⟩≡∷≡
        lam p (t [ σ₁ ⇑ ]) ∘⟨ p ⟩ (u [ σ₁ ]) ∷ B [ σ₁ ⇑ ] [ u [ σ₁ ] ]₀  ≡⟨ β-red (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢∷-⇑ ⊢t ⊢σ₁)
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
        in
        η-eq (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢∷ ⊢t₁ ⊢σ₁)
          (_⊢_∷_.conv (subst-⊢∷ ⊢t₂ ⊢σ₂) $
           _⊢_≡_.sym $
           ΠΣ-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂) (subst-⊢→⊢≡-⇑ ⊢B σ₁≡σ₂) ok)
          (PE.subst₃ (_⊢_≡_∷_ _)
             (PE.cong (_∘⟨ _ ⟩ _) (wk1-liftSubst t₁))
             (PE.cong (_∘⟨ _ ⟩ _) (wk1-liftSubst t₂))
             PE.refl $
           subst-⊢≡∷-⇑ t₁0≡t₂0 σ₁≡σ₂)
          ok
      (fst-cong ⊢B t₁≡t₂) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        fst-cong (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
      (snd-cong {G = B} ⊢B t₁≡t₂) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
        snd-cong (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
      (Σ-β₁ {G = B} {t} {u} {p} ⊢B ⊢t ⊢u PE.refl ok) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        fst p (prodˢ p t u) [ σ₁ ]  ≡⟨ Σ-β₁ (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢∷ ⊢t ⊢σ₁)
                                         (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
                                          subst-⊢∷ ⊢u ⊢σ₁)
                                         PE.refl ok ⟩⊢
        t [ σ₁ ]                    ≡⟨ subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂ ⟩⊢∎
        t [ σ₂ ]                    ∎
      (Σ-β₂ {G = B} {t} {u} {p} ⊢B ⊢t ⊢u PE.refl ok) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢B[σ₁⇑]     = subst-⊢-⇑ ⊢B ⊢σ₁
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
        Σ-η (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢∷ ⊢t₁ ⊢σ₁)
          (_⊢_∷_.conv (subst-⊢∷ ⊢t₂ ⊢σ₂) $
           _⊢_≡_.sym $
           ΠΣ-cong (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂) (subst-⊢→⊢≡-⇑ ⊢B σ₁≡σ₂) ok)
          (subst-⊢≡∷ fst-t₁≡fst-t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B _) $
           subst-⊢≡∷ snd-t₁≡snd-t₂ σ₁≡σ₂)
          ok
      (prod-cong {G = B} ⊢B t₁≡t₂ u₁≡u₂ ok) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        prod-cong (subst-⊢-⇑ ⊢B ⊢σ₁) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B _) $
           subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          ok
      (prodrec-cong {A = C} C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift C _) $
        prodrec-cong (subst-⊢≡-⇑ C₁≡C₂ σ₁≡σ₂) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (subst-β-prodrec C _) $
           subst-⊢≡∷-⇑ u₁≡u₂ σ₁≡σ₂)
          ok
      (prodrec-β
         {p} {G = B} {A = C} {t} {t′ = u} {u = v} {r} {q}
         ⊢C ⊢t ⊢u ⊢v PE.refl ok)
        PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
          ∷ C [ prodʷ p t u ]₀ [ σ₁ ]                       ⟨ singleSubstLift C _ ⟩≡∷≡

        prodrec r p q C (prodʷ p t u) v [ σ₁ ]
          ∷ C [ σ₁ ⇑ ] [ prodʷ p (t [ σ₁ ]) (u [ σ₁ ]) ]₀  ≡⟨ prodrec-β (subst-⊢-⇑ ⊢C ⊢σ₁) (subst-⊢∷ ⊢t ⊢σ₁)
                                                                (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
                                                                 subst-⊢∷ ⊢u ⊢σ₁)
                                                                (PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C _) $
                                                                 subst-⊢∷-⇑ ⊢v ⊢σ₁)
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
      (unitrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ ok no-η) PE.refl →
        let ⊢Δ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁
            ⊢Unit = univ (Unitⱼ ⊢Δ ok)
        in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ _) $
        unitrec-cong
          (subst-⊢≡ A₁≡A₂ (⊢ˢʷ≡∷-⇑ ⊢Unit (refl ⊢Unit) σ₁≡σ₂))
          (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift A₁ _) $
           subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          ok no-η
      (unitrec-β {A} {u = t} {p} {q} ⊢A ⊢t ok no-η) PE.refl →
        let ⊢Δ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        in
        unitrec p q A starʷ t [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
                                         unitrec-β (subst-⊢ ⊢A (⊢ˢʷ∷-⇑ (univ (Unitⱼ ⊢Δ ok)) ⊢σ₁))
                                           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                            subst-⊢∷ ⊢t ⊢σ₁)
                                           ok no-η ⟩⊢
        t [ σ₁ ]                      ≡⟨ subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂ ⟩⊢∎
        t [ σ₂ ]                      ∎
      (unitrec-β-η {A} {t} {u} {p} {q} ⊢A ⊢t ⊢u ok no-η) PE.refl →
        let ⊢Δ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢t[σ₁]       = subst-⊢∷ ⊢t ⊢σ₁
        in
        unitrec p q A t u [ σ₁ ] ∷ A [ t ]₀ [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
                                                         unitrec-β-η (subst-⊢-⇑ ⊢A ⊢σ₁) ⊢t[σ₁]
                                                           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                                            subst-⊢∷ ⊢u ⊢σ₁)
                                                           ok no-η ⟩⊢∷
                                                       ⟨ PE.subst₂ (_⊢_≡_ _)
                                                           (PE.sym $ substCompEq A) (PE.sym $ substCompEq A) $
                                                         subst-⊢→⊢≡ ⊢A $
                                                         ⊢ˢʷ≡∷∙⇔ .proj₂
                                                           ( refl-⊢ˢʷ≡∷ ⊢σ₁ , ⊢t[σ₁] , starⱼ ⊢Δ ok
                                                           , η-unit ⊢t[σ₁] (starⱼ ⊢Δ ok) ok (inj₂ no-η)
                                                           ) ⟩≡
        u [ σ₁ ] ∷ A [ starʷ ]₀ [ σ₁ ]              ≡⟨ subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂ ⟩⊢∷∎
        u [ σ₂ ]                                    ∎
      (η-unit ⊢t₁ ⊢t₂ ok η) PE.refl →
        let _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        η-unit (subst-⊢∷ ⊢t₁ ⊢σ₁) (subst-⊢∷ ⊢t₂ ⊢σ₂)
          ok η
      (suc-cong t₁≡t₂) PE.refl →
        suc-cong (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
      (natrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A₁ _) $
        natrec-cong (subst-⊢≡-⇑ A₁≡A₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift A₁ _) $
           subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (natrecSucCase _ A₁) $
           subst-⊢≡∷-⇑ u₁≡u₂ σ₁≡σ₂)
          (subst-⊢≡∷ v₁≡v₂ σ₁≡σ₂)
      (natrec-zero {z = t} {A} {s = u} {p} {q} {r} ⊢t ⊢u) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        natrec p q r A t u zero [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
                                           natrec-zero
                                             (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                              subst-⊢∷ ⊢t ⊢σ₁)
                                             (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
                                              subst-⊢∷-⇑ ⊢u ⊢σ₁) ⟩⊢
        t [ σ₁ ]                        ≡⟨ subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂ ⟩⊢∎
        t [ σ₂ ]                        ∎
      (natrec-suc {z = t} {A} {s = u} {p} {q} {r} {n = v} ⊢t ⊢u ⊢v)
        PE.refl →
        let _ , ⊢A        = ∙⊢∷→⊢-<ˢ ⊢u
            _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢t[σ₁]        = PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                            subst-⊢∷ ⊢t ⊢σ₁
            ⊢u[σ₁⇑²]      = PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
                            subst-⊢∷-⇑ ⊢u ⊢σ₁
            ⊢v[σ₁]        = subst-⊢∷ ⊢v ⊢σ₁
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
                                                                                       subst-⊢∷-⇑ ⊢u ⊢σ₂)
                                                                                      (subst-⊢∷ ⊢v ⊢σ₂))
                                                                               , PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstComp _ _ A)
                                                                                   (natrec-cong (subst-⊢→⊢≡-⇑-<ˢ ⊢A σ₁≡σ₂)
                                                                                      (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift A _) $
                                                                                       subst-⊢∷→⊢≡∷ ⊢t σ₁≡σ₂)
                                                                                      (PE.subst (_⊢_≡_∷_ _ _ _) (natrecSucCase _ A) $
                                                                                       subst-⊢∷→⊢≡∷-⇑ ⊢u σ₁≡σ₂)
                                                                                      (subst-⊢∷→⊢≡∷ ⊢v σ₁≡σ₂))
                                                                               ) ⟩⊢∷∎≡
        u [ consSubst (consSubst σ₂ (v [ σ₂ ]))
              (natrec p q r A t u v [ σ₂ ]) ]                             ≡˘⟨ [,]-[]-fusion u ⟩

        u [ v , natrec p q r A t u v ]₁₀ [ σ₂ ]                           ∎
      (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
        Id-cong (subst-⊢≡∷ A₁≡A₂ σ₁≡σ₂) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
      (J-cong {A₁} {t₁} {B₁} A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂)
        PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ [,]-[]-commute B₁) $
        J-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂) (subst-⊢∷ ⊢t₁ ⊢σ₁)
          (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (PE.subst₃ _⊢_≡_
             (PE.cong (_∙_ _) $
              PE.cong₃ Id (wk1-liftSubst A₁) (wk1-liftSubst t₁) PE.refl)
             PE.refl PE.refl $
           subst-⊢≡-⇑ B₁≡B₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) ([,]-[]-commute B₁) $
           subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          (subst-⊢≡∷ v₁≡v₂ σ₁≡σ₂) (subst-⊢≡∷ w₁≡w₂ σ₁≡σ₂)
      (J-β {t} {A} {B} {u} {p} {q} ⊢t ⊢B ⊢u PE.refl) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        J p q A t B u t rfl [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ [,]-[]-commute B) $
                                       J-β (subst-⊢∷ ⊢t ⊢σ₁)
                                         (PE.subst₂ _⊢_
                                            (PE.cong (_∙_ _) $
                                             PE.cong₃ Id (wk1-liftSubst A) (wk1-liftSubst t) PE.refl)
                                            PE.refl $
                                          subst-⊢-⇑ ⊢B ⊢σ₁)
                                         (PE.subst (_⊢_∷_ _ _) ([,]-[]-commute B) $
                                          subst-⊢∷ ⊢u ⊢σ₁)
                                         PE.refl ⟩⊢
        u [ σ₁ ]                    ≡⟨ subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂ ⟩⊢∎
        u [ σ₂ ]                    ∎
      (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B₁ _) $
        K-cong (subst-⊢≡ A₁≡A₂ σ₁≡σ₂) (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂)
          (subst-⊢≡-⇑ B₁≡B₂ σ₁≡σ₂)
          (PE.subst (_⊢_≡_∷_ _ _ _) (singleSubstLift B₁ _) $
           subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          (subst-⊢≡∷ v₁≡v₂ σ₁≡σ₂) ok
      (K-β {A} {t} {B} {u} {p} ⊢B ⊢u ok) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        K p A t B u rfl [ σ₁ ]  ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
                                   K-β (subst-⊢-⇑ ⊢B ⊢σ₁)
                                     (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
                                      subst-⊢∷ ⊢u ⊢σ₁)
                                     ok ⟩⊢
        u [ σ₁ ]                ≡⟨ subst-⊢∷→⊢≡∷ ⊢u σ₁≡σ₂ ⟩⊢∎
        u [ σ₂ ]                ∎
      ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
        PE.subst (_⊢_≡_∷_ _ _ _) (E.Id-Erased-[] _) $
        []-cong-cong (subst-⊢≡∷L l₁≡l₂ σ₁≡σ₂) (subst-⊢≡ A₁≡A₂ σ₁≡σ₂)
          (subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂) (subst-⊢≡∷ u₁≡u₂ σ₁≡σ₂)
          (subst-⊢≡∷ v₁≡v₂ σ₁≡σ₂) ok
      ([]-cong-β ⊢l ⊢t PE.refl ok) PE.refl →
        let _ , ⊢σ₁ , _ = wf-⊢ˢʷ≡∷ σ₁≡σ₂ in
        PE.subst (_⊢_≡_∷_ _ _ _) (E.Id-Erased-[] _) $
        []-cong-β (subst-⊢∷L ⊢l ⊢σ₁) (subst-⊢∷ ⊢t ⊢σ₁) PE.refl ok
      (equality-reflection ok ⊢Id ⊢v) PE.refl →
        let ⊢A , ⊢t , ⊢u  = inversion-Id-⊢ ⊢Id
            _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ σ₁≡σ₂
            ⊢A[σ₁]        = subst-⊢-<ˢ ⊢A ⊢σ₁
            ⊢t[σ₁]        = subst-⊢∷-<ˢ ⊢t ⊢σ₁
        in
        equality-reflection ok
          (Idⱼ ⊢A[σ₁] ⊢t[σ₁] $
           conv (subst-⊢∷-<ˢ ⊢u ⊢σ₂) (sym (subst-⊢→⊢≡-<ˢ ⊢A σ₁≡σ₂)))
          (_⊢_∷_.conv (subst-⊢∷ ⊢v ⊢σ₁) $
           Id-cong (refl ⊢A[σ₁]) (refl ⊢t[σ₁])
             (subst-⊢∷→⊢≡∷-<ˢ ⊢u σ₁≡σ₂))

  opaque
    unfolding size-⊢≡∷L

    -- A substitution lemma for _⊢_≡_∷Level.

    subst-⊢≡∷L′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
      (l₁≡l₂ : Γ ⊢ l₁ ≡ l₂ ∷Level) →
      size-⊢≡∷L l₁≡l₂ PE.≡ s₂ →
      Δ ⊢ l₁ [ σ₁ ] ≡ l₂ [ σ₂ ] ∷Level
    subst-⊢≡∷L′ {σ₁} {σ₂} hyp σ₁≡σ₂ = let open Lemmas hyp in λ where
      (term ok l₁≡l₂) PE.refl →
        term ok (subst-⊢≡∷ l₁≡l₂ σ₁≡σ₂)
      (literal not-ok _ l-lit) _ →
        PE.subst (_⊢_≡_∷Level _ _) (Level-literal→[]≡[] l-lit) $
        literal not-ok (wf-⊢ˢʷ≡∷ σ₁≡σ₂ .proj₁) (Level-literal-[] l-lit)

  opaque

    -- The type P s is inhabited for every s.

    P-inhabited : P s
    P-inhabited =
      well-founded-induction P
        (λ _ hyp →
           record
             { sym-⊢ˢʷ≡∷      = sym-⊢ˢʷ≡∷′      hyp
             ; subst-⊢        = subst-⊢′        hyp
             ; subst-⊢→⊢≡     = subst-⊢→⊢≡′     hyp
             ; subst-⊢≡       = subst-⊢≡′       hyp
             ; subst-⊢∷       = subst-⊢∷′       hyp
             ; subst-⊢∷L      = subst-⊢∷L′      hyp
             ; subst-⊢∷→⊢≡∷   = subst-⊢∷→⊢≡∷′   hyp
             ; subst-⊢∷L→⊢≡∷L = subst-⊢∷L→⊢≡∷L′ hyp
             ; subst-⊢≡∷      = subst-⊢≡∷′      hyp
             ; subst-⊢≡∷L     = subst-⊢≡∷L′     hyp
             })
        _

private
  module L {s} = Lemmas {s₂ = s} (λ _ → Inhabited.P-inhabited)

opaque

  -- A substitution lemma for _⊢_.

  subst-⊢ : Γ ⊢ A → Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ A [ σ ]
  subst-⊢ ⊢A ⊢σ = P.subst-⊢ Inhabited.P-inhabited ⊢σ ⊢A PE.refl

opaque

  -- Another substitution lemma for _⊢_.

  substType : Γ ∙ A ⊢ B → Γ ⊢ t ∷ A → Γ ⊢ B [ t ]₀
  substType ⊢B = subst-⊢ ⊢B ∘→ ⊢ˢʷ∷-sgSubst

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

  -- Another substitution lemma for _⊢_∷_.

  substTerm : Γ ∙ A ⊢ t ∷ B → Γ ⊢ u ∷ A → Γ ⊢ t [ u ]₀ ∷ B [ u ]₀
  substTerm ⊢B = subst-⊢∷ ⊢B ∘→ ⊢ˢʷ∷-sgSubst

opaque

  -- A substitution lemma for _⊢_∷Level.

  subst-⊢∷L : Γ ⊢ l ∷Level → Δ ⊢ˢʷ σ ∷ Γ → Δ ⊢ l [ σ ] ∷Level
  subst-⊢∷L ⊢l ⊢σ = P.subst-⊢∷L Inhabited.P-inhabited ⊢σ ⊢l PE.refl

opaque

  -- Another substitution lemma for _⊢_∷Level.

  substLevel : Γ ∙ A ⊢ l ∷Level → Γ ⊢ t ∷ A → Γ ⊢ l [ t ]₀ ∷Level
  substLevel ⊢l = subst-⊢∷L ⊢l ∘→ ⊢ˢʷ∷-sgSubst

opaque

  -- A substitution lemma for _⊢_≡_∷_.

  subst-⊢≡∷ :
    Γ ⊢ t₁ ≡ t₂ ∷ A → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊢ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ]
  subst-⊢≡∷ t₁≡t₂ σ₁≡σ₂ =
    P.subst-⊢≡∷ Inhabited.P-inhabited σ₁≡σ₂ t₁≡t₂ PE.refl

opaque

  -- A substitution lemma for _⊢_≡_∷Level.

  subst-⊢≡∷L :
    Γ ⊢ l₁ ≡ l₂ ∷Level → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊢ l₁ [ σ₁ ] ≡ l₂ [ σ₂ ] ∷Level
  subst-⊢≡∷L l₁≡l₂ σ₁≡σ₂ =
    P.subst-⊢≡∷L Inhabited.P-inhabited σ₁≡σ₂ l₁≡l₂ PE.refl

opaque

  -- A substitution lemma related to _⇑[_].

  subst-⊢-⇑ :
    Γ ⊢ A → Δ ⊢ˢʷ σ ∷ drop k Γ → Δ ∙[ k ][ Γ ][ σ ] ⊢ A [ σ ⇑[ k ] ]
  subst-⊢-⇑ ⊢A = L.subst-⊢-⇑ ⊢A ⦃ lt = ∃-<ˢ .proj₂ ⦄

opaque

  -- A substitution lemma related to _⇑[_].

  subst-⊢∷-⇑ :
    Γ ⊢ t ∷ A → Δ ⊢ˢʷ σ ∷ drop k Γ →
    Δ ∙[ k ][ Γ ][ σ ] ⊢ t [ σ ⇑[ k ] ] ∷ A [ σ ⇑[ k ] ]
  subst-⊢∷-⇑ ⊢t = L.subst-⊢∷-⇑ ⊢t ⦃ lt = ∃-<ˢ .proj₂ ⦄

opaque

  -- A substitution lemma related to _⇑[_].

  subst-⊢≡-⇑ :
    Γ ⊢ A ≡ B → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
    Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ A [ σ₁ ⇑[ k ] ] ≡ B [ σ₂ ⇑[ k ] ]
  subst-⊢≡-⇑ A≡B = L.subst-⊢≡-⇑ A≡B ⦃ lt = ∃-<ˢ .proj₂ ⦄

opaque

  -- A substitution lemma related to _⇑[_].

  subst-⊢≡∷-⇑ :
    Γ ⊢ t ≡ u ∷ A → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
    Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ t [ σ₁ ⇑[ k ] ] ≡ u [ σ₂ ⇑[ k ] ] ∷
      A [ σ₁ ⇑[ k ] ]
  subst-⊢≡∷-⇑ t≡u = L.subst-⊢≡∷-⇑ t≡u ⦃ lt = ∃-<ˢ .proj₂ ⦄

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

  -- A variant of ⊢ˢʷ∷-⇑.

  ⊢ˢʷ∷-⇑′ :
    Γ ⊢ A →
    Δ ⊢ˢʷ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊢ˢʷ σ ⇑ ∷ Γ ∙ A
  ⊢ˢʷ∷-⇑′ ⊢A =
    L.⊢ˢʷ∷-⇑-<ˢ (⊢A , ∃-<ˢ .proj₂) ⦃ lt = ∃-<ˢ .proj₂ ⦄

opaque

  -- A variant of ⊢ˢʷ≡∷-⇑.

  ⊢ˢʷ≡∷-⇑′ :
    Γ ⊢ A →
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊢ˢʷ σ₁ ⇑ ≡ σ₂ ⇑ ∷ Γ ∙ A
  ⊢ˢʷ≡∷-⇑′ ⊢A =
    L.⊢ˢʷ≡∷-⇑-<ˢ (⊢A , ∃-<ˢ .proj₂) ⦃ lt = ∃-<ˢ .proj₂ ⦄

opaque

  -- A variant of ⊢ˢʷ∷-⇑.

  ⊢ˢʷ∷-⇑[] :
    ⊢ Γ →
    Δ ⊢ˢʷ σ ∷ drop k Γ →
    Δ ∙[ k ][ Γ ][ σ ] ⊢ˢʷ σ ⇑[ k ] ∷ Γ
  ⊢ˢʷ∷-⇑[] ⊢Γ =
    L.⊢ˢʷ∷-⇑[]-<ˢ (⊢Γ , ∃-<ˢ .proj₂) ⦃ lt = ∃-<ˢ .proj₂ ⦄

opaque

  -- A variant of ⊢ˢʷ≡∷-⇑.

  ⊢ˢʷ≡∷-⇑[] :
    ⊢ Γ →
    Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ drop k Γ →
    Δ ∙[ k ][ Γ ][ σ₁ ] ⊢ˢʷ σ₁ ⇑[ k ] ≡ σ₂ ⇑[ k ] ∷ Γ
  ⊢ˢʷ≡∷-⇑[] ⊢Γ =
    L.⊢ˢʷ≡∷-⇑[]-<ˢ (⊢Γ , ∃-<ˢ .proj₂) ⦃ lt = ∃-<ˢ .proj₂ ⦄
