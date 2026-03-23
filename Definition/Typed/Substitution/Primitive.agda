------------------------------------------------------------------------
-- Substitution lemmas
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Substitution.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
import Definition.Typed.Substitution.Primitive.Primitive R as P
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M as U hiding (wk)
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

open P public
  hiding (lam-cong; lift-cong; ⊢ˢʷ≡∷-⇑; ⊢ˢʷ≡∷-sgSubst; ⊢ˢʷ≡∷-[][]↑)

private variable
  ∇                                             : DCon (Term 0) _
  k n                                           : Nat
  Δ Η Φ                                         : Con Term _
  Γ                                             : Cons _ _
  𝓙                                             : Judgement _
  A B B₁ B₂ C C₁ C₂ D E t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ σ₁ σ₁₁ σ₁₂ σ₂ σ₂₁ σ₂₂ σ₃                    : Subst _ _
  s                                             : Strength
  p q                                           : M

------------------------------------------------------------------------
-- Lemmas related to _⊢ˢʷ_∷_ and _⊢ˢʷ_≡_∷_

opaque

  -- A variant of ⊢ˢʷ≡∷⇔.

  ⊢ˢʷ≡∷⇔′ :
    ∇ »⊢ Δ → ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ ⇔ (∇ »⊢ Η × ∇ » Η ⊢ˢ σ₁ ≡ σ₂ ∷ Δ)
  ⊢ˢʷ≡∷⇔′ {∇} {Δ} {Η} {σ₁} {σ₂} ⊢Δ =
    ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ                                              ⇔⟨ ⊢ˢʷ≡∷⇔ ⟩
    ∇ »⊢ Η × ∇ » Η ⊢ˢ σ₁ ∷ Δ × ∇ » Η ⊢ˢ σ₂ ∷ Δ × ∇ » Η ⊢ˢ σ₁ ≡ σ₂ ∷ Δ  ⇔⟨ (λ (⊢Η , _ , _ , σ₁≡σ₂) → ⊢Η , σ₁≡σ₂)
                                                                        , (λ (⊢Η , σ₁≡σ₂) →
                                                                              let ⊢σ₁ , ⊢σ₂ = wf-⊢ˢ≡∷ ⊢Δ σ₁≡σ₂ in
                                                                              ⊢Η , ⊢σ₁ , ⊢σ₂ , σ₁≡σ₂)
                                                                        ⟩
    ∇ »⊢ Η × ∇ » Η ⊢ˢ σ₁ ≡ σ₂ ∷ Δ                                      □⇔

opaque

  -- A variant of ⊢ˢʷ≡∷∙⇔.

  ⊢ˢʷ≡∷∙⇔′ :
    ∇ » Δ ⊢ A →
    ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ ∙ A ⇔
    (∇ » Η ⊢ˢʷ tail σ₁ ≡ tail σ₂ ∷ Δ ×
     ∇ » Η ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ])
  ⊢ˢʷ≡∷∙⇔′ {∇} {Δ} {A} {Η} {σ₁} {σ₂} ⊢A =
    ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ ∙ A                    ⇔⟨ ⊢ˢʷ≡∷∙⇔ ⟩

    ∇ » Η ⊢ˢʷ tail σ₁ ≡ tail σ₂ ∷ Δ ×
    ∇ » Η ⊢ head σ₁ ∷ A [ tail σ₁ ] ×
    ∇ » Η ⊢ head σ₂ ∷ A [ tail σ₂ ] ×
    ∇ » Η ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]    ⇔⟨ (λ (σ₁₊≡σ₂₊ , _ , _ , σ₁₀≡σ₂₀) →
                                                        σ₁₊≡σ₂₊ , σ₁₀≡σ₂₀)
                                                  , (λ (σ₁₊≡σ₂₊ , σ₁₀≡σ₂₀) →
                                                        let _ , ⊢σ₁₀ , ⊢σ₂₀ = wf-⊢≡∷ σ₁₀≡σ₂₀ in
                                                        σ₁₊≡σ₂₊ , ⊢σ₁₀ , conv ⊢σ₂₀ (subst-⊢≡ (refl ⊢A) σ₁₊≡σ₂₊) , σ₁₀≡σ₂₀)
                                                  ⟩

    ∇ » Η ⊢ˢʷ tail σ₁ ≡ tail σ₂ ∷ Δ ×
      ∇ » Η ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]  □⇔

opaque

  -- An introduction lemma for _⊢ˢʷ_≡_∷_.

  →⊢ˢʷ≡∷∙ :
    ∇ » Δ ⊢ A →
    ∇ » Η ⊢ˢʷ tail σ₁ ≡ tail σ₂ ∷ Δ →
    ∇ » Η ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ] →
    ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ ∙ A
  →⊢ˢʷ≡∷∙ ⊢A σ₁₊≡σ₂₊ σ₁₀≡σ₂₀ =
    ⊢ˢʷ≡∷∙⇔′ ⊢A .proj₂ (σ₁₊≡σ₂₊ , σ₁₀≡σ₂₀)

opaque

  -- Transitivity for _⊢ˢʷ_≡_∷_.

  trans-⊢ˢʷ :
    ∇ »⊢ Δ →
    ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊢ˢʷ σ₂ ≡ σ₃ ∷ Δ →
    ∇ » Η ⊢ˢʷ σ₁ ≡ σ₃ ∷ Δ
  trans-⊢ˢʷ (ε »∇) σ₁≡σ₂ _ =
    ⊢ˢʷ≡∷ε⇔ .proj₂ (⊢ˢʷ≡∷ε⇔ .proj₁ σ₁≡σ₂)
  trans-⊢ˢʷ (∙ ⊢A) σ₁≡σ₂ σ₂≡σ₃ =
    let ⊢Δ                = wf ⊢A
        σ₁₊≡σ₂₊ , σ₁₀≡σ₂₀ = ⊢ˢʷ≡∷∙⇔′ ⊢A .proj₁ σ₁≡σ₂
        σ₂₊≡σ₃₊ , σ₂₀≡σ₃₀ = ⊢ˢʷ≡∷∙⇔′ ⊢A .proj₁ σ₂≡σ₃
    in
    →⊢ˢʷ≡∷∙ ⊢A (trans-⊢ˢʷ ⊢Δ σ₁₊≡σ₂₊ σ₂₊≡σ₃₊)
      (trans σ₁₀≡σ₂₀
         (conv σ₂₀≡σ₃₀ (subst-⊢≡ (refl ⊢A) (sym-⊢ˢʷ≡∷ ⊢Δ σ₁₊≡σ₂₊))))

opaque

  -- A lemma related to _⇑.

  ⊢ˢʷ≡∷-⇑ :
    ∇ » Η ⊢ A [ σ₁ ] ≡ A [ σ₂ ] →
    ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ∙ A [ σ₁ ] ⊢ˢʷ σ₁ ⇑ ≡ σ₂ ⇑ ∷ Δ ∙ A
  ⊢ˢʷ≡∷-⇑ A[σ₁]≡A[σ₂] =
    P.⊢ˢʷ≡∷-⇑ (wf-⊢≡ A[σ₁]≡A[σ₂] .proj₁) A[σ₁]≡A[σ₂]

opaque

  -- A lemma related to sgSubst.
  --
  -- See also Definition.Typed.Substitution.Primitive.⊢ˢʷ∷-sgSubst,
  -- which is re-exported from this module.

  ⊢ˢʷ≡∷-sgSubst :
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ A →
    ∇ » Δ ⊢ˢʷ sgSubst t₁ ≡ sgSubst t₂ ∷ Δ ∙ A
  ⊢ˢʷ≡∷-sgSubst t₁≡t₂ =
    let _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂ in
    P.⊢ˢʷ≡∷-sgSubst ⊢t₁ ⊢t₂ t₁≡t₂

opaque

  -- A lemma related to _ₛ•ₛ_.

  ⊢ˢ≡∷-ₛ•ₛ :
    ∇ » Φ ⊢ˢʷ σ₁₁ ≡ σ₁₂ ∷ Η →
    ∇ » Η ⊢ˢʷ σ₂₁ ≡ σ₂₂ ∷ Δ →
    ∇ » Φ ⊢ˢʷ σ₁₁ ₛ•ₛ σ₂₁ ≡ σ₁₂ ₛ•ₛ σ₂₂ ∷ Δ
  ⊢ˢ≡∷-ₛ•ₛ {Δ = ε} σ₁₁≡σ₁₂ _ =
    ⊢ˢʷ≡∷ε⇔ .proj₂ (wf-⊢ˢʷ≡∷ σ₁₁≡σ₁₂ .proj₁)
  ⊢ˢ≡∷-ₛ•ₛ {Δ = _ ∙ A} σ₁₁≡σ₁₂ σ₂₁≡σ₂₂ =
    let _ , ⊢σ₁₁ , ⊢σ₁₂                       = wf-⊢ˢʷ≡∷ σ₁₁≡σ₁₂
        σ₂₁₊≡σ₂₂₊ , ⊢σ₂₁₀ , ⊢σ₂₂₀ , σ₂₁₀≡σ₂₂₀ = ⊢ˢʷ≡∷∙⇔ .proj₁ σ₂₁≡σ₂₂
    in
    ⊢ˢʷ≡∷∙⇔ .proj₂
      ( ⊢ˢ≡∷-ₛ•ₛ σ₁₁≡σ₁₂ σ₂₁₊≡σ₂₂₊
      , PE.subst (_⊢_∷_ _ _) (substCompEq A) (subst-⊢∷ ⊢σ₂₁₀ ⊢σ₁₁)
      , PE.subst (_⊢_∷_ _ _) (substCompEq A) (subst-⊢∷ ⊢σ₂₂₀ ⊢σ₁₂)
      , PE.subst (_⊢_≡_∷_ _ _ _) (substCompEq A) (subst-⊢≡∷ σ₂₁₀≡σ₂₂₀ σ₁₁≡σ₁₂)
      )

opaque

  -- A lemma related to _ₛ•ₛ_.

  ⊢ˢ∷-ₛ•ₛ :
    ∇ » Φ ⊢ˢʷ σ₁ ∷ Η →
    ∇ » Η ⊢ˢʷ σ₂ ∷ Δ →
    ∇ » Φ ⊢ˢʷ σ₁ ₛ•ₛ σ₂ ∷ Δ
  ⊢ˢ∷-ₛ•ₛ ⊢σ₁ ⊢σ₂ =
    ⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₂
      (⊢ˢ≡∷-ₛ•ₛ (⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₁ ⊢σ₁) (⊢ˢʷ∷⇔⊢ˢʷ≡∷ .proj₁ ⊢σ₂))

opaque

  -- A lemma related to _[_][_]↑.

  ⊢ˢʷ≡∷-[][]↑ :
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ wk[ k ] A →
    ∇ » Δ ⊢ˢʷ consSubst (wkSubst k idSubst) t₁ ≡
      consSubst (wkSubst k idSubst) t₂ ∷ drop k Δ ∙ A
  ⊢ˢʷ≡∷-[][]↑ t₁≡t₂ =
    let _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂ in
    P.⊢ˢʷ≡∷-[][]↑ ⊢t₁ ⊢t₂ t₁≡t₂

------------------------------------------------------------------------
-- Substitution lemmas

opaque

  -- A substitution lemma for several kinds of judgements.

  subst-⊢≡₀ :
    Γ »∙ A ⊢[ 𝓙 ] → Γ ⊢ t ≡ u ∷ A →
    Γ ⊢[ 𝓙 [ sgSubst t ≡ sgSubst u ]J ]
  subst-⊢≡₀ ⊢𝓙 = subst-⊢≡ ⊢𝓙 ∘→ ⊢ˢʷ≡∷-sgSubst

opaque

  -- A substitution lemma related to Π.

  substTypeΠ : Γ ⊢ Π p , q ▷ A ▹ B → Γ ⊢ t ∷ A → Γ ⊢ B [ t ]₀
  substTypeΠ ⊢ΠAB ⊢t =
    let _ , ⊢B , _ = inversion-ΠΣ ⊢ΠAB in
    subst-⊢₀ ⊢B ⊢t

opaque

  -- A substitution lemma related to _[_][_]↑.

  subst-⊢-↑ :
    ∇ » drop k Δ ∙ A ⊢[ 𝓙 ] → ∇ » Δ ⊢ t ∷ wk[ k ] A →
    ∇ » Δ ⊢[ 𝓙 [ replace₁ k t ]J ]
  subst-⊢-↑ ⊢𝓙 = subst-⊢ ⊢𝓙 ∘→ ⊢ˢʷ∷-[][]↑

opaque

  -- A substitution lemma related to _[_][_]↑.

  subst-⊢≡-↑ :
    ∇ » drop k Δ ∙ A ⊢[ 𝓙 ] → ∇ » Δ ⊢ t ≡ u ∷ wk[ k ] A →
    ∇ » Δ ⊢[ 𝓙 [ replace₁ k t ≡ replace₁ k u ]J ]
  subst-⊢≡-↑ ⊢𝓙 = subst-⊢≡ ⊢𝓙 ∘→ ⊢ˢʷ≡∷-[][]↑

opaque

  -- A substitution lemma related to _[_]↑².

  subst↑²TypeEq-prod :
    Γ »∙ Σ⟨ s ⟩ p , q ▷ A ▹ B ⊢ C ≡ D →
    Γ »∙ A »∙ B ⊢
      C [ prod s p (var x1) (var x0) ]↑² ≡
      D [ prod s p (var x1) (var x0) ]↑²
  subst↑²TypeEq-prod {B} C≡D =
    let ⊢A , ⊢B , ok = inversion-ΠΣ (⊢∙→⊢ (wf C≡D))
        ⊢A′          = wk₁ ⊢A ⊢A
    in
    subst-⊢≡ C≡D $ ⊢ˢʷ≡∷-[][]↑ $ _⊢_≡_∷_.refl $
    prodⱼ
      (wk (liftʷ (step id) (wk₁ ⊢B ⊢A′)) (wk (liftʷ (step id) ⊢A′) ⊢B))
      (var₁ ⊢B)
      (PE.subst (_⊢_∷_ _ _)
         (PE.trans (PE.cong wk1 $ PE.sym $ wkSingleSubstId _) $
          wk-β (U.wk _ B)) $
       var₀ ⊢B)
      ok

opaque

  -- A substitution lemma related to _[_]↑².

  subst↑²Type-prod :
    Γ »∙ Σ⟨ s ⟩ p , q ▷ A ▹ B ⊢ C →
    Γ »∙ A »∙ B ⊢ C [ prod s p (var x1) (var x0) ]↑²
  subst↑²Type-prod = proj₁ ∘→ wf-⊢≡ ∘→ subst↑²TypeEq-prod ∘→ refl

opaque

  -- A substitution lemma related to _[_,_]₁₀.

  subst-⊢₁₀ :
    Γ »∙ A »∙ B ⊢[ 𝓙 ] →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊢[ 𝓙 [ consSubst (sgSubst t) u ]J ]
  subst-⊢₁₀ ⊢𝓙 ⊢t ⊢u = subst-⊢ ⊢𝓙 (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢t) ⊢u)

opaque

  -- A substitution lemma related to _[_,_]₁₀.

  subst-⊢≡₁₀ :
    Γ »∙ A »∙ B ⊢[ 𝓙 ] →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊢[ 𝓙 [ consSubst (sgSubst t₁) u₁ ≡ consSubst (sgSubst t₂) u₂ ]J ]
  subst-⊢≡₁₀ ⊢𝓙 t₁≡t₂ u₁≡u₂ =
    subst-⊢≡ ⊢𝓙 $
    ⊢ˢʷ≡∷∙⇔′ (⊢∙→⊢ (wf ⊢𝓙)) .proj₂
      (⊢ˢʷ≡∷-sgSubst t₁≡t₂ , u₁≡u₂)

opaque

  -- A variant of subst-⊢≡-↑.

  [][]↑-cong :
    ∇ » drop k Δ ∙ A ⊢[ 𝓙 ] →
    ∇ » Δ ⊢ t₁ ≡ t₂ ∷ A [ wkSubst k idSubst ] →
    ∇ » Δ ⊢[ 𝓙 [ replace₁ k t₁ ≡ replace₁ k t₂ ]J ]
  [][]↑-cong {k} B₁≡B₂ =
    subst-⊢≡-↑ B₁≡B₂ ∘→
    PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk[]≡[] k)

opaque

  -- A variant of subst-⊢-↑.

  ⊢[][]↑ :
    ∇ » drop k Δ ∙ A ⊢[ 𝓙 ] →
    ∇ » Δ ⊢ t ∷ A [ wkSubst k idSubst ] →
    ∇ » Δ ⊢[ 𝓙 [ replace₁ k t ]J ]
  ⊢[][]↑ {k} ⊢B =
    subst-⊢-↑ ⊢B ∘→
    PE.subst (_⊢_∷_ _ _) (PE.sym $ wk[]≡[] k)
