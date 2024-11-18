------------------------------------------------------------------------
-- Admissible rules for Lift
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Lift
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
import Definition.Typed.Weakening R as W

open import Definition.Untyped M hiding (lift)
open import Definition.Untyped.Lift 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Unit 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  Γ                         : Con Term _
  A B B₁ B₂ t t₁ t₂ u u₁ u₂ : Term _
  s                         : Strength
  l l₁ l₂                   : Universe-level
  q r                       : M

------------------------------------------------------------------------
-- Definitions related to Lift

-- Lift s l A is allowed if Lift-allowed s holds.

Lift-allowed : Strength → Set a
Lift-allowed s = Σ-allowed s 𝟙 𝟘 × Unit-allowed s

opaque
  unfolding Lift

  -- A typing rule for Lift.

  ⊢Lift :
    Lift-allowed s →
    Γ ⊢ A ∷ U l₁ →
    Γ ⊢ Lift s l₂ A ∷ U (l₁ ⊔ᵘ l₂)
  ⊢Lift (ok₁ , ok₂) ⊢A =
    ΠΣⱼ ⊢A (Unitⱼ (∙ univ ⊢A) ok₂) ok₁

opaque
  unfolding Lift

  -- An inversion lemma for Lift.

  inversion-Lift :
    Γ ⊢ Lift s l A →
    Lift-allowed s × Γ ⊢ A
  inversion-Lift ⊢Lift =
    let ⊢A , ⊢Unit , ok = inversion-ΠΣ ⊢Lift in
    (ok , inversion-Unit ⊢Unit) , ⊢A

------------------------------------------------------------------------
-- A typing rule for lift

opaque
  unfolding Lift lift

  -- A typing rule for lift.

  ⊢lift :
    Lift-allowed s →
    Γ ⊢ t ∷ A →
    Γ ⊢ lift s l t ∷ Lift s l A
  ⊢lift (ok₁ , ok₂) ⊢t =
    let ⊢A = syntacticTerm ⊢t in
    prodⱼ (Unitⱼ (∙ ⊢A) ok₂) ⊢t (starⱼ (wf ⊢A) ok₂) ok₁

------------------------------------------------------------------------
-- Typing rules for liftrec

private opaque
  unfolding Lift lift

  -- A lemma used below.

  liftrec-lemma :
    Γ ∙ Lift s l A ⊢ B₁ ≡ B₂ →
    Γ ∙ A ⊢ t₁ ≡ t₂ ∷ B₁ [ lift s l (var x0) ]↑ →
    Γ ∙ A ∙ Unit s l ⊢
      unitrec⟨ s ⟩ l r q
        (B₁ [ consSubst (wkSubst 3 idSubst)
                (prod s 𝟙 (var x2) (var x0)) ])
        (var x0) (wk1 t₁) ≡
      unitrec⟨ s ⟩ l r q
        (B₂ [ consSubst (wkSubst 3 idSubst)
                (prod s 𝟙 (var x2) (var x0)) ])
        (var x0) (wk1 t₂) ∷
      B₁ [ prod s 𝟙 (var x1) (var x0) ]↑²
  liftrec-lemma {s} {l} {B₁} B₁≡B₂ t₁≡t₂ =
    let (ok₁ , ok₂) , ⊢A = inversion-Lift (⊢∙→⊢ (wfEq B₁≡B₂))
        ⊢Γ               = wf ⊢A
        ⊢Unit            = Unitⱼ (∙ ⊢A) ok₂
        ⊢Unit′           = W.wk₁ ⊢Unit ⊢Unit
    in
    PE.subst (_⊢_≡_∷_ _ _ _)
      (B₁ [ consSubst (wkSubst 3 idSubst)
              (prod s 𝟙 (var x2) (var x0)) ]
          [ var x0 ]₀                         ≡⟨ substCompEq B₁ ⟩

       B₁ [ sgSubst (var x0) ₛ•ₛ
            consSubst (wkSubst 3 idSubst)
              (prod s 𝟙 (var x2) (var x0)) ]  ≡⟨ (flip substVar-to-subst B₁ λ where
                                                    x0     → PE.refl
                                                    (_ +1) → PE.refl) ⟩
       B₁ [ consSubst (wkSubst 2 idSubst)
              (prod s 𝟙 (var x1) (var x0)) ]  ≡⟨⟩

       B₁ [ prod s 𝟙 (var x1) (var x0) ]↑²    ∎) $
    unitrec⟨⟩-cong
      (subst-⊢≡ B₁≡B₂ $ refl-⊢ˢʷ≡∷ $ ⊢ˢʷ∷-[][]↑ $
       prodⱼ
         (Unitⱼ
            (∙ (PE.subst (_⊢_ _) (PE.sym wk[]≡wk[]′) $
                W.wk (W.stepʷ (W.step (W.step W.id)) ⊢Unit′) ⊢A))
            ok₂)
         (var₂ ⊢Unit′)
         (var₀ ⊢Unit′) ok₁)
      (refl (var₀ ⊢Unit)) $
    PE.subst (_⊢_≡_∷_ _ _ _)
      (wk1 (B₁ [ lift s l (var x0) ]↑)                                    ≡⟨⟩

       (wk1 $
        B₁ [ consSubst (wk1Subst idSubst)
               (prod s 𝟙 (var x0) (star s l)) ])                          ≡˘⟨ wk1Subst-wk1 B₁ ⟩

       B₁ [ wk1Subst $ consSubst (wk1Subst idSubst) $
            prod s 𝟙 (var x0) (star s l) ]                                ≡⟨ (flip substVar-to-subst B₁ λ where
                                                                                x0     → PE.refl
                                                                                (_ +1) → PE.refl) ⟩
       B₁ [ sgSubst (star s l) ₛ•ₛ
            consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]  ≡˘⟨ substCompEq B₁ ⟩

       B₁ [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
          [ star s l ]₀                                                   ∎) $
    W.wkEqTerm₁ ⊢Unit t₁≡t₂

opaque
  unfolding Lift liftrec

  -- An equality rule for liftrec.

  liftrec-cong :
    Γ ∙ Lift s l A ⊢ B₁ ≡ B₂ →
    Γ ∙ A ⊢ t₁ ≡ t₂ ∷ B₁ [ lift s l (var x0) ]↑ →
    Γ ⊢ u₁ ≡ u₂ ∷ Lift s l A →
    Γ ⊢ liftrec r q s l B₁ t₁ u₁ ≡ liftrec r q s l B₂ t₂ u₂ ∷ B₁ [ u₁ ]₀
  liftrec-cong B₁≡B₂ t₁≡t₂ u₁≡u₂ =
    prodrec⟨⟩-cong B₁≡B₂ u₁≡u₂ $
    liftrec-lemma B₁≡B₂ t₁≡t₂

opaque

  -- A typing rule for liftrec.

  ⊢liftrec :
    Γ ∙ Lift s l A ⊢ B →
    Γ ∙ A ⊢ t ∷ B [ lift s l (var x0) ]↑ →
    Γ ⊢ u ∷ Lift s l A →
    Γ ⊢ liftrec r q s l B t u ∷ B [ u ]₀
  ⊢liftrec ⊢B ⊢t ⊢u =
    syntacticEqTerm
      (liftrec-cong (refl ⊢B) (refl ⊢t) (refl ⊢u))
      .proj₂ .proj₁

opaque
  unfolding Lift lift liftrec

  -- An equality rule for liftrec.

  liftrec-β :
    Γ ∙ Lift s l A ⊢ B →
    Γ ∙ A ⊢ t ∷ B [ lift s l (var x0) ]↑ →
    Γ ⊢ u ∷ A →
    Γ ⊢ liftrec r q s l B t (lift s l u) ≡ t [ u ]₀ ∷ B [ lift s l u ]₀
  liftrec-β {s} {l} {B} {t} {u} {r} {q} ⊢B ⊢t ⊢u =
    let ⊢Γ               = wfTerm ⊢u
        (ok₁ , ok₂) , ⊢A = inversion-Lift (⊢∙→⊢ (wf ⊢B))
        ⊢Unit            = Unitⱼ ⊢Γ ok₂
    in

    liftrec r q s l B t (lift s l u)                                      ≡⟨⟩⊢

    prodrec⟨ s ⟩ r 𝟙 q B (prod s 𝟙 u (star s l))
      (unitrec⟨ s ⟩ l r q
         (B [ consSubst (wkSubst 3 idSubst)
                (prod s 𝟙 (var x2) (var x0)) ])
         (var x0) (wk1 t))                                                ≡⟨ prodrec⟨⟩-β (λ _ → ⊢B) ⊢u (starⱼ ⊢Γ ok₂)
                                                                               (syntacticEqTerm
                                                                                  (liftrec-lemma (refl ⊢B) (refl ⊢t))
                                                                                  .proj₂ .proj₁)
                                                                               (λ _ → ok₁) ⟩⊢
    unitrec⟨ s ⟩ l r q
      (B [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ])
      (var x0) (wk1 t) [ u , star s l ]₁₀ ∷
      B [ lift s l u ]₀                                                   ≡⟨ unitrec⟨⟩-[] ⟩⊢∷≡
                                                                          ˘⟨ lemma₂ ⟩≡≡
    unitrec⟨ s ⟩ l r q
      (B [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
         [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ])
      (star s l) (wk1 t [ u , star s l ]₁₀) ∷
      B [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
        [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ]
        [ star s l ]₀                                                     ≡⟨ unitrec⟨⟩-β-≡
                                                                               (λ _ →
                                                                                  PE.subst (_⊢_ _) (PE.sym lemma₁) $
                                                                                  subst↑Type ⊢B $
                                                                                  prodⱼ (W.wk₁ (W.wk₁ ⊢Unit ⊢A) (W.wk₁ ⊢Unit ⊢Unit))
                                                                                    (W.wkTerm₁ ⊢Unit ⊢u) (var₀ ⊢Unit) ok₁) $
                                                                             PE.subst₂ (_⊢_∷_ _) (PE.sym lemma₄) (PE.sym lemma₃) $
                                                                             substTerm ⊢t ⊢u ⟩⊢∷∎≡

    wk1 t [ u , star s l ]₁₀                                              ≡⟨ lemma₄ ⟩

    t [ u ]₀                                                              ∎
    where
    lemma₁ :
      B [ consSubst (wkSubst 3 idSubst)
            (prod s 𝟙 (var x2) (var x0)) ]
        [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ] PE.≡
      B [ prod s 𝟙 (wk1 u) (var x0) ]↑
    lemma₁ =
      B [ consSubst (wkSubst 3 idSubst)
            (prod s 𝟙 (var x2) (var x0)) ]
        [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ]      ≡⟨ substCompEq B ⟩

      B [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ₛ•ₛ
          consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]  ≡⟨ (flip substVar-to-subst B λ where
                                                                              x0     → PE.refl
                                                                              (_ +1) → PE.refl) ⟩
      B [ prod s 𝟙 (wk1 u) (var x0) ]↑                                  ∎

    lemma₂ :
      B [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
        [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ]
        [ star s l ]₀ PE.≡
      B [ lift s l u ]₀
    lemma₂ =
      B [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
        [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ]
        [ star s l ]₀                                                   ≡⟨ PE.cong _[ _ ]₀ lemma₁ ⟩

      B [ prod s 𝟙 (wk1 u) (var x0) ]↑ [ star s l ]₀                    ≡⟨ []↑-[]₀ B ⟩

      B [ prod s 𝟙 (wk1 u) (var x0) [ star s l ]₀ ]₀                    ≡⟨⟩

      B [ prod s 𝟙 (wk1 u [ star s l ]₀) (star s l) ]₀                  ≡⟨ PE.cong (B [_]₀) (PE.cong₂ (prod s 𝟙) (wk1-sgSubst _ _) PE.refl) ⟩

      B [ prod s 𝟙 u (star s l) ]₀                                      ≡⟨⟩

      B [ lift s l u ]₀                                                 ∎

    lemma₃ :
      B [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
        [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ]
        [ star s l ]₀ PE.≡
      B [ lift s l (var x0) ]↑ [ u ]₀
    lemma₃ =
      B [ consSubst (wkSubst 3 idSubst) (prod s 𝟙 (var x2) (var x0)) ]
        [ liftSubst (consSubst (consSubst idSubst u) (star s l)) ]
        [ star s l ]₀                                                   ≡⟨ lemma₂ ⟩

      B [ lift s l u ]₀                                                 ≡⟨⟩

      B [ lift s l (var x0) [ u ]₀ ]₀                                   ≡˘⟨ []↑-[]₀ B ⟩

      B [ lift s l (var x0) ]↑ [ u ]₀                                   ∎

    lemma₄ : wk1 t [ u , star s l ]₁₀ PE.≡ t [ u ]₀
    lemma₄ =
      wk1 t [ u , star s l ]₁₀  ≡⟨ step-consSubst t ⟩
      wk id t [ u ]₀            ≡⟨ PE.cong _[ _ ]₀ $ wk-id t ⟩
      t [ u ]₀                  ∎
