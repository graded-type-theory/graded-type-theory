------------------------------------------------------------------------
-- Some admissible rules related to identity types and quotients
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Quotient.Primitive
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Quotient 𝕄

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Stability.Primitive R
open import Definition.Typed.Substitution.Primitive.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Weakening R as W hiding (wk)

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  ∇                                         : DCon _ _
  Δ₁ Δ₂                                     : Con _ _
  Γ                                         : Cons _ _
  A₁ A₂ B₁ B₂ C₁ C₂ t₁ t₂ u₁ u₂ v₁ v₂ w₁ w₂ : Term _
  p                                         : M

opaque
  unfolding subst

  -- An equality rule for subst.

  subst-cong :
    Γ ⊢ A₁ →
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ∷ A₁ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ B₁ [ t₁ ]₀ →
    Γ ⊢ subst p A₁ B₁ t₁ u₁ v₁ w₁ ≡ subst p A₂ B₂ t₂ u₂ v₂ w₂ ∷
      B₁ [ u₁ ]₀
  subst-cong {B₁} ⊢A₁ A₁≡A₂ B₁≡B₂ ⊢t₁ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
    PE.subst (_⊢_≡_∷_ _ _ _) (subst-wk B₁) $
    J-cong A₁≡A₂ ⊢t₁ t₁≡t₂
      (wk₁ (Idⱼ (wk₁ ⊢A₁ ⊢A₁) (wk₁ ⊢A₁ ⊢t₁) (var₀ ⊢A₁)) B₁≡B₂)
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ subst-wk B₁) w₁≡w₂) u₁≡u₂
      v₁≡v₂

opaque
  unfolding Quot-rel-Con

  -- A congruence lemma for Quot-rel-Con.

  Quot-rel-Con-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₂ ⊢ A₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ »⊢ Quot-rel-Con Δ₁ A₁ ≡ Quot-rel-Con Δ₂ A₂
  Quot-rel-Con-cong Δ₁≡Δ₂ ⊢A₂ A₁≡A₂ =
    let A₁≡A₂ = stability-⊢ Δ₁≡Δ₂ A₁≡A₂ in
    Δ₁≡Δ₂ ∙⟨ ⊢A₂ ∣ A₁≡A₂ ⟩ ∙⟨ wk₁ ⊢A₂ ⊢A₂ ∣ wk₁ ⊢A₂ A₁≡A₂ ⟩

opaque
  unfolding Resp-Con

  -- A congruence lemma for Resp-Con.

  Resp-Con-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₂ ⊢ A₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ » Quot-rel-Con Δ₂ A₂ ⊢ B₂ →
    ∇ » Quot-rel-Con Δ₁ A₁ ⊢ B₁ ≡ B₂ →
    ∇ »⊢ Resp-Con Δ₁ A₁ B₁ ≡ Resp-Con Δ₂ A₂ B₂
  Resp-Con-cong Δ₁≡Δ₂ ⊢A₂ A₁≡A₂ ⊢B₂ B₁≡B₂ =
    let Eq = Quot-rel-Con-cong Δ₁≡Δ₂ ⊢A₂ A₁≡A₂ in
    Eq ∙⟨ ⊢B₂ ∣ stability-⊢ Eq B₁≡B₂ ⟩

opaque
  unfolding Quot-rel-Con Resp-Con Resp-type

  -- A congruence lemma for Resp-type.

  Resp-type-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Γ »∙ Quot A₁ B₁ ⊢ C₁ ≡ C₂ →
    Γ »∙ A₁ ⊢ t₁ ≡ t₂ ∷ C₁ [ class (var x0) ]↑ →
    Resp-Cons Γ A₁ B₁ ⊢ Resp-type A₁ B₁ C₁ t₁ ≡ Resp-type A₂ B₂ C₂ t₂
  Resp-type-cong {B₁} {C₁} A₁≡A₂ ⊢B₁ B₁≡B₂ C₁≡C₂ t₁≡t₂ =
    let ⊢Q₁          = ⊢∙→⊢ (wf C₁≡C₂)
        ok , ⊢A₁ , _ = inversion-Quot ⊢Q₁
        ΓA₁A₁B₁⊇ΓA₁  = ʷ⊇-drop (∙ ⊢B₁)
        ⊢Q₁′         = W.wk ΓA₁A₁B₁⊇ΓA₁ ⊢Q₁
        ⊢1           = PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ (var₁ ⊢B₁)
        ⊢class-2     = class ⊢Q₁′ (var₂′ ⊢B₁)
    in
    Id-cong
      (subst-⊢≡ C₁≡C₂ $ refl-⊢ˢʷ≡∷ $ ⊢ˢʷ∷-[][]↑ $
       PE.subst (_⊢_∷_ _ _) (PE.sym wk[]≡wk[]′) $
       class ⊢Q₁′
         (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
          var₁ ⊢B₁))
      (PE.subst (_⊢_≡_∷_ _ _ _) ([][]↑-[] 4 C₁) $
       subst-cong ⊢Q₁′
         (W.wk ΓA₁A₁B₁⊇ΓA₁ (Quot-cong ok A₁≡A₂ B₁≡B₂))
         (subst-⊢≡ C₁≡C₂ $ refl-⊢ˢʷ≡∷ $ ⊢ˢʷ∷-[][]↑ $
          PE.subst (_⊢_∷_ _ _)
            (PE.trans (wk-comp _ _ _) (PE.sym wk[]≡wk[]′)) $
          var₀ ⊢Q₁′)
         ⊢class-2
         (refl ⊢class-2)
         (refl (class ⊢Q₁′ ⊢1))
         (resp-cong ok (W.wk (ʷ⊇-drop (∙ ⊢B₁)) A₁≡A₂)
            (W.wk
               (PE.subst₄ _»_∷ʷ_⊇_ PE.refl PE.refl
                  (PE.cong (_∙_ _)
                     (PE.trans (wk-comp _ _ _) $
                      PE.sym (wk-comp _ _ _)))
                  PE.refl $
                 liftⁿʷ {k = 2} (⊇-drop {k = 3})
                   (∙_ $ PE.subst (_⊢_ _) (PE.sym (wk-comp _ _ _)) $
                    W.wk (ʷ⊇-drop (∙ W.wk (ʷ⊇-drop (∙ ⊢B₁)) ⊢A₁)) ⊢A₁))
               B₁≡B₂)
            (refl (var₂′ ⊢B₁)) (refl ⊢1)
            (refl $
             PE.subst (_⊢_∷_ _ _)
               (wk1 B₁                                                    ≡⟨ wk-liftn 0 ⟩

                B₁ [ wkSubst 1 idSubst ]                                  ≡⟨ (flip substVar-to-subst B₁ λ where
                                                                                x0        → PE.refl
                                                                                (x0 +1)   → PE.refl
                                                                                (_ +1 +1) → PE.refl) ⟩
                B₁
                  [ consSubst
                      (consSubst (toSubst (stepn id 3)) (var x2))
                      (var x1)
                  ]                                                       ≡˘⟨ doubleSubstComp B₁ _ _ _ ⟩

                B₁ [ toSubst (stepn id 3) ⇑[ 2 ] ] [ var x2 , var x1 ]₁₀  ≡˘⟨ PE.cong _[ _ , _ ]₁₀ (wk-liftn 2 {t = B₁}) ⟩

                wk (liftn (stepn id 3) 2) B₁ [ var x2 , var x1 ]₁₀        ∎) $
             var₀ ⊢B₁))
         (PE.subst (_⊢_≡_∷_ _ _ _)
            (wk[ 2 ]′ (C₁ [ class (var x0) ]↑)        ≡⟨ wk[]′[][]↑ 2 C₁ ⟩
             C₁ [ 3 ][ wk[ 2 ]′ (class (var x0)) ]↑   ≡˘⟨ [][]↑-[] 4 C₁ ⟩
             C₁ [ 4 ][ var x0 ]↑ [ class (var x2) ]₀  ∎) $
          W.wk (ʷ⊇-drop (∙ ⊢B₁)) t₁≡t₂))
      (PE.subst (_⊢_≡_∷_ _ _ _) ([][]↑-[] 1 C₁) $
       subst-⊢≡ t₁≡t₂ (refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-[][]↑ (var₁ ⊢B₁))))

opaque
  unfolding Is-set-Con

  -- A congruence lemma for Is-set-Con.

  Is-set-Con-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ » Quot-rel-Con Δ₁ A₁ ⊢ B₁ ≡ B₂ →
    ∇ » Δ₂ ∙ Quot A₂ B₂ ⊢ C₂ →
    ∇ » Δ₁ ∙ Quot A₁ B₁ ⊢ C₁ ≡ C₂ →
    ∇ »⊢ Is-set-Con Δ₁ A₁ B₁ C₁ ≡ Is-set-Con Δ₂ A₂ B₂ C₂
  Is-set-Con-cong Δ₁≡Δ₂ A₁≡A₂ B₁≡B₂ ⊢C₂ C₁≡C₂ =
    let ok , _ , ⊢B₂ = inversion-Quot (⊢∙→⊢ (wf ⊢C₂))
        Eq₁          = Δ₁≡Δ₂ ∙⟨ Quot ok ⊢B₂
                              ∣ stability-⊢ Δ₁≡Δ₂
                                  (Quot-cong ok A₁≡A₂ B₁≡B₂)
                              ⟩
        Eq₂          = Eq₁ ∙⟨ ⊢C₂ ∣ stability-⊢ Eq₁ C₁≡C₂ ⟩
        ⊢C₂′         = wk₁ ⊢C₂ ⊢C₂
        Eq₃          = Eq₂ ∙⟨ ⊢C₂′ ∣ wk₁ ⊢C₂ (stability-⊢ Eq₁ C₁≡C₂) ⟩
        ⊢Id-1-0      = Idⱼ (W.wk (ʷ⊇-drop (∙ ⊢C₂′)) ⊢C₂) (var₁′ ⊢C₂′)
                         (PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
                          var₀ ⊢C₂′)
        Eq₄          = Eq₃
                         ∙⟨ ⊢Id-1-0
                          ∣ _⊢_≡_.sym $
                            Id-cong
                              (_⊢_≡_.sym $
                               W.wk (ʷ⊇-drop (∙ ⊢C₂′))
                                 (stability-⊢ Eq₁ C₁≡C₂))
                              (refl (var₁′ ⊢C₂′))
                              (_⊢_≡_∷_.refl $
                               PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
                               var₀ ⊢C₂′)
                          ⟩
    in
    Eq₄
      ∙⟨ Idⱼ (W.wk (ʷ⊇-drop (∙ ⊢Id-1-0)) ⊢C₂) (var₂′ ⊢Id-1-0)
           (PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
            var₁′ ⊢Id-1-0)
       ∣ _⊢_≡_.sym $
         Id-cong
           (sym (W.wk (ʷ⊇-drop (∙ ⊢Id-1-0)) (stability-⊢ Eq₁ C₁≡C₂)))
           (refl (var₂′ ⊢Id-1-0))
           (_⊢_≡_∷_.refl $
            PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
            var₁′ ⊢Id-1-0)
       ⟩

opaque
  unfolding Is-set-Con Is-set-type

  -- A congruence lemma for Is-set-type.

  Is-set-type-cong :
    Γ »∙ Quot A₁ B₁ ⊢ C₁ →
    Γ »∙ Quot A₁ B₁ ⊢ C₁ ≡ C₂ →
    Is-set-Cons Γ A₁ B₁ C₁ ⊢ Is-set-type C₁ ≡ Is-set-type C₂
  Is-set-type-cong ⊢C₁ C₁≡C₂ =
    let ⊢C₁′    = wk₁ ⊢C₁ ⊢C₁
        ⊢Id-1-0 =
          Idⱼ (W.wk (ʷ⊇-drop (∙ ⊢C₁′)) ⊢C₁)
            (var₁′ ⊢C₁′)
            (PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
             var₀ ⊢C₁′)
        ⊢Id-2-1 =
          Idⱼ (W.wk (ʷ⊇-drop (∙ ⊢Id-1-0)) ⊢C₁)
            (var₂′ ⊢Id-1-0)
            (PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
             var₁′ ⊢Id-1-0)
    in
    Id-cong
      (Id-cong (W.wk (ʷ⊇-drop (∙ ⊢Id-2-1)) C₁≡C₂)
         (_⊢_≡_∷_.refl $
          var₃′ ⊢Id-2-1)
         (_⊢_≡_∷_.refl $
          PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
          var₂′ ⊢Id-2-1))
      (_⊢_≡_∷_.refl $
       PE.subst (_⊢_∷_ _ _)
         (PE.cong₃ Id (wk-comp _ _ _) PE.refl PE.refl) $
       var₁′ ⊢Id-2-1)
      (_⊢_≡_∷_.refl $
       PE.subst (_⊢_∷_ _ _)
         (PE.cong₃ Id (wk-comp _ _ _) PE.refl PE.refl) $
       var₀ ⊢Id-2-1)
