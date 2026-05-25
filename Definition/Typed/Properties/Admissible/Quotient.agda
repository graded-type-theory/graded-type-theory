------------------------------------------------------------------------
-- Some admissible rules related to identity types and quotients
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Quotient
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Quotient 𝕄

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Identity R
import Definition.Typed.Properties.Admissible.Quotient.Primitive R as Q
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Weakening R as W hiding (wk)
open import Definition.Typed.Weakening.Combined R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  ∇                                           : DCon _ _
  Δ₁ Δ₂                                       : Con _ _
  Γ Γ₁ Γ₂                                     : Cons _ _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ t t₁ t₂ u v w w₁ w₂ : Term _
  l                                           : Lvl _
  ρ                                           : Wk _ _

------------------------------------------------------------------------
-- Lemmas related to the term former Quot

opaque

  -- An admissible typing rule for Quot.

  ⊢Quot :
    Quot-allowed →
    Γ ⊢ A ∷ U l →
    Quot-rel-Cons Γ A ⊢ B ∷ U (wk[ 2 ]′ l) →
    Γ ⊢ Quot A B ∷ U l
  ⊢Quot ok ⊢A = Quot ok (inversion-U-Level (wf-⊢ ⊢A)) ⊢A

opaque

  -- An admissible equality rule for Quot.

  Quot-cong′ :
    Quot-allowed →
    Γ ⊢ A₁ ≡ A₂ ∷ U l →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk[ 2 ]′ l) →
    Γ ⊢ Quot A₁ B₁ ≡ Quot A₂ B₂ ∷ U l
  Quot-cong′ ok A₁≡A₂ =
    Quot-cong ok (inversion-U-Level (wf-⊢ A₁≡A₂ .proj₁)) A₁≡A₂

------------------------------------------------------------------------
-- Lemmas related to Quot-rel-Con

opaque
  unfolding Quot-rel-Con

  -- A congruence lemma for Quot-rel-Con.

  Quot-rel-Con-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ »⊢ Quot-rel-Con Δ₁ A₁ ≡ Quot-rel-Con Δ₂ A₂
  Quot-rel-Con-cong Δ₁≡Δ₂ A₁≡A₂ =
    let _ , ⊢A₂ = wf-⊢ A₁≡A₂ in
    ⊢≡⇔⊢≡ .proj₂ $
    Q.Quot-rel-Con-cong (⊢≡⇔⊢≡ .proj₁ Δ₁≡Δ₂) (stability Δ₁≡Δ₂ ⊢A₂) A₁≡A₂

opaque

  -- A typing rule for Quot-rel-Con.

  ⊢Quot-rel-Con :
    Γ ⊢ A →
    Γ .defs »⊢ Quot-rel-Con (Γ .vars) A
  ⊢Quot-rel-Con ⊢A =
    wf-⊢≡ˡ (Quot-rel-Con-cong (reflConEq (wf ⊢A)) (refl ⊢A))

opaque

  -- A weakening lemma for Quot-rel-Cons.

  Quot-rel-Cons-⊢ʷᵏ-liftn :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ → Γ₁ ⊢ A →
    Quot-rel-Cons Γ₂ (wk ρ A) ⊢ʷᵏ liftn ρ 2 ∷ Quot-rel-Cons Γ₁ A
  Quot-rel-Cons-⊢ʷᵏ-liftn ⊢ρ ⊢A =
    let ∇₂⊇∇₁ , ⊢ρ = ⊢ʷᵏ⇔ .proj₁ ⊢ρ in
    ⊢ʷᵏ⇔ .proj₂ (∇₂⊇∇₁ , liftʷ-Quot-rel-Con ⊢ρ (defn-wk ∇₂⊇∇₁ ⊢A))

------------------------------------------------------------------------
-- Lemmas related to Resp-Con and Resp-type

opaque

  -- A congruence lemma for Resp-Con.

  Resp-Con-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ » Quot-rel-Con Δ₁ A₁ ⊢ B₁ ≡ B₂ →
    ∇ »⊢ Resp-Con Δ₁ A₁ B₁ ≡ Resp-Con Δ₂ A₂ B₂
  Resp-Con-cong Δ₁≡Δ₂ A₁≡A₂ B₁≡B₂ =
    let ⊢A₁ , ⊢A₂ = wf-⊢ A₁≡A₂
        _   , ⊢B₂ = wf-⊢ B₁≡B₂
    in
    ⊢≡⇔⊢≡ .proj₂ $
    Q.Resp-Con-cong (⊢≡⇔⊢≡ .proj₁ Δ₁≡Δ₂) (stability Δ₁≡Δ₂ ⊢A₂) A₁≡A₂
      (stability (Quot-rel-Con-cong Δ₁≡Δ₂ A₁≡A₂) ⊢B₂) B₁≡B₂

opaque

  -- A typing rule for Resp-Con.
  --
  -- This rule could be made a little more general: there is no need
  -- to require that quotients are allowed.

  ⊢Resp-Con :
    Γ ⊢ Quot A B →
    Γ .defs »⊢ Resp-Con (Γ .vars) A B
  ⊢Resp-Con ⊢Q =
    let _ , ⊢A , ⊢B = inversion-Quot ⊢Q in
    wf-⊢≡ˡ $
    Resp-Con-cong (reflConEq (wf ⊢Q)) (refl ⊢A) (refl ⊢B)

opaque

  -- A congruence lemma for Resp-type.

  Resp-type-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Γ »∙ Quot A₁ B₁ ⊢ C₁ ≡ C₂ →
    Γ »∙ A₁ ⊢ t₁ ≡ t₂ ∷ C₁ [ class (var x0) ]↑ →
    Resp-Cons Γ A₁ B₁ ⊢ Resp-type A₁ B₁ C₁ t₁ ≡ Resp-type A₂ B₂ C₂ t₂
  Resp-type-cong A₁≡A₂ B₁≡B₂ =
    let ⊢B₁ , _ = wf-⊢ B₁≡B₂ in
    Q.Resp-type-cong A₁≡A₂ ⊢B₁ B₁≡B₂

opaque

  -- A typing rule for Resp-type.

  ⊢Resp-type :
    Γ »∙ Quot A B ⊢ C →
    Γ »∙ A ⊢ t ∷ C [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ Resp-type A B C t
  ⊢Resp-type ⊢C ⊢t =
    let ⊢Q          = ⊢∙→⊢ (wf ⊢C)
        _ , ⊢A , ⊢B = inversion-Quot ⊢Q
    in
    wf-⊢ (Resp-type-cong (refl ⊢A) (refl ⊢B) (refl ⊢C) (refl ⊢t)) .proj₁

opaque

  -- A weakening lemma for Resp-Cons.

  Resp-Cons-⊢ʷᵏ-liftn :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ → Quot-rel-Cons Γ₁ A ⊢ B →
    Resp-Cons Γ₂ (wk ρ A) (wk (liftn ρ 2) B) ⊢ʷᵏ liftn ρ 3 ∷
      Resp-Cons Γ₁ A B
  Resp-Cons-⊢ʷᵏ-liftn ⊢ρ ⊢B =
    let ∇₂⊇∇₁ , ⊢ρ = ⊢ʷᵏ⇔ .proj₁ ⊢ρ in
    ⊢ʷᵏ⇔ .proj₂ (∇₂⊇∇₁ , liftʷ-Resp-Con ⊢ρ (defn-wk ∇₂⊇∇₁ ⊢B))

opaque
  unfolding Quot-rel-Con Resp-Con Resp-type

  -- In the presence of equality reflection the existence of a proof
  -- that a function respects the relation can, up to logical
  -- equivalence, be expressed as a judgemental equality.

  ∷Resp-type⇔≡∷ :
    Equality-reflection →
    Γ »∙ Quot A B ⊢ C →
    Γ »∙ A ⊢ t ∷ C [ class (var x0) ]↑ →
    (∃ λ u → Resp-Cons Γ A B ⊢ u ∷ Resp-type A B C t) ⇔
    Resp-Cons Γ A B ⊢ wk[ 2 ]′ t ≡ t [ 3 ][ var x1 ]↑ ∷
      C [ 3 ][ class (var x1) ]↑
  ∷Resp-type⇔≡∷ {Γ} {A} {B} {C} {t} ok ⊢C ⊢t =
    let ⊢Q         = ⊢∙→⊢ (wf ⊢C)
        _ , _ , ⊢B = inversion-Quot ⊢Q
        ⊢ΓAAB      = ⊢Resp-Con ⊢Q
        ⊢Q′        = W.wk (ʷ⊇-drop ⊢ΓAAB) ⊢Q
        ⊢1         = PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ (var₁ ⊢B)

        lemma₁ =
          wk1 B                                              ≡⟨ wk≡subst _ B ⟩

          B [ toSubst (step id) ]                            ≡⟨ (flip substVar-to-subst B λ where
                                                                   x0        → PE.refl
                                                                   (x0 +1)   → PE.refl
                                                                   (_ +1 +1) → PE.refl) ⟩

          B [ consSubst (sgSubst (var x2)) (var x1) ₛ•ₛ
              toSubst (liftn (stepn id 3) 2)
            ]                                                ≡˘⟨ PE.trans (PE.cong _[ _ , _ ]₁₀ (wk≡subst _ B)) $
                                                                 substCompEq B ⟩
          wk (liftn (stepn id 3) 2) B [ var x2 , var x1 ]₁₀  ∎

        lemma₂ =
          wk[ 2 ]′ (C [ class (var x0) ]↑)        ≡⟨ wk[]′[][]↑ 2 C ⟩
          C [ 3 ][ class (var x2) ]↑              ≡˘⟨ [][]↑-[₀⇑] 0 C ⟩
          C [ 4 ][ var x0 ]↑ [ class (var x2) ]₀  ∎

        lemma₃ :
          Resp-Cons Γ A B ⊢
          subst ω (wk[ 3 ]′ (Quot A B)) (C [ 4 ][ var x0 ]↑)
            (class (var x2)) (class (var x1))
            (resp (wk[ 3 ]′ A) (wk (liftn (stepn id 3) 2) B) (var x2)
               (var x1) (var x0))
            (wk[ 2 ]′ t) ≡
          wk[ 2 ]′ t ∷
          C [ 3 ][ class (var x1) ]↑
        lemma₃ =
          PE.subst (_⊢_≡_∷_ _ _ _) ([][]↑-[₀⇑] 0 C) $
          drop-subst ok
            (subst-⊢ ⊢C $ ⊢ˢʷ∷-[][]↑′ $
             PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
             var₀ ⊢Q′)
            (resp ⊢Q′ (var₂′ ⊢B) ⊢1
               (PE.subst (_⊢_∷_ _ _) lemma₁ $
                var₀ ⊢B))
            (PE.subst (_⊢_∷_ _ _) lemma₂ $
             W.wk (ʷ⊇-drop ⊢ΓAAB) ⊢t)
    in
    (λ (_ , ⊢u) →
       equality-reflection′ ok
         (conv ⊢u $
          Id-cong (refl (subst-⊢ ⊢C (⊢ˢʷ∷-[][]↑′ (class ⊢Q′ ⊢1))))
            lemma₃
            (refl $ PE.subst (_⊢_∷_ _ _) ([][]↑-[] 1 C) $
             subst-⊢ ⊢t (⊢ˢʷ∷-[][]↑′ ⊢1)))) ,
    (λ t≡t →
       rfl ,
       rflⱼ′
         (subst ω (wk[ 3 ]′ (Quot A B)) (C [ 4 ][ var x0 ]↑)
            (class (var x2)) (class (var x1))
            (resp (wk[ 3 ]′ A) (wk (liftn (stepn id 3) 2) B)
               (var x2) (var x1) (var x0))
            (wk[ 2 ]′ t)                                      ≡⟨ lemma₃ ⟩⊢

          wk[ 2 ]′ t                                          ≡⟨ t≡t ⟩⊢∎

          t [ 3 ][ var x1 ]↑                                  ∎))

------------------------------------------------------------------------
-- Lemmas related to Is-set-Con and Is-set-type

opaque

  -- A congruence lemma for Is-set-Con.

  Is-set-Con-cong :
    ∇ »⊢ Δ₁ ≡ Δ₂ →
    ∇ » Δ₁ ⊢ A₁ ≡ A₂ →
    ∇ » Quot-rel-Con Δ₁ A₁ ⊢ B₁ ≡ B₂ →
    ∇ » Δ₁ ∙ Quot A₁ B₁ ⊢ C₁ ≡ C₂ →
    ∇ »⊢ Is-set-Con Δ₁ A₁ B₁ C₁ ≡ Is-set-Con Δ₂ A₂ B₂ C₂
  Is-set-Con-cong Δ₁≡Δ₂ A₁≡A₂ B₁≡B₂ C₁≡C₂ =
    let ok , _  = inversion-Quot (⊢∙→⊢ (wf C₁≡C₂))
        _ , ⊢C₂ = wf-⊢ C₁≡C₂
    in
    ⊢≡⇔⊢≡ .proj₂ $
    Q.Is-set-Con-cong (⊢≡⇔⊢≡ .proj₁ Δ₁≡Δ₂) A₁≡A₂ B₁≡B₂
      (stability (Δ₁≡Δ₂ ∙ Quot-cong ok A₁≡A₂ B₁≡B₂) ⊢C₂) C₁≡C₂

opaque

  -- A typing rule for Is-set-Con.

  ⊢Is-set-Con :
    Γ »∙ Quot A B ⊢ C →
    Γ .defs »⊢ Is-set-Con (Γ .vars) A B C
  ⊢Is-set-Con ⊢C =
    let (⊢Γ , _) , (⊢Q , _) = ∙⊢→⊢-<ˢ ⊢C
        _ , ⊢A , ⊢B         = inversion-Quot ⊢Q
    in
    wf-⊢≡ˡ $
    Is-set-Con-cong (reflConEq ⊢Γ) (refl ⊢A) (refl ⊢B) (refl ⊢C)

opaque

  -- A congruence lemma for Is-set-type.

  Is-set-type-cong :
    Γ »∙ Quot A₁ B₁ ⊢ C₁ ≡ C₂ →
    Is-set-Cons Γ A₁ B₁ C₁ ⊢ Is-set-type C₁ ≡ Is-set-type C₂
  Is-set-type-cong C₁≡C₂ =
    let ⊢C₁ , _ = wf-⊢ C₁≡C₂ in
    Q.Is-set-type-cong ⊢C₁ C₁≡C₂

opaque

  -- A typing rule for Is-set-type.

  ⊢Is-set-type :
    Γ »∙ Quot A B ⊢ C →
    Is-set-Cons Γ A B C ⊢ Is-set-type C
  ⊢Is-set-type ⊢C =
    wf-⊢ (Is-set-type-cong (refl ⊢C)) .proj₁

opaque

  -- A weakening lemma for Is-set-Cons.

  Is-set-Cons-⊢ʷᵏ-liftn :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ → Γ₁ »∙ Quot A B ⊢ C →
    Is-set-Cons Γ₂ (wk ρ A) (wk (liftn ρ 2) B) (wk (lift ρ) C) ⊢ʷᵏ
      liftn ρ 5 ∷ Is-set-Cons Γ₁ A B C
  Is-set-Cons-⊢ʷᵏ-liftn ⊢ρ ⊢C =
    let ∇₂⊇∇₁ , ⊢ρ = ⊢ʷᵏ⇔ .proj₁ ⊢ρ in
    ⊢ʷᵏ⇔ .proj₂ (∇₂⊇∇₁ , liftʷ-Is-set-Con ⊢ρ (defn-wk ∇₂⊇∇₁ ⊢C))

------------------------------------------------------------------------
-- Lemmas related to resp

opaque

  -- In the presence of equality reflection a judgemental variant of
  -- resp is admissible.
  --
  -- This rule is basically the same as one presented by Hofmann in
  -- his PhD thesis.

  resp-with-equality-reflection :
    Equality-reflection →
    Γ ⊢ Quot A B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ A →
    Γ ⊢ v ∷ B [ t , u ]₁₀ →
    Γ ⊢ class t ≡ class u ∷ Quot A B
  resp-with-equality-reflection ok ⊢Q ⊢t ⊢u ⊢v =
    equality-reflection′ ok (resp ⊢Q ⊢t ⊢u ⊢v)

opaque

  -- In the presence of equality reflection one can use rfl instead of
  -- resp.

  resp-with-equality-reflection-Id :
    Equality-reflection →
    Γ ⊢ Quot A B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ A →
    Γ ⊢ v ∷ B [ t , u ]₁₀ →
    Γ ⊢ rfl ∷ Id (Quot A B) (class t) (class u)
  resp-with-equality-reflection-Id ok ⊢Q ⊢t ⊢u ⊢v =
    rflⱼ′ (resp-with-equality-reflection ok ⊢Q ⊢t ⊢u ⊢v)

------------------------------------------------------------------------
-- Lemmas related to set

opaque

  -- An admissible typing rule for set.

  ⊢set :
    Γ ⊢ v ∷ Id (Quot A B) t u →
    Γ ⊢ w ∷ Id (Quot A B) t u →
    Γ ⊢ set A B t u v w ∷ Id (Id (Quot A B) t u) v w
  ⊢set ⊢v ⊢w =
    let ⊢Q , ⊢t , ⊢u = inversion-Id (wf-⊢ ⊢v) in
    set ⊢Q ⊢t ⊢u ⊢v ⊢w

------------------------------------------------------------------------
-- Lemmas related to qrec

opaque

  -- A variant of qrec-subst.

  qrec-subst* :
    Γ »∙ Quot A B ⊢ C →
    Γ »∙ A ⊢ t ∷ C [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ u ∷ Resp-type A B C t →
    Is-set-Cons Γ A B C ⊢ v ∷ Is-set-type C →
    Γ ⊢ w₁ ⇒* w₂ ∷ Quot A B →
    Γ ⊢ qrec C t u v w₁ ⇒* qrec C t u v w₂ ∷ C [ w₁ ]₀
  qrec-subst* {C} {t} {u} {v} ⊢C ⊢t ⊢u ⊢v = λ where
    (id ⊢w) →
      id (qrec ⊢C ⊢t ⊢u ⊢v ⊢w)
    (_⇨_ {t = w₁} {t′ = w₂} {u = w₃} w₁⇒w₂ w₂⇒*w₃) →
      qrec C t u v w₁ ∷ C [ w₁ ]₀  ⇒⟨ qrec-subst ⊢C ⊢t ⊢u ⊢v w₁⇒w₂ ⟩∷
                                    ⟨ subst-⊢≡₀ ⊢C (subsetTerm w₁⇒w₂) ⟩⇒
      qrec C t u v w₂ ∷ C [ w₂ ]₀  ⇒*⟨ qrec-subst* ⊢C ⊢t ⊢u ⊢v w₂⇒*w₃ ⟩∎∷
      qrec C t u v w₃              ∎

opaque
  unfolding Is-set-Con Is-set-type ∷Resp-type⇔≡∷

  -- A typing rule for qrec that can be used in the presence of
  -- equality reflection.
  --
  -- This rule is basically the same as one presented by Hofmann in
  -- his PhD thesis.

  qrec-with-equality-reflection :
    Equality-reflection →
    Γ »∙ Quot A B ⊢ C →
    Γ »∙ A ⊢ t ∷ C [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ wk[ 2 ]′ t ≡ t [ 3 ][ var x1 ]↑ ∷
      C [ 3 ][ class (var x1) ]↑ →
    Γ ⊢ u ∷ Quot A B →
    Γ ⊢ qrec C t rfl rfl u ∷ C [ u ]₀
  qrec-with-equality-reflection ok ⊢C ⊢t hyp ⊢u =
    let ⊢Id-2-1 = ⊢∙→⊢ (⊢Is-set-Con ⊢C) in
    qrec ⊢C ⊢t
      (∷Resp-type⇔≡∷ ok ⊢C ⊢t .proj₂ hyp .proj₂)
      (uip-with-equality-reflection-Id ok
         (PE.subst (_⊢_∷_ _ _)
            (PE.cong₃ Id (wk-comp _ _ _) PE.refl PE.refl) $
          var₁′ ⊢Id-2-1)
         (PE.subst (_⊢_∷_ _ _)
            (PE.cong₃ Id (wk-comp _ _ _) PE.refl PE.refl) $
          var₀ ⊢Id-2-1))
      ⊢u
