------------------------------------------------------------------------
-- Admissible rules related to Π and Σ
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Pi-Sigma
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Pi-Sigma M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.Lift R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n                                   : Nat
  Γ                                   : Cons _ _
  A A₁ A₂ B B₁ B₂ C E F G H a f g t u : Term n
  l l₁ l₁₁ l₁₂ l₂ l₂₁ l₂₂             : Lvl _
  p p′ p₁ p₂ p₃ q q₁ q₂ q₃            : M
  s                                   : Strength
  b                                   : BinderMode

------------------------------------------------------------------------
-- Simple variants of typing, equality and reduction rules

opaque

  ΠΣⱼ′ : Γ ⊢ A ∷ U l
       → Γ »∙ A ⊢ B ∷ U (wk1 l)
       → ΠΣ-allowed b p q
       → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U l
  ΠΣⱼ′ ⊢A ⊢B ok =
    let ⊢l = inversion-U-Level (wf-⊢∷ ⊢A) in
    ΠΣⱼ ⊢l ⊢A ⊢B ok

opaque

  ΠΣ-cong′ : Γ ⊢ F ≡ H ∷ U l
           → Γ »∙ F ⊢ G ≡ E ∷ U (wk1 l)
           → ΠΣ-allowed b p q
           → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡ ΠΣ⟨ b ⟩ p , q ▷ H ▹ E ∷ U l
  ΠΣ-cong′ F≡H G≡E ok =
    let ⊢l = inversion-U-Level (wf-⊢≡∷ F≡H .proj₁) in
    ΠΣ-cong ⊢l F≡H G≡E ok

------------------------------------------------------------------------
-- Some properties related to ΠΣʰ

opaque
  unfolding ΠΣʰ

  -- An admissible type equality rule for ΠΣʰ.

  ΠΣʰ-cong-⊢′ :
    ΠΣ-allowed b p q →
    Γ »∙ Lift l₂₁ A₁ ⊢ wk1 l₁₁ ≡ wk1 l₁₂ ∷Level →
    Γ ⊢ l₂₁ ≡ l₂₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ ΠΣʰ b p q l₁₁ l₂₁ A₁ B₁ ≡ ΠΣʰ b p q l₁₂ l₂₂ A₂ B₂
  ΠΣʰ-cong-⊢′ ok l₁₁≡l₁₂ l₂₁≡l₂₂ A₁≡A₂ B₁≡B₂ =
    let Lift≡Lift = Lift-cong l₂₁≡l₂₂ A₁≡A₂ in
    ΠΣ-cong Lift≡Lift
      (Lift-cong l₁₁≡l₁₂ (lower₀TypeEq (wf-⊢≡∷L l₂₁≡l₂₂ .proj₁) B₁≡B₂))
      ok

opaque

  -- An admissible type equality rule for ΠΣʰ.

  ΠΣʰ-cong-⊢ :
    ΠΣ-allowed b p q →
    Γ ⊢ l₁₁ ≡ l₁₂ ∷Level →
    Γ ⊢ l₂₁ ≡ l₂₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ ΠΣʰ b p q l₁₁ l₂₁ A₁ B₁ ≡ ΠΣʰ b p q l₁₂ l₂₂ A₂ B₂
  ΠΣʰ-cong-⊢ ok l₁₁≡l₁₂ l₂₁≡l₂₂ A₁≡A₂ =
    let ⊢l₂₁ , _ = wf-⊢≡∷L l₂₁≡l₂₂
        ⊢A₁  , _ = wf-⊢≡ A₁≡A₂
    in
    ΠΣʰ-cong-⊢′ ok (wkEqLevel₁ (Liftⱼ ⊢l₂₁ ⊢A₁) l₁₁≡l₁₂) l₂₁≡l₂₂ A₁≡A₂

opaque

  -- An admissible type well-formedness rule for ΠΣʰ.

  ⊢ΠΣʰ′ :
    ΠΣ-allowed b p q →
    Γ »∙ Lift l₂ A ⊢ wk1 l₁ ∷Level →
    Γ »∙ A ⊢ B →
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B
  ⊢ΠΣʰ′ ok ⊢l₁ ⊢B =
    let ⊢l₂ , _ = inversion-Lift (⊢∙→⊢ (wf ⊢l₁)) in
    wf-⊢≡
      (ΠΣʰ-cong-⊢′ ok (refl-⊢≡∷L ⊢l₁) (refl-⊢≡∷L ⊢l₂)
         (refl (⊢∙→⊢ (wf ⊢B))) (refl ⊢B))
      .proj₁

opaque

  -- An admissible type well-formedness rule for ΠΣʰ.

  ⊢ΠΣʰ :
    ΠΣ-allowed b p q →
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ »∙ A ⊢ B →
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B
  ⊢ΠΣʰ ok ⊢l₁ ⊢l₂ ⊢B =
    wf-⊢≡
      (ΠΣʰ-cong-⊢ ok (refl-⊢≡∷L ⊢l₁) (refl-⊢≡∷L ⊢l₂)
         (refl (⊢∙→⊢ (wf ⊢B))) (refl ⊢B))
      .proj₁

opaque
  unfolding ΠΣʰ lower₀

  -- An admissible term equality rule for ΠΣʰ.

  ΠΣʰ-cong-⊢∷′ :
    ΠΣ-allowed b p q →
    Γ »∙ Lift l₂₁ A₁ ⊢ wk1 l₁₁ ≡ wk1 l₁₂ ∷Level →
    Γ ⊢ l₂₁ ≡ l₂₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁₁ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk1 l₂₁) →
    Γ ⊢ ΠΣʰ b p q l₁₁ l₂₁ A₁ B₁ ≡ ΠΣʰ b p q l₁₂ l₂₂ A₂ B₂ ∷
      U (l₁₁ supᵘₗ l₂₁)
  ΠΣʰ-cong-⊢∷′ ok l₁₁≡l₁₂ l₂₁≡l₂₂ A₁≡A₂ B₁≡B₂ =
    let ⊢l₂₁ , _ = wf-⊢≡∷L l₂₁≡l₂₂ in
    ΠΣ-cong′
      (Lift-cong′ l₂₁≡l₂₂ A₁≡A₂)
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.cong U $ PE.sym wk-supᵘₗ) $
       Lift-cong-comm l₁₁≡l₁₂
         (PE.subst (_⊢_≡_∷_ _ _ _) wk[]′-[]↑ $
          lower₀TermEq ⊢l₂₁ B₁≡B₂))
      ok

opaque

  -- An admissible term equality rule for ΠΣʰ.

  ΠΣʰ-cong-⊢∷ :
    ΠΣ-allowed b p q →
    Γ ⊢ l₁₁ ≡ l₁₂ ∷Level →
    Γ ⊢ l₂₁ ≡ l₂₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁₁ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk1 l₂₁) →
    Γ ⊢ ΠΣʰ b p q l₁₁ l₂₁ A₁ B₁ ≡ ΠΣʰ b p q l₁₂ l₂₂ A₂ B₂ ∷
      U (l₁₁ supᵘₗ l₂₁)
  ΠΣʰ-cong-⊢∷ ok l₁₁≡l₁₂ l₂₁≡l₂₂ A₁≡A₂ =
    let ⊢l₂₁ , _    = wf-⊢≡∷L l₂₁≡l₂₂
        _ , ⊢A₁ , _ = wf-⊢≡∷ A₁≡A₂
    in
    ΠΣʰ-cong-⊢∷′ ok (wkEqLevel₁ (Liftⱼ ⊢l₂₁ (univ ⊢A₁)) l₁₁≡l₁₂) l₂₁≡l₂₂
      A₁≡A₂

opaque

  -- An admissible typing rule for ΠΣʰ.

  ⊢ΠΣʰ∷ :
    ΠΣ-allowed b p q →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ A ∷ U l₁ →
    Γ »∙ A ⊢ B ∷ U (wk1 l₂) →
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B ∷ U (l₁ supᵘₗ l₂)
  ⊢ΠΣʰ∷ ok ⊢l₂ ⊢A ⊢B =
    wf-⊢≡∷
      (ΠΣʰ-cong-⊢∷ ok (refl-⊢≡∷L (inversion-U-Level (wf-⊢∷ ⊢A)))
         (refl-⊢≡∷L ⊢l₂) (refl ⊢A) (refl ⊢B))
      .proj₂ .proj₁

opaque
  unfolding ΠΣʰ lower₀

  -- An alternative equality rule for ΠΣʰ.

  ΠΣʰ-cong-≤ₗ′ :
    ΠΣ-allowed b p q →
    Γ ⊢ l₁₁ ≤ₗ l₁ ∷Level →
    Γ »∙ Lift l₁ A₁ ⊢ wk1 l₁₂ ≤ₗ wk1 l₁ ∷Level →
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁₁ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk1 l₁₂) →
    Γ ⊢ ΠΣʰ b p q l₁ l₁ A₁ B₁ ≡ ΠΣʰ b p q l₂ l₂ A₂ B₂ ∷ U l₁
  ΠΣʰ-cong-≤ₗ′ ok l₁₁≤l₁ l₁₂≤l₁ l₁≡l₂ A₁≡A₂ B₁≡B₂ =
    let _ , ⊢l₁       = wf-⊢≤ₗ∷L l₁₁≤l₁
        Lift≡Lift     = Lift-cong-≤ₗ l₁₁≤l₁ l₁≡l₂ A₁≡A₂
        _ , ⊢Lift , _ = wf-⊢≡∷ Lift≡Lift
    in
    ΠΣ-cong ⊢l₁ Lift≡Lift
      (Lift-cong-≤ₗ
         (PE.subst (flip (_⊢_≤ₗ_∷Level _) _) (PE.sym (wk1-[][]↑ 1))
            l₁₂≤l₁)
         (wkEqLevel (stepʷ id (univ ⊢Lift)) l₁≡l₂)
         (lower₀TermEq ⊢l₁ B₁≡B₂))
      ok

opaque

  -- An alternative equality rule for ΠΣʰ.

  ΠΣʰ-cong-≤ₗ :
    ΠΣ-allowed b p q →
    Γ ⊢ l₁₁ ≤ₗ l₁ ∷Level →
    Γ ⊢ l₁₂ ≤ₗ l₁ ∷Level →
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁₁ →
    Γ »∙ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk1 l₁₂) →
    Γ ⊢ ΠΣʰ b p q l₁ l₁ A₁ B₁ ≡ ΠΣʰ b p q l₂ l₂ A₂ B₂ ∷ U l₁
  ΠΣʰ-cong-≤ₗ ok l₁₁≤l₁ l₁₂≤l₁ l₁≡l₂ A₁≡A₂ B₁≡B₂ =
    let _ , ⊢l₁       = wf-⊢≤ₗ∷L l₁₁≤l₁
        Lift≡Lift     = Lift-cong-≤ₗ l₁₁≤l₁ l₁≡l₂ A₁≡A₂
        _ , ⊢Lift , _ = wf-⊢≡∷ Lift≡Lift
    in
    ΠΣʰ-cong-≤ₗ′ ok l₁₁≤l₁ (wk-≤ₗ∷L (stepʷ id (univ ⊢Lift)) l₁₂≤l₁)
      l₁≡l₂ A₁≡A₂ B₁≡B₂

opaque

  -- An alternative typing rule for ΠΣʰ.

  ⊢ΠΣʰ∷-≤ₗ′ :
    ΠΣ-allowed b p q →
    Γ ⊢ l₁ ≤ₗ l ∷Level →
    Γ »∙ Lift l A ⊢ wk1 l₂ ≤ₗ wk1 l ∷Level →
    Γ ⊢ A ∷ U l₁ →
    Γ »∙ A ⊢ B ∷ U (wk1 l₂) →
    Γ ⊢ ΠΣʰ b p q l l A B ∷ U l
  ⊢ΠΣʰ∷-≤ₗ′ ok l₁≤l l₂≤l ⊢A ⊢B =
    let _ , ⊢l = wf-⊢≤ₗ∷L l₁≤l in
    wf-⊢≡∷
      (ΠΣʰ-cong-≤ₗ′ ok l₁≤l l₂≤l (refl-⊢≡∷L ⊢l) (refl ⊢A) (refl ⊢B))
      .proj₂ .proj₁

opaque

  -- An alternative typing rule for ΠΣʰ.

  ⊢ΠΣʰ∷-≤ₗ :
    ΠΣ-allowed b p q →
    Γ ⊢ l₁ ≤ₗ l ∷Level →
    Γ ⊢ l₂ ≤ₗ l ∷Level →
    Γ ⊢ A ∷ U l₁ →
    Γ »∙ A ⊢ B ∷ U (wk1 l₂) →
    Γ ⊢ ΠΣʰ b p q l l A B ∷ U l
  ⊢ΠΣʰ∷-≤ₗ ok l₁≤l l₂≤l ⊢A ⊢B =
    let _ , ⊢l = wf-⊢≤ₗ∷L l₁≤l in
    wf-⊢≡∷ (ΠΣʰ-cong-≤ₗ ok l₁≤l l₂≤l (refl-⊢≡∷L ⊢l) (refl ⊢A) (refl ⊢B))
      .proj₂ .proj₁

private opaque
  unfolding lower₀

  -- A kind of inversion lemma for lower₀.

  inversion-lower₀-⊢∷ :
    Γ »∙ Lift l A ⊢ lower₀ t ∷ B →
    Γ ⊢ l ∷Level ×
    Γ »∙ A ⊢ t [ lower (lift (var x0)) ]↑ ∷ B [ lift (var x0) ]↑
  inversion-lower₀-⊢∷ {t} ⊢lower₀-t =
    let ⊢l , ⊢A = inversion-Lift (⊢∙→⊢ (wf ⊢lower₀-t)) in
    ⊢l ,
    PE.subst (flip (_⊢_∷_ _) _) ([][]↑-[↑⇑] 0 t)
      (subst-⊢∷ ⊢lower₀-t $
       ⊢ˢʷ∷-[][]↑ (liftⱼ′ (wkLevel₁ ⊢A ⊢l) (var₀ ⊢A)))

private opaque
  unfolding lower₀

  -- A kind of inversion lemma for lower₀.

  inversion-lower₀-⊢ :
    Γ »∙ Lift l A ⊢ lower₀ B →
    Γ ⊢ l ∷Level ×
    Γ »∙ A ⊢ B [ lower (lift (var x0)) ]↑
  inversion-lower₀-⊢ {B} ⊢lower₀-B =
    let ⊢l , ⊢A = inversion-Lift (⊢∙→⊢ (wf ⊢lower₀-B)) in
    ⊢l ,
    PE.subst (_⊢_ _) ([][]↑-[↑⇑] 0 B)
      (subst-⊢ ⊢lower₀-B $
       ⊢ˢʷ∷-[][]↑ (liftⱼ′ (wkLevel₁ ⊢A ⊢l) (var₀ ⊢A)))

opaque
  unfolding ΠΣʰ lower₀

  -- A limited inversion lemma for ΠΣʰ.

  inversion-ΠΣʰ-⊢∷ :
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B ∷ C →
    Γ »∙ A ⊢ wk1 l₁ ∷Level ×
    Γ ⊢ l₂ ∷Level ×
    (∃ λ l → Γ ⊢ A ∷ U l) ×
    (∃ λ l → Γ »∙ A ⊢ B [ lower (lift (var x0)) ]↑ ∷ U l) ×
    (∃ λ l → Γ ⊢ C ≡ U l) ×
    ΠΣ-allowed b p q
  inversion-ΠΣʰ-⊢∷ {l₁} {l₂} {B} {C} ⊢ΠΣ =
    let _ , _ , ⊢Lift-A , ⊢Lift-B , C≡U , ok = inversion-ΠΣ-U ⊢ΠΣ
        _ , ⊢l₂ , ⊢A , U[l₃]≡U[l₄⊔l₂]        = inversion-Lift∷ ⊢Lift-A
        _ , ⊢l₁ , ⊢B , U[l₃]≡U[l₅⊔l₁]        = inversion-Lift∷ ⊢Lift-B
        ⊢A′                                  = univ ⊢A
        ⊢σ                                   =
          ⊢ˢʷ∷-[][]↑ (liftⱼ′ (wkLevel₁ ⊢A′ ⊢l₂) (var₀ ⊢A′))
    in
    PE.subst (_⊢_∷Level _) (wk1-[][]↑ 1) (subst-⊢∷L ⊢l₁ ⊢σ) ,
    ⊢l₂ , (_ , ⊢A) , (_ , inversion-lower₀-⊢∷ {t = B} ⊢B .proj₂) ,
    (_ , C≡U) , ok

opaque
  unfolding ΠΣʰ lower₀

  -- A limited inversion lemma for ΠΣʰ.

  inversion-ΠΣʰ-⊢ :
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B →
    Γ »∙ A ⊢ wk1 l₁ ∷Level ×
    Γ ⊢ l₂ ∷Level ×
    Γ ⊢ A ×
    Γ »∙ A ⊢ B [ lower (lift (var x0)) ]↑ ×
    ΠΣ-allowed b p q
  inversion-ΠΣʰ-⊢ {B} ⊢ΠΣ =
    let ⊢Lift-A , ⊢Lift-B , ok = inversion-ΠΣ ⊢ΠΣ
        ⊢l₂ , ⊢A               = inversion-Lift ⊢Lift-A
        ⊢l₁ , ⊢B               = inversion-Lift ⊢Lift-B
        ⊢σ                     =
          ⊢ˢʷ∷-[][]↑ (liftⱼ′ (wkLevel₁ ⊢A ⊢l₂) (var₀ ⊢A))
    in
    PE.subst (_⊢_∷Level _) (wk1-[][]↑ 1) (subst-⊢∷L ⊢l₁ ⊢σ) ,
    ⊢l₂ , ⊢A , inversion-lower₀-⊢ {B = B} ⊢B .proj₂ ,
    ok
