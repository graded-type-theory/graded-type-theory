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

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R
open import Definition.Typed.Properties.Admissible.Lift R
import Definition.Typed.Properties.Admissible.Pi-Sigma.Primitive R as PP
open import Definition.Typed.Properties.Admissible.Var R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n     : Nat
  Γ     : Con Term n
  A A₁ A₂ B B₁ B₂ C E F G H a f g l l₁ l₁₁ l₁₂ l₂ l₂₁ l₂₂ t u : Term n
  p p′ q : M
  s     : Strength
  b     : BinderMode

------------------------------------------------------------------------
-- Simple variants of typing, equality and reduction rules

opaque

  ΠΣⱼ′ : Γ     ⊢ A ∷ U l
       → Γ ∙ A ⊢ B ∷ U (wk1 l)
       → ΠΣ-allowed b p q
       → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U l
  ΠΣⱼ′ ⊢A ⊢B ok =
    let _ , ⊢l = inversion-U-Level (wf-⊢∷ ⊢A) in
    ΠΣⱼ ⊢l ⊢A ⊢B ok

opaque

  ΠΣ-cong′ : Γ     ⊢ F ≡ H ∷ U l
           → Γ ∙ F ⊢ G ≡ E ∷ U (wk1 l)
           → ΠΣ-allowed b p q
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡
                     ΠΣ⟨ b ⟩ p , q ▷ H ▹ E ∷ U l
  ΠΣ-cong′ F≡H G≡E ok =
    let _ , ⊢l = inversion-U-Level (wf-⊢≡∷ F≡H .proj₁) in
    ΠΣ-cong ⊢l F≡H G≡E ok

------------------------------------------------------------------------
-- Some properties related to ΠΣʰ

opaque

  -- An admissible typing rule for ΠΣʰ.

  ΠΣʰⱼ :
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ A ∷ U l₁ →
    Γ ∙ A ⊢ B ∷ U (wk1 l₂) →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B ∷ U (l₁ supᵘₗ l₂)
  ΠΣʰⱼ ⊢l₂ ⊢A =
    let _ , ⊢l₁ = inversion-U-Level (wf-⊢∷ ⊢A) in
    PP.ΠΣʰⱼ ⊢l₁ ⊢l₂ ⊢A

opaque

  -- An admissible equality rule for ΠΣʰ.

  ΠΣʰ-cong :
    Γ ⊢ l₁₁ ≡ l₁₂ ∷Level →
    Γ ⊢ l₂₁ ≡ l₂₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁₁ →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk1 l₂₁) →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣʰ b p q l₁₁ l₂₁ A₁ B₁ ≡ ΠΣʰ b p q l₁₂ l₂₂ A₂ B₂ ∷
      U (l₁₁ supᵘₗ l₂₁)
  ΠΣʰ-cong l₁₁≡l₁₂ l₂₁≡l₂₂ A₁≡A₂ =
    let ⊢l₁₁ , _    = wf-⊢≡∷L l₁₁≡l₁₂
        ⊢l₂₁ , _    = wf-⊢≡∷L l₂₁≡l₂₂
        _ , ⊢A₁ , _ = wf-⊢≡∷ A₁≡A₂
    in
    PP.ΠΣʰ-cong ⊢l₁₁ ⊢l₂₁ l₁₁≡l₁₂ l₂₁≡l₂₂ (univ ⊢A₁) A₁≡A₂

private opaque
  unfolding lower₀

  -- A kind of inversion lemma for lower₀.

  inversion-lower₀-⊢∷ :
    Γ ∙ Lift l A ⊢ lower₀ t ∷ B →
    Γ ⊢ l ∷Level ×
    Γ ∙ A ⊢ t [ lower (lift (var x0)) ]↑ ∷ B [ lift (var x0) ]↑
  inversion-lower₀-⊢∷ {t} ⊢lower₀-t =
    let ⊢l , ⊢A = inversion-Lift (⊢∙→⊢ (wfTerm ⊢lower₀-t)) in
    ⊢l ,
    PE.subst (flip (_⊢_∷_ _) _) ([][]↑-[↑⇑] 0 t)
      (subst-⊢∷ ⊢lower₀-t $
       ⊢ˢʷ∷-[][]↑ (liftⱼ′ (wkLevel₁ ⊢A ⊢l) (var₀ ⊢A)))
    where
    open import Definition.Typed.Properties.Well-formed R

private opaque
  unfolding lower₀

  -- A kind of inversion lemma for lower₀.

  inversion-lower₀-⊢ :
    Γ ∙ Lift l A ⊢ lower₀ B →
    Γ ⊢ l ∷Level ×
    Γ ∙ A ⊢ B [ lower (lift (var x0)) ]↑
  inversion-lower₀-⊢ {B} ⊢lower₀-B =
    let ⊢l , ⊢A = inversion-Lift (⊢∙→⊢ (wf ⊢lower₀-B)) in
    ⊢l ,
    PE.subst (_⊢_ _) ([][]↑-[↑⇑] 0 B)
      (subst-⊢ ⊢lower₀-B $
       ⊢ˢʷ∷-[][]↑ (liftⱼ′ (wkLevel₁ ⊢A ⊢l) (var₀ ⊢A)))
    where
    open import Definition.Typed.Properties.Well-formed R

opaque
  unfolding ΠΣʰ lower₀

  -- A limited inversion lemma for ΠΣʰ.

  inversion-ΠΣʰ-⊢∷ :
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B ∷ C →
    Γ ∙ A ⊢ wk1 l₁ ∷Level ×
    Γ ⊢ l₂ ∷Level ×
    (∃ λ l → Γ ⊢ A ∷ U l) ×
    (∃ λ l → Γ ∙ A ⊢ B [ lower (lift (var x0)) ]↑ ∷ U l) ×
    (∃ λ l → Γ ⊢ C ≡ U l) ×
    ΠΣ-allowed b p q
  inversion-ΠΣʰ-⊢∷ {l₁} {l₂} {B} {C} ⊢ΠΣ =
    let _ , _ , ⊢Lift-A , ⊢Lift-B , C≡U , ok = inversion-ΠΣ-U ⊢ΠΣ
        _ , _ , ⊢A , U[l₃]≡U[l₄⊔l₂]          = inversion-Lift∷ ⊢Lift-A
        _ , _ , ⊢B , U[l₃]≡U[l₅⊔l₁]          = inversion-Lift∷ ⊢Lift-B
        _ , ⊢l₂                              =
          inversion-supᵘₗ $
          inversion-U-Level (wf-⊢≡ U[l₃]≡U[l₄⊔l₂] .proj₂) .proj₂
        _ , ⊢l₁ =
          inversion-supᵘₗ $
          inversion-U-Level (wf-⊢≡ U[l₃]≡U[l₅⊔l₁] .proj₂) .proj₂
        ⊢A′ = univ ⊢A
        ⊢σ  = ⊢ˢʷ∷-[][]↑ (liftⱼ′ (wkLevel₁ ⊢A′ ⊢l₂) (var₀ ⊢A′))
    in
    PE.subst (_⊢_∷Level _) (wk1-[][]↑ 1) (subst-⊢∷L ⊢l₁ ⊢σ) ,
    ⊢l₂ , (_ , ⊢A) , (_ , inversion-lower₀-⊢∷ {t = B} ⊢B .proj₂) ,
    (_ , C≡U) , ok

opaque
  unfolding ΠΣʰ lower₀

  -- A limited inversion lemma for ΠΣʰ.

  inversion-ΠΣʰ-⊢ :
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B →
    Γ ∙ A ⊢ wk1 l₁ ∷Level ×
    Γ ⊢ l₂ ∷Level ×
    Γ ⊢ A ×
    Γ ∙ A ⊢ B [ lower (lift (var x0)) ]↑ ×
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
