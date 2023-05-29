------------------------------------------------------------------------
-- Derived typing rules
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.DerivedRules
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open Type-restrictions R

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as W hiding (wk)
open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M

private variable
  Γ       : Con Term _
  A B t u : Term _
  p q     : M

-- Lambdas preserve definitional equality.

lam-cong :
  Γ ∙ A ⊢ t ≡ u ∷ B →
  Π-restriction p q →
  Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B
lam-cong {B = B} t≡u ok = η-eq ⊢A (lamⱼ ⊢A ⊢t ok) (lamⱼ ⊢A ⊢u ok) $
  _⊢_≡_∷_.trans
    (PE.subst (_ ⊢ _ ≡ _ ∷_)
       (wkSingleSubstId _)
       (β-red A⊢A A∙A⊢B (wkTerm ρ ⊢∙A∙A ⊢t) (var ⊢∙A here)
          PE.refl ok)) $
  _⊢_≡_∷_.trans
    (PE.subst₂ (_ ⊢_≡_∷ _)
      (PE.sym (wkSingleSubstId _))
      (PE.sym (wkSingleSubstId _))
      t≡u) $
  _⊢_≡_∷_.sym $
  PE.subst (_ ⊢ _ ≡ _ ∷_)
    (wkSingleSubstId _)
    (β-red A⊢A A∙A⊢B (wkTerm ρ ⊢∙A∙A ⊢u) (var ⊢∙A here) PE.refl ok)
  where
  ρ     = lift (step id)
  ⊢t    = syntacticEqTerm t≡u .proj₂ .proj₁
  ⊢u    = syntacticEqTerm t≡u .proj₂ .proj₂
  ⊢B    = syntacticEqTerm t≡u .proj₁
  ⊢∙A   = wf ⊢B
  ⊢A    = case ⊢∙A of λ where
            (_ ∙ ⊢A) → ⊢A
  A⊢A   = W.wk (step id) ⊢∙A ⊢A
  ⊢∙A∙A = ⊢∙A ∙ A⊢A
  A∙A⊢B = W.wk (lift (step id)) ⊢∙A∙A ⊢B

-- An η-rule for Π-types.

Π-η :
  Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
  Γ ⊢ lam p (wk1 t ∘⟨ p ⟩ var x0) ≡ t ∷ Π p , q ▷ A ▹ B
Π-η {Γ = Γ} {t = t} {p = p} {q = q} {A = A} {B = B} ⊢t = η-eq
  ⊢A
  (                                                                $⟨ ⊢wkt0 ⟩
   Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ∷ wk (lift (step id)) B [ var x0 ]  →⟨ flip conv B[0]≡B ⟩
   Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ∷ B                                 →⟨ flip (lamⱼ ⊢A) ok ⟩
   Γ ⊢ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B               □)
  ⊢t
  (                                                                     $⟨ ⊢wkt0 ⟩

   Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ∷ wk (lift (step id)) B [ var x0 ]       →⟨ PE.subst (λ t → _ ⊢ t ∘⟨ _ ⟩ _ ≡ wk1 _ ∘⟨ _ ⟩ _ ∷ _)
                                                                             (PE.sym (wk1-sgSubst _ _)) ∘→
                                                                           refl ⟩
   Γ ∙ A ⊢
     (wk1 (wk1 t) ∘⟨ p ⟩ var x0) [ var x0 ] ≡
     wk1 t ∘⟨ p ⟩ var x0 ∷
     wk (lift (step id)) B [ var x0 ]                                   →⟨ _⊢_≡_∷_.trans $
                                                                           β-red ⊢wkA ⊢wkB
                                                                             (_⊢_∷_.conv (wkTerm (step id) ⊢ΓAA ⊢wkt ∘ⱼ var ⊢ΓAA here) $
                                                                              PE.subst₂ (_ ⊢_≡_) (PE.sym (wkSingleSubstId _)) PE.refl (refl ⊢wkB))
                                                                             (var ⊢ΓA here)
                                                                             PE.refl ok ⟩
   Γ ∙ A ⊢
     lam p (wk1 (wk1 t) ∘⟨ p ⟩ var x0) ∘⟨ p ⟩ var x0 ≡
     wk1 t ∘⟨ p ⟩ var x0 ∷
     wk (lift (step id)) B [ var x0 ]                                   →⟨ PE.subst (λ t → _ ⊢ lam _ (t ∘⟨ _ ⟩ _) ∘⟨ _ ⟩ _ ≡ wk1 _ ∘⟨ _ ⟩ _ ∷ _) $
                                                                           wk1-wk≡lift-wk1 _ _ ⟩
   Γ ∙ A ⊢
     lam p (wk (lift (step id)) (wk1 t) ∘⟨ p ⟩ var x0) ∘⟨ p ⟩ var x0 ≡
     wk1 t ∘⟨ p ⟩ var x0 ∷
     wk (lift (step id)) B [ var x0 ]                                   →⟨ flip conv B[0]≡B ⟩

   Γ ∙ A ⊢
     wk1 (lam p (wk1 t ∘⟨ p ⟩ var x0)) ∘⟨ p ⟩ var x0 ≡
     wk1 t ∘⟨ p ⟩ var x0 ∷
     B                                                                  □)
  where
  ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t)
  ⊢A       = ⊢A,⊢B,ok .proj₁
  ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
  ok       = ⊢A,⊢B,ok .proj₂ .proj₂
  ⊢Γ       = wfTerm ⊢t
  ⊢ΓA      = ⊢Γ ∙ ⊢A
  ⊢wkt     = wkTerm (step id) ⊢ΓA ⊢t
  ⊢wkt0    = ⊢wkt ∘ⱼ var ⊢ΓA here
  ⊢wkA     = W.wk (step id) ⊢ΓA ⊢A
  ⊢ΓAA     = ⊢ΓA ∙ ⊢wkA
  ⊢wkB     = W.wk (lift (step id)) ⊢ΓAA ⊢B

  B[0]≡B : Γ ∙ A ⊢ wk (lift (step id)) B [ var x0 ] ≡ B
  B[0]≡B = PE.subst (_ ⊢_≡ _) (PE.sym (wkSingleSubstId _)) (refl ⊢B)

-- An η-rule for strong Σ-types.

Σ-η-prod-fst-snd :
  Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
  Γ ⊢ prodₚ p (fst p t) (snd p t) ≡ t ∷ Σₚ p , q ▷ A ▹ B
Σ-η-prod-fst-snd ⊢t = Σ-η
  ⊢A
  ⊢B
  (prodⱼ ⊢A ⊢B ⊢fst ⊢snd ok)
  ⊢t
  (Σ-β₁ ⊢A ⊢B ⊢fst ⊢snd PE.refl ok)
  (Σ-β₂ ⊢A ⊢B ⊢fst ⊢snd PE.refl ok)
  where
  ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t)
  ⊢A       = ⊢A,⊢B,ok .proj₁
  ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
  ok       = ⊢A,⊢B,ok .proj₂ .proj₂
  ⊢fst     = fstⱼ ⊢A ⊢B ⊢t
  ⊢snd     = sndⱼ ⊢A ⊢B ⊢t

-- An η-rule for the Unit type.

Unit-η :
  Γ ⊢ t ∷ Unit →
  Γ ⊢ star ≡ t ∷ Unit
Unit-η ⊢t = η-unit
  (starⱼ (wfTerm ⊢t) (⊢∷Unit→Unit-restriction ⊢t))
  ⊢t
