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

import Definition.Typed.Consequences.Stability R as S
open import Definition.Typed R
open import Definition.Typed.Consequences.DerivedRules.Sigma R public
open import Definition.Typed.Consequences.DerivedRules.Nat R public
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as W hiding (wk)
open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M

private variable
  Γ           : Con Term _
  A B t u     : Term _
  p p′ p″ q r : M

-- Lambdas preserve definitional equality.

lam-cong :
  Γ ∙ A ⊢ t ≡ u ∷ B →
  Π-allowed p q →
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

-- A variant of the inversion lemma for lam.

inversion-lam′ :
  Γ ⊢ lam p t ∷ Π q , r ▷ A ▹ B →
  Γ ∙ A ⊢ t ∷ B × p PE.≡ q × Π-allowed q r
inversion-lam′ ⊢lam =
  case inversion-lam ⊢lam of λ {
    (_ , _ , _ , _ , ⊢t , ≡ΠΣ , ok) →
  case ΠΣ-injectivity ≡ΠΣ of λ {
    (A≡ , B≡ , PE.refl , PE.refl , _) →
  conv (S.stabilityTerm (S.reflConEq (wfTerm ⊢lam) S.∙ sym A≡) ⊢t)
    (sym B≡) ,
  PE.refl ,
  ok }}

-- A reduction rule for weakened lambdas applied to variable zero.

wk1-lam∘0⇒ :
  Γ ⊢ lam p t ∷ Π q , r ▷ A ▹ B →
  Γ ∙ A ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ⇒ t ∷ B
wk1-lam∘0⇒ {p = p} {t = t} ⊢lam =
  case inversion-lam′ ⊢lam of λ {
    (⊢t , PE.refl , ok) →
  let ⊢ΓA  = wfTerm ⊢t
      ΓA⊢A = case ⊢ΓA of λ {
               (_ ∙ ⊢A) → W.wk (step id) ⊢ΓA ⊢A }
      ⊢ΓAA = ⊢ΓA ∙ ΓA⊢A
  in PE.subst₂ (_ ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ⇒_∷_)
    (wkSingleSubstId _)
    (wkSingleSubstId _)
    (β-red ΓA⊢A
       (W.wk (lift (step id)) ⊢ΓAA (syntacticTerm ⊢t))
       (wkTerm (lift (step id)) ⊢ΓAA ⊢t)
       (var ⊢ΓA here) PE.refl ok) }

-- An equality rule for weakened lambdas applied to variable zero.

wk1-lam∘0≡ :
  Γ ⊢ lam p t ∷ Π q , r ▷ A ▹ B →
  Γ ∙ A ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ≡ t ∷ B
wk1-lam∘0≡ ⊢lam = subsetTerm (wk1-lam∘0⇒ ⊢lam)

-- An inverse of uncurry lam-cong (up to logical equivalence).

lam-cong⁻¹ :
  Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B →
  Γ ∙ A ⊢ t ≡ u ∷ B × Π-allowed p q
lam-cong⁻¹
  {Γ = Γ} {p = p} {t = t} {u = u} {q = q} {A = A} {B = B} lam-t≡lam-u =  $⟨ lam-t≡lam-u ⟩
  Γ ⊢ lam p t ≡ lam p u ∷ Π p , q ▷ A ▹ B                                →⟨ wkEqTerm (step id) ⊢ΓA ⟩

  Γ ∙ A ⊢ wk1 (lam p t) ≡ wk1 (lam p u) ∷ wk1 (Π p , q ▷ A ▹ B)          →⟨ flip app-cong (refl (var ⊢ΓA here)) ⟩

  Γ ∙ A ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ≡ wk1 (lam p u) ∘⟨ p ⟩ var x0 ∷
    wk (lift (step id)) B [ var x0 ]₀                                    →⟨ PE.subst (_ ⊢ _ ≡ _ ∷_) (wkSingleSubstId _) ⟩

  Γ ∙ A ⊢ wk1 (lam p t) ∘⟨ p ⟩ var x0 ≡ wk1 (lam p u) ∘⟨ p ⟩ var x0 ∷ B  →⟨ (λ hyp → trans
                                                                               (sym (wk1-lam∘0≡ ⊢lam-t))
                                                                               (trans hyp (wk1-lam∘0≡ ⊢lam-u))) ⟩

  Γ ∙ A ⊢ t ≡ u ∷ B                                                      →⟨ _, ok ⟩

  Γ ∙ A ⊢ t ≡ u ∷ B × Π-allowed p q                                      □
  where
  ⊢Γ     = wfEqTerm lam-t≡lam-u
  ⊢A     = inversion-ΠΣ (syntacticEqTerm lam-t≡lam-u .proj₁) .proj₁
  ⊢ΓA    = ⊢Γ ∙ ⊢A
  ⊢lam-t = syntacticEqTerm lam-t≡lam-u .proj₂ .proj₁
  ⊢lam-u = syntacticEqTerm lam-t≡lam-u .proj₂ .proj₂
  ok     = inversion-lam′ ⊢lam-t .proj₂ .proj₂

-- An injectivity lemma for lam.

lam-injective :
  Γ ⊢ lam p t ≡ lam p′ u ∷ Π p″ , q ▷ A ▹ B →
  p PE.≡ p′ × Γ ∙ A ⊢ t ≡ u ∷ B × Π-allowed p q × p′ PE.≡ p″
lam-injective
  {Γ = Γ} {p = p} {t = t} {p′ = p′} {u = u} {p″ = p″} {q = q}
  {A = A} {B = B} lam-t≡lam-u =
  case syntacticEqTerm lam-t≡lam-u of λ {
    (_ , ⊢lam₁ , ⊢lam₂) →
  case inversion-lam′ ⊢lam₁ of λ {
    (_ , PE.refl , _) →
  case inversion-lam′ ⊢lam₂ of λ {
    (_ , PE.refl , _) →
  case lam-cong⁻¹ lam-t≡lam-u of λ {
    (t≡u , ok) →
  PE.refl , t≡u , ok , PE.refl }}}}

-- An η-rule for Π-types.

Π-η :
  Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
  Γ ⊢ lam p (wk1 t ∘⟨ p ⟩ var x0) ≡ t ∷ Π p , q ▷ A ▹ B
Π-η {Γ = Γ} {t = t} {p = p} {q = q} {A = A} {B = B} ⊢t = η-eq
  ⊢A
  ⊢lam
  ⊢t
  (                                                     $⟨ ⊢lam ⟩

   Γ ⊢ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B    →⟨ wk1-lam∘0≡ ⟩

   Γ ∙ A ⊢
     wk1 (lam p (wk1 t ∘⟨ p ⟩ var x0)) ∘⟨ p ⟩ var x0 ≡
     wk1 t ∘⟨ p ⟩ var x0 ∷
     B                                                  □)
  where
  ⊢A,ok = inversion-ΠΣ (syntacticTerm ⊢t)
  ⊢A    = ⊢A,ok .proj₁
  ok    = ⊢A,ok .proj₂ .proj₂
  ⊢ΓA   = wfTerm ⊢t ∙ ⊢A

  ⊢lam =                                                            $⟨ wkTerm (step id) ⊢ΓA ⊢t ∘ⱼ var ⊢ΓA here ⟩
    Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ∷ wk (lift (step id)) B [ var x0 ]₀  →⟨ PE.subst (_ ⊢ _ ∷_) (wkSingleSubstId _) ⟩
    Γ ∙ A ⊢ wk1 t ∘⟨ p ⟩ var x0 ∷ B                                  →⟨ flip (lamⱼ ⊢A) ok ⟩
    Γ ⊢ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B                □

-- An η-rule for the Unit type.

Unit-η :
  Γ ⊢ t ∷ Unit →
  Γ ⊢ star ≡ t ∷ Unit
Unit-η ⊢t = η-unit
  (starⱼ (wfTerm ⊢t) (⊢∷Unit→Unit-allowed ⊢t))
  ⊢t
