------------------------------------------------------------------------
-- Admissible rules related to _⟶×⟨_⟩[_]_
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Non-dependent
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Pi-Sigma R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Non-dependent 𝕄
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ                                         : Cons _ _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ t t₁ t₂ u u₁ u₂ v : Term _
  l                                         : Lvl _
  b                                         : BinderMode
  s                                         : Strength
  p q r                                     : M

------------------------------------------------------------------------
-- Rules for _⟶×⟨_⟩[_]_

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An equality rule for _⟶×⟨_⟩[_]_.

  ⟶×-cong :
    ΠΣ-allowed b p 𝟘 →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ B₁ ≡ B₂ →
    Γ ⊢ A₁ ⟶×⟨ b ⟩[ p ] B₁ ≡ A₂ ⟶×⟨ b ⟩[ p ] B₂
  ⟶×-cong ok A₁≡A₂ B₁≡B₂ =
    ΠΣ-cong A₁≡A₂ (wkEq₁ (wf-⊢≡ A₁≡A₂ .proj₁) B₁≡B₂) ok

opaque

  -- A typing rule for _⟶×⟨_⟩[_]_.

  ⊢⟶× :
    ΠΣ-allowed b p 𝟘 →
    Γ ⊢ A →
    Γ ⊢ B →
    Γ ⊢ A ⟶×⟨ b ⟩[ p ] B
  ⊢⟶× ok ⊢A ⊢B =
    wf-⊢≡ (⟶×-cong ok (refl ⊢A) (refl ⊢B)) .proj₁

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An equality rule for _⟶×⟨_⟩[_]_.

  ⟶×-cong-U :
    ΠΣ-allowed b p 𝟘 →
    Γ ⊢ A₁ ≡ A₂ ∷ U l →
    Γ ⊢ B₁ ≡ B₂ ∷ U l →
    Γ ⊢ A₁ ⟶×⟨ b ⟩[ p ] B₁ ≡ A₂ ⟶×⟨ b ⟩[ p ] B₂ ∷ U l
  ⟶×-cong-U ok A₁≡A₂ B₁≡B₂ =
    ΠΣ-cong′ A₁≡A₂ (wkEqTerm₁ (univ (wf-⊢≡∷ A₁≡A₂ .proj₂ .proj₁)) B₁≡B₂)
      ok

opaque

  -- A typing rule for _⟶×⟨_⟩[_]_.

  ⊢⟶×-U :
    ΠΣ-allowed b p 𝟘 →
    Γ ⊢ A ∷ U l →
    Γ ⊢ B ∷ U l →
    Γ ⊢ A ⟶×⟨ b ⟩[ p ] B ∷ U l
  ⊢⟶×-U ok ⊢A ⊢B =
    wf-⊢≡∷ (⟶×-cong-U ok (refl ⊢A) (refl ⊢B)) .proj₂ .proj₁

------------------------------------------------------------------------
-- Rules for _⟶[_]_

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An equality rule for lam.

  lam-cong-⟶ :
    Π-allowed p 𝟘 →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ wk1 B →
    Γ ⊢ lam p t₁ ≡ lam p t₂ ∷ A ⟶[ p ] B
  lam-cong-⟶ = flip lam-cong

opaque

  -- A typing rule for lam.

  ⊢lam-⟶ :
    Π-allowed p 𝟘 →
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ lam p t ∷ A ⟶[ p ] B
  ⊢lam-⟶ ok ⊢t = wf-⊢≡∷ (lam-cong-⟶ ok (refl ⊢t)) .proj₂ .proj₁

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An equality rule for _∘⟨_⟩_.

  app-cong-⟶ :
    Γ ⊢ t₁ ≡ t₂ ∷ A ⟶[ p ] B →
    Γ ⊢ u₁ ≡ u₂ ∷ A →
    Γ ⊢ t₁ ∘⟨ p ⟩ u₁ ≡ t₂ ∘⟨ p ⟩ u₂ ∷ B
  app-cong-⟶ t₁≡t₂ u₁≡u₂ =
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    app-cong t₁≡t₂ u₁≡u₂

opaque

  -- A typing rule for _∘⟨_⟩_.

  ⊢app-⟶ :
    Γ ⊢ t ∷ A ⟶[ p ] B →
    Γ ⊢ u ∷ A →
    Γ ⊢ t ∘⟨ p ⟩ u ∷ B
  ⊢app-⟶ ⊢t ⊢u =
    wf-⊢≡∷ (app-cong-⟶ (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of app-subst.

  app-subst-⟶ :
    Γ ⊢ t₁ ⇒ t₂ ∷ A ⟶[ p ] B →
    Γ ⊢ u ∷ A →
    Γ ⊢ t₁ ∘⟨ p ⟩ u ⇒ t₂ ∘⟨ p ⟩ u ∷ B
  app-subst-⟶ t₁⇒t₂ u =
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk1-sgSubst _ _) $
    app-subst t₁⇒t₂ u

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of app-subst*.

  app-subst*-⟶ :
    Γ ⊢ t₁ ⇒* t₂ ∷ A ⟶[ p ] B →
    Γ ⊢ u ∷ A →
    Γ ⊢ t₁ ∘⟨ p ⟩ u ⇒* t₂ ∘⟨ p ⟩ u ∷ B
  app-subst*-⟶ t₁⇒*t₂ u =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (wk1-sgSubst _ _) $
    app-subst* t₁⇒*t₂ u

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of the reduction rule β-red.

  β-red-⟶-⇒ :
    Π-allowed p 𝟘 →
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ A →
    Γ ⊢ lam p t ∘⟨ p ⟩ u ⇒ t [ u ]₀ ∷ B
  β-red-⟶-⇒ ok ⊢t ⊢u =
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk1-sgSubst _ _) $
    β-red-⇒ ⊢t ⊢u ok

opaque

  -- A variant of the equality rule β-red.

  β-red-⟶-≡ :
    Π-allowed p 𝟘 →
    Γ »∙ A ⊢ t ∷ wk1 B →
    Γ ⊢ u ∷ A →
    Γ ⊢ lam p t ∘⟨ p ⟩ u ≡ t [ u ]₀ ∷ B
  β-red-⟶-≡ ok ⊢t ⊢u =
    subsetTerm (β-red-⟶-⇒ ok ⊢t ⊢u)

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of η-eq.

  η-eq-⟶ :
    Γ ⊢ t₁ ∷ A ⟶[ p ] B →
    Γ ⊢ t₂ ∷ A ⟶[ p ] B →
    Γ »∙ A ⊢ wk1 t₁ ∘⟨ p ⟩ var x0 ≡ wk1 t₂ ∘⟨ p ⟩ var x0 ∷ wk1 B →
    Γ ⊢ t₁ ≡ t₂ ∷ A ⟶[ p ] B
  η-eq-⟶ = η-eq′

------------------------------------------------------------------------
-- Rules for _×⟨_⟩[_]_

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An equality rule for prod.

  prod-cong-⟶ :
    Σ-allowed s p 𝟘 →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ u₁ ≡ u₂ ∷ B →
    Γ ⊢ prod s p t₁ u₁ ≡ prod s p t₂ u₂ ∷ A ×⟨ s ⟩[ p ] B
  prod-cong-⟶ ok t₁≡t₂ u₁≡u₂ =
    prod-cong (wk₁ (wf-⊢≡∷ t₁≡t₂ .proj₁) (wf-⊢≡∷ u₁≡u₂ .proj₁)) t₁≡t₂
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk1-sgSubst _ _) u₁≡u₂) ok

opaque

  -- A typing rule for prod.

  ⊢prod-⟶ :
    Σ-allowed s p 𝟘 →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B →
    Γ ⊢ prod s p t u ∷ A ×⟨ s ⟩[ p ] B
  ⊢prod-⟶ ok ⊢t ⊢u =
    wf-⊢≡∷ (prod-cong-⟶ ok (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

------------------------------------------------------------------------
-- Rules for _×ˢ[_]_

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An equality rule for fst.

  fst-cong-⟶ :
    Γ ⊢ t₁ ≡ t₂ ∷ A ×ˢ[ p ] B →
    Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A
  fst-cong-⟶ = fst-cong′

opaque

  -- A typing rule for fst.

  ⊢fst-⟶ :
    Γ ⊢ t ∷ A ×ˢ[ p ] B →
    Γ ⊢ fst p t ∷ A
  ⊢fst-⟶ ⊢t = wf-⊢≡∷ (fst-cong-⟶ (refl ⊢t)) .proj₂ .proj₁

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An equality rule for snd.

  snd-cong-⟶ :
    Γ ⊢ t₁ ≡ t₂ ∷ A ×ˢ[ p ] B →
    Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B
  snd-cong-⟶ t₁≡t₂ =
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    snd-cong′ t₁≡t₂

opaque

  -- A typing rule for snd.

  ⊢snd-⟶ :
    Γ ⊢ t ∷ A ×ˢ[ p ] B →
    Γ ⊢ snd p t ∷ B
  ⊢snd-⟶ ⊢t = wf-⊢≡∷ (snd-cong-⟶ (refl ⊢t)) .proj₂ .proj₁

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of fst-subst.

  fst-subst-⟶ :
    Γ ⊢ t₁ ⇒ t₂ ∷ A ×ˢ[ p ] B →
    Γ ⊢ fst p t₁ ⇒ fst p t₂ ∷ A
  fst-subst-⟶ = fst-subst′

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of fst-subst*.

  fst-subst*-⟶ :
    Γ ⊢ t₁ ⇒* t₂ ∷ A ×ˢ[ p ] B →
    Γ ⊢ fst p t₁ ⇒* fst p t₂ ∷ A
  fst-subst*-⟶ = fst-subst*

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of snd-subst.

  snd-subst-⟶ :
    Γ ⊢ t₁ ⇒ t₂ ∷ A ×ˢ[ p ] B →
    Γ ⊢ snd p t₁ ⇒ snd p t₂ ∷ B
  snd-subst-⟶ t₁⇒t₂ =
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk1-sgSubst _ _) $
    snd-subst′ t₁⇒t₂

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of snd-subst*.

  snd-subst*-⟶ :
    Γ ⊢ t₁ ⇒* t₂ ∷ A ×ˢ[ p ] B →
    Γ ⊢ snd p t₁ ⇒* snd p t₂ ∷ B
  snd-subst*-⟶ t₁⇒*t₂ =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (wk1-sgSubst _ _) $
    snd-subst* t₁⇒*t₂

opaque

  -- A variant of the reduction rule Σ-β₁.

  Σ-β₁-⟶-⇒ :
    Σˢ-allowed p 𝟘 →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B →
    Γ ⊢ fst p (prodˢ p t u) ⇒ t ∷ A
  Σ-β₁-⟶-⇒ ok ⊢t ⊢u =
    Σ-β₁-⇒ (wk₁ (wf-⊢∷ ⊢t) (wf-⊢∷ ⊢u)) ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) ⊢u) ok

opaque

  -- A variant of the equality rule Σ-β₁.

  Σ-β₁-⟶-≡ :
    Σˢ-allowed p 𝟘 →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B →
    Γ ⊢ fst p (prodˢ p t u) ≡ t ∷ A
  Σ-β₁-⟶-≡ ok ⊢t ⊢u =
    subsetTerm (Σ-β₁-⟶-⇒ ok ⊢t ⊢u)

opaque

  -- A variant of the reduction rule Σ-β₂.

  Σ-β₂-⟶-⇒ :
    Σˢ-allowed p 𝟘 →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B →
    Γ ⊢ snd p (prodˢ p t u) ⇒ u ∷ B
  Σ-β₂-⟶-⇒ ok ⊢t ⊢u =
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk1-sgSubst _ _) $
    Σ-β₂-⇒ (wk₁ (wf-⊢∷ ⊢t) (wf-⊢∷ ⊢u)) ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) ⊢u) ok

opaque

  -- A variant of the equality rule Σ-β₂.

  Σ-β₂-⟶-≡ :
    Σˢ-allowed p 𝟘 →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B →
    Γ ⊢ snd p (prodˢ p t u) ≡ u ∷ B
  Σ-β₂-⟶-≡ ok ⊢t ⊢u =
    subsetTerm (Σ-β₂-⟶-⇒ ok ⊢t ⊢u)

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of Σ-η.

  Σ-η-⟶ :
    Γ ⊢ t₁ ∷ A ×ˢ[ p ] B →
    Γ ⊢ t₂ ∷ A ×ˢ[ p ] B →
    Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A →
    Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B →
    Γ ⊢ t₁ ≡ t₂ ∷ A ×ˢ[ p ] B
  Σ-η-⟶ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ =
    Σ-η′ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk1-sgSubst _ _)
         snd-t₁≡snd-t₂)

------------------------------------------------------------------------
-- Rules for _×ʷ[_]_

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- An equality rule for prodrec.

  prodrec-cong-⟶ :
    Γ »∙ A ×ʷ[ p ] B ⊢ C₁ ≡ C₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A ×ʷ[ p ] B →
    Γ »∙ A »∙ wk1 B ⊢ u₁ ≡ u₂ ∷ C₁ [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C₁ t₁ u₁ ≡ prodrec r p q C₂ t₂ u₂ ∷ C₁ [ t₁ ]₀
  prodrec-cong-⟶ = prodrec-cong′

opaque

  -- A typing rule prodrec.

  ⊢prodrec-⟶ :
    Γ »∙ A ×ʷ[ p ] B ⊢ C →
    Γ ⊢ t ∷ A ×ʷ[ p ] B →
    Γ »∙ A »∙ wk1 B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C t u ∷ C [ t ]₀
  ⊢prodrec-⟶ ⊢C ⊢t ⊢u =
    wf-⊢≡∷ (prodrec-cong-⟶ (refl ⊢C) (refl ⊢t) (refl ⊢u)) .proj₂ .proj₁

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of prodrec-subst.

  prodrec-subst-⟶ :
    Γ »∙ A ×ʷ[ p ] B ⊢ C →
    Γ ⊢ t₁ ⇒ t₂ ∷ A ×ʷ[ p ] B →
    Γ »∙ A »∙ wk1 B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C t₁ u ⇒ prodrec r p q C t₂ u ∷ C [ t₁ ]₀
  prodrec-subst-⟶ = flip ∘→ prodrec-subst′

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of prodrec-subst*.

  prodrec-subst*-⟶ :
    Γ »∙ A ×ʷ[ p ] B ⊢ C →
    Γ ⊢ t₁ ⇒* t₂ ∷ A ×ʷ[ p ] B →
    Γ »∙ A »∙ wk1 B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C t₁ u ⇒* prodrec r p q C t₂ u ∷ C [ t₁ ]₀
  prodrec-subst*-⟶ = prodrec-subst*

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A variant of the reduction rule prodrec-β.

  prodrec-β-⟶-⇒ :
    Γ »∙ A ×ʷ[ p ] B ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B →
    Γ »∙ A »∙ wk1 B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C (prodʷ p t u) v ⇒ v [ t , u ]₁₀ ∷
      C [ prodʷ p t u ]₀
  prodrec-β-⟶-⇒ ⊢C ⊢t ⊢u ⊢v =
    prodrec-β-⇒ ⊢C ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) ⊢u) ⊢v

opaque

  -- A variant of the equality rule prodrec-β.

  prodrec-β-⟶-≡ :
    Γ »∙ A ×ʷ[ p ] B ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B →
    Γ »∙ A »∙ wk1 B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C (prodʷ p t u) v ≡ v [ t , u ]₁₀ ∷
      C [ prodʷ p t u ]₀
  prodrec-β-⟶-≡ ⊢C ⊢t ⊢u ⊢v =
    subsetTerm (prodrec-β-⟶-⇒ ⊢C ⊢t ⊢u ⊢v)
