------------------------------------------------------------------------
-- Substitution theorems for reduction closures.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.RedSteps
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
  hiding (_∷_) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Properties R
import Definition.LogicalRelation.Substitution.Introductions.Identity R
  as I

open import Tools.Function
open import Tools.Nat
open import Tools.Fin
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B F G t t′ u v v₁ v₂ w₁ w₂ : Term n
    p q q′ r : M

-- Second projector substitution of reduction closures

snd-subst* : Γ ⊢ t ⇒* t′ ∷ Σₚ p , q ▷ F ▹ G
           → Γ ⊢ F
           → Γ ∙ F ⊢ G
           → Γ ⊢ snd p t ⇒* snd p t′ ∷ G [ fst p t ]₀
snd-subst* (id x) ⊢F ⊢G = id (sndⱼ ⊢F ⊢G x)
snd-subst* (x ⇨ t⇒t′) ⊢F ⊢G =
  snd-subst ⊢F ⊢G x ⇨ conv* (snd-subst* t⇒t′ ⊢F ⊢G)
                              (substTypeEq (refl ⊢G) (sym (fst-cong ⊢F ⊢G (subsetTerm x))))


-- Natrec substitution of reduction closures

natrec-subst* : ∀ {z s} → Γ ⊢ t ⇒* t′ ∷ ℕ
              → Γ ∙ ℕ ⊢ A
              → Γ ⊢ z ∷ A [ zero ]₀
              → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
              → Γ ⊢ natrec p q r A z s t ⇒* natrec p q r A z s t′ ∷ A [ t ]₀
natrec-subst* (id x) ⊢A ⊢z ⊢s = id (natrecⱼ ⊢A ⊢z ⊢s x)
natrec-subst* (x ⇨ t⇒t′) ⊢A ⊢z ⊢s =
  natrec-subst ⊢A ⊢z ⊢s x ⇨ conv* (natrec-subst* t⇒t′ ⊢A ⊢z ⊢s)
                                    (substTypeEq (refl ⊢A) (sym (subsetTerm x)))

-- Prodrec substitution of reduction closures

prodrec-subst* : Γ ⊢ t ⇒* t′ ∷ Σᵣ p , q ▷ F ▹ G
               → Γ ⊢ F
               → Γ ∙ F ⊢ G
               → Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A
               → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var x1) (var x0) ]↑²
               → Γ ⊢ prodrec r p q′ A t u ⇒* prodrec r p q′ A t′ u ∷ A [ t ]₀
prodrec-subst* (id x) ⊢F ⊢G ⊢A ⊢u =
  id (prodrecⱼ ⊢F ⊢G ⊢A x ⊢u ok)
  where
  ok = ⊢∷ΠΣ→ΠΣ-allowed (var (wf ⊢A) here)
prodrec-subst* (x ⇨ t⇒t′) ⊢F ⊢G ⊢A ⊢u =
  prodrec-subst ⊢F ⊢G ⊢A ⊢u x ok ⇨
  conv* (prodrec-subst* t⇒t′ ⊢F ⊢G ⊢A ⊢u)
    (substTypeEq (refl ⊢A) (sym (subsetTerm x)))
  where
  ok = ⊢∷ΠΣ→ΠΣ-allowed (var (wf ⊢A) here)

opaque

  -- A variant of K-subst for _⊢_⇒*_∷_.

  K-subst* :
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t t →
    K-allowed →
    Γ ⊢ K p A t B u v₁ ⇒* K p A t B u v₂ ∷ B [ v₁ ]₀
  K-subst* ⊢B ⊢u v₁⇒*v₂ =
    case syntacticRedTerm v₁⇒*v₂ of λ {
      (⊢Id , _ , ⊢v₂) →
    case inversion-Id ⊢Id of λ {
      (⊢A , ⊢t , _) →
    case reducibleTerm ⊢v₂ of λ {
      (⊩Id , ⊩v₂) →
    I.K-subst* ⊢A ⊢t ⊢B ⊢u v₁⇒*v₂ ⊩Id ⊩v₂
      (λ _ _ v₁≡v₂ →
         substTypeEq (refl ⊢B) (escapeTermEq ⊩Id v₁≡v₂)) }}}

opaque

  -- A variant of J-subst for _⊢_⇒*_∷_.

  J-subst* :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ w₁ ⇒* w₂ ∷ Id A t v →
    Γ ⊢ J p q A t B u v w₁ ⇒* J p q A t B u v w₂ ∷ B [ v , w₁ ]₁₀
  J-subst* {Γ} ⊢B ⊢u w₁⇒*w₂ =
    case syntacticRedTerm w₁⇒*w₂ of λ {
      (⊢Id , _ , ⊢w₂) →
    case inversion-Id ⊢Id of λ {
      (⊢A , ⊢t , ⊢v) →
    case reducibleTerm ⊢w₂ of λ {
      (⊩Id , ⊩w₂) →
    I.J-subst* ⊢A ⊢t ⊢B ⊢u ⊢v w₁⇒*w₂ ⊩Id ⊩w₂
      (λ _ _ w₁≡w₂ →
         J-result-cong (refl ⊢B) (refl ⊢v) (escapeTermEq ⊩Id w₁≡w₂)) }}}
