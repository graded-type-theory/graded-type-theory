{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.RedSteps (M : Set) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.RedSteps M
open import Definition.Typed.Consequences.Substitution M

open import Tools.Nat
open import Tools.Fin
open import Tools.Product


private
  variable
    n : Nat
    Γ : Con Term n
    A  : Term n
    t t′ : Term n
    p r : M


-- Natrec substitution of reduction closures

natrec-subst* : ∀ {z s} → Γ ⊢ t ⇒* t′ ∷ ℕ
              → Γ ∙ ℕ ⊢ A
              → Γ ⊢ z ∷ A [ zero ]
              → Γ ∙ ℕ ∙ A ⊢ s ∷ wk1 (A [ suc (var x0) ]↑)
              → Γ ⊢ natrec p r A z s t ⇒* natrec p r A z s t′ ∷ A [ t ]
natrec-subst* (id x) ⊢A ⊢z ⊢s = id (natrecⱼ ⊢A ⊢z ⊢s x)
natrec-subst* (x ⇨ t⇒t′) ⊢A ⊢z ⊢s =
  (natrec-subst ⊢A ⊢z ⊢s x) ⇨ conv* (natrec-subst* t⇒t′ ⊢A ⊢z ⊢s)
                                    (substTypeEq (refl ⊢A) (sym (subsetTerm x)))
