{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Typed.Consequences.RedSteps {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.RedSteps M′
open import Definition.Typed.Consequences.Reduction M′
open import Definition.Typed.Consequences.Substitution M′
open import Definition.Typed.Consequences.Syntactic M′

open import Tools.Nat
open import Tools.Fin
open import Tools.Product


private
  variable
    n : Nat
    Γ : Con Term n
    A F : Term n
    G : Term (1+ n)
    t t′ : Term n
    u : Term (1+ (1+ n))
    p q r : M

-- Second projector substitution of reduction closures

snd-subst* : Γ ⊢ t ⇒* t′ ∷ Σ q ▷ F ▹ G
           → Γ ⊢ F
           → Γ ∙ F ⊢ G
           → Γ ⊢ snd t ⇒* snd t′ ∷ G [ fst t ]
snd-subst* (id x) ⊢F ⊢G = id (sndⱼ ⊢F ⊢G x)
snd-subst* (x ⇨ t⇒t′) ⊢F ⊢G =
  snd-subst ⊢F ⊢G x ⇨ conv* (snd-subst* t⇒t′ ⊢F ⊢G)
                            (substTypeEq (refl ⊢G) (sym (fst-cong ⊢F ⊢G (subsetTerm x))))


-- Natrec substitution of reduction closures

natrec-subst* : ∀ {z s} → Γ ⊢ t ⇒* t′ ∷ ℕ
              → Γ ∙ ℕ ⊢ A
              → Γ ⊢ z ∷ A [ zero ]
              → Γ ∙ ℕ ∙ A ⊢ s ∷ wk1 (A [ suc (var x0) ]↑)
              → Γ ⊢ natrec p r A z s t ⇒* natrec p r A z s t′ ∷ A [ t ]
natrec-subst* (id x) ⊢A ⊢z ⊢s = id (natrecⱼ ⊢A ⊢z ⊢s x)
natrec-subst* (x ⇨ t⇒t′) ⊢A ⊢z ⊢s =
  natrec-subst ⊢A ⊢z ⊢s x ⇨ conv* (natrec-subst* t⇒t′ ⊢A ⊢z ⊢s)
                                  (substTypeEq (refl ⊢A) (sym (subsetTerm x)))

-- Prodrec substitution of reduction closures

prodrec-subst* : Γ ⊢ t ⇒* t′ ∷ Σ q ▷ F ▹ G
               → Γ ⊢ F
               → Γ ∙ F ⊢ G
               → Γ ∙ (Σ q ▷ F ▹ G) ⊢ A
               → Γ ⊢ t ∷ Σ q ▷ F ▹ G
               → Γ ∙ F ∙ G ⊢ u ∷ A [ prod (var (x0 +1)) (var x0) ]↑²
               → Γ ⊢ prodrec p A t u ⇒* prodrec p A t′ u ∷ A [ t ]
prodrec-subst* (id x) ⊢F ⊢G ⊢A ⊢t ⊢u = id (prodrecⱼ ⊢F ⊢G ⊢t ⊢A ⊢u)
prodrec-subst* (x ⇨ t⇒t′) ⊢F ⊢G ⊢A ⊢t ⊢u =
  let _ , _ , ⊢t′ = syntacticRedTerm (redMany x)
  in  (prodrec-subst ⊢F ⊢G ⊢u ⊢A x) ⇨ conv* (prodrec-subst* t⇒t′ ⊢F ⊢G ⊢A ⊢t′ ⊢u)
                                            (substTypeEq (refl ⊢A) (sym (subsetTerm x)))
