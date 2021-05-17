{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.RedSteps (M : Set) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Consequences.Reduction M
open import Definition.Typed.Consequences.Syntactic M

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    t t′ A B : Term n
    q : M


-- First projection of reduction closures
fst-subst* : Γ ⊢ t ⇒* t′ ∷ Σ q ▷ A ▹ B
           → Γ ⊢ fst t ⇒* fst t′ ∷ A
fst-subst* (id x) with syntacticΣ (syntacticTerm x)
... | Γ⊢A , Γ⊢B = id (fstⱼ Γ⊢A Γ⊢B x)
fst-subst* (x ⇨ t⇒t′) with syntacticΣ (proj₁ (syntacticRedTerm (redMany x)))
... | Γ⊢A , Γ⊢B = (fst-subst Γ⊢A Γ⊢B x) ⇨ (fst-subst* t⇒t′)

-- Second projection of reduction closures
-- snd-subst* : Γ ⊢ t ⇒* t′ ∷ Σ q ▷ A ▹ B
--            → Γ ⊢ snd t ⇒* snd t′ ∷ B [ fst t′ ]
-- snd-subst* (id x) with syntacticΣ (syntacticTerm x)
-- ... | Γ⊢A , Γ⊢B = id (sndⱼ Γ⊢A Γ⊢B x)
-- snd-subst* (x ⇨ t⇒t′) with syntacticΣ (proj₁ (syntacticRedTerm (redMany x)))
-- ... | Γ⊢A , Γ⊢B = (snd-subst {!!} {!!} {!x!}) ⇨ (snd-subst* ?)
