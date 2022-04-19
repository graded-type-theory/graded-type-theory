{-# OPTIONS --without-K --safe #-}

module Definition.Typed.RedSteps (M : Set) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Tools.Nat

private
  variable
    n : Nat
    Γ : Con Term n
    A B C : Term n
    a t t′ u r : Term n
    p q : M

-- Concatenation of type reduction closures
_⇨*_ : Γ ⊢ A ⇒* B → Γ ⊢ B ⇒* C → Γ ⊢ A ⇒* C
id ⊢B ⇨* B⇒C = B⇒C
(A⇒A′ ⇨ A′⇒B) ⇨* B⇒C = A⇒A′ ⇨ (A′⇒B ⇨* B⇒C)

-- Concatenation of term reduction closures
_⇨∷*_ : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒* r ∷ A → Γ ⊢ t ⇒* r ∷ A
id ⊢u ⇨∷* u⇒r = u⇒r
(t⇒t′ ⇨ t′⇒u) ⇨∷* u⇒r = t⇒t′ ⇨ (t′⇒u ⇨∷* u⇒r)

-- Conversion of reduction closures
conv* : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* u ∷ B
conv* (id x) A≡B = id (conv x A≡B)
conv* (x ⇨ d) A≡B = conv x A≡B ⇨ conv* d A≡B

-- Universe of reduction closures
univ* : Γ ⊢ A ⇒* B ∷ U → Γ ⊢ A ⇒* B
univ* (id x) = id (univ x)
univ* (x ⇨ A⇒B) = univ x ⇨ univ* A⇒B

-- Application substitution of reduction closures
app-subst* : Γ ⊢ t ⇒* t′ ∷ Π p , q ▷ A ▹ B → Γ ⊢ a ∷ A
           → Γ ⊢ t ∘ p ▷ a ⇒* t′ ∘ p ▷ a ∷ B [ a ]
app-subst* (id x) a₁ = id (x ∘ⱼ a₁)
app-subst* (x ⇨ t⇒t′) a₁ = app-subst x a₁ ⇨ app-subst* t⇒t′ a₁

-- Fisrt projection substitution of reduction closures
fst-subst* : ∀ {F G t t′} → Γ ⊢ F → Γ ∙ F ⊢ G
           → Γ ⊢ t ⇒* t′ ∷ Σₚ q ▷ F ▹ G → Γ ⊢ fst t ⇒* fst t′ ∷ F
fst-subst* ⊢F ⊢G (id x) = id (fstⱼ ⊢F ⊢G x)
fst-subst* ⊢F ⊢G (x ⇨ t⇒t′) = fst-subst ⊢F ⊢G x ⇨ fst-subst* ⊢F ⊢G t⇒t′
