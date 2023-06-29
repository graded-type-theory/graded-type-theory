------------------------------------------------------------------------
-- Properties of reduction closures
--
-- Further substitution theorems for reduction closures follow from
-- the fundamental lemma. These are located in
-- Definition.Typed.Consequeces.RedSteps
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.RedSteps
  {ℓ} {M : Set ℓ}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
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
           → Γ ⊢ t ∘⟨ p ⟩ a ⇒* t′ ∘⟨ p ⟩ a ∷ B [ a ]₀
app-subst* (id x) a₁ = id (x ∘ⱼ a₁)
app-subst* (x ⇨ t⇒t′) a₁ = app-subst x a₁ ⇨ app-subst* t⇒t′ a₁

-- First projection substitution of reduction closures
fst-subst* : Γ ⊢ t ⇒* t′ ∷ Σₚ p , q ▷ A ▹ B
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ fst p t ⇒* fst p t′ ∷ A
fst-subst* (id x) ⊢F ⊢G = id (fstⱼ ⊢F ⊢G x)
fst-subst* (x ⇨ t⇒t′) ⊢F ⊢G = (fst-subst ⊢F ⊢G x) ⇨ (fst-subst* t⇒t′ ⊢F ⊢G)
