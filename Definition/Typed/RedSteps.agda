------------------------------------------------------------------------
-- Properties of reduction closures
--
-- Further substitution theorems for reduction closures follow from
-- the fundamental lemma. These are located in
-- Definition.Typed.Consequeces.RedSteps
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.RedSteps
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R

import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n l : Nat
    Γ : Con Term n
    A B C : Term n
    a t t₁ t₂ t′ u v v₁ v₂ r : Term n
    p q : M
    s : Strength

-- Concatenation of type reduction closures
_⇨*_ : Γ ⊢ A ⇒* B → Γ ⊢ B ⇒* C → Γ ⊢ A ⇒* C
id ⊢B ⇨* B⇒C = B⇒C
(A⇒A′ ⇨ A′⇒B) ⇨* B⇒C = A⇒A′ ⇨ (A′⇒B ⇨* B⇒C)

-- Concatenation of term reduction closures
_⇨∷*_ : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒* r ∷ A → Γ ⊢ t ⇒* r ∷ A
id ⊢u ⇨∷* u⇒r = u⇒r
(t⇒t′ ⇨ t′⇒u) ⇨∷* u⇒r = t⇒t′ ⇨ (t′⇒u ⇨∷* u⇒r)

opaque

  -- A variant of _⇨∷*_ for _⊢_:⇒*:_∷_.

  trans-:⇒*: : Γ ⊢ t :⇒*: u ∷ A → Γ ⊢ u :⇒*: v ∷ A → Γ ⊢ t :⇒*: v ∷ A
  trans-:⇒*: [ ⊢t , _ , t⇒*u ] [ _ , ⊢v , u⇒*v ] =
    [ ⊢t , ⊢v , t⇒*u ⇨∷* u⇒*v ]

opaque

  -- A variant of _⇨*_ for _⊢_⇒*_ and _⊢_↘_.

  ⇒*→↘→↘ : Γ ⊢ A ⇒* B → Γ ⊢ B ↘ C → Γ ⊢ A ↘ C
  ⇒*→↘→↘ A⇒*B (B⇒*C , C-whnf) = (A⇒*B ⇨* B⇒*C) , C-whnf

opaque

  -- A variant of _⇨∷*_ for _⊢_⇒*_∷_ and _⊢_↘_∷_.

  ⇒*∷→↘∷→↘∷ : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ↘ v ∷ A → Γ ⊢ t ↘ v ∷ A
  ⇒*∷→↘∷→↘∷ t⇒*u (u⇒*v , v-whnf) = (t⇒*u ⇨∷* u⇒*v) , v-whnf

-- Conversion of reduction closures
conv* : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* u ∷ B
conv* (id x) A≡B = id (conv x A≡B)
conv* (x ⇨ d) A≡B = conv x A≡B ⇨ conv* d A≡B

-- Conversion of syntactic reduction closures.
convRed:*: : ∀ {t u A B} → Γ ⊢ t :⇒*: u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t :⇒*: u ∷ B
convRed:*: [ ⊢t , ⊢u , d ] A≡B = [ conv ⊢t  A≡B , conv ⊢u  A≡B , conv* d  A≡B ]

opaque

  -- A variant of conv* for _⊢_↘_∷_.

  conv↘∷ : Γ ⊢ t ↘ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ↘ u ∷ B
  conv↘∷ (t⇒*u , u-whnf) A≡B = conv* t⇒*u A≡B , u-whnf

-- Universe of reduction closures
univ* : Γ ⊢ A ⇒* B ∷ U l → Γ ⊢ A ⇒* B
univ* (id x) = id (univ x)
univ* (x ⇨ A⇒B) = univ x ⇨ univ* A⇒B

opaque

  -- A variant of univ*.

  univ:*: : Γ ⊢ A :⇒*: B ∷ U l → Γ ⊢ A :⇒*: B
  univ:*: [ ⊢A , ⊢B , A⇒*B ] = [ univ ⊢A , univ ⊢B , univ* A⇒*B ]

-- Application substitution of reduction closures
app-subst* : Γ ⊢ t ⇒* t′ ∷ Π p , q ▷ A ▹ B → Γ ⊢ a ∷ A
           → Γ ⊢ t ∘⟨ p ⟩ a ⇒* t′ ∘⟨ p ⟩ a ∷ B [ a ]₀
app-subst* (id x) a₁ = id (x ∘ⱼ a₁)
app-subst* (x ⇨ t⇒t′) a₁ = app-subst x a₁ ⇨ app-subst* t⇒t′ a₁

opaque

  -- A variant of app-subst*.

  app-subst:*: :
    Γ ⊢ t₁ :⇒*: t₂ ∷ Π p , q ▷ A ▹ B →
    Γ ⊢ u ∷ A →
    Γ ⊢ t₁ ∘⟨ p ⟩ u :⇒*: t₂ ∘⟨ p ⟩ u ∷ B [ u ]₀
  app-subst:*: [ ⊢t₁ , ⊢t₂ , t₁⇒*t₂ ] ⊢u =
    [ ⊢t₁ ∘ⱼ ⊢u , ⊢t₂ ∘ⱼ ⊢u , app-subst* t₁⇒*t₂ ⊢u ]

-- First projection substitution of reduction closures
fst-subst* : Γ ⊢ t ⇒* t′ ∷ Σˢ p , q ▷ A ▹ B
           → Γ ⊢ A
           → Γ ∙ A ⊢ B
           → Γ ⊢ fst p t ⇒* fst p t′ ∷ A
fst-subst* (id x) ⊢F ⊢G = id (fstⱼ ⊢F ⊢G x)
fst-subst* (x ⇨ t⇒t′) ⊢F ⊢G = (fst-subst ⊢F ⊢G x) ⇨ (fst-subst* t⇒t′ ⊢F ⊢G)

opaque

  -- emptyrec substitution of reduction closures
  emptyrec-subst* : Γ ⊢ t ⇒* t′ ∷ Empty
                  → Γ ⊢ A
                  → Γ ⊢ emptyrec p A t ⇒* emptyrec p A t′ ∷ A
  emptyrec-subst* (id x) ⊢A = id (emptyrecⱼ ⊢A x)
  emptyrec-subst* (x ⇨ d) ⊢A = emptyrec-subst ⊢A x ⇨ emptyrec-subst* d ⊢A

-- A variant of []-cong-subst for _⊢_⇒*_∷_.

[]-cong-subst* :
  Γ ⊢ A →
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ A →
  Γ ⊢ v₁ ⇒* v₂ ∷ Id A t u →
  []-cong-allowed s →
  let open Erased s in
    Γ ⊢ []-cong s A t u v₁ ⇒* []-cong s A t u v₂ ∷
      Id (Erased A) ([ t ]) ([ u ])
[]-cong-subst* ⊢A ⊢t ⊢u = λ where
  (id ⊢v₁)         ok → id ([]-congⱼ ⊢t ⊢u ⊢v₁ ok)
  (v₁⇒v₃ ⇨ v₃⇒*v₂) ok →
    []-cong-subst  ⊢A ⊢t ⊢u v₁⇒v₃  ok ⇨
    []-cong-subst* ⊢A ⊢t ⊢u v₃⇒*v₂ ok

-- A variant of []-cong-subst for _⊢_:⇒*:_∷_.

[]-cong-subst:*: :
  Γ ⊢ A →
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ A →
  Γ ⊢ v₁ :⇒*: v₂ ∷ Id A t u →
  []-cong-allowed s →
  let open Erased s in
    Γ ⊢ []-cong s A t u v₁ :⇒*: []-cong s A t u v₂ ∷
      Id (Erased A) ([ t ]) ([ u ])
[]-cong-subst:*: ⊢A ⊢t ⊢u [ ⊢v₁ , ⊢v₂ , v₁⇒*v₂ ] ok = record
  { ⊢t = []-congⱼ ⊢t ⊢u ⊢v₁ ok
  ; ⊢u = []-congⱼ ⊢t ⊢u ⊢v₂ ok
  ; d  = []-cong-subst* ⊢A ⊢t ⊢u v₁⇒*v₂ ok
  }
