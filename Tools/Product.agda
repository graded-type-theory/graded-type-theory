------------------------------------------------------------------------
-- Σ type (also used as existential) and
-- cartesian product (also used as conjunction).
------------------------------------------------------------------------

module Tools.Product where

open import Level

open import Data.Product public
  using (Σ; ∃; ∃₂; _×_; _,_; proj₁; proj₂; map; curry; uncurry)
open import Relation.Nullary.Decidable public
  using (_×-dec_)

open import Tools.Relation

private variable
  a b c d e f g h i j : Level
  A B                 : Set _
  P                   : A → Set _

-- 4-tuples.

∃₃ :
  {A : Set a}
  {B : A → Set b}
  {C : (a : A) → B a → Set c} →
  (∀ a b → C a b → Set d) →
  Set (a ⊔ b ⊔ c ⊔ d)
∃₃ D = ∃ λ a → ∃₂ (D a)

-- 5-tuples.

∃₄ :
  {A : Set a}
  {B : A → Set b}
  {C : (a : A) → B a → Set c}
  {D : (a : A) (b : B a) → C a b → Set d} →
  (∀ a b c → D a b c → Set e) →
  Set (a ⊔ b ⊔ c ⊔ d ⊔ e)
∃₄ E = ∃ λ a → ∃₃ (E a)

-- 6-tuples.

∃₅ :
  {A : Set a}
  {B : A → Set b}
  {C : (a : A) → B a → Set c}
  {D : (a : A) (b : B a) → C a b → Set d}
  {E : (a : A) (b : B a) (c : C a b) → D a b c → Set e} →
  ((a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d → Set f) →
  Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f)
∃₅ F = ∃ λ a → ∃₄ (F a)

-- 7-tuples.

∃₆ :
  {A : Set a}
  {B : A → Set b}
  {C : (a : A) → B a → Set c}
  {D : (a : A) (b : B a) → C a b → Set d}
  {E : (a : A) (b : B a) (c : C a b) → D a b c → Set e}
  {F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d →
       Set f} →
  ((a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) →
   F a b c d e → Set g) →
  Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f ⊔ g)
∃₆ G = ∃ λ a → ∃₅ (G a)

-- 8-tuples.

∃₇ :
  {A : Set a}
  {B : A → Set b}
  {C : (a : A) → B a → Set c}
  {D : (a : A) (b : B a) → C a b → Set d}
  {E : (a : A) (b : B a) (c : C a b) → D a b c → Set e}
  {F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d →
       Set f}
  {G : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) →
       F a b c d e → Set g} →
  ((a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d)
   (f : F a b c d e) → G a b c d e f → Set h) →
  Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f ⊔ g ⊔ h)
∃₇ H = ∃ λ a → ∃₆ (H a)

-- 9-tuples.

∃₈ :
  {A : Set a}
  {B : A → Set b}
  {C : (a : A) → B a → Set c}
  {D : (a : A) (b : B a) → C a b → Set d}
  {E : (a : A) (b : B a) (c : C a b) → D a b c → Set e}
  {F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d →
       Set f}
  {G : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) →
       F a b c d e → Set g}
  {H : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d)
       (f : F a b c d e) → G a b c d e f → Set h} →
  ((a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d)
   (f : F a b c d e) (g : G a b c d e f) → H a b c d e f g → Set i) →
  Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f ⊔ g ⊔ h ⊔ i)
∃₈ I = ∃ λ a → ∃₇ (I a)

-- 10-tuples.

∃₉ :
  {A : Set a}
  {B : A → Set b}
  {C : (a : A) → B a → Set c}
  {D : (a : A) (b : B a) → C a b → Set d}
  {E : (a : A) (b : B a) (c : C a b) → D a b c → Set e}
  {F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d →
       Set f}
  {G : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) →
       F a b c d e → Set g}
  {H : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d)
       (f : F a b c d e) → G a b c d e f → Set h}
  {I : (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d)
   (f : F a b c d e) (g : G a b c d e f) → H a b c d e f g → Set i} →
  ((a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d)
   (f : F a b c d e) (g : G a b c d e f) (h : H a b c d e f g) →
   I a b c d e f g h → Set j) →
  Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f ⊔ g ⊔ h ⊔ i ⊔ j)
∃₉ J = ∃ λ a → ∃₈ (J a)

-- A generalisation of _×-dec_.

infixr 2 _×-dec′_

_×-dec′_ : Dec A → (A → Dec B) → Dec (A × B)
no ¬A ×-dec′ _ = no (λ (a , _) → ¬A a)
yes a ×-dec′ d with d a
… | yes b = yes (a , b)
… | no ¬B = no (λ (_ , b) → ¬B b)

-- A variant of _×-dec_ for Σ-types.

Σ-dec :
  Dec A → (∀ x y → P x → P y) → ((x : A) → Dec (P x)) → Dec (Σ A P)
Σ-dec (no ¬A) _   _ = no (λ (a , _) → ¬A a)
Σ-dec (yes a) irr d with d a
… | yes b = yes (a , b)
… | no ¬B = no (λ (_ , b) → ¬B (irr _ _ b))
