-- Σ type (also used as existential) and
-- cartesian product (also used as conjunction).

module Tools.Product where

open import Level

open import Data.Product public using (Σ; ∃; ∃₂; _×_; _,_; proj₁; proj₂)

∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c}
     (D : (x : A) → (y : B x) → C x y → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ D = ∃ λ a → ∃ λ b → ∃ λ c → D a b c

∃₄ : ∀ {a b c d e} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} {D : (a : A) (b : B a) (c : C a b) → Set d}
   → (E : (x : A) → (y : B x) → (z : C x y) → (w : D x y z) → Set e) → Set (a ⊔ b ⊔ c ⊔ d ⊔ e)
∃₄ E = ∃ λ a → ∃ λ b → ∃ λ c → ∃ λ d → E a b c d
