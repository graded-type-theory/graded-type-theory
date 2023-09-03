------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

module Tools.Relation where

open import Relation.Binary
  using ( Rel; _Preserves₂_⟶_⟶_
        ; Decidable; Reflexive; Symmetric; Transitive
        ; DecSetoid; Poset; Preorder; Setoid
        ; IsEquivalence; IsPartialOrder; IsPreorder
        )
  public
open import Relation.Nullary using (¬_; Dec; yes; no) public

-- If A and B are logically equivalent, then so are Dec A and Dec B.

map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → (B → A) → Dec A → Dec B
map f g (yes p) = yes (f p)
map f g (no ¬p) = no (λ x → ¬p (g x))
