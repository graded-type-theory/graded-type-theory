module Tools.Function where

open import Function.Base
  using (case_of_; flip; _$_)
  renaming (id to idᶠ; _∘_ to _∘→_)
  public

-- Function composition (simply typed variant)
_∘ᶠ_ : ∀ {ℓ} → {A B C : Set ℓ} → (B → C) → (A → B) → A → C
_∘ᶠ_ f g a = f (g a)
