------------------------------------------------------------------------
-- A non-dependent variant of ΠΣ⟨_⟩_,_▷_▹_
------------------------------------------------------------------------

-- Typing rules for the term former defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Non-dependent, and
-- usage rules can be found in Graded.Derived.Non-dependent.

open import Graded.Modality

module Definition.Untyped.Non-dependent
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n   : Nat
  A B : Term _
  σ   : Subst _ _
  ρ   : Wk _ _
  b   : BinderMode
  p   : M

opaque

  infixr 30 _⟶×⟨_⟩[_]_

  -- A non-dependent variant of ΠΣ⟨_⟩_,_▷_▹_.

  _⟶×⟨_⟩[_]_ : Term n → BinderMode → M → Term n → Term n
  A ⟶×⟨ b ⟩[ p ] B = ΠΣ⟨ b ⟩ p , 𝟘 ▷ A ▹ wk1 B

-- A non-dependent variant of Π_,_▷_▹_.

infixr 30 _⟶[_]_

_⟶[_]_ : Term n → M → Term n → Term n
A ⟶[ p ] B = A ⟶×⟨ BMΠ ⟩[ p ] B

-- A non-dependent variant of Σ⟨_⟩_,_▷_▹_.

infixr 30 _×⟨_⟩[_]_

_×⟨_⟩[_]_ : Term n → Strength → M → Term n → Term n
A ×⟨ s ⟩[ p ] B = A ⟶×⟨ BMΣ s ⟩[ p ] B

-- A non-dependent variant of Σˢ_,_▷_▹_.

infixr 30 _×ˢ[_]_

_×ˢ[_]_ : Term n → M → Term n → Term n
A ×ˢ[ p ] B = A ×⟨ 𝕤 ⟩[ p ] B

-- A non-dependent variant of Σʷ_,_▷_▹_.

infixr 30 _×ʷ[_]_

_×ʷ[_]_ : Term n → M → Term n → Term n
A ×ʷ[ p ] B = A ×⟨ 𝕨 ⟩[ p ] B

opaque
  unfolding _⟶×⟨_⟩[_]_

  -- A substitution lemma for _⟶×⟨_⟩[_]_.

  ⟶×⟨⟩[]-[] : A ⟶×⟨ b ⟩[ p ] B [ σ ] ≡ (A [ σ ]) ⟶×⟨ b ⟩[ p ] (B [ σ ])
  ⟶×⟨⟩[]-[] {A} {b} {p} {B} {σ} =
    ΠΣ⟨ b ⟩ p , 𝟘 ▷ A ▹ wk1 B [ σ ]            ≡⟨⟩
    ΠΣ⟨ b ⟩ p , 𝟘 ▷ A [ σ ] ▹ (wk1 B [ σ ⇑ ])  ≡⟨ cong (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹_) (wk1-liftSubst B) ⟩
    ΠΣ⟨ b ⟩ p , 𝟘 ▷ A [ σ ] ▹ wk1 (B [ σ ])    ∎

opaque

  -- A weakening lemma for _⟶×⟨_⟩[_]_.

  wk-⟶×⟨⟩[] : wk ρ (A ⟶×⟨ b ⟩[ p ] B) ≡ wk ρ A ⟶×⟨ b ⟩[ p ] wk ρ B
  wk-⟶×⟨⟩[] {ρ} {A} {b} {p} {B} =
    wk ρ (A ⟶×⟨ b ⟩[ p ] B)                           ≡⟨ wk≡subst _ _ ⟩
    A ⟶×⟨ b ⟩[ p ] B [ toSubst ρ ]                    ≡⟨ ⟶×⟨⟩[]-[] ⟩
    (A [ toSubst ρ ]) ⟶×⟨ b ⟩[ p ] (B [ toSubst ρ ])  ≡˘⟨ cong₂ _⟶×⟨ _ ⟩[ _ ]_ (wk≡subst _ _) (wk≡subst _ _) ⟩
    wk ρ A ⟶×⟨ b ⟩[ p ] wk ρ B                        ∎
