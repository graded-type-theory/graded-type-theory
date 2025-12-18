------------------------------------------------------------------------
-- Constraints used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Constraints
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open import Definition.Typed.Decidable.Internal.Term TR

open import Tools.Function
open import Tools.Level
open import Tools.List
open import Tools.Product
open import Tools.Unit

private variable
  c : Constants
  γ : Contexts _

-- Constraints that can be returned by the type-checker and other
-- functions.

infixr 5 _∪_

data Constraints (c : Constants) : Set (lsuc a) where
  none : Constraints c
  con  : (Contexts c → Set a) → Constraints c
  _∪_  : (Cs₁ Cs₂ : Constraints c) → Constraints c

-- Turns constraints into a type family.

⟦_⟧′ : Constraints c → Contexts c → Set a
⟦ none      ⟧′ _ = Lift _ ⊤
⟦ con C     ⟧′ γ = C γ
⟦ Cs₁ ∪ Cs₂ ⟧′ γ = ⟦ Cs₁ ⟧′ γ × ⟦ Cs₂ ⟧′ γ

-- A smart constructor.
--
-- This constructor is used to make certain proofs a little easier.

infixr 5 _∪′_

_∪′_ : Constraints c → Constraints c → Constraints c
Cs   ∪′ none = Cs
none ∪′ Cs   = Cs
Cs₁  ∪′ Cs₂  = Cs₁ ∪ Cs₂

private

  -- Turns constraints into lists of constraints.

  to-list :
    Constraints c → List (Contexts c → Set a) →
    List (Contexts c → Set a)
  to-list none        Cs  = Cs
  to-list (con C)     Cs  = C ∷ Cs
  to-list (Cs₁ ∪ Cs₂) Cs₃ = to-list Cs₁ (to-list Cs₂ Cs₃)

  -- Turns a list of constraints into a type.

  as-type : List (Contexts c → Set a) → Contexts c → Set a
  as-type []       _ = Lift _ ⊤
  as-type (C ∷ []) γ = C γ
  as-type (C ∷ Cs) γ = C γ × as-type Cs γ

-- Turns constraints into a type family.

⟦_⟧ : Constraints c → Contexts c → Set a
⟦ Cs ⟧ γ = as-type (to-list Cs []) γ

opaque

  -- ⟦ Cs ⟧ γ is logically equivalent to ⟦ Cs ⟧′ γ.

  ⟦⟧⇔⟦⟧′ : ∀ Cs → ⟦ Cs ⟧ γ ⇔ ⟦ Cs ⟧′ γ
  ⟦⟧⇔⟦⟧′ Cs = (λ cs → to Cs cs .proj₁) , (λ cs → from Cs cs _)
    where
    to :
      ∀ {Cs′} Cs →
      as-type (to-list Cs Cs′) γ →
      ⟦ Cs ⟧′ γ × as-type Cs′ γ
    to none cont =
      lift tt , cont
    to {Cs′ = []} (con _) cont =
      cont , lift tt
    to {Cs′ = _ ∷ _} (con _) cont =
      cont
    to (Cs₁ ∪ Cs₂) cont =
      let cs₁ , cont = to Cs₁ cont in
      let cs₂ , cont = to Cs₂ cont in
      (cs₁ , cs₂) , cont

    from :
      ∀ {Cs′} Cs →
      ⟦ Cs ⟧′ γ →
      as-type Cs′ γ →
      as-type (to-list Cs Cs′) γ
    from                 none        _           cs  = cs
    from {Cs′ = []}    (con _)     cs          _   = cs
    from {Cs′ = _ ∷ _} (con _)     cs₁         cs₂ = cs₁ , cs₂
    from                 (Cs₁ ∪ Cs₂) (cs₁ , cs₂) cs₃ =
      from Cs₁ cs₁ (from Cs₂ cs₂ cs₃)

opaque

  -- ⟦ Cs₁ ∪ Cs₂ ⟧ γ is logically equivalent to ⟦ Cs₁ ⟧ γ × ⟦ Cs₂ ⟧ γ.

  ⟦∪⟧⇔⟦⟧×⟦⟧ : ∀ Cs₁ Cs₂ → ⟦ Cs₁ ∪ Cs₂ ⟧ γ ⇔ (⟦ Cs₁ ⟧ γ × ⟦ Cs₂ ⟧ γ)
  ⟦∪⟧⇔⟦⟧×⟦⟧ {γ} Cs₁ Cs₂ =
    ⟦ Cs₁ ∪ Cs₂ ⟧ γ          ⇔⟨ ⟦⟧⇔⟦⟧′ (Cs₁ ∪ Cs₂) ⟩
    ⟦ Cs₁ ∪ Cs₂ ⟧′ γ         ⇔⟨ id⇔ ⟩
    ⟦ Cs₁ ⟧′ γ × ⟦ Cs₂ ⟧′ γ  ⇔˘⟨ ⟦⟧⇔⟦⟧′ Cs₁ ×-cong-⇔ ⟦⟧⇔⟦⟧′ Cs₂ ⟩
    ⟦ Cs₁ ⟧ γ × ⟦ Cs₂ ⟧ γ    □⇔

opaque

  -- ⟦ Cs₁ ∪ Cs₂ ⟧′ γ is logically equivalent to ⟦ Cs₁ ∪′ Cs₂ ⟧′ γ.

  ⟦∪⟧′⇔⟦∪′⟧′ : ∀ Cs₁ Cs₂ → ⟦ Cs₁ ∪ Cs₂ ⟧′ γ ⇔ ⟦ Cs₁ ∪′ Cs₂ ⟧′ γ
  ⟦∪⟧′⇔⟦∪′⟧′ _       none    = proj₁ , (_, _)
  ⟦∪⟧′⇔⟦∪′⟧′ none    (con _) = proj₂ , (_ ,_)
  ⟦∪⟧′⇔⟦∪′⟧′ (con _) (con _) = id⇔
  ⟦∪⟧′⇔⟦∪′⟧′ (_ ∪ _) (con _) = id⇔
  ⟦∪⟧′⇔⟦∪′⟧′ none    (_ ∪ _) = proj₂ , (_ ,_)
  ⟦∪⟧′⇔⟦∪′⟧′ (con _) (_ ∪ _) = id⇔
  ⟦∪⟧′⇔⟦∪′⟧′ (_ ∪ _) (_ ∪ _) = id⇔
