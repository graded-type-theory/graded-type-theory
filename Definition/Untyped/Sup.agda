------------------------------------------------------------------------
-- The term former _supᵘₗ_
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Untyped.Sup
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  n               : Nat
  ρ               : Wk _ _
  σ               : Subst _ _
  A B l l₁ l₂ t u : Term _
  b               : BinderMode
  p q             : M

opaque

  -- A variant of _supᵘ_.
  --
  -- If only level literals are allowed, and the inputs are
  -- literals, then a literal is returned.

  infixr 30 _supᵘₗ_

  _supᵘₗ_ : Term n → Term n → Term n
  l₁ supᵘₗ l₂ with level-support
  … | only-literals = l₁ supᵘₗ′ l₂
  … | level-type _  = l₁ supᵘ l₂

opaque
  unfolding _supᵘₗ_

  -- A weakening lemma for _supᵘₗ_.

  wk-supᵘₗ : wk ρ (l₁ supᵘₗ l₂) ≡ wk ρ l₁ supᵘₗ wk ρ l₂
  wk-supᵘₗ with level-support
  … | only-literals = wk-supᵘₗ′
  … | level-type _  = refl

opaque
  unfolding _supᵘₗ_

  -- A substitution lemma for _supᵘₗ_.

  supᵘₗ-[]′ :
    (¬ Level-allowed →
     Level-literal (l₁ [ σ ]) × Level-literal (l₂ [ σ ]) →
     Level-literal l₁ × Level-literal l₂) →
    l₁ supᵘₗ l₂ [ σ ] ≡ (l₁ [ σ ]) supᵘₗ (l₂ [ σ ])
  supᵘₗ-[]′ {l₁} {σ} {l₂} hyp with level-support in eq
  … | level-type _  = refl
  … | only-literals
    using not-ok ← ¬Level-allowed⇔ .proj₂ eq
    with Level-literal? (l₁ [ σ ]) ×-dec Level-literal? (l₂ [ σ ])
  … | yes both    = uncurry supᵘₗ′-[] (hyp not-ok both)
  … | no not-both =
    l₁ supᵘₗ′ l₂ [ σ ]            ≡⟨ (cong _[ _ ] $
                                      supᵘₗ′≡supᵘ λ (l₁-lit , l₂-lit) →
                                      not-both (Level-literal-[] l₁-lit , Level-literal-[] l₂-lit)) ⟩
    l₁ supᵘ l₂ [ σ ]              ≡⟨⟩
    (l₁ [ σ ]) supᵘ (l₂ [ σ ])    ≡˘⟨ supᵘₗ′≡supᵘ not-both ⟩
    (l₁ [ σ ]) supᵘₗ′ (l₂ [ σ ])  ∎

opaque
  unfolding _supᵘₗ_

  -- A "computation rule" for _supᵘₗ_.

  supᵘₗ≡supᵘ :
    Level-allowed →
    l₁ supᵘₗ l₂ ≡ l₁ supᵘ l₂
  supᵘₗ≡supᵘ ok with level-support in eq
  … | level-type _ =
    refl
  … | only-literals =
    ⊥-elim (¬Level-allowed⇔ .proj₂ eq ok)

opaque
  unfolding _supᵘₗ_

  -- A "computation rule" rule for _supᵘₗ_.

  supᵘₗ≡supᵘₗ′ :
    ¬ Level-allowed →
    l₁ supᵘₗ l₂ ≡ l₁ supᵘₗ′ l₂
  supᵘₗ≡supᵘₗ′ not-ok with level-support in eq
  … | only-literals =
    refl
  … | level-type _ =
    case trans (sym eq) (¬Level-allowed⇔ .proj₁ not-ok) of λ ()

opaque

  -- A variant of supᵘₗ≡supᵘₗ′.

  supᵘₗ≡↓ᵘ⊔ :
    ¬ Level-allowed →
    (l₁-lit : Level-literal l₁) (l₂-lit : Level-literal l₂) →
    l₁ supᵘₗ l₂ ≡ ↓ᵘ (size-of-Level l₁-lit ⊔ size-of-Level l₂-lit)
  supᵘₗ≡↓ᵘ⊔ {l₁} {l₂} not-ok l₁-lit l₂-lit =
    l₁ supᵘₗ l₂                                       ≡⟨ supᵘₗ≡supᵘₗ′ not-ok ⟩
    l₁ supᵘₗ′ l₂                                      ≡⟨ supᵘₗ′≡↓ᵘ⊔ l₁-lit l₂-lit ⟩
    ↓ᵘ (size-of-Level l₁-lit ⊔ size-of-Level l₂-lit)  ∎

opaque
  unfolding _supᵘₗ_

  -- If l₁ supᵘₗ l₂ is a level literal, then both l₁ and l₂ are level
  -- literals, and Level is not allowed.

  Level-literal-supᵘₗ→ :
    Level-literal (l₁ supᵘₗ l₂) →
    ¬ Level-allowed × Level-literal l₁ × Level-literal l₂
  Level-literal-supᵘₗ→ _     with level-support in eq
  Level-literal-supᵘₗ→ ()    | level-type _
  Level-literal-supᵘₗ→ ⊔-lit | only-literals =
    ¬Level-allowed⇔ .proj₂ eq , Level-literal-supᵘₗ′⇔ .proj₁ ⊔-lit

opaque

  -- If Level is not allowed, then l₁ supᵘₗ l₂ is a level literal if
  -- and only if l₁ and l₂ are.

  Level-literal-supᵘₗ⇔ :
    ¬ Level-allowed →
    Level-literal (l₁ supᵘₗ l₂) ⇔ (Level-literal l₁ × Level-literal l₂)
  Level-literal-supᵘₗ⇔ {l₁} {l₂} not-ok =
    let lemma = supᵘₗ≡supᵘₗ′ not-ok in
    Level-literal (l₁ supᵘₗ l₂)            ⇔⟨ subst Level-literal lemma
                                            , subst Level-literal (sym lemma)
                                            ⟩
    Level-literal (l₁ supᵘₗ′ l₂)           ⇔⟨ Level-literal-supᵘₗ′⇔ ⟩
    (Level-literal l₁ × Level-literal l₂)  □⇔

opaque

  -- If l₁ supᵘₗ l₂ [ σ ] is a level literal, then l₁ supᵘₗ l₂ is a
  -- level literal.

  Level-literal-supᵘₗ-[] :
    Level-literal (l₁ supᵘₗ l₂ [ σ ]) →
    Level-literal (l₁ supᵘₗ l₂)
  Level-literal-supᵘₗ-[] {l₁} {l₂} {σ} with Level-allowed?
  … | yes ok =
    Level-literal (l₁ supᵘₗ l₂ [ σ ])  ≡⟨ cong (Level-literal ∘→ _[ _ ]) (supᵘₗ≡supᵘ ok) ⟩→
    Level-literal (l₁ supᵘ l₂ [ σ ])   →⟨ (λ ()) ⟩
    Level-literal (l₁ supᵘₗ l₂)        □
  … | no not-ok
    with Level-literal? l₁ ×-dec Level-literal? l₂
  … | yes both =
    Level-literal (l₁ supᵘₗ l₂ [ σ ])    →⟨ (λ _ → both) ⟩
    Level-literal l₁ × Level-literal l₂  →⟨ Level-literal-supᵘₗ⇔ not-ok .proj₂ ⟩
    Level-literal (l₁ supᵘₗ l₂)          □
  … | no not-both =
    Level-literal (l₁ supᵘₗ l₂ [ σ ])   ≡⟨ cong (Level-literal ∘→ _[ _ ]) (supᵘₗ≡supᵘₗ′ not-ok) ⟩→
    Level-literal (l₁ supᵘₗ′ l₂ [ σ ])  ≡⟨ cong (Level-literal ∘→ _[ _ ]) (supᵘₗ′≡supᵘ not-both) ⟩→
    Level-literal (l₁ supᵘ l₂ [ σ ])    →⟨ (λ ()) ⟩
    Level-literal (l₁ supᵘₗ l₂)         □

opaque
  unfolding Level-literal-supᵘₗ⇔

  -- A lemma relating size-of-Level, Level-literal-supᵘₗ⇔ and _⊔_.

  size-of-Level-Level-literal-supᵘₗ⇔ :
    {not-ok : ¬ Level-allowed}
    {l₁-lit : Level-literal l₁}
    {l₂-lit : Level-literal l₂} →
    size-of-Level
      (Level-literal-supᵘₗ⇔ not-ok .proj₂ (l₁-lit , l₂-lit)) ≡
    size-of-Level l₁-lit ⊔ size-of-Level l₂-lit
  size-of-Level-Level-literal-supᵘₗ⇔ {not-ok} {l₁-lit} {l₂-lit} =
    size-of-Level
      (Level-literal-supᵘₗ⇔ not-ok .proj₂ (l₁-lit , l₂-lit))        ≡⟨ size-of-Level-subst ⟩

    size-of-Level (Level-literal-supᵘₗ′⇔ .proj₂ (l₁-lit , l₂-lit))  ≡⟨ size-of-Level-Level-literal-supᵘₗ′⇔ ⟩

    size-of-Level l₁-lit ⊔ size-of-Level l₂-lit                     ∎

opaque
  unfolding _supᵘₗ_ _supᵘₗ′_

  -- Applications of _supᵘₗ_ are equal to (applications of) ↓ᵘ_ or
  -- _supᵘ_.

  supᵘₗ≡ :
    (l₁ l₂ : Term n) →
    (∃ λ n → l₁ supᵘₗ l₂ ≡ ↓ᵘ n) ⊎ l₁ supᵘₗ l₂ ≡ l₁ supᵘ l₂
  supᵘₗ≡ l₁ l₂ with level-support
  … | level-type _  = inj₂ refl
  … | only-literals
    with Level-literal? l₁ ×-dec Level-literal? l₂
  …   | no _  = inj₂ refl
  …   | yes _ = inj₁ (_ , refl)

opaque

  -- Applications of _supᵘₗ_ are not equal to Level.

  supᵘₗ≢Level : l₁ supᵘₗ l₂ ≢ Level
  supᵘₗ≢Level {l₁} {l₂} eq with supᵘₗ≡ l₁ l₂
  … | inj₁ (0 , eq′)    = case trans (sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case trans (sym eq) eq′ of λ ()
  … | inj₂ eq′          = case trans (sym eq) eq′ of λ ()

opaque

  -- Applications of _supᵘₗ_ are not equal to applications of Lift.

  supᵘₗ≢Lift : l₁ supᵘₗ l₂ ≢ Lift l A
  supᵘₗ≢Lift {l₁} {l₂} eq with supᵘₗ≡ l₁ l₂
  … | inj₁ (0 , eq′)    = case trans (sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case trans (sym eq) eq′ of λ ()
  … | inj₂ eq′          = case trans (sym eq) eq′ of λ ()

opaque

  -- Applications of _supᵘₗ_ are not equal to applications of
  -- ΠΣ⟨_⟩_,_▷_▹_.

  supᵘₗ≢ΠΣ : l₁ supᵘₗ l₂ ≢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  supᵘₗ≢ΠΣ {l₁} {l₂} eq with supᵘₗ≡ l₁ l₂
  … | inj₁ (0 , eq′)    = case trans (sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case trans (sym eq) eq′ of λ ()
  … | inj₂ eq′          = case trans (sym eq) eq′ of λ ()

opaque

  -- Applications of _supᵘₗ_ are not equal to applications of Id.

  supᵘₗ≢Id : l₁ supᵘₗ l₂ ≢ Id A t u
  supᵘₗ≢Id {l₁} {l₂} eq with supᵘₗ≡ l₁ l₂
  … | inj₁ (0 , eq′)    = case trans (sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case trans (sym eq) eq′ of λ ()
  … | inj₂ eq′          = case trans (sym eq) eq′ of λ ()
