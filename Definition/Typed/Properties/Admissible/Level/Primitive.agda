------------------------------------------------------------------------
-- Admissible rules for Level as well as some lemmas related to
-- _⊢_≡_∷Level
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Level.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Nat as N using (Nat; 1+; _⊔_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  n                                  : Nat
  Γ                                  : Con Term _
  A B l l₁ l₁₁ l₁₂ l₂ l₂₁ l₂₂ l₃ t u : Term _
  b                                  : BinderMode
  p q                                : M

------------------------------------------------------------------------
-- A lemma related to Level

opaque
  unfolding Level-allowed Level-is-small Level-is-not-small

  -- A variant of _⊢_.Levelⱼ.

  Levelⱼ′ : Level-allowed → ⊢ Γ → Γ ⊢ Level
  Levelⱼ′ ok ⊢Γ with level-support in eq
  … | only-literals        = ⊥-elim (ok PE.refl)
  … | level-type small     = univ (Levelⱼ ⊢Γ eq)
  … | level-type not-small = Levelⱼ eq ⊢Γ

------------------------------------------------------------------------
-- Lemmas related to zeroᵘ and sucᵘ

opaque
  unfolding Level-allowed

  -- A variant of zeroᵘⱼ.

  ⊢zeroᵘ : ⊢ Γ → Γ ⊢ zeroᵘ ∷Level
  ⊢zeroᵘ ⊢Γ with level-support in eq
  … | only-literals = literal (_$ eq) ⊢Γ zeroᵘ
  … | level-type _  =
    let ok = λ eq′ → case PE.trans (PE.sym eq) eq′ of λ () in
    term ok (zeroᵘⱼ ok ⊢Γ)

opaque

  -- A variant of sucᵘⱼ.

  ⊢sucᵘ : Γ ⊢ l ∷Level → Γ ⊢ sucᵘ l ∷Level
  ⊢sucᵘ (term ok ⊢l)              = term ok (sucᵘⱼ ⊢l)
  ⊢sucᵘ (literal not-ok ⊢Γ l-lit) = literal not-ok ⊢Γ (sucᵘ l-lit)

------------------------------------------------------------------------
-- A lemma related to Level-literal

opaque

  -- If l is a level literal, then l is a well-formed level in
  -- well-formed contexts.

  Level-literal→⊢∷Level : ⊢ Γ → Level-literal l → Γ ⊢ l ∷Level
  Level-literal→⊢∷Level ⊢Γ zeroᵘ        = ⊢zeroᵘ ⊢Γ
  Level-literal→⊢∷Level ⊢Γ (sucᵘ l-lit) =
    ⊢sucᵘ (Level-literal→⊢∷Level ⊢Γ l-lit)

------------------------------------------------------------------------
-- Some lemmas related to _⊢_∷Level or _⊢_≡_∷Level

opaque

  -- Reflexivity for _⊢_≡_∷Level.

  refl-⊢≡∷L : Γ ⊢ l ∷Level → Γ ⊢ l ≡ l ∷Level
  refl-⊢≡∷L (term ok ⊢l)              = term ok (refl ⊢l)
  refl-⊢≡∷L (literal not-ok ⊢Γ l-lit) = literal not-ok ⊢Γ l-lit

opaque

  -- Symmetry for _⊢_≡_∷Level.

  sym-⊢≡∷L : Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₂ ≡ l₁ ∷Level
  sym-⊢≡∷L (term ok l₁≡l₂) =
    term ok (sym (Levelⱼ′ ok (wfEqTerm l₁≡l₂)) l₁≡l₂)
  sym-⊢≡∷L (literal not-ok ⊢Γ l-lit) =
    literal not-ok ⊢Γ l-lit

opaque

  -- Transitivity for _⊢_≡_∷Level.

  trans-⊢≡∷L :
    Γ ⊢ l₁ ≡ l₂ ∷Level → Γ ⊢ l₂ ≡ l₃ ∷Level → Γ ⊢ l₁ ≡ l₃ ∷Level
  trans-⊢≡∷L (term ok l₁≡l₂) (term _ l₂≡l₃) =
    term ok (trans l₁≡l₂ l₂≡l₃)
  trans-⊢≡∷L (term ok _) (literal not-ok _ _) =
    ⊥-elim (not-ok ok)
  trans-⊢≡∷L (literal not-ok _ _) (term ok _) =
    ⊥-elim (not-ok ok)
  trans-⊢≡∷L (literal not-ok ⊢Γ l-lit) (literal _ _ _) =
    literal not-ok ⊢Γ l-lit

------------------------------------------------------------------------
-- A lemma related to _supᵘ_

opaque

  -- The level zeroᵘ is a right unit for _supᵘ_ (if Level is allowed).

  supᵘ-zeroʳⱼ :
    Level-allowed →
    Γ ⊢ l ∷ Level →
    Γ ⊢ l supᵘ zeroᵘ ≡ l ∷ Level
  supᵘ-zeroʳⱼ ok ⊢l =
    trans (supᵘ-comm ⊢l (zeroᵘⱼ ok (wfTerm ⊢l))) (supᵘ-zeroˡ ⊢l)

------------------------------------------------------------------------
-- Some lemmas related to _supᵘₗ_

opaque
  unfolding _supᵘₗ_

  -- A "computation rule" for _supᵘₗ_.

  supᵘₗ≡supᵘ :
    Level-allowed →
    l₁ supᵘₗ l₂ PE.≡ l₁ supᵘ l₂
  supᵘₗ≡supᵘ ok with level-support in eq
  … | level-type _ =
    PE.refl
  … | only-literals =
    ⊥-elim (¬Level-allowed⇔ .proj₂ eq ok)

opaque
  unfolding _supᵘₗ_

  -- A "computation rule" rule for _supᵘₗ_.

  supᵘₗ≡supᵘₗ′ :
    ¬ Level-allowed →
    l₁ supᵘₗ l₂ PE.≡ l₁ supᵘₗ′ l₂
  supᵘₗ≡supᵘₗ′ not-ok with level-support in eq
  … | only-literals =
    PE.refl
  … | level-type _ =
    case PE.trans (PE.sym eq) (¬Level-allowed⇔ .proj₁ not-ok) of λ ()

opaque

  -- A variant of supᵘₗ≡supᵘₗ′.

  supᵘₗ≡↓ᵘ⊔ :
    ¬ Level-allowed →
    (l₁-lit : Level-literal l₁) (l₂-lit : Level-literal l₂) →
    l₁ supᵘₗ l₂ PE.≡ ↓ᵘ (size-of-Level l₁-lit ⊔ size-of-Level l₂-lit)
  supᵘₗ≡↓ᵘ⊔ {l₁} {l₂} not-ok l₁-lit l₂-lit =
    l₁ supᵘₗ l₂                                       ≡⟨ supᵘₗ≡supᵘₗ′ not-ok ⟩
    l₁ supᵘₗ′ l₂                                      ≡⟨ supᵘₗ′≡↓ᵘ⊔ l₁-lit l₂-lit ⟩
    ↓ᵘ (size-of-Level l₁-lit ⊔ size-of-Level l₂-lit)  ∎

opaque

  -- If Level is not allowed, then l₁ supᵘₗ l₂ is a level literal if
  -- and only if l₁ and l₂ are.

  Level-literal-supᵘₗ⇔ :
    ¬ Level-allowed →
    Level-literal (l₁ supᵘₗ l₂) ⇔ (Level-literal l₁ × Level-literal l₂)
  Level-literal-supᵘₗ⇔ {l₁} {l₂} not-ok =
    let lemma = supᵘₗ≡supᵘₗ′ not-ok in
    Level-literal (l₁ supᵘₗ l₂)            ⇔⟨ PE.subst Level-literal lemma
                                            , PE.subst Level-literal (PE.sym lemma)
                                            ⟩
    Level-literal (l₁ supᵘₗ′ l₂)           ⇔⟨ Level-literal-supᵘₗ′⇔ ⟩
    (Level-literal l₁ × Level-literal l₂)  □⇔

opaque
  unfolding Level-literal-supᵘₗ⇔

  -- A lemma relating size-of-Level, Level-literal-supᵘₗ⇔ and _⊔_.

  size-of-Level-Level-literal-supᵘₗ⇔ :
    {not-ok : ¬ Level-allowed}
    {l₁-lit : Level-literal l₁}
    {l₂-lit : Level-literal l₂} →
    size-of-Level
      (Level-literal-supᵘₗ⇔ not-ok .proj₂ (l₁-lit , l₂-lit)) PE.≡
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
    (∃ λ n → l₁ supᵘₗ l₂ PE.≡ ↓ᵘ n) ⊎ l₁ supᵘₗ l₂ PE.≡ l₁ supᵘ l₂
  supᵘₗ≡ l₁ l₂ with level-support
  … | level-type _  = inj₂ PE.refl
  … | only-literals
    with Level-literal? l₁ ×-dec Level-literal? l₂
  …   | no _  = inj₂ PE.refl
  …   | yes _ = inj₁ (_ , PE.refl)

opaque

  -- Applications of _supᵘₗ_ are not equal to Level.

  supᵘₗ≢Level : l₁ supᵘₗ l₂ PE.≢ Level
  supᵘₗ≢Level {l₁} {l₂} eq with supᵘₗ≡ l₁ l₂
  … | inj₁ (0 , eq′)    = case PE.trans (PE.sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case PE.trans (PE.sym eq) eq′ of λ ()
  … | inj₂ eq′          = case PE.trans (PE.sym eq) eq′ of λ ()

opaque

  -- Applications of _supᵘₗ_ are not equal to applications of Lift.

  supᵘₗ≢Lift : l₁ supᵘₗ l₂ PE.≢ Lift l A
  supᵘₗ≢Lift {l₁} {l₂} eq with supᵘₗ≡ l₁ l₂
  … | inj₁ (0 , eq′)    = case PE.trans (PE.sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case PE.trans (PE.sym eq) eq′ of λ ()
  … | inj₂ eq′          = case PE.trans (PE.sym eq) eq′ of λ ()

opaque

  -- Applications of _supᵘₗ_ are not equal to applications of
  -- ΠΣ⟨_⟩_,_▷_▹_.

  supᵘₗ≢ΠΣ : l₁ supᵘₗ l₂ PE.≢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  supᵘₗ≢ΠΣ {l₁} {l₂} eq with supᵘₗ≡ l₁ l₂
  … | inj₁ (0 , eq′)    = case PE.trans (PE.sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case PE.trans (PE.sym eq) eq′ of λ ()
  … | inj₂ eq′          = case PE.trans (PE.sym eq) eq′ of λ ()

opaque

  -- Applications of _supᵘₗ_ are not equal to applications of Id.

  supᵘₗ≢Id : l₁ supᵘₗ l₂ PE.≢ Id A t u
  supᵘₗ≢Id {l₁} {l₂} eq with supᵘₗ≡ l₁ l₂
  … | inj₁ (0 , eq′)    = case PE.trans (PE.sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case PE.trans (PE.sym eq) eq′ of λ ()
  … | inj₂ eq′          = case PE.trans (PE.sym eq) eq′ of λ ()

opaque

  -- A variant of supᵘⱼ.

  ⊢supᵘₗ : Γ ⊢ l₁ ∷Level → Γ ⊢ l₂ ∷Level → Γ ⊢ l₁ supᵘₗ l₂ ∷Level
  ⊢supᵘₗ (term ok ⊢l₁) (term _ ⊢l₂) =
    PE.subst (_⊢_∷Level _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘⱼ ⊢l₁ ⊢l₂)
  ⊢supᵘₗ (term ok _) (literal not-ok _ _) =
    ⊥-elim (not-ok ok)
  ⊢supᵘₗ (literal not-ok _ _) (term ok _) =
    ⊥-elim (not-ok ok)
  ⊢supᵘₗ (literal not-ok ⊢Γ l₁-lit) (literal _ _ l₂-lit) =
    PE.subst (_⊢_∷Level _) (PE.sym $ supᵘₗ≡supᵘₗ′ not-ok) $
    literal not-ok ⊢Γ (Level-literal-supᵘₗ′⇔ .proj₂ (l₁-lit , l₂-lit))

opaque

  -- The operator _supᵘₗ_ preserves equality.

  supᵘₗ-cong :
    Γ ⊢ l₁₁ ≡ l₂₁ ∷Level →
    Γ ⊢ l₁₂ ≡ l₂₂ ∷Level →
    Γ ⊢ l₁₁ supᵘₗ l₁₂ ≡ l₂₁ supᵘₗ l₂₂ ∷Level
  supᵘₗ-cong (term ok l₁₁≡l₂₁) (term _ l₁₂≡l₂₂) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡supᵘ ok) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-cong l₁₁≡l₂₁ l₁₂≡l₂₂)
  supᵘₗ-cong (term ok _) (literal not-ok _ _) =
    ⊥-elim (not-ok ok)
  supᵘₗ-cong (literal not-ok _ _) (term ok _) =
    ⊥-elim (not-ok ok)
  supᵘₗ-cong (literal not-ok ⊢Γ l₁-lit) (literal _ _ l₂-lit) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok l₁-lit l₂-lit)
      (PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok l₁-lit l₂-lit) $
    literal not-ok ⊢Γ Level-literal-↓ᵘ

opaque

  -- The operator _supᵘₗ_ is commutative.

  supᵘₗ-comm :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ l₁ supᵘₗ l₂ ≡ l₂ supᵘₗ l₁ ∷Level
  supᵘₗ-comm (term ok ⊢l₁) (term _ ⊢l₂) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡supᵘ ok) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-comm ⊢l₁ ⊢l₂)
  supᵘₗ-comm (term ok _) (literal not-ok _ _) =
    ⊥-elim (not-ok ok)
  supᵘₗ-comm (literal not-ok _ _) (term ok _) =
    ⊥-elim (not-ok ok)
  supᵘₗ-comm (literal not-ok ⊢Γ l₁-lit) (literal _ _ l₂-lit) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok l₁-lit l₂-lit)
      (PE.trans (PE.cong ↓ᵘ_ (N.⊔-comm (size-of-Level _) _)) $
       PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok l₂-lit l₁-lit) $
    literal not-ok ⊢Γ Level-literal-↓ᵘ

opaque
  unfolding size-of-Level

  -- The level zeroᵘ is a left identity for _supᵘₗ_.

  supᵘₗ-identityˡ :
    Γ ⊢ l ∷Level →
    Γ ⊢ zeroᵘ supᵘₗ l ≡ l ∷Level
  supᵘₗ-identityˡ (term ok ⊢l) =
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-zeroˡ ⊢l)
  supᵘₗ-identityˡ (literal not-ok ⊢Γ l-lit) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok zeroᵘ l-lit)
      ↓ᵘ-size-of-Level $
    literal not-ok ⊢Γ Level-literal-↓ᵘ

------------------------------------------------------------------------
-- Some lemmas related to _⊢_∷Level or _⊢_≡_∷Level

opaque

  -- If Γ ⊢ l ∷Level holds and Level is allowed, then Γ ⊢ l ∷ Level
  -- holds.

  ⊢∷Level→⊢∷Level :
    Level-allowed →
    Γ ⊢ l ∷Level →
    Γ ⊢ l ∷ Level
  ⊢∷Level→⊢∷Level _  (term _ ⊢l)          = ⊢l
  ⊢∷Level→⊢∷Level ok (literal not-ok _ _) = ⊥-elim (not-ok ok)

opaque

  -- If Γ ⊢ l₁ ≡ l₂ ∷Level holds and Level is allowed, then
  -- Γ ⊢ l₁ ≡ l₂ ∷ Level holds.

  ⊢≡∷Level→⊢≡∷Level :
    Level-allowed →
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ l₁ ≡ l₂ ∷ Level
  ⊢≡∷Level→⊢≡∷Level _  (term _ l₁≡l₂)       = l₁≡l₂
  ⊢≡∷Level→⊢≡∷Level ok (literal not-ok _ _) = ⊥-elim (not-ok ok)

opaque

  -- If Γ ⊢ l₁ ≤ₗ l₂ ∷Level holds and Level is allowed, then
  -- Γ ⊢ l₁ ≤ l₂ ∷Level holds.

  ⊢≤ₗ∷Level→⊢≤∷Level :
    Level-allowed →
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ l₁ ≤ l₂ ∷Level
  ⊢≤ₗ∷Level→⊢≤∷Level ok l₁≤l₂ = ⊢≤ₗ∷Level→⊢≤∷Level′ l₁≤l₂ PE.refl
    where
    ⊢≤ₗ∷Level→⊢≤∷Level′ :
      Γ ⊢ l ≡ l₂ ∷Level →
      l PE.≡ l₁ supᵘₗ l₂ →
      Γ ⊢ l₁ ≤ l₂ ∷Level
    ⊢≤ₗ∷Level→⊢≤∷Level′ (term _ l₁≤l₂) PE.refl =
      PE.subst₃ (_⊢_≡_∷_ _) (supᵘₗ≡supᵘ ok) PE.refl PE.refl l₁≤l₂
    ⊢≤ₗ∷Level→⊢≤∷Level′ (literal not-ok _ _) _ =
      ⊥-elim (not-ok ok)
