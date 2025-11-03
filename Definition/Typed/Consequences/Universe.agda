------------------------------------------------------------------------
-- Some results about universes
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R
open import Definition.Typed.Consequences.Injectivity R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  l                     : Term _
  Γ                     : Con _ _
  p p₁ p₂ p₃ q q₁ q₂ q₃ : M

opaque

  -- It is not the case that U l has type U l (assuming that the
  -- context is empty or equality reflection is disallowed).

  ¬U∷U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ¬ Γ ⊢ U l ∷ U l
  ¬U∷U U∷U =
    t≢sucᵘt (U-injectivity (inversion-U U∷U))

opaque

  -- Type-in-type for arbitrary well-formed levels does not hold in a
  -- well-formed context Γ (assuming that Γ is empty or equality
  -- reflection is disallowed): it is not the case that, given a
  -- well-formed level l, U l has type U l.

  no-type-in-type :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ⊢ Γ →
    ¬ (∀ {l} → Γ ⊢ l ∷Level → Γ ⊢ U l ∷ U l)
  no-type-in-type ⊢Γ U∷U =
    ¬U∷U (U∷U (⊢zeroᵘ ⊢Γ))

opaque

  -- For any context Γ, the type of the universe-polymorphic identity
  -- function (with certain grades)
  --
  -- * is well-formed if Γ is, Level is allowed, and certain forms of
  --   Π-types are also allowed,
  --
  -- * does not have a type, and
  --
  -- * consequently does not live in any universe
  --
  -- (assuming that Γ is empty or equality reflection is not allowed).

  ¬ΠU∷U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    let A = Π p₁ , q₁ ▷ Level ▹
            Π p₂ , q₂ ▷ U (var x0) ▹
            Π p₃ , q₃ ▷ var x0 ▹ var x1
    in
    (Level-allowed →
     Π-allowed p₁ q₁ → Π-allowed p₂ q₂ → Π-allowed p₃ q₃ → ⊢ Γ →
     Γ ⊢ A) ×
    (¬ ∃ λ B → Γ ⊢ A ∷ B) ×
    (¬ ∃ λ l → Γ ⊢ A ∷ U l)
  ¬ΠU∷U =
    let ¬⊢∷ = λ (_ , ⊢A) →
          let l , ⊢l , ⊢Level , ⊢ΠU , _ , _  = inversion-ΠΣ-U ⊢A
              l′ , _ , ⊢U , _ , U≡U , _      = inversion-ΠΣ-U ⊢ΠU
              ⊢l                             =
                ⊢∷Level→⊢∷Level
                  (Level-allowed⇔⊎ .proj₂ $ inj₁ $
                   inversion-Level ⊢Level .proj₂)
                  ⊢l
          in
          ¬U∷U $
          conv (substTerm ⊢U ⊢l)
            (U (l′ [ l ]₀)     ≡˘⟨ substTypeEq U≡U (refl ⊢l) ⟩⊢∎≡
             U (wk1 l [ l ]₀)  ≡⟨ PE.cong U $ wk1-sgSubst _ _ ⟩
             U l               ∎)
    in
    (λ ok ok₁ ok₂ ok₃ ⊢Γ →
       ΠΣⱼ
         (ΠΣⱼ
            (ΠΣⱼ
               (univ (var₁ (univ (var₀ (⊢U′ (var₀ (Levelⱼ′ ok ⊢Γ)))))))
               ok₃)
            ok₂)
         ok₁) ,
    ¬⊢∷ ,
    ¬⊢∷ ∘→ Σ.map _ idᶠ

opaque

  -- There is a type that
  --
  -- * is well-formed if the context is and a certain form of Π-type
  --   is allowed,
  --
  -- * does not have a type, and
  --
  -- * consequently does not live in any universe
  --
  -- (assuming that equality reflection is not allowed).
  --
  -- Note that there is no assumption that Level is allowed. This
  -- result makes use of the fact that Π-types are homogeneous: if
  -- Π p , q ▷ A ▹ B has type U l, then A and B must both have type
  -- U l (in the latter case weakened).

  type-without-type :
    ⦃ ok : No-equality-reflection ⦄ →
    let A = Π p , q ▷ ℕ ▹ U zeroᵘ in
    (Π-allowed p q → ⊢ Γ → Γ ⊢ A) ×
    (¬ ∃ λ B → Γ ⊢ A ∷ B) ×
    (¬ ∃ λ l → Γ ⊢ A ∷ U l)
  type-without-type =
    let ¬⊢∷ = λ (_ , ⊢A) →
          let _ , _ , ⊢ℕ , ⊢U , _ , _ = inversion-ΠΣ-U ⊢A in
          ¬U∷U ⦃ ok = possibly-nonempty ⦄ $
          conv ⊢U (wkEq₁ (univ ⊢ℕ) (inversion-ℕ ⊢ℕ))
    in
    (λ ok ⊢Γ → ΠΣⱼ (⊢U₀ (∙ ⊢ℕ ⊢Γ)) ok) ,
    ¬⊢∷ ,
    ¬⊢∷ ∘→ Σ.map _ idᶠ
