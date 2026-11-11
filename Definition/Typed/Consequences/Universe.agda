------------------------------------------------------------------------
-- Some results about universes
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Typed.Consequences.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open Type-configuration TC

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Definition.Typed TC
open import Definition.Typed.Consequences.Inequality TC
open import Definition.Typed.Inversion TC
open import Definition.Typed.Properties TC
open import Definition.Typed.Reasoning.Type TC
open import Definition.Typed.Substitution TC
open import Definition.Typed.Well-formed TC
open import Definition.Typed.Consequences.Injectivity TC

open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  l                     : Lvl _
  Γ                     : Cons _ _
  p p₁ p₂ p₃ q q₁ q₂ q₃ : M

opaque

  -- It is not the case that U l has type U l (assuming that the
  -- variable context is empty or equality reflection is disallowed).

  ¬U∷U :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ U l ∷ U l
  ¬U∷U U∷U = ≢1ᵘ+ (U-injectivity (inversion-U U∷U))

opaque

  -- Type-in-type for arbitrary well-formed levels does not hold in a
  -- well-formed context Γ (assuming that Γ .vars is empty or equality
  -- reflection is disallowed): it is not the case that, given a
  -- well-formed level l, U l has type U l.

  no-type-in-type :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ⊢ Γ →
    ¬ (∀ {l} → Γ ⊢ l ∷Level → Γ ⊢ U l ∷ U l)
  no-type-in-type ⊢Γ U∷U =
    ¬U∷U (U∷U (⊢zeroᵘ ⊢Γ))

opaque

  -- For any context Γ a certain type
  --
  -- * is the type of a universe-polymorphic identity function if Γ is
  --   well-formed, Level is allowed, and certain forms of Π-types are
  --   allowed,
  --
  -- * does not have a type, and
  --
  -- * consequently does not live in any universe
  --
  -- (assuming that Γ .vars is empty or equality reflection is not
  -- allowed).

  a-type-of-id-does-not-have-a-type :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    let A = Π p₁ , q₁ ▷ Level ▹
            Π p₂ , q₂ ▷ U (level (var x0)) ▹
            Π p₃ , q₃ ▷ var x0 ▹ var x1
        t = lam p₁ (lam p₂ (lam p₃ (var x0)))
    in
    (Level-allowed →
     Π-allowed p₁ q₁ → Π-allowed p₂ q₂ → Π-allowed p₃ q₃ → ⊢ Γ →
     (Γ ⊢ A) × Γ ⊢ t ∷ A) ×
    (¬ ∃ λ B → Γ ⊢ A ∷ B) ×
    (¬ ∃ λ l → Γ ⊢ A ∷ U l)
  a-type-of-id-does-not-have-a-type =
    let ¬⊢∷ = λ (_ , ⊢A) →
          case inversion-ΠΣ-U ⊢A of λ where
            (ωᵘ+ _ , _ , ⊢Level , _) →
              level≢ωᵘ+ $ U-injectivity $ _⊢_≡_.sym $
              inversion-Level ⊢Level .proj₁
            (level l , ⊢l , ⊢Level , ⊢ΠU , _) →
              let l′ , _ , ⊢U , _ , U≡U , _ = inversion-ΠΣ-U ⊢ΠU
                  ⊢l                        =
                    ⊢∷Level→⊢∷Level
                      (Level-allowed⇔⊎ .proj₂ $ inj₁ $
                       inversion-Level ⊢Level .proj₂)
                      ⊢l
              in
              ¬U∷U $
              conv (subst-⊢₀ ⊢U ⊢l)
                (U (l′ [ l ]₀)             ≡˘⟨ subst-⊢≡₀ U≡U (refl ⊢l) ⟩⊢∎≡
                 U (wk1 (level l) [ l ]₀)  ≡⟨ PE.cong U $ wk1-sgSubst _ _ ⟩
                 U (level l)               ∎)
    in
    (λ ok ok₁ ok₂ ok₃ ⊢Γ →
       let ⊢t =
             lamⱼ′ ok₁ $
             lamⱼ′ ok₂ $
             lamⱼ′ ok₃ $
             var₀ (univ (var₀ (⊢U′ (var₀ (Levelⱼ′ ok ⊢Γ)))))
       in
       wf-⊢ ⊢t ,
       ⊢t) ,
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
  -- (assuming that equality reflection is not allowed or the variable
  -- context is empty).
  --
  -- Note that there is no assumption that Level is allowed. This
  -- result makes use of the fact that Π-types are homogeneous: if
  -- Π p , q ▷ A ▹ B has type U l, then A and B must both have type
  -- U l (in the latter case weakened).

  type-without-type :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    let A = Π p , q ▷ U₀ ▹ U (level (sucᵘ zeroᵘ)) in
    (Π-allowed p q → ⊢ Γ → Γ ⊢ A) ×
    (¬ ∃ λ B → Γ ⊢ A ∷ B) ×
    (¬ ∃ λ l → Γ ⊢ A ∷ U l)
  type-without-type =
    let ¬⊢∷ = λ (_ , ⊢A) →
          let _ , _ , ⊢U₀ , ⊢U₁ , _ = inversion-ΠΣ-U ⊢A in
          ¬U∷U $
          conv (subst-⊢₀ ⊢U₁ (Emptyⱼ (wf ⊢U₀)))
            (PE.subst (flip (_⊢_≡_ _) _) (PE.sym $ wk1-sgSubst _ _) $
             inversion-U ⊢U₀)
    in
    (λ ok ⊢Γ → ΠΣⱼ (⊢U (⊢1ᵘ+ (⊢zeroᵘ (∙ ⊢U₀ ⊢Γ)))) ok) ,
    ¬⊢∷ ,
    ¬⊢∷ ∘→ Σ.map _ idᶠ
