------------------------------------------------------------------------
-- Some examples showing how Definition.Typed.Decidable.Internal can
-- be used
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Examples
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR

open import Definition.Typed TR
open import Definition.Typed.Decidable.Internal TR
import Definition.Typed.Decidable.Internal.Context TR as C
import Definition.Typed.Decidable.Internal.Term 𝕄 as I
import Definition.Typed.Decidable.Internal.Substitution 𝕄 as S
import Definition.Typed.Decidable.Internal.Weakening 𝕄 as W
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties.Well-formed TR
open import Definition.Typed.Substitution.Primitive TR
open import Definition.Typed.Weakening.Definition TR
open import Definition.Typed.Well-formed TR

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
import Tools.Level as L
open import Tools.Maybe
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Vec as V

private variable
  m n         : Nat
  c           : I.Constants
  Δ           : Con _ _
  A B t u v w : Term _
  p           : M

opaque

  -- An example.
  --
  -- One of the terms contains a β-redex, so a type annotation is
  -- used.

  let-α≡zero-in-λλ0∘zero≡λα :
    Π-allowed ω ω →
    Unit-allowed 𝕤 →
    ε ∙⟨ tra ⟩[ zero ∷ ℕ ] » ε ⊢
      lam ω (lam ω (var x0) ∘⟨ ω ⟩ zero) ≡
      lam ω (defn 0) ∷
      Π ω , ω ▷ Unit 𝕤 0 ▹ ℕ
  let-α≡zero-in-λλ0∘zero≡λα ok₁ ok₂ =
    check-and-equal-cons-type-and-terms-sound
      (I.empty-Contexts false)
      (I.ε I.∙⟨ tra ⟩[ I.zero ∷ I.ℕ ] I.» I.ε)
      (I.lam I.ω nothing $
       I.lam I.ω (just (I.ω , I.ℕ)) (I.var x0) I.∘⟨ I.ω ⟩ I.zero)
      (I.lam I.ω nothing (I.defn 0))
      (I.Π I.ω , I.ω ▷ I.Unit I.𝕤 I.zero ▹ I.ℕ)
      10
      PE.refl
      (ok₂ , ok₁ , ok₁ , ok₂ , ok₁ , ok₁ , ok₁ , ok₁ , ok₂ , ok₁)
      (C.Meta-con-wf-empty PE.refl)
      ε
      (λ ())

opaque

  -- An example.
  --
  -- Leaving the variable context as a meta-level variable works fine.
  -- Leaving an initial prefix of the definition context as a
  -- meta-level variable with a non-literal size might not work so
  -- well if any definitions from the suffix are used, because of the
  -- use of de Bruijn levels: if the context's length is unknown
  -- (something like 2+ n where n is a meta-level variable), how do
  -- you know what definition a given level refers to?

  let-α≡zero-in-let-β≡λ0-in-λβ∙zero≡λα :
    ε »⊢ Δ →
    Π-allowed ω ω →
    Unit-allowed 𝕤 →
    ε ∙⟨ tra ⟩[ zero ∷ ℕ ]
      ∙⟨ tra ⟩[ lam ω (var x0) ∷ Π ω , ω ▷ ℕ ▹ ℕ ]
      » Δ ⊢
      lam ω (defn 1 ∘⟨ ω ⟩ zero) ≡
      lam ω (defn 0) ∷
      Π ω , ω ▷ Unit 𝕤 0 ▹ ℕ
  let-α≡zero-in-let-β≡λ0-in-λβ∙zero≡λα {Δ} ⊢Δ ok₁ ok₂ =
    check-and-equal-type-and-terms-sound
      {c = record { base-con-allowed = true }}
      (record
         { grades       = V.ε
         ; levels       = V.ε
         ; strengths    = V.ε
         ; binder-modes = V.ε
         ; metas        = I.emptyᶜᵐ
         ; ⌜base⌝       = ε » Δ
         })
      (I.ε I.∙⟨ tra ⟩[ I.zero ∷ I.ℕ ]
           I.∙⟨ tra ⟩[ I.lam I.ω nothing (I.var x0) ∷
                       I.Π I.ω , I.ω ▷ I.ℕ ▹ I.ℕ ] I.»
           I.base)
      (I.lam I.ω nothing (I.defn 1 I.∘⟨ I.ω ⟩ I.zero))
      (I.lam I.ω nothing (I.defn 0))
      (I.Π I.ω , I.ω ▷ I.Unit I.𝕤 I.zero ▹ I.ℕ)
      10
      PE.refl
      (ok₂ , ok₁ , ok₂ , ok₁ , ok₂ , ok₁)
      (C.Meta-con-wf-empty PE.refl)
      (flip defn-wk′ ⊢Δ $ »⊇ε $
       check-dcon-sound
         (I.empty-Contexts false)
         (I.ε I.∙⟨ tra ⟩[ I.zero ∷ I.ℕ ]
              I.∙⟨ tra ⟩[ I.lam I.ω nothing (I.var x0) ∷
                          I.Π I.ω , I.ω ▷ I.ℕ ▹ I.ℕ ])
         6
         PE.refl
         ok₁
         ε)

opaque
  unfolding subst

  -- An example that includes use of a meta-variable context.

  ⊢subst′ :
    {Γ : Cons m n} →
    Γ »∙ A ⊢ B →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ w ∷ B [ t ]₀ →
    Γ ⊢ subst p A B t u v w ∷ B [ u ]₀
  ⊢subst′ {m} {n} {A} {B} {v} {t} {u} {w} {p} {Γ} ⊢B ⊢v ⊢w =
    let ⊢A , ⊢t , ⊢u = inversion-Id (wf-⊢∷ ⊢v) in
    check-type-and-term-sound
      γ′
      (I.base nothing I.» I.base)
      (substᵢ (I.var x0) (I.varᵐ x0) (I.varᵐ x1) (I.varᵐ x2) (I.varᵐ x3)
         (I.varᵐ x4) (I.varᵐ x5))
      (I.subst (I.varᵐ x1) (S.sgSubst (I.varᵐ x3)))
      9
      PE.refl
      _
      (record
         { bindings-wf = λ where
             (I.var! x0)       → ⊢A
             (I.var! x1)       → ⊢B
             (I.var! x2)       → ⊢t
             (I.var! x3)       → ⊢u
             (I.var! x4)       → ⊢v
             (I.var! x5)       → ⊢w
             (I.var  not-x6 _)
         })
      (wfTerm ⊢v)
      where
      c′ : I.Constants
      c′ .I.gs               = 1
      c′ .I.ls               = 0
      c′ .I.ss               = 0
      c′ .I.bms              = 0
      c′ .I.ms               = 6
      c′ .I.base-dcon-size   = m
      c′ .I.base-con-allowed = true
      c′ .I.base-con-size    = n
      c′ .I.meta-con-size    =
        n V.∷ 1+ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ V.ε

      γ′ : I.Contexts c′
      γ′ .I.grades            = p V.∷ V.ε
      γ′ .I.levels            = V.ε
      γ′ .I.strengths         = V.ε
      γ′ .I.binder-modes      = V.ε
      γ′ .I.⌜base⌝            = Γ
      γ′ .I.metas .I.bindings = λ where
        (I.var! x0) → I.base , I.type A
        (I.var! x1) → I.base I.∙ I.varᵐ x0 , I.type B
        (I.var! x2) → I.base , I.term t (I.varᵐ x0)
        (I.var! x3) → I.base , I.term u (I.varᵐ x0)
        (I.var! x4) →
          I.base , I.term v (I.Id (I.varᵐ x0) (I.varᵐ x2) (I.varᵐ x3))
        (I.var! x5) →
          I.base ,
          I.term w (I.subst (I.varᵐ x1) (S.sgSubst (I.varᵐ x2)))
        (I.var not-x6 _)

opaque
  unfolding cong subst

  -- An example.
  --
  -- Note that this lemma does not make use of ⊢subst′, even though
  -- cong is constructed using subst, because subst is not a term but
  -- a term former that takes a number of arguments on the meta-level.

  ⊢cong′ :
    {Γ : Cons m n} →
    Γ »∙ A ⊢ v ∷ wk1 B →
    Γ ⊢ w ∷ Id A t u →
    Γ ⊢ cong p A t u B v w ∷ Id B (v [ t ]₀) (v [ u ]₀)
  ⊢cong′ {m} {n} {A} {v} {B} {w} {t} {u} {p} {Γ} ⊢v ⊢w =
    let ⊢A , ⊢t , ⊢u = inversion-Id (wf-⊢∷ ⊢w)
        ⊢B           = PE.subst (_⊢_ _) (wk1-sgSubst B _) $
                       substType (wf-⊢∷ ⊢v) ⊢t
    in
    check-type-and-term-sound
      γ′
      (I.base nothing I.» I.base)
      (congᵢ (I.var x0) (I.varᵐ x0) (I.varᵐ x1) (I.varᵐ x2) (I.varᵐ x3)
         (I.varᵐ x4) (I.varᵐ x5))
      (I.Id (I.varᵐ x3) (I.subst (I.varᵐ x4) (S.sgSubst (I.varᵐ x1)))
         (I.subst (I.varᵐ x4) (S.sgSubst (I.varᵐ x2))))
      10
      PE.refl
      _
      (record
         { bindings-wf = λ where
             (I.var! x0)       → ⊢A
             (I.var! x1)       → ⊢t
             (I.var! x2)       → ⊢u
             (I.var! x3)       → ⊢B
             (I.var! x4)       → ⊢v
             (I.var! x5)       → ⊢w
             (I.var  not-x6 _)
         })
      (wfTerm ⊢w)
      where
      c′ : I.Constants
      c′ .I.gs               = 1
      c′ .I.ls               = 0
      c′ .I.ss               = 0
      c′ .I.bms              = 0
      c′ .I.ms               = 6
      c′ .I.base-dcon-size   = m
      c′ .I.base-con-allowed = true
      c′ .I.base-con-size    = n
      c′ .I.meta-con-size    =
        n V.∷ n V.∷ n V.∷ n V.∷ 1+ n V.∷ n V.∷ V.ε

      γ′ : I.Contexts c′
      γ′ .I.grades            = p V.∷ V.ε
      γ′ .I.levels            = V.ε
      γ′ .I.strengths         = V.ε
      γ′ .I.binder-modes      = V.ε
      γ′ .I.⌜base⌝            = Γ
      γ′ .I.metas .I.bindings = λ where
        (I.var! x0) → I.base , I.type A
        (I.var! x1) → I.base , I.term t (I.varᵐ x0)
        (I.var! x2) → I.base , I.term u (I.varᵐ x0)
        (I.var! x3) → I.base , I.type B
        (I.var! x4) →
          I.base I.∙ I.varᵐ x0 ,
          I.term v (W.wk[ 1 ] (I.varᵐ x3))
        (I.var! x5) →
          I.base , I.term w (I.Id (I.varᵐ x0) (I.varᵐ x1) (I.varᵐ x2))
        (I.var not-x6 _)
