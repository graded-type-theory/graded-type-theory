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
open import
  Definition.Typed.Properties.Admissible.Identity.Very-primitive TR
open import Definition.Typed.Properties.Well-formed TR
open import Definition.Typed.Stability TR
open import Definition.Typed.Substitution.Primitive TR
open import Definition.Typed.Weakening TR
open import Definition.Typed.Weakening.Definition TR
open import Definition.Typed.Well-formed TR

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
import Tools.Level as L
import Tools.List as L
open import Tools.Maybe
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Vec as V

private variable
  m n                                             : Nat
  c                                               : I.Constants
  Δ                                               : Con _ _
  A A₁ A₂ B B₁ B₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  p                                               : M

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
      (record (I.empty-Contexts false)
         { constraints =
             I.π-allowed I.ω I.ω L.∷
             I.unit-allowed I.𝕤  L.∷
             L.[]
         })
      (I.ε I.∙⟨ tra ⟩[ I.zero ∷ I.ℕ ] I.» I.ε)
      (I.lam I.ω nothing $
       I.lam I.ω (just (I.ω , I.ℕ)) (I.var x0) I.∘⟨ I.ω ⟩ I.zero)
      (I.lam I.ω nothing (I.defn 0))
      (I.Π I.ω , I.ω ▷ I.Unit I.𝕤 I.zero ▹ I.ℕ)
      10
      PE.refl
      (record
         { metas-wf       = C.Meta-con-wf-empty PE.refl
         ; constraints-wf = ok₁ L.∷ ok₂ L.∷ L.[]
         })
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
         ; constraints  =
             I.π-allowed I.ω I.ω L.∷
             I.unit-allowed I.𝕤  L.∷
             L.[]
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
      (record
         { metas-wf       = C.Meta-con-wf-empty PE.refl
         ; constraints-wf = ok₁ L.∷ ok₂ L.∷ L.[]
         })
      (flip defn-wk′ ⊢Δ $ »⊇ε $
       check-dcon-sound
         (record (I.empty-Contexts false)
            { constraints =
                I.π-allowed I.ω I.ω L.∷
                L.[]
            })
         (I.ε I.∙⟨ tra ⟩[ I.zero ∷ I.ℕ ]
              I.∙⟨ tra ⟩[ I.lam I.ω nothing (I.var x0) ∷
                          I.Π I.ω , I.ω ▷ I.ℕ ▹ I.ℕ ])
         6
         PE.refl
         (ok₁ L.∷ L.[])
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
      (λ where
         .C.constraints-wf            → L.[]
         .C.metas-wf .C.equalities-wf → L.[]
         .C.metas-wf .C.bindings-wf   → λ where
           (I.var! x0)       → ⊢A
           (I.var! x1)       → ⊢B
           (I.var! x2)       → ⊢t
           (I.var! x3)       → ⊢u
           (I.var! x4)       → ⊢v
           (I.var! x5)       → ⊢w
           (I.var  not-x6 _))
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
      γ′ .I.grades              = p V.∷ V.ε
      γ′ .I.levels              = V.ε
      γ′ .I.strengths           = V.ε
      γ′ .I.binder-modes        = V.ε
      γ′ .I.⌜base⌝              = Γ
      γ′ .I.constraints         = L.[]
      γ′ .I.metas .I.equalities = L.[]
      γ′ .I.metas .I.bindings   = λ where
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
      (λ where
         .C.constraints-wf            → L.[]
         .C.metas-wf .C.equalities-wf → L.[]
         .C.metas-wf .C.bindings-wf   → λ where
           (I.var! x0)       → ⊢A
           (I.var! x1)       → ⊢t
           (I.var! x2)       → ⊢u
           (I.var! x3)       → ⊢B
           (I.var! x4)       → ⊢v
           (I.var! x5)       → ⊢w
           (I.var  not-x6 _))
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
      γ′ .I.grades              = p V.∷ V.ε
      γ′ .I.levels              = V.ε
      γ′ .I.strengths           = V.ε
      γ′ .I.binder-modes        = V.ε
      γ′ .I.⌜base⌝              = Γ
      γ′ .I.constraints         = L.[]
      γ′ .I.metas .I.equalities = L.[]
      γ′ .I.metas .I.bindings   = λ where
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

opaque
  unfolding cong subst

  -- An example that involves use of hypothetical judgemental
  -- equalities.

  cong-cong′ :
    {Γ : Cons m n} →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ B₁ ≡ B₂ →
    Γ »∙ A₁ ⊢ v₁ ≡ v₂ ∷ wk1 B₁ →
    Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ u₁ →
    Γ ⊢ cong p A₁ t₁ u₁ B₁ v₁ w₁ ≡ cong p A₂ t₂ u₂ B₂ v₂ w₂ ∷
      Id B₁ (v₁ [ t₁ ]₀) (v₁ [ u₁ ]₀)
  cong-cong′
    {m} {n}
    {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} {B₁} {B₂} {v₁} {v₂} {w₁} {w₂} {p} {Γ}
    A₁≡A₂ t₁≡t₂ u₁≡u₂ B₁≡B₂ v₁≡v₂ w₁≡w₂ =
    let ⊢A₁ , ⊢A₂     = wf-⊢≡  A₁≡A₂
        ⊢B₁ , ⊢B₂     = wf-⊢≡  B₁≡B₂
        _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
        _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
        _ , ⊢v₁ , ⊢v₂ = wf-⊢≡∷ v₁≡v₂
        _ , ⊢w₁ , ⊢w₂ = wf-⊢≡∷ w₁≡w₂
        ⊢Γ            = wf ⊢A₁
    in
    check-and-equal-type-and-terms-sound
      γ′
      (I.base nothing I.» I.base)
      (congᵢ xp xA₁ xt₁ xu₁ xB₁ xv₁ xw₁)
      (congᵢ xp xA₂ xt₂ xu₂ xB₂ xv₂ xw₂)
      (I.Id xB₁ (I.subst xv₁ (S.sgSubst xt₁))
         (I.subst xv₁ (S.sgSubst xu₁)))
      10
      PE.refl
      (λ where
         .C.constraints-wf            → L.[]
         .C.metas-wf .C.equalities-wf →
           (reflConEq ⊢Γ      , C.type                       A₁≡A₂) L.∷
           (reflConEq ⊢Γ      , C.type                       B₁≡B₂) L.∷
           (reflConEq ⊢Γ      , C.term (refl ⊢A₁)            t₁≡t₂) L.∷
           (reflConEq ⊢Γ      , C.term (refl ⊢A₁)            u₁≡u₂) L.∷
           (reflConEq (∙ ⊢A₁) , C.term (refl (wk₁ ⊢A₁ ⊢B₁))  v₁≡v₂) L.∷
           (reflConEq ⊢Γ      , C.term (refl (Idⱼ′ ⊢t₁ ⊢u₁)) w₁≡w₂) L.∷
           L.[]
         .C.metas-wf .C.bindings-wf → λ where
           (I.var! x0)        → ⊢A₁
           (I.var! x1)        → ⊢A₂
           (I.var! x2)        → ⊢B₁
           (I.var! x3)        → ⊢B₂
           (I.var! x4)        → ⊢t₁
           (I.var! x5)        → ⊢t₂
           (I.var! x6)        → ⊢u₁
           (I.var! x7)        → ⊢u₂
           (I.var! x8)        → ⊢v₁
           (I.var! x9)        → ⊢v₂
           (I.var! x10)       → ⊢w₁
           (I.var! x11)       → ⊢w₂
           (I.var  not-x12 _))
      ⊢Γ
      where
      c′ : I.Constants
      c′ .I.gs               = 1
      c′ .I.ls               = 0
      c′ .I.ss               = 0
      c′ .I.bms              = 0
      c′ .I.ms               = 12
      c′ .I.base-dcon-size   = m
      c′ .I.base-con-allowed = true
      c′ .I.base-con-size    = n
      c′ .I.meta-con-size    =
        n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷
        1+ n V.∷ 1+ n V.∷ n V.∷ n V.∷ V.ε

      xp : I.Termᵍ 1
      xp = I.var x0

      xA₁ xA₂ xB₁ xB₂ xt₁ xt₂ xu₁ xu₂ xw₁ xw₂ : I.Term c′ n
      xA₁ = I.varᵐ x0
      xA₂ = I.varᵐ x1
      xB₁ = I.varᵐ x2
      xB₂ = I.varᵐ x3
      xt₁ = I.varᵐ x4
      xt₂ = I.varᵐ x5
      xu₁ = I.varᵐ x6
      xu₂ = I.varᵐ x7
      xw₁ = I.varᵐ x10
      xw₂ = I.varᵐ x11

      xv₁ xv₂ : I.Term c′ (1+ n)
      xv₁ = I.varᵐ x8
      xv₂ = I.varᵐ x9

      γ′ : I.Contexts c′
      γ′ .I.grades              = p V.∷ V.ε
      γ′ .I.levels              = V.ε
      γ′ .I.strengths           = V.ε
      γ′ .I.binder-modes        = V.ε
      γ′ .I.⌜base⌝              = Γ
      γ′ .I.constraints         = L.[]
      γ′ .I.metas .I.equalities =
        (_ , I.var! x0  , I.var! x1)  L.∷
        (_ , I.var! x2  , I.var! x3)  L.∷
        (_ , I.var! x4  , I.var! x5)  L.∷
        (_ , I.var! x6  , I.var! x7)  L.∷
        (_ , I.var! x8  , I.var! x9)  L.∷
        (_ , I.var! x10 , I.var! x11) L.∷
        L.[]
      γ′ .I.metas .I.bindings = λ where
        (I.var! x0)  → I.base         , I.type A₁
        (I.var! x1)  → I.base         , I.type A₂
        (I.var! x2)  → I.base         , I.type B₁
        (I.var! x3)  → I.base         , I.type B₂
        (I.var! x4)  → I.base         , I.term t₁ xA₁
        (I.var! x5)  → I.base         , I.term t₂ xA₁
        (I.var! x6)  → I.base         , I.term u₁ xA₁
        (I.var! x7)  → I.base         , I.term u₂ xA₁
        (I.var! x8)  → I.base I.∙ xA₁ , I.term v₁ (W.wk[ 1 ] xB₁)
        (I.var! x9)  → I.base I.∙ xA₁ , I.term v₂ (W.wk[ 1 ] xB₁)
        (I.var! x10) → I.base         , I.term w₁ (I.Id xA₁ xt₁ xu₁)
        (I.var! x11) → I.base         , I.term w₂ (I.Id xA₁ xt₁ xu₁)
        (I.var not-x12 _)
