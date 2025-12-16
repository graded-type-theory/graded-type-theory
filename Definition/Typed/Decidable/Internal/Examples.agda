------------------------------------------------------------------------
-- Some examples showing how Definition.Typed.Decidable.Internal can
-- be used
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Usage.Restrictions

module Definition.Typed.Decidable.Internal.Examples
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR

open import Definition.Typed TR
open import Definition.Typed.Decidable.Internal TR UR
import Definition.Typed.Decidable.Internal.Context TR UR as C
import Definition.Typed.Decidable.Internal.Term TR UR as I
import Definition.Typed.Decidable.Internal.Substitution TR UR as S
import Definition.Typed.Decidable.Internal.Weakening TR UR as W
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR
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
  m n                     : Nat
  c                       : I.Constants
  Γ                       : DCon _ _
  Δ                       : Con _ _
  A A₁ A₂ B B₁ B₂ t u v w : Term _
  l₁ l₂                   : Universe-level
  b                       : BinderMode
  p p′ p″ q q′ q″         : M

opaque

  -- An example.
  --
  -- One of the terms contains a β-redex, so a type annotation is
  -- used.

  let-α≡zero-in-λλ0∘zero≡λα :
    ⦃ ok : No-equality-reflection ⦄ →
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
      (I.lam I.ω $
       I.lam I.ω (I.var x0) I.∷[ I.Π I.ω , I.ω ▷ I.ℕ ▹ I.ℕ ]
         I.∘⟨ I.ω ⟩ I.zero)
      (I.lam I.ω (I.defn 0))
      (I.Π I.ω , I.ω ▷ I.Unit I.𝕤 I.zero ▹ I.ℕ)
      9
      PE.refl
      (ok₂ , ok₁ , ok₁)
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
    ⦃ ok : No-equality-reflection ⦄ →
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
           I.∙⟨ tra ⟩[ I.lam I.ω (I.var x0) ∷
                       I.Π I.ω , I.ω ▷ I.ℕ ▹ I.ℕ ] I.»
           I.base)
      (I.lam I.ω (I.defn 1 I.∘⟨ I.ω ⟩ I.zero))
      (I.lam I.ω (I.defn 0))
      (I.Π I.ω , I.ω ▷ I.Unit I.𝕤 I.zero ▹ I.ℕ)
      8
      PE.refl
      (ok₂ , ok₁)
      (C.Meta-con-wf-empty PE.refl)
      (flip defn-wk′ ⊢Δ $ »⊇ε $
       check-dcon-sound
         (I.empty-Contexts false)
         (I.ε I.∙⟨ tra ⟩[ I.zero ∷ I.ℕ ]
              I.∙⟨ tra ⟩[ I.lam I.ω (I.var x0) ∷
                          I.Π I.ω , I.ω ▷ I.ℕ ▹ I.ℕ ])
         5
         PE.refl
         ok₁
         ε)

private

  -- Some term formers used in the examples below.

  subst′ :
    I.Termᵍ (c .I.gs) → I.Term c n → I.Term c (1+ n) → I.Term c n →
    I.Term c n → I.Term c n → I.Term c n → I.Term c n
  subst′ p A B t u v w =
    I.J p I.𝟘 A t (W.wk[ 1 ] B) w u v

  cong′ :
    I.Termᵍ (c .I.gs) → I.Term c n → I.Term c n → I.Term c n →
    I.Term c n → I.Term c (1+ n) → I.Term c n → I.Term c n
  cong′ p A t u B v w =
    subst′ p A
      (I.Id (W.wk[ 1 ] B) (W.wk[ 1 ] (I.subst v (S.sgSubst t))) v) t u w
      I.rfl

  cast′ :
    I.Termˡ (c .I.ls) → I.Term c n → I.Term c n → I.Term c n →
    I.Term c n → I.Term c n
  cast′ l A B t u =
    subst′ I.𝟙 (I.U l) (I.var x0) A B t u

  Funext′ :
    I.Termᵍ (c .I.gs) → I.Termᵍ (c .I.gs) → I.Termᵍ (c .I.gs) →
    I.Termᵍ (c .I.gs) → I.Termˡ (c .I.ls) → I.Termˡ (c .I.ls) →
    I.Term c n
  Funext′ p q p′ q′ l₁ l₂ =
    I.Π p , q ▷ I.U l₁ ▹
    I.Π p′ , q′ ▷ (I.Π p , q ▷ I.var x0 ▹ I.U l₂) ▹
    let Π-type = I.Π p , q ▷ I.var x1 ▹ (I.var x1 I.∘⟨ p ⟩ I.var x0)
    in
    I.Π p′ , q′ ▷ Π-type ▹
    I.Π p′ , q′ ▷ W.wk[ 1 ] Π-type ▹
    I.Π p′ , q′ ▷
      (I.Π p , q ▷ I.var x3 ▹
       I.Id (I.var x3 I.∘⟨ p ⟩ I.var x0)
         (I.var x2 I.∘⟨ p ⟩ I.var x0)
         (I.var x1 I.∘⟨ p ⟩ I.var x0)) ▹
    I.Id (W.wk[ 3 ] Π-type) (I.var x2) (I.var x1)

opaque
  unfolding subst

  -- An example that includes use of a meta-variable context.

  ⊢subst′ :
    ⦃ ok : No-equality-reflection ⦄
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
      (subst′ (I.var x0) (I.varᵐ x0) (I.varᵐ x1) (I.varᵐ x2) (I.varᵐ x3)
         (I.varᵐ x4) (I.varᵐ x5))
      (I.subst (I.varᵐ x1) (S.sgSubst (I.varᵐ x3)))
      8
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
    ⦃ ok : No-equality-reflection ⦄
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
      (cong′ (I.var x0) (I.varᵐ x0) (I.varᵐ x1) (I.varᵐ x2) (I.varᵐ x3)
         (I.varᵐ x4) (I.varᵐ x5))
      (I.Id (I.varᵐ x3) (I.subst (I.varᵐ x4) (S.sgSubst (I.varᵐ x1)))
         (I.subst (I.varᵐ x4) (S.sgSubst (I.varᵐ x2))))
      9
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

opaque
  unfolding Funext Has-function-extensionality cast cong subst

  -- A larger example.
  --
  -- This example makes use of a type annotation, because the code
  -- that is type-checked contains a β-redex (the application of cong′
  -- gives rise to a β-redex).

  ΠΣ-cong-Idˡ′ :
    ⦃ ok : No-equality-reflection ⦄
    {Γ : Cons m n} →
    ΠΣ-allowed b p q →
    Π-allowed p′ q′ →
    Π-allowed p″ q″ →
    Has-function-extensionality p′ q′ p″ q″ l₁ (1+ l₂) Γ →
    Γ »∙ A₂ ⊢ B₂ ∷ U l₂ →
    Γ ⊢ t ∷ Id (U l₁) A₁ A₂ →
    Γ »∙ A₁ ⊢ u ∷
      Id (U l₂) B₁
        (B₂ [ cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t) (var x0) ]↑) →
    ∃ λ v →
      Γ ⊢ v ∷
        Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
          (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
  ΠΣ-cong-Idˡ′
    {m} {n} {b} {p} {q} {p′} {q′} {p″} {q″} {l₁} {l₂}
    {A₂} {B₂} {t} {A₁} {u} {B₁} {Γ}
    ok₁ ok₂ ok₃ (funext , ⊢funext) ⊢B₂ ⊢t ⊢u =
    let _ , ⊢A₁ , ⊢A₂ = inversion-Id (wf-⊢∷ ⊢t)
        _ , ⊢B₁ , _   = inversion-Id (wf-⊢∷ ⊢u)
    in
    _ ,
    check-type-and-term-sound
      γ′
      (I.base nothing I.» I.base)
      (I.J I.ω I.ω (I.U xl₁) xA₁
         (I.Π xp″ , xq″ ▷ (I.Π xp′ , xq′ ▷ I.var x1 ▹ I.U xl₂) ▹
          I.Π xp″ , xq″ ▷
            I.Π xp′ , xq′ ▷ W.wk[ 3 ] xA₁ ▹
            I.Id (I.U xl₂)
              (I.subst xB₁ (I.cons (S.wkSubst 4 I.id) (I.var x0)))
              (I.var x1 I.∘⟨ xp′ ⟩
               cast′ xl₁ (W.wk[ 4 ] xA₁) (I.var x3) (I.var x2)
                 (I.var x0)) ▹
          I.Id (I.U (xl₁ I.⊔ᵘ xl₂))
            (W.wk[ 4 ] (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₁ ▹ xB₁))
            (I.ΠΣ⟨ xb ⟩ xp , xq ▷ I.var x3 ▹
             (I.var x2 I.∘⟨ xp′ ⟩ I.var x0)))
         (I.lam xp″ $ I.lam xp″ $
          cong′ I.ω (W.wk[ 2 ] (I.Π xp′ , xq′ ▷ xA₁ ▹ I.U xl₂))
            (W.wk[ 2 ]
               (I.lam xp′ xB₁ I.∷[ I.Π xp′ , xq′ ▷ xA₁ ▹ I.U xl₂ ]))
            (I.var x1)
            (I.U (xl₁ I.⊔ᵘ xl₂))
            (I.ΠΣ⟨ xb ⟩ xp , xq ▷ W.wk[ 3 ] xA₁ ▹
             (I.var x1 I.∘⟨ xp′ ⟩ I.var x0))
            (W.wk[ 2 ]
               (xfunext I.∘⟨ xp′ ⟩ xA₁ I.∘⟨ xp″ ⟩
                I.lam xp′ (I.U xl₂) I.∘⟨ xp″ ⟩ I.lam xp′ xB₁) I.∘⟨ xp″ ⟩
             I.var x1 I.∘⟨ xp″ ⟩
             I.var x0))
         xA₂ xt I.∘⟨ xp″ ⟩
       I.lam xp′ xB₂ I.∘⟨ xp″ ⟩
       I.lam xp′ xu)
      (I.Id (I.U (xl₁ I.⊔ᵘ xl₂)) (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₁ ▹ xB₁)
         (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₂ ▹ xB₂))
      25
      PE.refl
      (ok₁ , ok₁ , ok₂ , ok₂ , ok₁ , ok₁ , ok₃ , ok₃ , ok₂ , ok₂ , ok₂ ,
       ok₁ , ok₁)
      (record
         { bindings-wf = λ where
             (I.var! x0)       → ⊢A₁
             (I.var! x1)       → ⊢B₁
             (I.var! x2)       → ⊢A₂
             (I.var! x3)       → ⊢B₂
             (I.var! x4)       → ⊢t
             (I.var! x5)       → ⊢u
             (I.var! x6)       → ⊢funext
             (I.var  not-x7 _)
         })
      (wfTerm ⊢A₁)
      where
      c′ : I.Constants
      c′ .I.gs               = 6
      c′ .I.ls               = 2
      c′ .I.ss               = 0
      c′ .I.bms              = 1
      c′ .I.ms               = 7
      c′ .I.base-dcon-size   = m
      c′ .I.base-con-size    = n
      c′ .I.base-con-allowed = true
      c′ .I.meta-con-size    =
        n V.∷ 1+ n V.∷ n V.∷ 1+ n V.∷ n V.∷ 1+ n V.∷ n V.∷ V.ε

      xb : I.Termᵇᵐ 0 1
      xb = I.var x0

      xl₁ xl₂ : I.Termˡ 2
      xl₁ = I.var x0
      xl₂ = I.var x1

      xp xp′ xp″ xq xq′ xq″ : I.Termᵍ 6
      xp  = I.var x0
      xp′ = I.var x1
      xp″ = I.var x2
      xq  = I.var x3
      xq′ = I.var x4
      xq″ = I.var x5

      xA₁ xA₂ xt xfunext : I.Term c′ n
      xA₁     = I.varᵐ x0
      xA₂     = I.varᵐ x2
      xt      = I.varᵐ x4
      xfunext = I.varᵐ x6

      xB₁ xB₂ xu : I.Term c′ (1+ n)
      xB₁ = I.varᵐ x1
      xB₂ = I.varᵐ x3
      xu  = I.varᵐ x5

      γ′ : I.Contexts c′
      γ′ .I.grades            = p V.∷ p′ V.∷ p″ V.∷ q V.∷ q′ V.∷ q″ V.∷
                                V.ε
      γ′ .I.levels            = l₁ V.∷ l₂ V.∷ V.ε
      γ′ .I.strengths         = V.ε
      γ′ .I.binder-modes      = b V.∷ V.ε
      γ′ .I.⌜base⌝            = Γ
      γ′ .I.metas .I.bindings = λ where
        (I.var! x0) → I.base , I.term A₁ (I.U xl₁)
        (I.var! x1) → I.base I.∙ xA₁ , I.term B₁ (I.U xl₂)
        (I.var! x2) → I.base , I.term A₂ (I.U xl₁)
        (I.var! x3) → I.base I.∙ xA₂ , I.term B₂ (I.U xl₂)
        (I.var! x4) → I.base , I.term t  (I.Id (I.U xl₁) xA₁ xA₂)
        (I.var! x5) →
          I.base I.∙ xA₁ ,
          I.term u
            (I.Id (I.U xl₂) xB₁
               (I.subst xB₂
                  (I.cons (I.wk1 I.id)
                     (I.J I.𝟙 I.𝟘 (I.U xl₁) (W.wk[ 1 ] xA₁)
                        (W.wk[ 1 ] (I.var x0)) (I.var x0)
                        (W.wk[ 1 ] xA₂) (W.wk[ 1 ] xt)))))
        (I.var! x6) →
          I.base ,
          I.term funext (Funext′ xp′ xq′ xp″ xq″ xl₁ (I.suc xl₂))
        (I.var not-x7 _)
