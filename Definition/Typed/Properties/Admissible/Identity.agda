------------------------------------------------------------------------
-- Admissible rules related to identity types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Decidable.Internal R
import Definition.Typed.Decidable.Internal.Term 𝕄 as I
import Definition.Typed.Decidable.Internal.Substitution 𝕄 as IS
import Definition.Typed.Decidable.Internal.Weakening 𝕄 as IW
open import Definition.Typed.Inversion R
import Definition.Typed.Properties.Admissible.Identity.Primitive
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M as U
open import Definition.Untyped.Identity 𝕄

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Maybe
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Vec as V

open Definition.Typed.Properties.Admissible.Identity.Primitive R public

private variable
  m n                           : Nat
  Η                             : Cons _ _
  A₁ A₂ B₁ B₂ t t₁ t₂ u u₁ u₂ v : Term _
  p p′ p″ q q′ q″               : M
  b                             : BinderMode
  l l₁ l₂                       : Universe-level

------------------------------------------------------------------------
-- Some preservation lemmas

private opaque

  -- A variant of the J rule.

  J′ :
    ∀ {a p} {A : Set a} {x y : A}
    (P : ∀ y → x PE.≡ y → Set p) →
    P x PE.refl →
    (x≡y : x PE.≡ y) →
    P y x≡y
  J′ _ p PE.refl = p

  -- The following code illustrates roughly how ΠΣ-cong-Idˡ below is
  -- defined.

  Π-cong-Idˡ′ :
    ∀ {a b} →
    Function-extensionality a (lsuc b) →
    {A₁ A₂ : Set a} {B₁ : A₁ → Set b} {B₂ : A₂ → Set b} →
    (A₁≡A₂ : A₁ PE.≡ A₂) →
    ((x : A₁) → B₁ x PE.≡ B₂ (PE.subst (λ A → A) A₁≡A₂ x)) →
    ((x : A₁) → B₁ x) PE.≡ ((x : A₂) → B₂ x)
  Π-cong-Idˡ′ {b} fe {A₁} {A₂} {B₁} {B₂} A₁≡A₂ B₁≡B₂ =
    J′ (λ A₂ A₁≡A₂ →
          {B₂ : A₂ → Set b} →
          ((x : A₁) → B₁ x PE.≡ B₂ (PE.subst (λ A → A) A₁≡A₂ x)) →
          ((x : A₁) → B₁ x) PE.≡ ((x : A₂) → B₂ x))
       (λ {B₂} B₁≡B₂ →
          PE.cong (λ B → (x : A₁) → B x) {x = B₁} {y = B₂}
            (ext {A = A₁} {P = λ _ → Set b} {f = B₁} {g = B₂} fe B₁≡B₂))
       A₁≡A₂ B₁≡B₂

opaque
  unfolding Funext Has-function-extensionality cast cong subst

  -- Allowed Π- and Σ-types preserve propositional equality in a
  -- certain sense, assuming that a certain form of function
  -- extensionality can be proved (and that certain Π-types are
  -- allowed).

  ΠΣ-cong-Idˡ :
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
  ΠΣ-cong-Idˡ
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
            I.Π xp′ , xq′ ▷ IW.wk[ 3 ] xA₁ ▹
            I.Id (I.U xl₂)
              (I.subst xB₁ (I.cons (IS.wkSubst 4 I.id) (I.var x0)))
              (I.var x1 I.∘⟨ xp′ ⟩
               castᵢ xl₁ (IW.wk[ 4 ] xA₁) (I.var x3) (I.var x2)
                 (I.var x0)) ▹
          I.Id (I.U (xl₁ I.⊔ᵘ xl₂))
            (IW.wk[ 4 ] (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₁ ▹ xB₁))
            (I.ΠΣ⟨ xb ⟩ xp , xq ▷ I.var x3 ▹
             (I.var x2 I.∘⟨ xp′ ⟩ I.var x0)))
         (I.lam xp″ nothing $ I.lam xp″ nothing $
          congᵢ I.ω (IW.wk[ 2 ] (I.Π xp′ , xq′ ▷ xA₁ ▹ I.U xl₂))
            (IW.wk[ 2 ] (I.lam xp′ (just (xq′ , xA₁)) xB₁))
            (I.var x1)
            (I.U (xl₁ I.⊔ᵘ xl₂))
            (I.ΠΣ⟨ xb ⟩ xp , xq ▷ IW.wk[ 3 ] xA₁ ▹
             (I.var x1 I.∘⟨ xp′ ⟩ I.var x0))
            (IW.wk[ 2 ]
               (xfunext I.∘⟨ xp′ ⟩ xA₁ I.∘⟨ xp″ ⟩
                I.lam xp′ nothing (I.U xl₂) I.∘⟨ xp″ ⟩
                I.lam xp′ nothing xB₁) I.∘⟨ xp″ ⟩
             I.var x1 I.∘⟨ xp″ ⟩
             I.var x0))
         xA₂ xt I.∘⟨ xp″ ⟩
       I.lam xp′ nothing xB₂ I.∘⟨ xp″ ⟩
       I.lam xp′ nothing xu)
      (I.Id (I.U (xl₁ I.⊔ᵘ xl₂)) (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₁ ▹ xB₁)
         (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₂ ▹ xB₂))
      25
      PE.refl
      (ok₃ , ok₁ , ok₂)
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
                     (I.J I.𝟙 I.𝟘 (I.U xl₁) (IW.wk[ 1 ] xA₁)
                        (IW.wk[ 1 ] (I.var x0)) (I.var x0)
                        (IW.wk[ 1 ] xA₂) (IW.wk[ 1 ] xt)))))
        (I.var! x6) →
          I.base ,
          I.term funext (Funextᵢ xp′ xq′ xp″ xq″ xl₁ (I.suc xl₂))
        (I.var not-x7 _)

opaque

  -- A variant of ΠΣ-cong-Idˡ.

  ΠΣ-cong-Idʳ :
    ΠΣ-allowed b p q →
    Π-allowed p′ q′ →
    Π-allowed p″ q″ →
    Has-function-extensionality p′ q′ p″ q″ l₁ (1+ l₂) Η →
    Η »∙ A₁ ⊢ B₁ ∷ U l₂ →
    Η ⊢ t ∷ Id (U l₁) A₂ A₁ →
    Η »∙ A₂ ⊢ u ∷
      Id (U l₂) (B₁ [ cast l₁ (wk1 A₂) (wk1 A₁) (wk1 t) (var x0) ]↑)
        B₂ →
    ∃ λ v →
      Η ⊢ v ∷
        Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
          (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
  ΠΣ-cong-Idʳ ok ok′ ok″ ext ⊢B₁ ⊢t ⊢u =
    _ ,
    ⊢symmetry (ΠΣ-cong-Idˡ ok ok′ ok″ ext ⊢B₁ ⊢t (⊢symmetry ⊢u) .proj₂)

private opaque

  -- The following code illustrates roughly how Id-cong-Idˡ below is
  -- defined.

  Id-cong-Idˡ′ :
    ∀ {a} {A₁ A₂ : Set a} {t₁ u₁ : A₁} {t₂ u₂ : A₂}
    (A₁≡A₂ : A₁ PE.≡ A₂) →
    PE.subst (λ A → A) A₁≡A₂ t₁ PE.≡ t₂ →
    PE.subst (λ A → A) A₁≡A₂ u₁ PE.≡ u₂ →
    (t₁ PE.≡ u₁) PE.≡ (t₂ PE.≡ u₂)
  Id-cong-Idˡ′ {A₁} {t₁} {u₁} {t₂} {u₂} A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    J′ (λ A₂ A₁≡A₂ →
           (t₂ u₂ : A₂) →
           PE.subst (λ A → A) A₁≡A₂ t₁ PE.≡ t₂ →
           PE.subst (λ A → A) A₁≡A₂ u₁ PE.≡ u₂ →
           (t₁ PE.≡ u₁) PE.≡ (t₂ PE.≡ u₂))
      (λ t₂ u₂ t₁≡t₂ u₁≡u₂ →
         PE.cong₂ (PE._≡_ {A = A₁}) t₁≡t₂ u₁≡u₂)
      A₁≡A₂ t₂ u₂ t₁≡t₂ u₁≡u₂

opaque
  unfolding cast subst

  -- Id preserves propositional equality in a certain sense (assuming
  -- that some Π-type is allowed).

  Id-cong-Idˡ :
    {Γ : Cons m n} →
    Π-allowed p q →
    Γ ⊢ t ∷ Id (U l) A₁ A₂ →
    Γ ⊢ u ∷ Id A₂ (cast l A₁ A₂ t t₁) t₂ →
    Γ ⊢ v ∷ Id A₂ (cast l A₁ A₂ t u₁) u₂ →
    ∃ λ w → Γ ⊢ w ∷ Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂)
  Id-cong-Idˡ
    {m} {n} {p} {q} {t} {l} {A₁} {A₂} {u} {t₁} {t₂} {v} {u₁} {u₂} {Γ}
    ok ⊢t ⊢u ⊢v =
    let _ , ⊢A₁ , ⊢A₂       = inversion-Id (wf-⊢∷ ⊢t)
        _ , ⊢cast-t₁ , ⊢t₂  = inversion-Id (wf-⊢∷ ⊢u)
        _ , ⊢cast-u₁ , ⊢u₂  = inversion-Id (wf-⊢∷ ⊢v)
        _ , _ , _ , ⊢t₁ , _ = inversion-cast ⊢cast-t₁
        _ , _ , _ , ⊢u₁ , _ = inversion-cast ⊢cast-u₁
    in
    _ ,
    check-type-and-term-sound
      γ′
      (I.base nothing I.» I.base)
      (I.J I.ω I.ω (I.U xl) xA₁
         (I.Π xp , xq ▷ I.var x1 ▹
          I.Π xp , xq ▷ I.var x2 ▹
          I.Π xp , xq ▷
            I.Id (I.var x3)
              (castᵢ xl (IW.wk[ 4 ] xA₁) (I.var x3) (I.var x2)
              (IW.wk[ 4 ] xt₁)) (I.var x1) ▹
          I.Π xp , xq ▷
            I.Id (I.var x4)
              (castᵢ xl (IW.wk[ 5 ] xA₁) (I.var x4) (I.var x3)
                 (IW.wk[ 5 ] xu₁))
              (I.var x1) ▹
          I.Id (I.U xl) (IW.wk[ 6 ] (I.Id xA₁ xt₁ xu₁))
            (I.Id (I.var x5) (I.var x3) (I.var x2)))
         (I.lam xp nothing $ I.lam xp nothing $ I.lam xp nothing $
          I.lam xp nothing $
          cong₂ᵢ I.ω (IW.wk[ 4 ] xA₁) (IW.wk[ 4 ] xt₁) (I.var x3)
            (IW.wk[ 4 ] xA₁) (IW.wk[ 4 ] xu₁) (I.var x2) (I.U xl)
            (I.Id (IW.wk[ 6 ] xA₁) (I.var x1) (I.var x0)) (I.var x1)
            (I.var x0))
         xA₂ xt I.∘⟨ xp ⟩
       xt₂ I.∘⟨ xp ⟩ xu₂ I.∘⟨ xp ⟩ xu  I.∘⟨ xp ⟩ xv)
      (I.Id (I.U xl) (I.Id xA₁ xt₁ xu₁) (I.Id xA₂ xt₂ xu₂))
      29
      PE.refl
      ok
      (record
         { bindings-wf = λ where
             (I.var! x0)       → ⊢A₁
             (I.var! x1)       → ⊢A₂
             (I.var! x2)       → ⊢t
             (I.var! x3)       → ⊢t₁
             (I.var! x4)       → ⊢t₂
             (I.var! x5)       → ⊢u
             (I.var! x6)       → ⊢u₁
             (I.var! x7)       → ⊢u₂
             (I.var! x8)       → ⊢v
             (I.var  not-x9 _)
         })
      (wfTerm ⊢A₁)
      where
      c′ : I.Constants
      c′ .I.gs               = 2
      c′ .I.ls               = 1
      c′ .I.ss               = 0
      c′ .I.bms              = 0
      c′ .I.ms               = 9
      c′ .I.base-dcon-size   = m
      c′ .I.base-con-size    = n
      c′ .I.base-con-allowed = true
      c′ .I.meta-con-size    = V.replicate 9 n

      xl : I.Termˡ 1
      xl = I.var x0

      xp xq : I.Termᵍ 2
      xp = I.var x0
      xq = I.var x1

      xA₁ xA₂ xt xt₁ xt₂ xu xu₁ xu₂ xv : I.Term c′ n
      xA₁ = I.varᵐ x0
      xA₂ = I.varᵐ x1
      xt  = I.varᵐ x2
      xt₁ = I.varᵐ x3
      xt₂ = I.varᵐ x4
      xu  = I.varᵐ x5
      xu₁ = I.varᵐ x6
      xu₂ = I.varᵐ x7
      xv  = I.varᵐ x8

      γ′ : I.Contexts c′
      γ′ .I.grades            = p V.∷ q V.∷ V.ε
      γ′ .I.levels            = l V.∷ V.ε
      γ′ .I.strengths         = V.ε
      γ′ .I.binder-modes      = V.ε
      γ′ .I.⌜base⌝            = Γ
      γ′ .I.metas .I.bindings = λ where
        (I.var! x0) → I.base , I.term A₁ (I.U xl)
        (I.var! x1) → I.base , I.term A₂ (I.U xl)
        (I.var! x2) → I.base , I.term t (I.Id (I.U xl) xA₁ xA₂)
        (I.var! x3) → I.base , I.term t₁ xA₁
        (I.var! x4) → I.base , I.term t₂ xA₂
        (I.var! x5) →
          I.base , I.term u (I.Id xA₂ (castᵢ xl xA₁ xA₂ xt xt₁) xt₂)
        (I.var! x6) → I.base , I.term u₁ xA₁
        (I.var! x7) → I.base , I.term u₂ xA₂
        (I.var! x8) →
          I.base , I.term v (I.Id xA₂ (castᵢ xl xA₁ xA₂ xt xu₁) xu₂)
        (I.var not-x9 _)

opaque

  -- A variant of Id-cong-Idˡ.

  Id-cong-Idʳ :
    Π-allowed p q →
    Η ⊢ t ∷ Id (U l) A₂ A₁ →
    Η ⊢ u ∷ Id A₁ t₁ (cast l A₂ A₁ t t₂) →
    Η ⊢ v ∷ Id A₁ u₁ (cast l A₂ A₁ t u₂) →
    ∃ λ w → Η ⊢ w ∷ Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂)
  Id-cong-Idʳ ok ⊢t ⊢u ⊢v =
    Id-cong-Idˡ ok (⊢symmetry ⊢t) (cast-right-left ⊢t ⊢u .proj₂)
      (cast-right-left ⊢t ⊢v .proj₂)
