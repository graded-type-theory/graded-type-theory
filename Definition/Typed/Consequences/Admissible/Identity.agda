------------------------------------------------------------------------
-- Admissible rules related to identity types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Consequences.Admissible.Identity
  {a a′} {M : Set a} {Mode : Set a′}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Decidable.Internal 𝐌 R
import Definition.Typed.Decidable.Internal.Context 𝐌 R as IC
import Definition.Typed.Decidable.Internal.Term 𝐌 R as I
import Definition.Typed.Decidable.Internal.Substitution 𝐌 R as IS
import Definition.Typed.Decidable.Internal.Weakening 𝐌 R as IW
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Identity R
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.U R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R

open import Definition.Untyped M as U
open import Definition.Untyped.Identity 𝕄 as Id
open import Definition.Untyped.Sup R

open Id.Internal 𝐌 R

open import Tools.Bool
open import Tools.Fin
open import Tools.Function as F hiding (ext)
open import Tools.Level as Lvl using (lsuc; _⊔_)
import Tools.List as L
open import Tools.Maybe
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Vec as V

private variable
  m n                                   : Nat
  Γ                                     : Cons _ _
  A A₁ A₂ B B₁ B₂ ext t t₁ t₂ u u₁ u₂ v : Term _
  l l₁ l₁′ l₂ l₂′                       : Lvl _
  p p′ p″ q q′ q″                       : M
  b                                     : BinderMode

------------------------------------------------------------------------
-- Some lemmas related to function extensionality

private opaque

  -- A formulation of function extensionality for certain levels.

  Funext′ : (a b : Lvl.Level) → Set (lsuc (a ⊔ b))
  Funext′ a b =
    (A : Set a) (B : A → Set b)
    (f g : (x : A) → B x) →
    ((x : A) → f x PE.≡ g x) →
    f PE.≡ g

  -- The following code illustrates roughly how lower-ext below is
  -- defined.

  Is-function-extensionality-lower-ext′ :
    ∀ a a′ b b′ →
    Funext′ (a ⊔ a′) (b ⊔ b′) →
    Funext′ a b
  Is-function-extensionality-lower-ext′ a a′ b b′ ext =
    λ A B f g f≡g →
      PE.cong
        {A = (x : Lvl.Lift a′ A) → Lvl.Lift b′ (B (Lvl.Lift.lower x))}
        {B = (x : A) → B x} (λ f x → Lvl.Lift.lower (f (Lvl.lift x)))
        {x = λ (x : Lvl.Lift a′ A) →
               Lvl.lift {ℓ = b′} (f (Lvl.Lift.lower x))}
        {y = λ x → Lvl.lift (g (Lvl.Lift.lower x))}
        (ext (Lvl.Lift a′ A) (λ x → Lvl.Lift b′ (B (Lvl.Lift.lower x)))
           (λ x → Lvl.lift (f (Lvl.Lift.lower x)))
           (λ x → Lvl.lift (g (Lvl.Lift.lower x)))
           (λ x →
              PE.cong {A = B (Lvl.Lift.lower x)}
                {B = Lvl.Lift b′ (B (Lvl.Lift.lower x))}
                (λ x → Lvl.lift x)
                {x = f (Lvl.Lift.lower x)} {y = g (Lvl.Lift.lower x)}
                (f≡g (Lvl.Lift.lower x))))

opaque
  unfolding cong subst

  -- A definition that is used to state
  -- Is-function-extensionality-lower-ext below.

  lower-ext : M → M → M → Lvl n → Lvl n → Term n → Term n
  lower-ext p q p′ l₁′ l₂′ ext =
    lam p $ lam p′ $ lam p′ $ lam p′ $ lam p′ $
    cong ω
      (Π p , q ▷ Lift (wk[ 5 ]′ l₁′) (var x4) ▹
       Lift (wk[ 6 ]′ l₂′) (var x4 ∘⟨ p ⟩ lower (var x0)))
      (lam p (lift (var x3 ∘⟨ p ⟩ lower (var x0))))
      (lam p (lift (var x2 ∘⟨ p ⟩ lower (var x0))))
      (Π p , q ▷ var x4 ▹ (var x4 ∘⟨ p ⟩ var x0))
      (lam p (lower (var x1 ∘⟨ p ⟩ lift (var x0))))
      (wk[ 5 ]′ ext ∘⟨ p ⟩ Lift (wk[ 5 ]′ l₁′) (var x4) ∘⟨ p′ ⟩
       lam p (Lift (wk[ 6 ]′ l₂′) (var x4 ∘⟨ p ⟩ lower (var x0)))
         ∘⟨ p′ ⟩
       lam p (lift (var x3 ∘⟨ p ⟩ lower (var x0))) ∘⟨ p′ ⟩
       lam p (lift (var x2 ∘⟨ p ⟩ lower (var x0))) ∘⟨ p′ ⟩
       lam p
         (cong ω (var x4 ∘⟨ p ⟩ lower (var x0))
            (var x3 ∘⟨ p ⟩ lower (var x0))
            (var x2 ∘⟨ p ⟩ lower (var x0))
            (Lift (wk[ 6 ]′ l₂′) (var x4 ∘⟨ p ⟩ lower (var x0)))
            (lift (var x0)) (var x1 ∘⟨ p ⟩ lower (var x0))))

opaque
  unfolding Funext Is-function-extensionality lower-ext

  -- If function extensionality holds for l₁ supᵘₗ l₁′ and
  -- l₂ supᵘₗ l₂′, then it also holds for l₁ and l₂ (if all the levels
  -- are well-formed).

  Is-function-extensionality-lower-ext :
    {Γ : Cons m n} →
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₁′ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ l₂′ ∷Level →
    Is-function-extensionality
      p q p′ q′ (l₁ supᵘₗ l₁′) (l₂ supᵘₗ l₂′) Γ ext →
    Is-function-extensionality
      p q p′ q′ l₁ l₂ Γ (lower-ext p q p′ l₁′ l₂′ ext)
  Is-function-extensionality-lower-ext
    {m} {n} {l₁} {l₁′} {l₂} {l₂′} {p} {q} {p′} {q′} {ext} {Γ}
    ⊢l₁ ⊢l₁′ ⊢l₂ ⊢l₂′ ⊢ext =
    let _ , ⊢Π , ok₁ = inversion-ΠΣ (wf-⊢ ⊢ext)
        _ , _  , ok₂ = inversion-ΠΣ ⊢Π
    in
    check-type-and-term-sound
      γ′
      (I.base nothing I.» I.base)
      (I.lam xp nothing $ I.lam xp′ nothing $ I.lam xp′ nothing $
       I.lam xp′ nothing $ I.lam xp′ nothing $
       congᵢ I.ω
         (I.Π xp , xq ▷ I.Lift (IW.wk[ 5 ] xl₁′) (I.var x4) ▹
          I.Lift (IW.wk[ 6 ] xl₂′)
            (I.var x4 I.∘⟨ xp ⟩ I.lower (I.var x0)))
         (I.lam xp (just (xq , I.Lift (IW.wk[ 5 ] xl₁′) (I.var x4))) $
          I.lift (just (IW.wk[ 6 ] xl₂′))
            (I.var x3 I.∘⟨ xp ⟩ I.lower (I.var x0)))
         (I.lam xp nothing $
          I.lift nothing (I.var x2 I.∘⟨ xp ⟩ I.lower (I.var x0)))
         (I.Π xp , xq ▷ I.var x4 ▹ (I.var x4 I.∘⟨ xp ⟩ I.var x0))
         (I.lam xp nothing $
          I.lower (I.var x1 I.∘⟨ xp ⟩ I.lift nothing (I.var x0)))
         (IW.wk[ 5 ] xext I.∘⟨ xp ⟩
          I.Lift (IW.wk[ 5 ] xl₁′) (I.var x4) I.∘⟨ xp′ ⟩
          I.lam xp nothing
            (I.Lift (IW.wk[ 6 ] xl₂′)
               (I.var x4 I.∘⟨ xp ⟩ I.lower (I.var x0))) I.∘⟨ xp′ ⟩
          I.lam xp nothing
            (I.lift nothing (I.var x3 I.∘⟨ xp ⟩ I.lower (I.var x0)))
            I.∘⟨ xp′ ⟩
          I.lam xp nothing
            (I.lift nothing (I.var x2 I.∘⟨ xp ⟩ I.lower (I.var x0)))
            I.∘⟨ xp′ ⟩
          I.lam xp nothing
            (congᵢ I.ω (I.var x4 I.∘⟨ xp ⟩ I.lower (I.var x0))
               (I.var x3 I.∘⟨ xp ⟩ I.lower (I.var x0))
               (I.var x2 I.∘⟨ xp ⟩ I.lower (I.var x0))
               (I.Lift (IW.wk[ 6 ] xl₂′)
                  (I.var x4 I.∘⟨ xp ⟩ I.lower (I.var x0)))
               (I.lift nothing (I.var x0))
               (I.var x1 I.∘⟨ xp ⟩ I.lower (I.var x0)))))
      (Funextᵢ xp xq xp′ xq′ xl₁ xl₂)
      26
      PE.refl
      (λ where
         .IC.constraints-wf             → ok₁ L.∷ ok₂ L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → ⊢l₁
           (I.var! x1)         → ⊢l₁′
           (I.var! x2)         → ⊢l₂
           (I.var! x3)         → ⊢l₂′
           (I.var! x4)         → ⊢ext
           (I.var  not-x5 _ _))
      (wf ⊢ext)
      where
      c′ : I.Constants
      c′ .I.gs                 = 4
      c′ .I.ss                 = 0
      c′ .I.bms                = 0
      c′ .I.ms                 = 5
      c′ .I.base-dcon-size     = m
      c′ .I.base-con-size      = n
      c′ .I.base-con-allowed   = true
      c′ .I.meta-con-size      = V.replicate 5 n
      c′ .I.meta-con-term-kind =
        lvl V.∷ lvl V.∷ lvl V.∷ lvl V.∷ tm V.∷ V.ε

      xp xp′ xq xq′ : I.Termᵍ 4
      xp  = I.var x0
      xp′ = I.var x1
      xq  = I.var x2
      xq′ = I.var x3

      xl₁ xl₁′ xl₂ xl₂′ : I.Lvl c′ n
      xl₁  = I.varᵐ x0
      xl₁′ = I.varᵐ x1
      xl₂  = I.varᵐ x2
      xl₂′ = I.varᵐ x3

      xext : I.Term c′ n
      xext = I.varᵐ x4

      γ′ : I.Contexts c′
      γ′ .I.grades       = p V.∷ p′ V.∷ q V.∷ q′ V.∷ V.ε
      γ′ .I.strengths    = V.ε
      γ′ .I.binder-modes = V.ε
      γ′ .I.⌜base⌝       = Γ
      γ′ .I.constraints⁰ = I.emptyᶜ⁰
      γ′ .I.constraints⁺ =
        I.π-allowed xp  xq  L.∷
        I.π-allowed xp′ xq′ L.∷
        L.[]
      γ′ .I.metas .I.equalities = L.[]
      γ′ .I.metas .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l₁
        (I.var! x1) → I.base , I.level l₁′
        (I.var! x2) → I.base , I.level l₂
        (I.var! x3) → I.base , I.level l₂′
        (I.var! x4) →
          I.base ,
          I.term ext
            (Funextᵢ xp xq xp′ xq′ (xl₁ I.supᵘₗ xl₁′)
               (xl₂ I.supᵘₗ xl₂′))
        (I.var not-x5 _ _)

opaque
  unfolding Has-function-extensionality

  -- If function extensionality holds for l₁ supᵘₗ l₁′ and
  -- l₂ supᵘₗ l₂′, then it also holds for l₁ and l₂ (if all the levels
  -- are well-formed).

  Has-function-extensionality-supᵘₗ :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₁′ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ l₂′ ∷Level →
    Has-function-extensionality p q p′ q′
      (l₁ supᵘₗ l₁′) (l₂ supᵘₗ l₂′) Γ →
    Has-function-extensionality p q p′ q′ l₁ l₂ Γ
  Has-function-extensionality-supᵘₗ ⊢l₁ ⊢l₁′ ⊢l₂ ⊢l₂′ (_ , ⊢ext) =
    _ , Is-function-extensionality-lower-ext ⊢l₁ ⊢l₁′ ⊢l₂ ⊢l₂′ ⊢ext

opaque
  unfolding
    Funext Has-function-extensionality Is-function-extensionality

  -- If function extensionality holds for l₁′ and l₂′, then it also
  -- holds for smaller levels l₁ and l₂.

  Has-function-extensionality-downwards-closed :
    Γ ⊢ l₁ ≤ₗ l₁′ ∷Level →
    Γ ⊢ l₂ ≤ₗ l₂′ ∷Level →
    Has-function-extensionality p q p′ q′ l₁′ l₂′ Γ →
    Has-function-extensionality p q p′ q′ l₁ l₂ Γ
  Has-function-extensionality-downwards-closed
    l₁≤l₁′ l₂≤l₂′ (ext , ⊢ext) =
    let ⊢l₁ , ⊢l₁′       = wf-⊢≤ₗ∷L l₁≤l₁′
        ⊢l₂ , ⊢l₂′       = wf-⊢≤ₗ∷L l₂≤l₂′
        ⊢Ul₁′ , ⊢Π , ok₁ = inversion-ΠΣ (wf-⊢ ⊢ext)
        _     , ⊢Π , ok₂ = inversion-ΠΣ ⊢Π
    in
    Has-function-extensionality-supᵘₗ ⊢l₁ ⊢l₁′ ⊢l₂ ⊢l₂′
      (ext ,
       conv ⊢ext
         (ΠΣ-cong (U-cong-⊢≡ (sym-⊢≡∷L (⊢≤ₗ∷L→⊢≡∷L l₁≤l₁′)))
            (ΠΣ-cong
               (ΠΣ-cong (refl (univ (var₀ ⊢Ul₁′)))
                  (U-cong-⊢≡ $ sym-⊢≡∷L $
                   W.wk (ʷ⊇-drop (∙ univ (var₀ ⊢Ul₁′))) $
                   ⊢≤ₗ∷L→⊢≡∷L l₂≤l₂′)
                  ok₁)
               (refl ⊢Π) ok₂)
            ok₁))

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
    ∀ {a} →
    Function-extensionality a (lsuc a) →
    {A₁ A₂ : Set a} {B₁ : A₁ → Set a} {B₂ : A₂ → Set a} →
    (A₁≡A₂ : A₁ PE.≡ A₂) →
    ((x : A₁) → B₁ x PE.≡ B₂ (PE.subst (λ A → A) A₁≡A₂ x)) →
    ((x : A₁) → B₁ x) PE.≡ ((x : A₂) → B₂ x)
  Π-cong-Idˡ′ {a} fe {A₁} {A₂} {B₁} {B₂} A₁≡A₂ B₁≡B₂ =
    J′ (λ A₂ A₁≡A₂ →
          {B₂ : A₂ → Set a} →
          ((x : A₁) → B₁ x PE.≡ B₂ (PE.subst (λ A → A) A₁≡A₂ x)) →
          ((x : A₁) → B₁ x) PE.≡ ((x : A₂) → B₂ x))
       (λ {B₂} B₁≡B₂ →
          PE.cong (λ B → (x : A₁) → B x) {x = B₁} {y = B₂}
            (F.ext {A = A₁} {P = λ _ → Set a} {f = B₁} {g = B₂}
               fe B₁≡B₂))
       A₁≡A₂ B₁≡B₂

opaque
  unfolding cast cong subst

  -- A term used to state ⊢ΠΣ-cong-Idˡ.

  ΠΣ-cong-Idˡ :
    BinderMode → M → M → M → M → M → M → Lvl n → Term n → Term n →
    Term (1+ n) → Term n → Term (1+ n) → Term n → Term (1+ n) → Term n
  ΠΣ-cong-Idˡ b p q p′ q′ p″ q″ l ext A₁ B₁ A₂ B₂ t u =
    J ω ω (U l) A₁
      (Π p″ , q″ ▷ (Π p′ , q′ ▷ var x1 ▹ U (wk[ 3 ]′ l)) ▹
       (Π p″ , q″ ▷
         (Π p′ , q′ ▷ wk[ 3 ]′ A₁ ▹
          Id (U (wk[ 4 ]′ l)) (B₁ [ 4 ][ var x0 ]↑)
            (var x1 ∘⟨ p′ ⟩
             cast (wk[ 4 ]′ l) (wk[ 4 ]′ A₁) (var x3) (var x2)
               (var x0))) ▹
       Id (U (wk[ 4 ]′ l)) (wk[ 4 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
         (ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0))))
      (lam p″ $ lam p″ $
       cong ω (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U (wk1 l)))
         (wk[ 2 ]′ (lam p′ B₁)) (var x1) (U (wk[ 2 ]′ l))
         (ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0))
         (wk[ 2 ]′
            (ext ∘⟨ p′ ⟩ A₁ ∘⟨ p″ ⟩ lam p′ (U (wk1 l)) ∘⟨ p″ ⟩
             lam p′ B₁) ∘⟨ p″ ⟩
          var x1 ∘⟨ p″ ⟩ var x0))
      A₂ t ∘⟨ p″ ⟩
    lam p′ B₂ ∘⟨ p″ ⟩ lam p′ u

opaque
  unfolding Funext Is-function-extensionality ΠΣ-cong-Idˡ

  -- Allowed Π- and Σ-types preserve propositional equality in a
  -- certain sense, assuming that a certain form of function
  -- extensionality can be proved (and that certain Π-types are
  -- allowed).

  ⊢ΠΣ-cong-Idˡ :
    {Γ : Cons m n} →
    ΠΣ-allowed b p q →
    Π-allowed p′ q′ →
    Π-allowed p″ q″ →
    Is-function-extensionality p′ q′ p″ q″ l (1ᵘ+ l) Γ ext →
    Γ »∙ A₂ ⊢ B₂ ∷ U (wk1 l) →
    Γ ⊢ t ∷ Id (U l) A₁ A₂ →
    Γ »∙ A₁ ⊢ u ∷
      Id (U (wk1 l)) B₁
        (B₂ [ cast (wk1 l) (wk1 A₁) (wk1 A₂) (wk1 t) (var x0) ]↑) →
    Γ ⊢ ΠΣ-cong-Idˡ b p q p′ q′ p″ q″ l ext A₁ B₁ A₂ B₂ t u ∷
      Id (U l) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
  ⊢ΠΣ-cong-Idˡ
    {m} {n} {b} {p} {q} {p′} {q′} {p″} {q″}
    {l} {ext} {A₂} {B₂} {t} {A₁} {u} {B₁} {Γ}
    ok₁ ok₂ ok₃ ⊢ext ⊢B₂ ⊢t ⊢u =
    let _ , ⊢A₁ , ⊢A₂ = inversion-Id (wf-⊢ ⊢t)
        _ , ⊢B₁ , _   = inversion-Id (wf-⊢ ⊢u)
        ⊢l            = inversion-U-Level (wf-⊢ ⊢A₁)
    in
    check-type-and-term-sound
      γ′
      (I.base nothing I.» I.base)
      (I.J I.ω I.ω (I.U xl) xA₁
         (I.Π xp″ , xq″ ▷
            I.Π xp′ , xq′ ▷ I.var x1 ▹ I.U (IW.wk[ 3 ] xl) ▹
          I.Π xp″ , xq″ ▷
            I.Π xp′ , xq′ ▷ IW.wk[ 3 ] xA₁ ▹
            I.Id (I.U (IW.wk[ 4 ] xl))
              (I.subst xB₁ (I.cons (IS.wkSubst 4 I.id) (I.var x0)))
              (I.var x1 I.∘⟨ xp′ ⟩
               castᵢ (IW.wk[ 4 ] xl) (IW.wk[ 4 ] xA₁) (I.var x3)
                 (I.var x2) (I.var x0)) ▹
          I.Id (I.U (IW.wk[ 4 ] xl))
            (IW.wk[ 4 ] (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₁ ▹ xB₁))
            (I.ΠΣ⟨ xb ⟩ xp , xq ▷ I.var x3 ▹
             (I.var x2 I.∘⟨ xp′ ⟩ I.var x0)))
         (I.lam xp″ nothing $ I.lam xp″ nothing $
          congᵢ I.ω
            (IW.wk[ 2 ] (I.Π xp′ , xq′ ▷ xA₁ ▹ I.U (IW.wk[ 1 ] xl)))
            (IW.wk[ 2 ] (I.lam xp′ (just (xq′ , xA₁)) xB₁)) (I.var x1)
            (I.U (IW.wk[ 2 ] xl))
            (I.ΠΣ⟨ xb ⟩ xp , xq ▷ IW.wk[ 3 ] xA₁ ▹
             (I.var x1 I.∘⟨ xp′ ⟩ I.var x0))
            (IW.wk[ 2 ]
               (xfunext I.∘⟨ xp′ ⟩ xA₁ I.∘⟨ xp″ ⟩
                I.lam xp′ nothing (I.U (IW.wk[ 1 ] xl)) I.∘⟨ xp″ ⟩
                I.lam xp′ nothing xB₁) I.∘⟨ xp″ ⟩
             I.var x1 I.∘⟨ xp″ ⟩
             I.var x0))
         xA₂ xt I.∘⟨ xp″ ⟩
       I.lam xp′ nothing xB₂ I.∘⟨ xp″ ⟩
       I.lam xp′ nothing xu)
      (I.Id (I.U xl) (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₁ ▹ xB₁)
         (I.ΠΣ⟨ xb ⟩ xp , xq ▷ xA₂ ▹ xB₂))
      27
      PE.refl
      (λ where
         .IC.constraints-wf             → ok₁ L.∷ ok₂ L.∷ ok₃ L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → ⊢l
           (I.var! x1)         → ⊢A₁
           (I.var! x2)         → ⊢B₁
           (I.var! x3)         → ⊢A₂
           (I.var! x4)         → ⊢B₂
           (I.var! x5)         → ⊢t
           (I.var! x6)         → ⊢u
           (I.var! x7)         → ⊢ext
           (I.var  not-x8 _ _))
      (wf ⊢A₁)
      where
      c′ : I.Constants
      c′ .I.gs                 = 6
      c′ .I.ss                 = 0
      c′ .I.bms                = 1
      c′ .I.ms                 = 8
      c′ .I.base-dcon-size     = m
      c′ .I.base-con-size      = n
      c′ .I.base-con-allowed   = true
      c′ .I.meta-con-term-kind = lvl V.∷ V.replicate 7 tm
      c′ .I.meta-con-size      =
        n V.∷ n V.∷ 1+ n V.∷ n V.∷ 1+ n V.∷ n V.∷ 1+ n V.∷ n V.∷ V.ε

      xb : I.Termᵇᵐ 0 1
      xb = I.var x0

      xp xp′ xp″ xq xq′ xq″ : I.Termᵍ 6
      xp  = I.var x0
      xp′ = I.var x1
      xp″ = I.var x2
      xq  = I.var x3
      xq′ = I.var x4
      xq″ = I.var x5

      xl : I.Lvl c′ n
      xl = I.varᵐ x0

      xA₁ xA₂ xt xfunext : I.Term c′ n
      xA₁     = I.varᵐ x1
      xA₂     = I.varᵐ x3
      xt      = I.varᵐ x5
      xfunext = I.varᵐ x7

      xB₁ xB₂ xu : I.Term c′ (1+ n)
      xB₁ = I.varᵐ x2
      xB₂ = I.varᵐ x4
      xu  = I.varᵐ x6

      γ′ : I.Contexts c′
      γ′ .I.grades       = p V.∷ p′ V.∷ p″ V.∷ q V.∷ q′ V.∷ q″ V.∷ V.ε
      γ′ .I.strengths    = V.ε
      γ′ .I.binder-modes = b V.∷ V.ε
      γ′ .I.⌜base⌝       = Γ
      γ′ .I.constraints⁰ = I.emptyᶜ⁰
      γ′ .I.constraints⁺ =
        I.πσ-allowed xb xp xq L.∷
        I.π-allowed xp′ xq′   L.∷
        I.π-allowed xp″ xq″   L.∷
        L.[]
      γ′ .I.metas .I.equalities = L.[]
      γ′ .I.metas .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l
        (I.var! x1) → I.base , I.term A₁ (I.U xl)
        (I.var! x2) → I.base I.∙ xA₁ , I.term B₁ (I.U (IW.wk[ 1 ] xl))
        (I.var! x3) → I.base , I.term A₂ (I.U xl)
        (I.var! x4) → I.base I.∙ xA₂ , I.term B₂ (I.U (IW.wk[ 1 ] xl))
        (I.var! x5) → I.base , I.term t  (I.Id (I.U xl) xA₁ xA₂)
        (I.var! x6) →
          I.base I.∙ xA₁ ,
          I.term u
            (I.Id (I.U (IW.wk[ 1 ] xl)) xB₁
               (I.subst xB₂
                  (I.cons (I.wk1 I.id)
                     (I.J I.𝟙 I.𝟘 (I.U (IW.wk[ 1 ] xl)) (IW.wk[ 1 ] xA₁)
                        (IW.wk[ 1 ] (I.var x0)) (I.var x0)
                        (IW.wk[ 1 ] xA₂) (IW.wk[ 1 ] xt)))))
        (I.var! x7) →
          I.base , I.term ext (Funextᵢ xp′ xq′ xp″ xq″ xl (I.1ᵘ+ xl))
        (I.var not-x8 _ _)

opaque
  unfolding ΠΣ-cong-Idˡ

  -- A term used to state ⊢ΠΣ-cong-Idʳ.

  ΠΣ-cong-Idʳ :
    BinderMode → M → M → M → M → M → M → Lvl n → Term n → Term n →
    Term (1+ n) → Term n → Term (1+ n) → Term n → Term (1+ n) → Term n
  ΠΣ-cong-Idʳ b p q p′ q′ p″ q″ l ext A₁ B₁ A₂ B₂ t u =
    symmetry (U l) (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
      (ΠΣ-cong-Idˡ b p q p′ q′ p″ q″ l ext A₂ B₂ A₁ B₁ t
         (symmetry (U (wk1 l))
            (B₁ [ cast (wk1 l) (wk1 A₂) (wk1 A₁) (wk1 t) (var x0) ]↑) B₂
            u))

opaque
  unfolding ΠΣ-cong-Idʳ

  -- A variant of ⊢ΠΣ-cong-Idˡ.

  ⊢ΠΣ-cong-Idʳ :
    ΠΣ-allowed b p q →
    Π-allowed p′ q′ →
    Π-allowed p″ q″ →
    Is-function-extensionality p′ q′ p″ q″ l (1ᵘ+ l) Γ ext →
    Γ »∙ A₁ ⊢ B₁ ∷ U (wk1 l) →
    Γ ⊢ t ∷ Id (U l) A₂ A₁ →
    Γ »∙ A₂ ⊢ u ∷
      Id (U (wk1 l))
        (B₁ [ cast (wk1 l) (wk1 A₂) (wk1 A₁) (wk1 t) (var x0) ]↑) B₂ →
    Γ ⊢ ΠΣ-cong-Idʳ b p q p′ q′ p″ q″ l ext A₁ B₁ A₂ B₂ t u ∷
      Id (U l) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
  ⊢ΠΣ-cong-Idʳ ok ok′ ok″ ext ⊢B₁ ⊢t ⊢u =
    ⊢symmetry (⊢ΠΣ-cong-Idˡ ok ok′ ok″ ext ⊢B₁ ⊢t (⊢symmetry ⊢u))

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
    let _ , ⊢A₁ , ⊢A₂       = inversion-Id (wf-⊢ ⊢t)
        _ , ⊢cast-t₁ , ⊢t₂  = inversion-Id (wf-⊢ ⊢u)
        _ , ⊢cast-u₁ , ⊢u₂  = inversion-Id (wf-⊢ ⊢v)
        _ , _ , _ , ⊢t₁ , _ = inversion-cast ⊢cast-t₁
        _ , _ , _ , ⊢u₁ , _ = inversion-cast ⊢cast-u₁
        ⊢l                  = inversion-U-Level (wf-⊢ ⊢A₁)
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
              (castᵢ (IW.wk[ 4 ] xl) (IW.wk[ 4 ] xA₁) (I.var x3)
                 (I.var x2)
              (IW.wk[ 4 ] xt₁)) (I.var x1) ▹
          I.Π xp , xq ▷
            I.Id (I.var x4)
              (castᵢ (IW.wk[ 5 ] xl) (IW.wk[ 5 ] xA₁) (I.var x4)
                 (I.var x3) (IW.wk[ 5 ] xu₁))
              (I.var x1) ▹
          I.Id (I.U (IW.wk[ 6 ] xl)) (IW.wk[ 6 ] (I.Id xA₁ xt₁ xu₁))
            (I.Id (I.var x5) (I.var x3) (I.var x2)))
         (I.lam xp nothing $ I.lam xp nothing $ I.lam xp nothing $
          I.lam xp nothing $
          cong₂ᵢ I.ω (IW.wk[ 4 ] xA₁) (IW.wk[ 4 ] xt₁) (I.var x3)
            (IW.wk[ 4 ] xA₁) (IW.wk[ 4 ] xu₁) (I.var x2)
            (I.U (IW.wk[ 4 ] xl))
            (I.Id (IW.wk[ 6 ] xA₁) (I.var x1) (I.var x0)) (I.var x1)
            (I.var x0))
         xA₂ xt I.∘⟨ xp ⟩
       xt₂ I.∘⟨ xp ⟩ xu₂ I.∘⟨ xp ⟩ xu  I.∘⟨ xp ⟩ xv)
      (I.Id (I.U xl) (I.Id xA₁ xt₁ xu₁) (I.Id xA₂ xt₂ xu₂))
      29
      PE.refl
      (λ where
         .IC.constraints-wf             → ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)          → ⊢l
           (I.var! x1)          → ⊢A₁
           (I.var! x2)          → ⊢A₂
           (I.var! x3)          → ⊢t
           (I.var! x4)          → ⊢t₁
           (I.var! x5)          → ⊢t₂
           (I.var! x6)          → ⊢u
           (I.var! x7)          → ⊢u₁
           (I.var! x8)          → ⊢u₂
           (I.var! x9)          → ⊢v
           (I.var  not-x10 _ _))
      (wf ⊢A₁)
      where
      c′ : I.Constants
      c′ .I.gs                 = 2
      c′ .I.ss                 = 0
      c′ .I.bms                = 0
      c′ .I.ms                 = 10
      c′ .I.base-dcon-size     = m
      c′ .I.base-con-size      = n
      c′ .I.base-con-allowed   = true
      c′ .I.meta-con-size      = V.replicate 10 n
      c′ .I.meta-con-term-kind = lvl V.∷ V.replicate 9 tm

      xp xq : I.Termᵍ 2
      xp = I.var x0
      xq = I.var x1

      xl : I.Lvl c′ n
      xl = I.varᵐ x0

      xA₁ xA₂ xt xt₁ xt₂ xu xu₁ xu₂ xv : I.Term c′ n
      xA₁ = I.varᵐ x1
      xA₂ = I.varᵐ x2
      xt  = I.varᵐ x3
      xt₁ = I.varᵐ x4
      xt₂ = I.varᵐ x5
      xu  = I.varᵐ x6
      xu₁ = I.varᵐ x7
      xu₂ = I.varᵐ x8
      xv  = I.varᵐ x9

      γ′ : I.Contexts c′
      γ′ .I.grades              = p V.∷ q V.∷ V.ε
      γ′ .I.strengths           = V.ε
      γ′ .I.binder-modes        = V.ε
      γ′ .I.⌜base⌝              = Γ
      γ′ .I.constraints⁰        = I.emptyᶜ⁰
      γ′ .I.constraints⁺        = I.π-allowed xp xq L.∷ L.[]
      γ′ .I.metas .I.equalities = L.[]
      γ′ .I.metas .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l
        (I.var! x1) → I.base , I.term A₁ (I.U xl)
        (I.var! x2) → I.base , I.term A₂ (I.U xl)
        (I.var! x3) → I.base , I.term t (I.Id (I.U xl) xA₁ xA₂)
        (I.var! x4) → I.base , I.term t₁ xA₁
        (I.var! x5) → I.base , I.term t₂ xA₂
        (I.var! x6) →
          I.base , I.term u (I.Id xA₂ (castᵢ xl xA₁ xA₂ xt xt₁) xt₂)
        (I.var! x7) → I.base , I.term u₁ xA₁
        (I.var! x8) → I.base , I.term u₂ xA₂
        (I.var! x9) →
          I.base , I.term v (I.Id xA₂ (castᵢ xl xA₁ xA₂ xt xu₁) xu₂)
        (I.var not-x10 _ _)

opaque

  -- A variant of Id-cong-Idˡ.

  Id-cong-Idʳ :
    Π-allowed p q →
    Γ ⊢ t ∷ Id (U l) A₁ A₂ →
    Γ ⊢ u ∷ Id A₁ t₁ (cast⁻¹ l A₁ A₂ t t₂) →
    Γ ⊢ v ∷ Id A₁ u₁ (cast⁻¹ l A₁ A₂ t u₂) →
    ∃ λ w → Γ ⊢ w ∷ Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂)
  Id-cong-Idʳ ok ⊢t ⊢u ⊢v =
    Id-cong-Idˡ ok ⊢t (cast-right-left′ ⊢t ⊢u .proj₂)
      (cast-right-left′ ⊢t ⊢v .proj₂)

private opaque

  -- The following code illustrates roughly how lam-cong-Id below is
  -- defined.

  lam-cong-Id′ :
    ∀ {a b} →
    Function-extensionality a b →
    {A : Set a} {B : A → Set b} {t₁ t₂ : (x : A) → B x} →
    (∀ x → t₁ x PE.≡ t₂ x) →
    (λ x → t₁ x) PE.≡ (λ x → t₂ x)
  lam-cong-Id′ fe t₁≡t₂ =
    F.ext fe t₁≡t₂

opaque

  -- A term used to state ⊢lam-cong-Id.

  lam-cong-Id :
    M → M → Term n → Term n → Term (1+ n) → Term (1+ n) → Term (1+ n) →
    Term (1+ n) → Term n
  lam-cong-Id p p′ ext A B t₁ t₂ t =
    ext ∘⟨ p ⟩ A ∘⟨ p′ ⟩ lam p B ∘⟨ p′ ⟩ lam p t₁ ∘⟨ p′ ⟩
    lam p t₂ ∘⟨ p′ ⟩ lam p t

opaque
  unfolding Funext Is-function-extensionality lam-cong-Id

  -- Lambdas preserve propositional equality in a certain sense (for
  -- allowed Π-types), assuming that a certain form of function
  -- extensionality can be proved.

  ⊢lam-cong-Id :
    {Γ : Cons m n} →
    Π-allowed p q →
    Is-function-extensionality p q p′ q′ l₁ l₂ Γ ext →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ A ∷ U l₁ →
    Γ »∙ A ⊢ B ∷ U (wk1 l₂) →
    Γ »∙ A ⊢ t ∷ Id B t₁ t₂ →
    Γ ⊢ lam-cong-Id p p′ ext A B t₁ t₂ t ∷
      Id (Π p , q ▷ A ▹ B) (lam p t₁) (lam p t₂)
  ⊢lam-cong-Id
    {m} {n} {p} {q} {p′} {q′} {l₁} {l₂} {ext} {A} {B} {t} {t₁} {t₂} {Γ}
    ok ⊢ext ⊢l₂ ⊢A ⊢B ⊢t =
    let ⊢l₁           = inversion-U-Level (wf-⊢ ⊢A)
        _ , ⊢t₁ , ⊢t₂ = inversion-Id (wf-⊢ ⊢t)
    in
    check-type-and-term-sound
      γ′
      (I.base nothing I.» I.base)
      (xext I.∘⟨ xp ⟩ xA I.∘⟨ xp′ ⟩ I.lam xp nothing xB I.∘⟨ xp′ ⟩
       I.lam xp nothing xt₁ I.∘⟨ xp′ ⟩ I.lam xp nothing xt₂ I.∘⟨ xp′ ⟩
       I.lam xp nothing xt)
      (I.Id (I.Π xp , xq ▷ xA ▹ xB) (I.lam xp nothing xt₁)
         (I.lam xp nothing xt₂))
      14
      PE.refl
      (λ where
         .IC.constraints-wf             → ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → ⊢l₁
           (I.var! x1)         → ⊢l₂
           (I.var! x2)         → ⊢A
           (I.var! x3)         → ⊢B
           (I.var! x4)         → ⊢t₁
           (I.var! x5)         → ⊢t₂
           (I.var! x6)         → ⊢t
           (I.var! x7)         → ⊢ext
           (I.var  not-x8 _ _))
      (wf ⊢A)
      where
      c′ : I.Constants
      c′ .I.gs                 = 4
      c′ .I.ss                 = 0
      c′ .I.bms                = 0
      c′ .I.ms                 = 8
      c′ .I.base-dcon-size     = m
      c′ .I.base-con-size      = n
      c′ .I.base-con-allowed   = true
      c′ .I.meta-con-term-kind = lvl V.∷ lvl V.∷ V.replicate 6 tm
      c′ .I.meta-con-size      =
        n V.∷ n V.∷ n V.∷ 1+ n V.∷ 1+ n V.∷ 1+ n V.∷ 1+ n V.∷ n V.∷ V.ε

      xp xp′ xq xq′ : I.Termᵍ 4
      xp  = I.var x0
      xp′ = I.var x1
      xq  = I.var x2
      xq′ = I.var x3

      xl₁ xl₂ : I.Lvl c′ n
      xl₁ = I.varᵐ x0
      xl₂ = I.varᵐ x1

      xA xext : I.Term c′ n
      xA   = I.varᵐ x2
      xext = I.varᵐ x7

      xB xt₁ xt₂ xt : I.Term c′ (1+ n)
      xB  = I.varᵐ x3
      xt₁ = I.varᵐ x4
      xt₂ = I.varᵐ x5
      xt  = I.varᵐ x6

      γ′ : I.Contexts c′
      γ′ .I.grades              = p V.∷ p′ V.∷ q V.∷ q′ V.∷ V.ε
      γ′ .I.strengths           = V.ε
      γ′ .I.binder-modes        = V.ε
      γ′ .I.⌜base⌝              = Γ
      γ′ .I.constraints⁰        = I.emptyᶜ⁰
      γ′ .I.constraints⁺        = I.π-allowed xp xq L.∷ L.[]
      γ′ .I.metas .I.equalities = L.[]
      γ′ .I.metas .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l₁
        (I.var! x1) → I.base , I.level l₂
        (I.var! x2) → I.base , I.term A (I.U xl₁)
        (I.var! x3) → I.base I.∙ xA , I.term B (I.U (IW.wk[ 1 ] xl₂))
        (I.var! x4) → I.base I.∙ xA , I.term t₁ xB
        (I.var! x5) → I.base I.∙ xA , I.term t₂ xB
        (I.var! x6) → I.base I.∙ xA , I.term t (I.Id xB xt₁ xt₂)
        (I.var! x7) →
          I.base , I.term ext (Funextᵢ xp xq xp′ xq′ xl₁ xl₂)
        (I.var not-x8 _ _)
