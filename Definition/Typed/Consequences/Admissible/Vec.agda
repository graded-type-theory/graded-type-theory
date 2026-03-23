------------------------------------------------------------------------
-- Typing and equality rules related to Vec
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Consequences.Admissible.Vec
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (open Definition.Untyped M)
  (s : Strength)
  (p : M)
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that a certain unit type is allowed.
  (Unit-ok : Unit-allowed s)
  -- It is assumed that a certain Σ-type is allowed
  (Σ-ok : Σ-allowed s p 𝟘)
  where

private module M = Modality 𝕄

open import Definition.Typed R
open import Definition.Typed.Decidable.Internal 𝐌 R
import Definition.Typed.Decidable.Internal.Context 𝐌 R as IC
import Definition.Typed.Decidable.Internal.Substitution 𝐌 R as IS
import Definition.Typed.Decidable.Internal.Term 𝐌 R as I
import Definition.Typed.Decidable.Internal.Tests 𝐌 R as IT
import Definition.Typed.Decidable.Internal.Weakening 𝐌 R as IW
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Well-formed R

open import Definition.Untyped.Vec 𝕄 𝐌 s p as Vec

open Vec.Internal R

open import Tools.Bool
open import Tools.Fin
open import Tools.List as L using (List)
open import Tools.Maybe
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Vec as V

private variable
  m ms n                                       : Nat
  A A₁ A₂ B t t₁ t₂ t₃ t₄ t₅ u u₁ u₂ v v₁ v₂ w : Term _
  l l₁                                         : Lvl _
  Γ                                            : Cons _ _
  p₁ p₂ q q₁ q₂ q₃ q₄ r                        : M

-- Some definitions used below.

private
  module Defs
    (p₁ p₂ q₁ q₂ q₃ q₄ r : M) (Γ : Cons m n)
    (meta-con-size : V.Vec Nat ms)
    where
    c : I.Constants
    c .I.gs                 = 8
    c .I.ss                 = 1
    c .I.bms                = 0
    c .I.ms                 = 1+ ms
    c .I.base-dcon-size     = m
    c .I.base-con-size      = n
    c .I.base-con-allowed   = true
    c .I.meta-con-term-kind = lvl V.∷ V.replicate ms tm
    c .I.meta-con-size      = n V.∷ meta-con-size

    xp xp₁ xp₂ xq xq₁ xq₂ xq₃ xq₄ xr : I.Termᵍ 8
    xp  = I.var x0
    xp₁ = I.var x1
    xp₂ = I.var x2
    xq₁ = I.var x3
    xq  = xq₁
    xq₂ = I.var x4
    xq₃ = I.var x5
    xq₄ = I.var x6
    xr  = I.var x7

    xs : I.Termˢ 1
    xs = I.var x0

    xl : I.Lvl c n
    xl = I.varᵐ x0

    γ :
      List (I.Constraint⁺ c) →
      (∀ {k n} (x : I.Meta-var c k n) →
       I.Con c n × I.Type-or-term c k n) →
      I.Contexts c
    γ _  _ .I.grades              = p V.∷ p₁ V.∷ p₂ V.∷ q₁ V.∷ q₂ V.∷
                                     q₃ V.∷ q₄ V.∷ r V.∷ V.ε
    γ _  _ .I.strengths           = s V.∷ V.ε
    γ _  _ .I.binder-modes        = V.ε
    γ _  _ .I.⌜base⌝              = Γ
    γ _  Μ .I.metas .I.bindings   = Μ
    γ _  _ .I.metas .I.equalities = L.[]
    γ _  _ .I.constraints⁰        = I.emptyᶜ⁰
    γ cs _ .I.constraints⁺        =
      cs L.++ I.unit-allowed xs L.∷ I.σ-allowed xs xp I.𝟘 L.∷ L.[]

    γ′ :
      List (I.Constraint⁺ c) →
      I.Meta-con c →
      I.Contexts c
    γ′ cs Μ = record (γ cs (Μ .I.bindings)) { metas = Μ }

------------------------------------------------------------------------
-- Some admissible typing and equality rules for Vec′

opaque
  unfolding Vec′

  -- An equality rule for Vec′.

  Vec′-cong :
    {Γ : Cons m n} →
    Γ ⊢ A₁ ≡ A₂ ∷ U l →
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ →
    Γ ⊢ Vec′ l A₁ t₁ ≡ Vec′ l A₂ t₂ ∷ U l
  Vec′-cong {m} {n} {A₁} {A₂} {l} {t₁} {t₂} {Γ} A₁≡A₂ t₁≡t₂ =
    let _ , ⊢A₁ , ⊢A₂ = wf-⊢≡∷ A₁≡A₂
        _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
        ⊢l            = inversion-U-Level (wf-⊢∷ ⊢A₁)
        ⊢Γ            = wf ⊢A₁
    in
    check-and-equal-type-and-terms-sound
      γ
      (I.base nothing I.» I.base)
      (Vec′ᵢ xs xp xl xA₁ xt₁)
      (Vec′ᵢ xs xp xl xA₂ xt₂)
      (I.U xl)
      10
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf →
           (reflConEq ⊢Γ , IC.term (refl (⊢U ⊢l)) A₁≡A₂) L.∷
           (reflConEq ⊢Γ , IC.term (refl (⊢ℕ ⊢Γ)) t₁≡t₂) L.∷
           L.[]
         .IC.metas-wf .IC.bindings-wf → λ where
           (I.var! x0)         → ⊢l
           (I.var! x1)         → ⊢A₁
           (I.var! x2)         → ⊢A₂
           (I.var! x3)         → ⊢t₁
           (I.var! x4)         → ⊢t₂
           (I.var  not-x5 _ _))
      ⊢Γ
      where
      c : I.Constants
      c .I.gs                 = 1
      c .I.ss                 = 1
      c .I.bms                = 0
      c .I.ms                 = 5
      c .I.base-dcon-size     = m
      c .I.base-con-allowed   = true
      c .I.base-con-size      = n
      c .I.meta-con-term-kind = lvl V.∷ V.replicate 4 tm
      c .I.meta-con-size      = n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ V.ε

      xp : I.Termᵍ 1
      xp = I.var x0

      xs : I.Termˢ 1
      xs = I.var x0

      xl : I.Lvl c n
      xl = I.varᵐ x0

      xA₁ xA₂ xt₁ xt₂ : I.Term c n
      xA₁ = I.varᵐ x1
      xA₂ = I.varᵐ x2
      xt₁ = I.varᵐ x3
      xt₂ = I.varᵐ x4

      γ : I.Contexts c
      γ .I.grades       = p V.∷ V.ε
      γ .I.strengths    = s V.∷ V.ε
      γ .I.binder-modes = V.ε
      γ .I.⌜base⌝       = Γ
      γ .I.constraints⁰ = I.emptyᶜ⁰
      γ .I.constraints⁺ =
        I.unit-allowed xs     L.∷
        I.σ-allowed xs xp I.𝟘 L.∷
        L.[]
      γ .I.metas .I.equalities =
        (_ , IT.meta xA₁ , IT.meta xA₂) L.∷
        (_ , IT.meta xt₁ , IT.meta xt₂) L.∷
        L.[]
      γ .I.metas .I.bindings = λ where
        (I.var! x0)        → I.base , I.level l
        (I.var! x1)        → I.base , I.term A₁ (I.U xl)
        (I.var! x2)        → I.base , I.term A₂ (I.U xl)
        (I.var! x3)        → I.base , I.term t₁ I.ℕ
        (I.var! x4)        → I.base , I.term t₂ I.ℕ
        (I.var not-x5 _ _)

opaque

  -- A typing rule for Vec′.

  ⊢Vec′ :
    {Γ : Cons m n} →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ Vec′ l A t ∷ U l
  ⊢Vec′ ⊢A ⊢t =
    wf-⊢≡∷ (Vec′-cong (refl ⊢A) (refl ⊢t)) .proj₂ .proj₁

opaque
  unfolding Vec′

  -- An equality rule for Vec′.

  ⊢Vec′-zero≡ :
    {Γ : Cons m n} →
    Γ ⊢ A ∷ U l →
    Γ ⊢ Vec′ l A zero ≡ Lift l (Unit s) ∷ U l
  ⊢Vec′-zero≡ {n} {A} {l} {Γ} ⊢A =
    check-and-equal-type-and-terms-sound
      (γ L.[] λ where
         (I.var! x0)        → I.base , I.level l
         (I.var! x1)        → I.base , I.term A (I.U xl)
         (I.var not-x2 _ _))
      (I.base nothing I.» I.base)
      (Vec′ᵢ xs xp xl xA I.zero)
      (I.Lift xl (I.Unit xs))
      (I.U xl)
      10
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → inversion-U-Level (wf-⊢∷ ⊢A)
           (I.var! x1)         → ⊢A
           (I.var  not-x2 _ _))
      (wf ⊢A)
      where
      open Defs p p p p p p p Γ (n V.∷ V.ε)

      xA : I.Term c n
      xA = I.varᵐ x1

opaque
  unfolding Vec′

  -- An equality rule for Vec.

  ⊢Vec′-suc≡ :
    {Γ : Cons m n} →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ Vec′ l A (suc t) ≡ Σ⟨ s ⟩ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A t) ∷ U l
  ⊢Vec′-suc≡ {n} {A} {l} {t} {Γ} ⊢A ⊢t =
    check-and-equal-type-and-terms-sound
      (γ L.[] λ where
         (I.var! x0)        → I.base , I.level l
         (I.var! x1)        → I.base , I.term A (I.U xl)
         (I.var! x2)        → I.base , I.term t I.ℕ
         (I.var not-x3 _ _))
      (I.base nothing I.» I.base)
      (Vec′ᵢ xs xp xl xA (I.suc xt))
      (I.ΠΣ⟨ I.BMΣ xs ⟩ xp , I.𝟘 ▷ xA ▹
       IW.wk[ 1 ] (Vec′ᵢ xs xp xl xA xt))
      (I.U xl)
      12
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → inversion-U-Level (wf-⊢∷ ⊢A)
           (I.var! x1)         → ⊢A
           (I.var! x2)         → ⊢t
           (I.var  not-x3 _ _))
      (wf ⊢A)
      where
      open Defs p p p p p p p Γ (n V.∷ n V.∷ V.ε)

      xA xt : I.Term c n
      xA = I.varᵐ x1
      xt = I.varᵐ x2

------------------------------------------------------------------------
-- Some admissible typing and equality rules for Vec

opaque
  unfolding Vec Vec′

  -- A typing rule for Vec.

  ⊢Vec :
    {Γ : Cons m n} →
    Π-allowed 𝟙 q →
    Π-allowed 𝟙 r →
    Γ ⊢ l ∷Level →
    Γ ⊢ Vec l ∷ Π 𝟙 , q ▷ U l ▹ (Π 𝟙 , r ▷ ℕ ▹ U (wk[ 2 ]′ l))
  ⊢Vec {n} {q} {r} {l} {Γ} Π-ok₁ Π-ok₂ ⊢l =
    check-type-and-term-sound
      (γ (I.π-allowed I.𝟙 xq L.∷ I.π-allowed I.𝟙 xr L.∷ L.[]) λ where
         (I.var! x0)        → I.base , I.level l
         (I.var not-x1 _ _))
      (I.base nothing I.» I.base)
      (Vecᵢ xs xp xq xr xl)
      (I.Π I.𝟙 , xq ▷ I.U xl ▹ I.Π I.𝟙 , xr ▷ I.ℕ ▹ I.U (IW.wk[ 2 ] xl))
      12
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok₁ L.∷ Π-ok₂ L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → ⊢l
           (I.var  not-x1 _ _))
      (wf ⊢l)
      where
      open Defs p p q q q q r Γ V.ε

opaque
  unfolding Vec Vec′

  -- An equality rule for Vec.

  ⊢Vec-zero≡ :
    {Γ : Cons m n} →
    Π-allowed 𝟙 q →
    Π-allowed 𝟙 r →
    Γ ⊢ A ∷ U l →
    Γ ⊢ Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ zero ≡ Lift l (Unit s) ∷ U l
  ⊢Vec-zero≡ {n} {q} {r} {A} {l} {Γ} Π-ok₁ Π-ok₂ ⊢A =
    check-and-equal-type-and-terms-sound
      (γ (I.π-allowed I.𝟙 xq L.∷ I.π-allowed I.𝟙 xr L.∷ L.[]) λ where
         (I.var! x0)        → I.base , I.level l
         (I.var! x1)        → I.base , I.term A (I.U xl)
         (I.var not-x2 _ _))
      (I.base nothing I.» I.base)
      (Vecᵢ xs xp xq xr xl I.∘⟨ I.𝟙 ⟩ xA I.∘⟨ I.𝟙 ⟩ I.zero)
      (I.Lift xl (I.Unit xs))
      (I.U xl)
      14
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok₁ L.∷ Π-ok₂ L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → inversion-U-Level (wf-⊢∷ ⊢A)
           (I.var! x1)         → ⊢A
           (I.var  not-x2 _ _))
      (wf ⊢A)
      where
      open Defs p p q q q q r Γ (n V.∷ V.ε)

      xA : I.Term c n
      xA = I.varᵐ x1

opaque
  unfolding Vec Vec′

  -- An equality rule for Vec.

  ⊢Vec-suc≡ :
    {Γ : Cons m n} →
    Π-allowed 𝟙 q →
    Π-allowed 𝟙 r →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ suc t ≡
      Σ⟨ s ⟩ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A t) ∷ U l
  ⊢Vec-suc≡ {n} {q} {r} {A} {l} {t} {Γ} Π-ok₁ Π-ok₂ ⊢A ⊢t =
    check-and-equal-type-and-terms-sound
      (γ (I.π-allowed I.𝟙 xq L.∷ I.π-allowed I.𝟙 xr L.∷ L.[]) λ where
         (I.var! x0)        → I.base , I.level l
         (I.var! x1)        → I.base , I.term A (I.U xl)
         (I.var! x2)        → I.base , I.term t I.ℕ
         (I.var not-x3 _ _))
      (I.base nothing I.» I.base)
      (Vecᵢ xs xp xq xr xl I.∘⟨ I.𝟙 ⟩ xA I.∘⟨ I.𝟙 ⟩ I.suc xt)
      (I.ΠΣ⟨ I.BMΣ xs ⟩ xp , I.𝟘 ▷ xA ▹
       IW.wk[ 1 ] (Vec′ᵢ xs xp xl xA xt))
      (I.U xl)
      14
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok₁ L.∷ Π-ok₂ L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → inversion-U-Level (wf-⊢∷ ⊢A)
           (I.var! x1)         → ⊢A
           (I.var! x2)         → ⊢t
           (I.var  not-x3 _ _))
      (wf ⊢A)
      where
      open Defs p p q q q q r Γ (n V.∷ n V.∷ V.ε)

      xA xt : I.Term c n
      xA = I.varᵐ x1
      xt = I.varᵐ x2

------------------------------------------------------------------------
-- Some admissible typing rules for nil′ and nil

opaque
  unfolding Vec′ nil′

  -- A typing rule for nil′.

  ⊢nil′ :
    {Γ : Cons m n} →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nil′ A ∷ Vec′ l A zero
  ⊢nil′ {n} {A} {l} {Γ} ⊢A =
    check-type-and-term-sound
      (γ L.[] λ where
         (I.var! x0)        → I.base , I.level l
         (I.var! x1)        → I.base , I.term A (I.U xl)
         (I.var not-x2 _ _))
      (I.base nothing I.» I.base)
      (nil′ᵢ xs)
      (Vec′ᵢ xs xp xl xA I.zero)
      11
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → inversion-U-Level (wf-⊢∷ ⊢A)
           (I.var! x1)         → ⊢A
           (I.var  not-x2 _ _))
      (wf ⊢A)
      where
      open Defs p p p p p p p Γ (n V.∷ V.ε)

      xA : I.Term c n
      xA = I.varᵐ x1

opaque
  unfolding Vec Vec′ nil nil′

  -- A typing rule for nil.

  ⊢nil :
    {Γ : Cons m n} →
    Π-allowed 𝟘 q →
    Π-allowed 𝟙 r →
    Γ ⊢ l ∷Level →
    Γ ⊢ nil ∷ Π 𝟘 , q ▷ U l ▹ (Vec (wk1 l) ∘⟨ 𝟙 ⟩ var x0 ∘⟨ 𝟙 ⟩ zero)
  ⊢nil {n} {q} {r} {l} {Γ} Π-ok₁ Π-ok₂ ⊢l =
    check-type-and-term-sound
      (γ (I.π-allowed I.𝟘 xq L.∷ I.π-allowed I.𝟙 xr L.∷ L.[]) λ where
         (I.var! x0)        → I.base , I.level l
         (I.var not-x1 _ _))
      (I.base nothing I.» I.base)
      (nilᵢ xs)
      (I.Π I.𝟘 , xq ▷ I.U xl ▹
       (Vecᵢ xs xp xr xr (IW.wk[ 1 ] xl) I.∘⟨ I.𝟙 ⟩ I.var x0 I.∘⟨ I.𝟙 ⟩
        I.zero))
      16
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok₁ L.∷ Π-ok₂ L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → ⊢l
           (I.var  not-x1 _ _))
      (wf ⊢l)
      where
      open Defs p p q q q q r Γ V.ε

------------------------------------------------------------------------
-- Some admissible typing and equality rules for cons′ and cons

opaque
  unfolding Vec′ cons′

  -- An equality rule for cons′.

  cons′-cong :
    {Γ : Cons m n} →
    Γ ⊢ A₁ ∷ U l₁ →
    Γ ⊢ t₁ ∷ ℕ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊢ v₁ ≡ v₂ ∷ Vec′ l₁ A₁ t₁ →
    Γ ⊢ cons′ A₁ t₁ u₁ v₁ ≡ cons′ A₂ t₂ u₂ v₂ ∷ Vec′ l₁ A₁ (suc t₁)
  cons′-cong
    {m} {n} {A₁} {l₁} {t₁} {u₁} {u₂} {v₁} {v₂} {Γ} ⊢A₁ ⊢t₁ u₁≡u₂ v₁≡v₂ =
    let _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
        _ , ⊢v₁ , ⊢v₂ = wf-⊢≡∷ v₁≡v₂
        ⊢l₁           = inversion-U-Level (wf-⊢∷ ⊢A₁)
        ⊢Γ            = wf ⊢A₁
    in
    check-and-equal-type-and-terms-sound
      γ
      (I.base nothing I.» I.base)
      (cons′ᵢ xs xp xu₁ xv₁)
      (cons′ᵢ xs xp xu₂ xv₂)
      (Vec′ᵢ xs xp xl₁ xA₁ (I.suc xt₁))
      13
      PE.refl
      (λ where
         .IC.constraints-wf →
           Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf →
           (reflConEq ⊢Γ , IC.term (refl (univ ⊢A₁)) u₁≡u₂) L.∷
           (reflConEq ⊢Γ ,
            IC.term (refl (univ (⊢Vec′ ⊢A₁ ⊢t₁))) v₁≡v₂) L.∷
           L.[]
         .IC.metas-wf .IC.bindings-wf → λ where
           (I.var! x0)         → ⊢l₁
           (I.var! x1)         → ⊢A₁
           (I.var! x2)         → ⊢t₁
           (I.var! x3)         → ⊢u₁
           (I.var! x4)         → ⊢u₂
           (I.var! x5)         → ⊢v₁
           (I.var! x6)         → ⊢v₂
           (I.var  not-x7 _ _))
      ⊢Γ
      where
      c : I.Constants
      c .I.gs                 = 1
      c .I.ss                 = 1
      c .I.bms                = 0
      c .I.ms                 = 7
      c .I.base-dcon-size     = m
      c .I.base-con-allowed   = true
      c .I.base-con-size      = n
      c .I.meta-con-term-kind = lvl V.∷ V.replicate 6 tm
      c .I.meta-con-size      =
        n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ n V.∷ V.ε

      xp : I.Termᵍ 1
      xp = I.var x0

      xs : I.Termˢ 1
      xs = I.var x0

      xl₁ : I.Lvl c n
      xl₁ = I.varᵐ x0

      xA₁ xt₁ xu₁ xu₂ xv₁ xv₂ : I.Term c n
      xA₁ = I.varᵐ x1
      xt₁ = I.varᵐ x2
      xu₁ = I.varᵐ x3
      xu₂ = I.varᵐ x4
      xv₁ = I.varᵐ x5
      xv₂ = I.varᵐ x6

      γ : I.Contexts c
      γ .I.grades       = p V.∷ V.ε
      γ .I.strengths    = s V.∷ V.ε
      γ .I.binder-modes = V.ε
      γ .I.⌜base⌝       = Γ
      γ .I.constraints⁰ = I.emptyᶜ⁰
      γ .I.constraints⁺ =
        I.unit-allowed xs     L.∷
        I.σ-allowed xs xp I.𝟘 L.∷
        L.[]
      γ .I.metas .I.equalities =
        (_ , IT.meta xu₁ , IT.meta xu₂) L.∷
        (_ , IT.meta xv₁ , IT.meta xv₂) L.∷
        L.[]
      γ .I.metas .I.bindings = λ where
        (I.var! x0) → I.base , I.level l₁
        (I.var! x1) → I.base , I.term A₁ (I.U xl₁)
        (I.var! x2) → I.base , I.term t₁ I.ℕ
        (I.var! x3) → I.base , I.term u₁ xA₁
        (I.var! x4) → I.base , I.term u₂ xA₁
        (I.var! x5) → I.base , I.term v₁ (Vec′ᵢ xs xp xl₁ xA₁ xt₁)
        (I.var! x6) → I.base , I.term v₂ (Vec′ᵢ xs xp xl₁ xA₁ xt₁)
        (I.var not-x7 _ _)

opaque

  -- A typing rule for cons′.

  ⊢cons′ :
    {Γ : Cons m n} →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ u ∷ A →
    Γ ⊢ v ∷ Vec′ l A t →
    Γ ⊢ cons′ A t u v ∷ Vec′ l A (suc t)
  ⊢cons′ ⊢A ⊢t ⊢u ⊢v =
    wf-⊢≡∷ (cons′-cong {A₂ = ℕ} {t₂ = ℕ} ⊢A ⊢t (refl ⊢u) (refl ⊢v))
      .proj₂ .proj₁

opaque
  unfolding Vec′ cons cons′

  -- A typing rule for cons.

  ⊢cons :
    {Γ : Cons m n} →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟙 q₃ →
    Π-allowed 𝟙 q₄ →
    Γ ⊢ l ∷Level →
    Γ ⊢ cons ∷
      Π 𝟘 , q₁ ▷ U l ▹ Π 𝟘 , q₂ ▷ ℕ ▹ Π 𝟙 , q₃ ▷ var x1 ▹
      Π 𝟙 , q₄ ▷ Vec′ (wk[ 3 ]′ l) (var x2) (var x1) ▹
      Vec′ (wk[ 4 ]′ l) (var x3) (suc (var x2))
  ⊢cons {n} {q₁} {q₂} {q₃} {q₄} {l} {Γ} Π-ok₁ Π-ok₂ Π-ok₃ Π-ok₄ ⊢l =
    check-type-and-term-sound
      (γ (I.π-allowed I.𝟘 xq₁ L.∷
          I.π-allowed I.𝟘 xq₂ L.∷
          I.π-allowed I.𝟙 xq₃ L.∷
          I.π-allowed I.𝟙 xq₄ L.∷
          L.[]) λ where
         (I.var! x0)        → I.base , I.level l
         (I.var not-x1 _ _))
      (I.base nothing I.» I.base)
      (consᵢ xs xp)
      (I.Π I.𝟘 , xq₁ ▷ I.U xl ▹ I.Π I.𝟘 , xq₂ ▷ I.ℕ ▹
       I.Π I.𝟙 , xq₃ ▷ I.var x1 ▹
       I.Π I.𝟙 , xq₄ ▷
         Vec′ᵢ xs xp (IW.wk[ 3 ] xl) (I.var x2) (I.var x1) ▹
       (Vec′ᵢ xs xp (IW.wk[ 4 ] xl) (I.var x3) (I.suc (I.var x2))))
      17
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok₁ L.∷ Π-ok₂ L.∷ Π-ok₃ L.∷ Π-ok₄ L.∷ Unit-ok L.∷ Σ-ok L.∷
           L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → ⊢l
           (I.var  not-x1 _ _))
      (wf ⊢l)
      where
      open Defs p p q₁ q₂ q₃ q₄ q₁ Γ V.ε

------------------------------------------------------------------------
-- Some admissible typing and equality rules for vecrec′

opaque
  unfolding Vec′ cons′ nil′ replace₂ vecrec′ vecrec-nil vecrec-cons

  -- A typing rule for vecrec′.

  ⊢vecrec′ :
    {Γ : Cons m n} →
    s PE.≡ 𝕨 →
    Π-allowed r q₂ →
    Γ ⊢ A ∷ U l →
    Γ »∙ ℕ »∙ Vec′ (wk1 l) (wk1 A) (var x0) ⊢ B →
    Γ ⊢ t ∷ B [ zero , nil′ A ]₁₀ →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ (wk[ 2 ]′ l) (wk₂ A) (var x1) »∙
      B [ wk1Subst idSubst ⇑ ] ⊢
      u ∷
      B [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3)))
            (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ] →
    Γ ⊢ v ∷ ℕ →
    Γ ⊢ w ∷ Vec′ l A v →
    Γ ⊢ vecrec′ p₁ p₂ r q₁ q₂ l A B t u v w ∷ B [ v , w ]₁₀
  ⊢vecrec′
    {n} {r} {q₂} {A} {l} {B} {t} {u} {v} {w} {p₁} {p₂} {q₁} {Γ}
    PE.refl Π-ok ⊢A ⊢B ⊢t ⊢u ⊢v ⊢w =
    check-type-and-term-sound
      (record (γ′ L.[] Μ)
         { constraints⁺ =
             I.π-allowed xr xq₂     L.∷
             I.unit-allowed I.𝕨     L.∷
             I.σ-allowed I.𝕨 xp I.𝟘 L.∷
             L.[]
         })
      (I.base nothing I.» I.base)
      (vecrecᵢ I.𝕨 xp xp₁ xp₂ xr xq₁ xq₂ xl xA xB xt xu xv xw)
      (I.subst xB (I.cons (IS.sgSubst xv) xw))
      22
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → inversion-U-Level (wf-⊢∷ ⊢A)
           (I.var! x1)         → ⊢A
           (I.var! x2)         → ⊢B
           (I.var! x3)         → ⊢t
           (I.var! x4)         → ⊢u
           (I.var! x5)         → ⊢v
           (I.var! x6)         → ⊢w
           (I.var  not-x7 _ _))
      (wf ⊢A)
      where
      open Defs p₁ p₂ q₁ q₂ r r r Γ
             (n V.∷ 2+ n V.∷ n V.∷ 4+ n V.∷ n V.∷ n V.∷ V.ε)

      xA xt xv xw : I.Term c n
      xA = I.varᵐ x1
      xt = I.varᵐ x3
      xv = I.varᵐ x5
      xw = I.varᵐ x6

      xB : I.Term c (2+ n)
      xB = I.varᵐ x2

      xu : I.Term c (4+ n)
      xu = I.varᵐ x4

      Μ : I.Meta-con c
      Μ .I.equalities = L.[]
      Μ .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l
        (I.var! x1) → I.base , I.term A (I.U xl)
        (I.var! x2) →
          I.base I.∙ I.ℕ I.∙
          Vec′ᵢ I.𝕨 xp (IW.wk[ 1 ] xl) (IW.wk[ 1 ] xA) (I.var x0) ,
          I.type B
        (I.var! x3) →
          I.base ,
          I.term t (I.subst xB (I.cons (IS.sgSubst I.zero) (nil′ᵢ I.𝕨)))
        (I.var! x4) →
          I.base I.∙ I.ℕ I.∙ IW.wk[ 1 ] xA I.∙
          Vec′ᵢ I.𝕨 xp (IW.wk[ 2 ] xl) (IW.wk[ 2 ] xA) (I.var x1) I.∙
          I.subst xB (I.wk1 I.id I.⇑) ,
          I.term u
            (I.subst xB
               (I.cons
                  (I.cons (IS.wkSubst 4 I.id) (I.suc (I.var x3)))
                  (cons′ᵢ I.𝕨 xp (I.var x2) (I.var x1))))
        (I.var! x5) → I.base , I.term v I.ℕ
        (I.var! x6) → I.base , I.term w (Vec′ᵢ I.𝕨 xp xl xA xv)
        (I.var not-x7 _ _)

opaque
  unfolding Vec′ cons′ nil′ replace₂ vecrec′ vecrec-nil vecrec-cons

  -- An equality rule for vecrec′.

  ⊢vecrec′-nil′≡ :
    {Γ : Cons m n} →
    s PE.≡ 𝕨 →
    Π-allowed r q₂ →
    Γ ⊢ A ∷ U l →
    Γ »∙ ℕ »∙ Vec′ (wk1 l) (wk1 A) (var x0) ⊢ B →
    Γ ⊢ t ∷ B [ zero , nil′ A ]₁₀ →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ (wk[ 2 ]′ l) (wk[ 2 ]′ A) (var x1) »∙
      B [ wk1Subst idSubst ⇑ ] ⊢
      u ∷
      B [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3)))
            (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ] →
    Γ ⊢ vecrec′ p₁ p₂ r q₁ q₂ l A B t u zero (nil′ A) ≡ t ∷
      B [ zero , nil′ A ]₁₀
  ⊢vecrec′-nil′≡
    {n} {r} {q₂} {A} {l} {B} {t} {u} {p₁} {p₂} {q₁} {Γ}
    PE.refl Π-ok ⊢A ⊢B ⊢t ⊢u =
    check-and-equal-type-and-terms-sound
      (record (γ′ L.[] Μ)
         { constraints⁺ =
             I.π-allowed xr xq₂     L.∷
             I.unit-allowed I.𝕨     L.∷
             I.σ-allowed I.𝕨 xp I.𝟘 L.∷
             L.[]
         })
      (I.base nothing I.» I.base)
      (vecrecᵢ I.𝕨 xp xp₁ xp₂ xr xq₁ xq₂ xl xA xB xt xu I.zero
         (nil′ᵢ I.𝕨))
      xt
      (I.subst xB (I.cons (IS.sgSubst I.zero) (nil′ᵢ I.𝕨)))
      22
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → inversion-U-Level (wf-⊢∷ ⊢A)
           (I.var! x1)         → ⊢A
           (I.var! x2)         → ⊢B
           (I.var! x3)         → ⊢t
           (I.var! x4)         → ⊢u
           (I.var  not-x5 _ _))
      (wf ⊢A)
      where
      open Defs p₁ p₂ q₁ q₂ r r r Γ (n V.∷ 2+ n V.∷ n V.∷ 4+ n V.∷ V.ε)

      xA xt : I.Term c n
      xA = I.varᵐ x1
      xt = I.varᵐ x3

      xB : I.Term c (2+ n)
      xB = I.varᵐ x2

      xu : I.Term c (4+ n)
      xu = I.varᵐ x4

      Μ : I.Meta-con c
      Μ .I.equalities = L.[]
      Μ .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l
        (I.var! x1) → I.base , I.term A (I.U xl)
        (I.var! x2) →
          I.base I.∙ I.ℕ I.∙
          Vec′ᵢ I.𝕨 xp (IW.wk[ 1 ] xl) (IW.wk[ 1 ] xA) (I.var x0) ,
          I.type B
        (I.var! x3) →
          I.base ,
          I.term t (I.subst xB (I.cons (IS.sgSubst I.zero) (nil′ᵢ I.𝕨)))
        (I.var! x4) →
          I.base I.∙ I.ℕ I.∙ IW.wk[ 1 ] xA I.∙
          Vec′ᵢ I.𝕨 xp (IW.wk[ 2 ] xl) (IW.wk[ 2 ] xA) (I.var x1) I.∙
          I.subst xB (I.wk1 I.id I.⇑) ,
          I.term u
            (I.subst xB
               (I.cons (I.cons (IS.wkSubst 4 I.id) (I.suc (I.var x3)))
                  (cons′ᵢ I.𝕨 xp (I.var x2) (I.var x1))))
        (I.var not-x5 _ _)

opaque
  unfolding Vec′ cons′ nil′ replace₂ vecrec′ vecrec-nil vecrec-cons

  -- An equality rule for vecrec′.

  ⊢vecrec′-cons′≡ :
    {Γ : Cons m n} →
    s PE.≡ 𝕨 →
    Π-allowed r q₂ →
    Γ ⊢ A ∷ U l →
    Γ »∙ ℕ »∙ Vec′ (wk1 l) (wk1 A) (var x0) ⊢ B →
    Γ ⊢ t₁ ∷ B [ zero , nil′ A ]₁₀ →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ (wk[ 2 ]′ l) (wk[ 2 ]′ A) (var x1) »∙
      B [ wk1Subst idSubst ⇑ ] ⊢
      t₂ ∷
      B [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3)))
            (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ] →
    Γ ⊢ t₃ ∷ ℕ →
    Γ ⊢ t₄ ∷ A →
    Γ ⊢ t₅ ∷ Vec′ l A t₃ →
    Γ ⊢ vecrec′ p₁ p₂ r q₁ q₂ l A B t₁ t₂ (suc t₃) (cons′ A t₃ t₄ t₅) ≡
      t₂ [ consSubst (consSubst (consSubst (sgSubst t₃) t₄) t₅)
             (vecrec′ p₁ p₂ r q₁ q₂ l A B t₁ t₂ t₃ t₅) ] ∷
      B [ suc t₃ , cons′ A t₃ t₄ t₅ ]₁₀
  ⊢vecrec′-cons′≡
    {n} {r} {q₂} {A} {l} {B} {t₁} {t₂} {t₃} {t₄} {t₅} {p₁} {p₂} {q₁} {Γ}
    PE.refl Π-ok ⊢A ⊢B ⊢t₁ ⊢t₂ ⊢t₃ ⊢t₄ ⊢t₅ =
    check-and-equal-type-and-terms-sound
      (record (γ′ L.[] Μ)
         { constraints⁺ =
             I.π-allowed xr xq₂     L.∷
             I.unit-allowed I.𝕨     L.∷
             I.σ-allowed I.𝕨 xp I.𝟘 L.∷
             L.[]
         })
      (I.base nothing I.» I.base)
      (vecrecᵢ I.𝕨 xp xp₁ xp₂ xr xq₁ xq₂ xl xA xB xt₁ xt₂ (I.suc xt₃)
         (cons′ᵢ I.𝕨 xp xt₄ xt₅))
      (I.subst xt₂
         (I.cons (I.cons (I.cons (IS.sgSubst xt₃) xt₄) xt₅)
            (vecrecᵢ I.𝕨 xp xp₁ xp₂ xr xq₁ xq₂ xl xA xB xt₁ xt₂ xt₃
               xt₅)))
      (I.subst xB
         (I.cons (IS.sgSubst (I.suc xt₃)) (cons′ᵢ I.𝕨 xp xt₄ xt₅)))
      28
      PE.refl
      (λ where
         .IC.constraints-wf →
           Π-ok L.∷ Unit-ok L.∷ Σ-ok L.∷ L.[]
         .IC.metas-wf .IC.equalities-wf → L.[]
         .IC.metas-wf .IC.bindings-wf   → λ where
           (I.var! x0)         → inversion-U-Level (wf-⊢∷ ⊢A)
           (I.var! x1)         → ⊢A
           (I.var! x2)         → ⊢B
           (I.var! x3)         → ⊢t₁
           (I.var! x4)         → ⊢t₂
           (I.var! x5)         → ⊢t₃
           (I.var! x6)         → ⊢t₄
           (I.var! x7)         → ⊢t₅
           (I.var  not-x8 _ _))
      (wf ⊢A)
      where
      open Defs p₁ p₂ q₁ q₂ r r r Γ
             (n V.∷ 2+ n V.∷ n V.∷ 4+ n V.∷ n V.∷ n V.∷ n V.∷ V.ε)

      xA xt₁ xt₃ xt₄ xt₅ : I.Term c n
      xA  = I.varᵐ x1
      xt₁ = I.varᵐ x3
      xt₃ = I.varᵐ x5
      xt₄ = I.varᵐ x6
      xt₅ = I.varᵐ x7

      xB : I.Term c (2+ n)
      xB = I.varᵐ x2

      xt₂ : I.Term c (4+ n)
      xt₂ = I.varᵐ x4

      Μ : I.Meta-con c
      Μ .I.equalities = L.[]
      Μ .I.bindings   = λ where
        (I.var! x0) → I.base , I.level l
        (I.var! x1) → I.base , I.term A (I.U xl)
        (I.var! x2) →
          I.base I.∙ I.ℕ I.∙
          Vec′ᵢ I.𝕨 xp (IW.wk[ 1 ] xl) (IW.wk[ 1 ] xA) (I.var x0) ,
          I.type B
        (I.var! x3) →
          I.base ,
          I.term t₁
            (I.subst xB (I.cons (IS.sgSubst I.zero) (nil′ᵢ I.𝕨)))
        (I.var! x4) →
          I.base I.∙ I.ℕ I.∙ IW.wk[ 1 ] xA I.∙
          Vec′ᵢ I.𝕨 xp (IW.wk[ 2 ] xl) (IW.wk[ 2 ] xA) (I.var x1) I.∙
          I.subst xB (I.wk1 I.id I.⇑) ,
          I.term t₂
            (I.subst xB
               (I.cons (I.cons (IS.wkSubst 4 I.id) (I.suc (I.var x3)))
                  (cons′ᵢ I.𝕨 xp (I.var x2) (I.var x1))))
        (I.var! x5) → I.base , I.term t₃ I.ℕ
        (I.var! x6) → I.base , I.term t₄ xA
        (I.var! x7) → I.base , I.term t₅ (Vec′ᵢ I.𝕨 xp xl xA xt₃)
        (I.var not-x8 _ _)
