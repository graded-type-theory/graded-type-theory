------------------------------------------------------------------------
-- Definitions related to ℕ
------------------------------------------------------------------------

-- Typing rules for the term former defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Nat, and a usage
-- rule can be found in Graded.Derived.Nat.

open import Graded.Modality

module Definition.Untyped.Nat
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open Modality 𝕄

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Graded.Mode

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n       : Nat
  A t u v : Term _
  σ       : Subst _ _
  ρ       : Wk _ _
  p q     : M

-- A term used to define double

double′ : (t : Term n) → Term n
double′ t = (natrec 𝟘 𝟘 𝟙 ℕ t (suc (var x0)) t)

-- A program that takes a natural number and adds it to itself:
-- λ n. n + n. This program should presumably not be seen as linear,
-- because the variable "n" is used twice.

double : Term 0
double = lam 𝟙 (double′ (var x0))

-- A term used to define plus

plus′ : (t u : Term n) → Term n
plus′ t u = natrec 𝟘 𝟘 𝟙 ℕ t (suc (var x0)) u

-- A program that takes two natural numbers and adds them:
-- λ m n. m + n. It might make sense to see this program as linear in
-- both arguments.

plus : Term 0
plus = lam 𝟙 $ lam 𝟙 $ plus′ (var x0) (var x1)

opaque

  -- A term used to define f below.

  f′ : Term n → Term n → Term n
  f′ t u = natrec 𝟙 𝟘 𝟘 ℕ t (plus′ (wk₂ t) (var x1)) u

opaque

  -- An implementation of something like the following Agda code:
  --
  --   f : ℕ → ℕ → ℕ
  --   f m zero    = m
  --   f m (suc n) = m + n

  f : Term 0
  f = lam 𝟙 $ lam 𝟙 $ f′ (var x1) (var x0)

-- A term used to define pred

pred′ : Term n → Term n
pred′ t = natrec 𝟙 𝟘 𝟘 ℕ zero (var x1) t

-- A program that takes a natural numbers and returns its predecessor (truncated)
-- It might make sense to see this program as linear.

pred : Term 0
pred = lam 𝟙 $ pred′ (var x0)

opaque

  -- A case analysis principle for natural numbers.

  natcase : M → M → Term (1+ n) → Term n → Term (1+ n) → Term n → Term n
  natcase p q A t u v =
    natrec p q 𝟘 A t (wk1 u) v

opaque
  unfolding natcase

  -- A substitution lemma for natcase.

  natcase-[] :
    natcase p q A t u v [ σ ] ≡
    natcase p q (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ⇑ ]) (v [ σ ])
  natcase-[] {p} {q} {A} {t} {u} {v} {σ} =
    natrec p q 𝟘 A t (wk1 u) v [ σ ]                                ≡⟨⟩
    natrec p q 𝟘 (A [ σ ⇑ ]) (t [ σ ]) (wk1 u [ σ ⇑ ⇑ ]) (v [ σ ])  ≡⟨ cong₂ (natrec _ _ _ _ _) (wk1-liftSubst u) refl ⟩
    natrec p q 𝟘 (A [ σ ⇑ ]) (t [ σ ]) (wk1 (u [ σ ⇑ ])) (v [ σ ])  ∎

opaque

  -- A weakening lemma for natcase.

  wk-natcase :
    wk ρ (natcase p q A t u v) ≡
    natcase p q (wk (lift ρ) A) (wk ρ t) (wk (lift ρ) u) (wk ρ v)
  wk-natcase {ρ} {p} {q} {A} {t} {u} {v} =
    wk ρ (natcase p q A t u v)                                     ≡⟨ wk≡subst _ _ ⟩

    natcase p q A t u v [ toSubst ρ ]                              ≡⟨ natcase-[] ⟩

    natcase p q (A [ toSubst ρ ⇑ ]) (t [ toSubst ρ ])
      (u [ toSubst ρ ⇑ ]) (v [ toSubst ρ ])                        ≡˘⟨ cong₄ (natcase _ _) (wk-liftn 1) (wk≡subst _ _)
                                                                         (wk-liftn 1) (wk≡subst _ _) ⟩
    natcase p q (wk (lift ρ) A) (wk ρ t) (wk (lift ρ) u) (wk ρ v)  ∎

opaque

  -- A "strict const function". The idea is that strict-const A t u
  -- traverses u and then returns t.

  strict-const : Term n → Term n → Term n → Term n
  strict-const A t u =
    natrec 𝟘 𝟘 𝟙 (wk1 A) t (var x0) u

opaque
  unfolding strict-const

  -- A substitution lemma for strict-const.

  strict-const-[] :
    strict-const A t u [ σ ] ≡
    strict-const (A [ σ ]) (t [ σ ]) (u [ σ ])
  strict-const-[] {A} {t} {u} {σ} =
    natrec 𝟘 𝟘 𝟙 (wk1 A) t (var x0) u [ σ ]                    ≡⟨⟩
    natrec 𝟘 𝟘 𝟙 (wk1 A [ σ ⇑ ]) (t [ σ ]) (var x0) (u [ σ ])  ≡⟨ cong₄ (natrec _ _ _) (wk1-liftSubst A) refl refl refl ⟩
    natrec 𝟘 𝟘 𝟙 (wk1 (A [ σ ])) (t [ σ ]) (var x0) (u [ σ ])  ∎

opaque

  -- A weakening lemma for strict-const.

  wk-strict-const :
    wk ρ (strict-const A t u) ≡
    strict-const (wk ρ A) (wk ρ t) (wk ρ u)
  wk-strict-const {ρ} {A} {t} {u} =
    wk ρ (strict-const A t u)                                           ≡⟨ wk≡subst _ _ ⟩
    strict-const A t u [ toSubst ρ ]                                    ≡⟨ strict-const-[] ⟩
    strict-const (A [ toSubst ρ ]) (t [ toSubst ρ ]) (u [ toSubst ρ ])  ≡˘⟨ cong₃ strict-const (wk≡subst _ _) (wk≡subst _ _) (wk≡subst _ _) ⟩
    strict-const (wk ρ A) (wk ρ t) (wk ρ u)                             ∎

------------------------------------------------------------------------
-- A variant of one term former, intended to be used with the internal
-- type-checker

module Internal
  {b} {Mode : Set b}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

  private
    module I  = Definition.Typed.Decidable.Internal.Term 𝐌 R
    module IW = Definition.Typed.Decidable.Internal.Weakening 𝐌 R

  private variable
    c           : I.Constants
    pᵢ qᵢ       : I.Termᵍ _
    Aᵢ tᵢ uᵢ vᵢ : I.Term _ _
    γ           : I.Contexts _

  -- A variant of natcase, intended to be used with the internal
  -- type-checker.

  natcaseᵢ :
    I.Termᵍ (c .I.gs) → I.Termᵍ (c .I.gs) → I.Term c (1+ n) →
    I.Term c n → I.Term c (1+ n) → I.Term c n → I.Term c n
  natcaseᵢ p q A t u v =
    I.natrec p q I.𝟘 A t (IW.wk[ 1 ] u) v

  opaque
    unfolding natcase

    -- A translation lemma for natcaseᵢ.

    ⌜natcaseᵢ⌝ :
      I.⌜ natcaseᵢ pᵢ qᵢ Aᵢ tᵢ uᵢ vᵢ ⌝ γ ≡
      natcase (I.⟦ pᵢ ⟧ᵍ γ) (I.⟦ qᵢ ⟧ᵍ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
        (I.⌜ uᵢ ⌝ γ) (I.⌜ vᵢ ⌝ γ)
    ⌜natcaseᵢ⌝ = refl
