------------------------------------------------------------------------
-- Booleans, defined using other types, for the theory with greatest
-- lower bounds in the usage rule for natrec
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Bool.OK and
-- Definition.Typed.Properties.Admissible.Bool, and usage rules can be
-- found in Graded.Derived.Bool.Greatest-lower-bound.

import Graded.Modality

module Definition.Untyped.Bool.Greatest-lower-bound
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

private
  open module M = Modality 𝕄 using (𝟘; 𝟙; ω; _+_; _·_; _∧_)

open import Definition.Untyped M
open import Definition.Untyped.Empty 𝕄
  hiding (module Internal)
open import Definition.Untyped.Nat 𝕄
  hiding (module Internal)
open import Definition.Untyped.Properties M
import Definition.Untyped.Bool

import Definition.Typed.Decidable.Internal.Term
open import Definition.Typed.Restrictions 𝕄

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄 hiding (has-nr)
open import Graded.Mode

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat as N hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality
open import Tools.Unit

private variable
  k k₁ k₂ n : Nat
  A t u v w : Term _
  σ         : Subst _ _
  ρ         : Wk _ _
  p         : M

------------------------------------------------------------------------
-- Term formers

-- The grades are chosen in order to get "reasonable" usage rules
-- It might also be the case that other choices would not give
-- well-resourced terms in general.

private module B = Definition.Untyped.Bool 𝕄 𝟙 (𝟙 ∧ 𝟘) (𝟙 ∧ 𝟘)

-- Export some term formers from Definition.Untyped.Bool

open B using (OK; Bool; true; false; Target) public

opaque
  unfolding B.boolrec

  -- An eliminator for Bool.
  -- The grade p corresponds to the uses in the motive

  boolrec : M → Term (1+ n) → Term n → Term n → Term n → Term n
  boolrec p A t u v =
    B.boolrec 𝟙 𝟙 𝟙 ((𝟙 + p) ∧ p) 𝟙 p A t u v

------------------------------------------------------------------------
-- Unfolding, substitution and weakening lemmas

-- Export lemmas from Definition.Untyped.Bool

open B using
  (Target≡; OK-[]; Bool-[]; true-[]; false-[];
   Target-[⇑]; Target-+-[⇑]; Target-[₀⇑]; Target-[↑⇑]; Target-[,⇑];
   wk-OK; wk-Bool; wk-true; wk-false; wk-liftn-Target; Target-wk[]′)
   public

opaque
  unfolding boolrec

  -- A substitution lemma for boolrec.

  boolrec-[] :
    boolrec p A t u v [ σ ] ≡
    boolrec p (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
  boolrec-[] {v} = B.boolrec-[] {v = v}

opaque
  unfolding boolrec

  -- A weakening lemma for boolrec.

  wk-boolrec :
    wk ρ (boolrec p A t u v) ≡
    boolrec p (wk (lift ρ) A) (wk ρ t) (wk ρ u) (wk ρ v)
  wk-boolrec = B.wk-boolrec

module Internal
  {b} {Mode : Set b}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions)
  where

  private
    module I =
      Definition.Typed.Decidable.Internal.Term 𝐌 R
    module IB = B.Internal 𝐌 R

  private variable
    c           : I.Constants
    pᵢ          : I.Termᵍ _
    Aᵢ tᵢ uᵢ vᵢ : I.Term _ _
    γ           : I.Contexts _


  -- A variant of OK.

  OKᵢ : I.Term c n → I.Term c n
  OKᵢ = IB.OKᵢ (I.𝟙 I.∧ I.𝟘)

  opaque

    -- A translation lemma for OKᵢ.

    ⌜OKᵢ⌝ : I.⌜ OKᵢ tᵢ ⌝ γ ≡ OK (I.⌜ tᵢ ⌝ γ)
    ⌜OKᵢ⌝ {tᵢ} {γ} =
      IB.⌜OKᵢ⌝ {pᵢ = I.𝟙 I.∧ I.𝟘} {γ = γ} {tᵢ = tᵢ} refl

  -- A variant of Bool.

  Boolᵢ : I.Term c n
  Boolᵢ = IB.Boolᵢ I.𝟙 (I.𝟙 I.∧ I.𝟘) (I.𝟙 I.∧ I.𝟘)

  opaque

    -- A translation lemma for Boolᵢ.

    ⌜Boolᵢ⌝ : I.⌜ Boolᵢ {n = n} ⌝ γ ≡ Bool
    ⌜Boolᵢ⌝ {γ} =
      IB.⌜Boolᵢ⌝ {p₁ᵢ = I.𝟙} {γ = γ} {p₂ᵢ = I.𝟙 I.∧ I.𝟘}
        {p₃ᵢ = I.𝟙 I.∧ I.𝟘} refl refl refl

  -- A variant of true.

  trueᵢ : I.Term c n
  trueᵢ = IB.trueᵢ I.𝟙 (I.𝟙 I.∧ I.𝟘) (I.𝟙 I.∧ I.𝟘)

  opaque

    -- A translation lemma for trueᵢ.

    ⌜trueᵢ⌝ :
      I.⌜ trueᵢ {n = n} ⌝ γ ≡ true
    ⌜trueᵢ⌝ {γ} =
      IB.⌜trueᵢ⌝ {p₁ᵢ = I.𝟙} {γ = γ} {p₂ᵢ = I.𝟙 I.∧ I.𝟘}
        {p₃ᵢ = I.𝟙 I.∧ I.𝟘} refl

  -- A variant of false.

  falseᵢ : I.Term c n
  falseᵢ = IB.falseᵢ I.𝟙 (I.𝟙 I.∧ I.𝟘) (I.𝟙 I.∧ I.𝟘)

  opaque

    -- A translation lemma for falseᵢ.

    ⌜falseᵢ⌝ :
      I.⌜ falseᵢ {n = n} ⌝ γ ≡ false
    ⌜falseᵢ⌝ {γ} =
      IB.⌜falseᵢ⌝ {p₁ᵢ = I.𝟙} {γ = γ} {p₂ᵢ = I.𝟙 I.∧ I.𝟘}
        {p₃ᵢ = I.𝟙 I.∧ I.𝟘} refl

  -- A variant of Target.

  Targetᵢ :
    ∀ k → I.Term c (1+ n) → I.Term c (k N.+ n) → I.Term c (k N.+ n) →
    I.Term c (k N.+ n)
  Targetᵢ = IB.Targetᵢ I.𝟙 (I.𝟙 I.∧ I.𝟘) (I.𝟙 I.∧ I.𝟘)

  -- A variant of boolrec.

  boolrecᵢ :
    I.Termᵍ (c .I.gs) → I.Term c (1+ n) → (_ _ _ : I.Term c n) → I.Term c n
  boolrecᵢ p =
    IB.boolrecᵢ I.𝟙 (I.𝟙 I.∧ I.𝟘) (I.𝟙 I.∧ I.𝟘)
      I.𝟙 I.𝟙 I.𝟙 ((I.𝟙 I.+ p) I.∧ p) I.𝟙 p

  opaque
    unfolding boolrec

    -- A translation lemma for boolrecᵢ.

    ⌜boolrecᵢ⌝ :
      I.⌜ boolrecᵢ pᵢ Aᵢ tᵢ uᵢ vᵢ ⌝ γ ≡
        boolrec (I.⟦ pᵢ ⟧ᵍ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
          (I.⌜ uᵢ ⌝ γ) (I.⌜ vᵢ ⌝ γ)
    ⌜boolrecᵢ⌝ {pᵢ} {Aᵢ} {tᵢ} {uᵢ} {vᵢ} {γ} =
      IB.⌜boolrecᵢ⌝ {q₁ᵢ = I.𝟙} {γ = γ} {q₂ᵢ = I.𝟙 I.∧ I.𝟘}
        {q₃ᵢ = I.𝟙} {q₄ᵢ = I.𝟙} {q₅ᵢ = I.𝟙}
        {q₆ᵢ = (I.𝟙 I.+ pᵢ) I.∧ pᵢ} {q₇ᵢ = I.𝟙} {q₈ᵢ = I.𝟙 I.∧ I.𝟘} {pᵢ = pᵢ}
        {Aᵢ = Aᵢ} {tᵢ = tᵢ} {uᵢ = uᵢ} {vᵢ = vᵢ}
        refl refl refl refl refl refl refl
