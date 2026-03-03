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
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M
import Definition.Untyped.Bool

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄 hiding (has-nr)

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
   wk-OK; wk-Bool; wk-true; wk-false; wk-liftn-Target; Target-wk[]′;
   module Internal)
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
