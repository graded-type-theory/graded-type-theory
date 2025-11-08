------------------------------------------------------------------------
-- Booleans, defined using other types
------------------------------------------------------------------------

-- The definitions in this module mostly make no choices about which
-- grades are used. See Definition.Untyped.Bool.Nr and
-- Definition.Untyped.Bool.Greatest-lower-bound for definitions where
-- grades have been suitably chosen for the theory with nr functions
-- and with greatest lower bounds for the natrec rule respectively.

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Consequences.Admissible.Bool.OK and
-- Definition.Typed.Consequences.Admissible.Bool, and usage rules can be
-- found in Graded/Derived/Bool.

import Graded.Modality
import Graded.Mode

module Definition.Untyped.Bool
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (Boolᵍ₁ Boolᵍ₂ OKᵍ : M)
  where

open Modality 𝕄

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Substitution.Primitive
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

import Definition.Untyped.Bool.OK 𝕄 OKᵍ as B-OK

open import Definition.Untyped M
open import Definition.Untyped.Empty 𝕄 as UE hiding (module Internal)
open import Definition.Untyped.Nat 𝕄 as UN hiding (module Internal)
open import Definition.Untyped.Properties M

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄 hiding (has-nr)
open import Graded.Mode

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Maybe
open import Tools.Nat as N hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality
open import Tools.Unit

private variable
  k k₁ k₂ n                   : Nat
  A t u v w                   : Term _
  σ                           : Subst _ _
  ρ                           : Wk _ _
  p boolrecᵍ-pr boolrecᵍ-nc₁
    boolrecᵍ-nc₂ boolrecᵍ-nc₃
    boolrecᵍ-Π                : M

------------------------------------------------------------------------
-- An Agda sketch of the implementation

private module Sketch where

  prodrec′ :
    ∀ {a p q} {A : Set a} {P : A → Set p}
    (Q : Σ A P → Set q) → ∀ x → (∀ x y → Q (x , y)) → Q x
  prodrec′ _ (x , y) f = f x y

  emptyrec′ : ∀ {a} (A : Set a) → ⊥ → A
  emptyrec′ _ ()

  unitrec′ : ∀ {p} (P : ⊤ → Set p) → ∀ x → P tt → P x
  unitrec′ _ _ x = x

  natcase′ :
    ∀ {p} (P : Nat → Set p) → P 0 → (∀ n → P (1+ n)) → ∀ n → P n
  natcase′ _ z _ 0      = z
  natcase′ _ _ s (1+ n) = s n

  OK : Nat → Set
  OK =
    natcase′ (λ _ → Set) ⊤
      (natcase′ (λ _ → Set) ⊤ (λ _ → ⊥))

  Bool : Set
  Bool = Σ Nat OK

  true : Bool
  true = 1 , tt

  false : Bool
  false = 0 , tt

  Target : ∀ {p} → (Bool → Set p) → (n : Nat) → OK n → Set p
  Target P n ok = P (n , ok)

  boolrec : ∀ {p} (P : Bool → Set p) → P true → P false → ∀ b → P b
  boolrec P t f b =
    prodrec′ P b
      (λ n ok →
         natcase′
           (λ n → (ok : OK n) → Target P n ok)
           (λ ok → unitrec′ (λ ok → Target P 0 ok) ok f)
           (λ n →
              natcase′ (λ n → (ok : OK (1+ n)) → Target P (1+ n) ok)
                (λ ok → unitrec′ (λ ok → Target P 1 ok) ok t)
                (λ n ok → emptyrec′ (Target P (2+ n) ok) ok)
                n)
           n ok)

------------------------------------------------------------------------
-- Term formers

-- Export the term OK, used to define the type of Booleans (as well as
-- some properties)

open B-OK public

opaque

  -- A type of booleans.

  Bool : Term n
  Bool = Σʷ Boolᵍ₁ , Boolᵍ₂ ▷ ℕ ▹ OK (var x0)

opaque

  -- The constructor true.

  true : Term n
  true = prodʷ Boolᵍ₁ (suc zero) starʷ

opaque

  -- The constructor false.

  false : Term n
  false = prodʷ Boolᵍ₁ zero starʷ

opaque

  -- A definition that is used in the implementation of boolrec.

  Target :
    ∀ k → Term (1+ n) → Term (k N.+ n) → Term (k N.+ n) → Term (k N.+ n)
  Target k A t u = A [ k ][ prodʷ Boolᵍ₁ t u ]↑

opaque

  -- An eliminator for Bool.

  boolrec :
    (boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p : M) →
    Term (1+ n) → Term n → Term n → Term n → Term n
  boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p A t u v =
    prodrec boolrecᵍ-pr Boolᵍ₁ p A v
      (natcase boolrecᵍ-nc₂ boolrecᵍ-nc₃
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 4 A zero (var x0))
            (var x0) (wk[ 3 ]′ u))
         (natcase boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p
               (Target 5 A (suc zero) (var x0)) (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ-Π $
             emptyrec-sink (Target 5 A (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ-Π ⟩
       var x0)

------------------------------------------------------------------------
-- Variants of the term formers, intended to be used with the internal
-- type-checker

module Internal
  {b} {Mode : Set b}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

  open UE.Internal 𝐌 R
  open UN.Internal 𝐌 R

  private
    module I =
      Definition.Typed.Decidable.Internal.Term 𝐌 R
    module IS =
      Definition.Typed.Decidable.Internal.Substitution.Primitive 𝐌 R
    module IW =
      Definition.Typed.Decidable.Internal.Weakening 𝐌 R

  private variable
    c                                              : I.Constants
    pᵢ p₁ᵢ p₂ᵢ p₃ᵢ q₁ᵢ q₂ᵢ q₃ᵢ q₄ᵢ q₅ᵢ q₆ᵢ q₇ᵢ q₈ᵢ : I.Termᵍ _
    Aᵢ tᵢ uᵢ vᵢ                                    : I.Term _ _
    γ                                              : I.Contexts _

  -- A variant of OK.

  OKᵢ : I.Termᵍ (c .I.gs) → I.Term c n → I.Term c n
  OKᵢ p t =
    natcaseᵢ p I.𝟘 (I.U I.zeroᵘ) (I.Unit I.𝕨)
      (natcaseᵢ I.𝟘 I.𝟘 (I.U I.zeroᵘ) (I.Unit I.𝕨) I.Empty (I.var x0)) t

  opaque
    unfolding OK natcase

    -- A translation lemma for OKᵢ.

    ⌜OKᵢ⌝ :
      I.⟦ pᵢ ⟧ᵍ γ ≡ OKᵍ →
      I.⌜ OKᵢ pᵢ tᵢ ⌝ γ ≡ OK (I.⌜ tᵢ ⌝ γ)
    ⌜OKᵢ⌝ eq rewrite eq = refl

  -- A variant of Bool.

  Boolᵢ : (_ _ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  Boolᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ = I.Σʷ Boolᵍ₁ , Boolᵍ₂ ▷ I.ℕ ▹ OKᵢ OKᵍ (I.var x0)

  opaque
    unfolding Bool OK natcase

    -- A translation lemma for Boolᵢ.

    ⌜Boolᵢ⌝ :
      I.⟦ p₁ᵢ ⟧ᵍ γ ≡ Boolᵍ₁ →
      I.⟦ p₂ᵢ ⟧ᵍ γ ≡ Boolᵍ₂ →
      I.⟦ p₃ᵢ ⟧ᵍ γ ≡ OKᵍ →
      I.⌜ Boolᵢ {n = n} p₁ᵢ p₂ᵢ p₃ᵢ ⌝ γ ≡ Bool
    ⌜Boolᵢ⌝ eq₁ eq₂ eq₃ rewrite eq₁ | eq₂ | eq₃ = refl

  -- A variant of true.

  trueᵢ : (_ _ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  trueᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ =
    I.prod I.𝕨 Boolᵍ₁ ((just (Boolᵍ₂ , OKᵢ OKᵍ (I.var x0)))) (I.suc I.zero)
      (I.star I.𝕨)

  opaque
    unfolding true

    -- A translation lemma for trueᵢ.

    ⌜trueᵢ⌝ :
      I.⟦ p₁ᵢ ⟧ᵍ γ ≡ Boolᵍ₁ →
      I.⌜ trueᵢ {n = n} p₁ᵢ p₂ᵢ p₃ᵢ ⌝ γ ≡ true
    ⌜trueᵢ⌝ eq rewrite eq = refl

  -- A variant of false.

  falseᵢ : (_ _ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  falseᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ =
    I.prod I.𝕨 Boolᵍ₁ (just (Boolᵍ₂ , OKᵢ OKᵍ (I.var x0))) I.zero
      (I.star I.𝕨)

  opaque
    unfolding false

    -- A translation lemma for falseᵢ.

    ⌜falseᵢ⌝ :
      I.⟦ p₁ᵢ ⟧ᵍ γ ≡ Boolᵍ₁ →
      I.⌜ falseᵢ {n = n} p₁ᵢ p₂ᵢ p₃ᵢ ⌝ γ ≡ false
    ⌜falseᵢ⌝ eq rewrite eq = refl

  -- A variant of Target.

  Targetᵢ :
    (_ _ _ : I.Termᵍ (c . I.gs)) →
    ∀ k → I.Term c (1+ n) → I.Term c (k N.+ n) → I.Term c (k N.+ n) →
    I.Term c (k N.+ n)
  Targetᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ k A t u =
    I.subst A
      (I.cons (IS.wkSubst k I.id)
        (I.prod I.𝕨 Boolᵍ₁ (just (Boolᵍ₂ , OKᵢ OKᵍ (I.var x0))) t u))

  -- A variant of boolrec.

  boolrecᵢ :
    (_ _ _ _ _ _ _ _ _ : I.Termᵍ (c .I.gs)) → I.Term c (1+ n) →
    (_ _ _ : I.Term c n) → I.Term c n
  boolrecᵢ
    Boolᵍ₁ Boolᵍ₂ OKᵍ boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p
    A t u v =
    I.prodrec boolrecᵍ-pr Boolᵍ₁ p A v
      (natcaseᵢ boolrecᵍ-nc₂ boolrecᵍ-nc₃
         (I.Π boolrecᵍ-Π , p ▷ OKᵢ OKᵍ (I.var x0) ▹
          Targetᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ 4 A (I.var x1) (I.var x0))
         (I.lam boolrecᵍ-Π nothing $
          I.unitrec boolrecᵍ-Π p (Targetᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ 4 A I.zero (I.var x0))
            (I.var x0) (IW.wk[ 3 ] u))
         (natcaseᵢ boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (I.Π boolrecᵍ-Π , p ▷ OKᵢ OKᵍ (I.suc (I.var x0)) ▹
             Targetᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ 5 A (I.suc (I.var x1)) (I.var x0))
            (I.lam boolrecᵍ-Π nothing $
             I.unitrec boolrecᵍ-Π p
               (Targetᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ 5 A (I.suc I.zero) (I.var x0)) (I.var x0)
                  (IW.wk[ 4 ] t))
            (I.lam boolrecᵍ-Π nothing $
             emptyrec-sinkᵢ
               (Targetᵢ Boolᵍ₁ Boolᵍ₂ OKᵍ 5 A (I.suc (I.suc (I.var x1))) (I.var x0))
               (I.var x0))
            (I.var x0))
         (I.var x1) I.∘⟨ boolrecᵍ-Π ⟩
       I.var x0)

  opaque
    unfolding OK Target boolrec emptyrec-sink natcase

    -- A translation lemma for boolrecᵢ.

    ⌜boolrecᵢ⌝ :
      I.⟦ q₁ᵢ ⟧ᵍ γ ≡ Boolᵍ₁ →
      I.⟦ q₂ᵢ ⟧ᵍ γ ≡ OKᵍ →
      I.⟦ q₃ᵢ ⟧ᵍ γ ≡ boolrecᵍ-pr →
      I.⟦ q₄ᵢ ⟧ᵍ γ ≡ boolrecᵍ-nc₁ →
      I.⟦ q₅ᵢ ⟧ᵍ γ ≡ boolrecᵍ-nc₂ →
      I.⟦ q₆ᵢ ⟧ᵍ γ ≡ boolrecᵍ-nc₃ →
      I.⟦ q₇ᵢ ⟧ᵍ γ ≡ boolrecᵍ-Π →
      I.⌜ boolrecᵢ q₁ᵢ q₈ᵢ q₂ᵢ q₃ᵢ q₄ᵢ q₅ᵢ q₆ᵢ q₇ᵢ pᵢ Aᵢ tᵢ uᵢ vᵢ ⌝ γ ≡
        boolrec (I.⟦ q₃ᵢ ⟧ᵍ γ) (I.⟦ q₄ᵢ ⟧ᵍ γ) (I.⟦ q₅ᵢ ⟧ᵍ γ) (I.⟦ q₆ᵢ ⟧ᵍ γ)
          (I.⟦ q₇ᵢ ⟧ᵍ γ) (I.⟦ pᵢ ⟧ᵍ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
          (I.⌜ uᵢ ⌝ γ) (I.⌜ vᵢ ⌝ γ)
    ⌜boolrecᵢ⌝ eq₁ eq₂ eq₃ eq₄ eq₅ eq₆ eq₇
      rewrite eq₁ | eq₂ | eq₃ | eq₄ | eq₅ | eq₆ | eq₇ = refl

------------------------------------------------------------------------
-- An unfolding lemma

opaque
  unfolding Target

  -- An unfolding lemma for Target.

  Target≡ : Target k A t u ≡ A [ k ][ prodʷ Boolᵍ₁ t u ]↑
  Target≡ = refl

------------------------------------------------------------------------
-- Substitution lemmas

opaque
  unfolding Bool

  -- A substitution lemma for Bool.

  Bool-[] : Bool [ σ ] ≡ Bool
  Bool-[] {σ} =
    (Σʷ Boolᵍ₁ , Boolᵍ₂ ▷ ℕ ▹ OK (var x0)) [ σ ]    ≡⟨⟩
    Σʷ Boolᵍ₁ , Boolᵍ₂ ▷ ℕ ▹ (OK (var x0) [ σ ⇑ ])  ≡⟨ cong (Σ⟨_⟩_,_▷_▹_ _ _ _ _) OK-[] ⟩
    Σʷ Boolᵍ₁ , Boolᵍ₂ ▷ ℕ ▹ OK (var x0)            ∎

opaque
  unfolding true

  -- A substitution lemma for true.

  true-[] : true [ σ ] ≡ true
  true-[] = refl

opaque
  unfolding false

  -- A substitution lemma for false.

  false-[] : false [ σ ] ≡ false
  false-[] = refl

opaque
  unfolding Target

  -- A substitution lemma for Target.

  Target-[⇑] :
    Target k A t u [ σ ⇑[ k ] ] ≡
    Target k (A [ σ ⇑ ]) (t [ σ ⇑[ k ] ]) (u [ σ ⇑[ k ] ])
  Target-[⇑] {A} = [][]↑-commutes A

opaque
  unfolding Target

  -- A substitution lemma for Target.

  Target-+-[⇑] :
    ∀ j {t u} →
    let cast =
          subst₂ Subst (sym $ N.+-assoc j k₂ n) (sym $ N.+-assoc j k₁ n)
    in
    (∀ x → wk[ k₁ ] (var x) [ σ ] ≡ wk[ k₂ ] (var x)) →
    Target (j N.+ k₁) A t u [ cast (σ ⇑[ j ]) ] ≡
    Target (j N.+ k₂) A (t [ cast (σ ⇑[ j ]) ]) (u [ cast (σ ⇑[ j ]) ])
  Target-+-[⇑] {A} _ = [][]↑-commutes-+ A

opaque
  unfolding Target

  -- A substitution lemma for Target.

  Target-[₀⇑] :
    ∀ j {t u} →
    let cast =
          subst₂ Subst (sym $ N.+-assoc j k n) (sym $ N.+-assoc j (1+ k) n)
    in
    Target (j N.+ 1+ k) A t u [ cast (sgSubst v ⇑[ j ]) ] ≡
    Target (j N.+ k) A (t [ cast (sgSubst v ⇑[ j ]) ])
      (u [ cast (sgSubst v ⇑[ j ]) ])
  Target-[₀⇑] {A} _ = [][]↑-[₀⇑] _ A

opaque
  unfolding Target

  -- A substitution lemma for Target.

  Target-[↑⇑] :
    ∀ j {t u} →
    let cast =
          subst₂ Subst (sym $ N.+-assoc j (1+ k) n)
            (sym $ N.+-assoc j (1+ k) n)
    in
    Target (j N.+ 1+ k) A t u
      [ cast (consSubst (wk1Subst idSubst) v ⇑[ j ]) ] ≡
    Target (j N.+ 1+ k) A
      (t [ cast (consSubst (wk1Subst idSubst) v ⇑[ j ]) ])
      (u [ cast (consSubst (wk1Subst idSubst) v ⇑[ j ]) ])
  Target-[↑⇑] {A} _ = [][]↑-[↑⇑] _ A

opaque
  unfolding Target

  -- A substitution lemma for Target.

  Target-[,⇑] :
    ∀ j {t u} →
    let cast =
          subst₂ Subst (sym $ N.+-assoc j k n) (sym $ N.+-assoc j (2+ k) n)
    in
    Target (j N.+ 2+ k) A t u
      [ cast (consSubst (sgSubst v) w ⇑[ j ]) ] ≡
    Target (j N.+ k) A
      (t [ cast (consSubst (sgSubst v) w ⇑[ j ]) ])
      (u [ cast (consSubst (sgSubst v) w ⇑[ j ]) ])
  Target-[,⇑] {A} _ = [][]↑-[,⇑] _ A

opaque
  unfolding boolrec

  -- A substitution lemma for boolrec.

  boolrec-[] :
    boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p A t u v [ σ ] ≡
    boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
  boolrec-[] {boolrecᵍ-pr} {boolrecᵍ-nc₁} {boolrecᵍ-nc₂} {boolrecᵍ-nc₃} {boolrecᵍ-Π} {p} {A} {t} {u} {v} {σ} =
    prodrec boolrecᵍ-pr Boolᵍ₁ p A v
      (natcase boolrecᵍ-nc₂ boolrecᵍ-nc₃
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 4 A zero (var x0))
            (var x0) (wk[ 3 ]′ u))
         (natcase boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p
               (Target 5 A (suc zero) (var x0)) (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ-Π $
             emptyrec-sink (Target 5 A (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ-Π ⟩
       var x0)
      [ σ ]                                                               ≡⟨ cong (prodrec _ _ _ _ _) $
                                                                             cong (flip _∘⟨ boolrecᵍ-Π ⟩_ _) $
                                                                             trans natcase-[] $
                                                                             cong₄ (natcase _ _)
                                                                               (cong₂ (Π_,_▷_▹_ _ _) OK-[] refl)
                                                                               refl
                                                                               (trans natcase-[] $
                                                                                cong₄ (natcase _ _)
                                                                                  (cong₂ (Π_,_▷_▹_ _ _) OK-[] refl)
                                                                                  refl
                                                                                  (cong (lam _) emptyrec-sink-[])
                                                                                  refl)
                                                                               refl ⟩
    prodrec boolrecᵍ-pr Boolᵍ₁ p (A [ σ ⇑ ]) (v [ σ ])
      (natcase boolrecᵍ-nc₂ boolrecᵍ-nc₃
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
          (Target 4 A (var x1) (var x0) [ σ ⇑[ 4 ] ]))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p
            (Target 4 A zero (var x0) [ σ ⇑[ 4 ] ]) (var x0)
            (wk[ 3 ]′ u [ σ ⇑[ 3 ] ]))
         (natcase boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             (Target 5 A (suc (var x1)) (var x0) [ σ ⇑[ 5 ] ]))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p
               (Target 5 A (suc zero) (var x0) [ σ ⇑[ 5 ] ]) (var x0)
               (wk[ 4 ]′ t [ σ ⇑[ 4 ] ]))
            (lam boolrecᵍ-Π $
             emptyrec-sink
               (Target 5 A (suc (suc (var x1))) (var x0) [ σ ⇑[ 5 ] ])
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ-Π ⟩
       var x0)                                                            ≡⟨ cong (prodrec _ _ _ _ _) $
                                                                             cong (flip (_∘⟨ boolrecᵍ-Π ⟩_) _) $
                                                                             cong₄ (natcase _ _)
                                                                               (cong (Π_,_▷_▹_ _ _ _) Target-[⇑])
                                                                               (cong (lam _) $
                                                                                cong₃ (unitrec _ _)
                                                                                  Target-[⇑] refl (wk[]′-[⇑] u))
                                                                               (cong₄ (natcase _ _)
                                                                                  (cong (Π_,_▷_▹_ _ _ _) Target-[⇑])
                                                                                  (cong (lam _) $
                                                                                   cong₃ (unitrec _ _)
                                                                                     Target-[⇑] refl (wk[]′-[⇑] t))
                                                                                  (cong (lam _) $
                                                                                   cong₂ emptyrec-sink Target-[⇑] refl)
                                                                                  refl)
                                                                               refl ⟩
    prodrec boolrecᵍ-pr Boolᵍ₁ p (A [ σ ⇑ ]) (v [ σ ])
      (natcase boolrecᵍ-nc₂ boolrecᵍ-nc₃
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
          Target 4 (A [ σ ⇑ ]) (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p
            (Target 4 (A [ σ ⇑ ]) zero (var x0)) (var x0)
            (wk[ 3 ]′ (u [ σ ])))
         (natcase boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Target 5 (A [ σ ⇑ ]) (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec boolrecᵍ-Π p
               (Target 5 (A [ σ ⇑ ]) (suc zero) (var x0)) (var x0)
               (wk[ 4 ]′ (t [ σ ])))
            (lam boolrecᵍ-Π $
             emptyrec-sink
               (Target 5 (A [ σ ⇑ ]) (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ-Π ⟩
       var x0)                                                            ∎

------------------------------------------------------------------------
-- Weakening lemmas

opaque

  -- A weakening lemma for Bool.

  wk-Bool : wk ρ Bool ≡ Bool
  wk-Bool {ρ} =
    wk ρ Bool           ≡⟨ wk≡subst _ _ ⟩
    Bool [ toSubst ρ ]  ≡⟨ Bool-[] ⟩
    Bool                ∎

opaque

  -- A weakening lemma for true.

  wk-true : wk ρ true ≡ true
  wk-true {ρ} =
    wk ρ true           ≡⟨ wk≡subst _ _ ⟩
    true [ toSubst ρ ]  ≡⟨ true-[] ⟩
    true                ∎

opaque

  -- A weakening lemma for false.

  wk-false : wk ρ false ≡ false
  wk-false {ρ} =
    wk ρ false           ≡⟨ wk≡subst _ _ ⟩
    false [ toSubst ρ ]  ≡⟨ false-[] ⟩
    false                ∎

opaque

  -- A weakening lemma for Target.

  wk-liftn-Target :
    wk (liftn ρ k) (Target k A t u) ≡
    Target k (wk (lift ρ) A) (wk (liftn ρ k) t) (wk (liftn ρ k) u)
  wk-liftn-Target {ρ} {k} {A} {t} {u} =
    wk (liftn ρ k) (Target k A t u)                                 ≡⟨ wk-liftn k ⟩

    Target k A t u [ toSubst ρ ⇑[ k ] ]                             ≡⟨ Target-[⇑] ⟩

    Target k (A [ toSubst ρ ⇑ ]) (t [ toSubst ρ ⇑[ k ] ])
      (u [ toSubst ρ ⇑[ k ] ])                                      ≡˘⟨ cong₃ (Target _) (wk-liftn 1) (wk-liftn k) (wk-liftn k) ⟩

    Target k (wk (lift ρ) A) (wk (liftn ρ k) t) (wk (liftn ρ k) u)  ∎

opaque
  unfolding Target

  -- Another weakening lemma for Target.

  Target-wk[]′ :
    Target k A (wk[ k ]′ t) (wk[ k ]′ u) ≡
    wk[ k ]′ (A [ prodʷ Boolᵍ₁ t u ]₀)
  Target-wk[]′ {k} {A} {t} {u} =
    A [ k ][ prodʷ Boolᵍ₁ (wk[ k ]′ t) (wk[ k ]′ u) ]↑  ≡⟨⟩
    A [ k ][ wk[ k ]′ (prodʷ Boolᵍ₁ t u) ]↑             ≡⟨ [][wk[]′]↑ A ⟩
    wk[ k ]′ (A [ prodʷ Boolᵍ₁ t u ]₀)                  ∎

opaque

  -- A weakening lemma for boolrec.

  wk-boolrec :
    wk ρ (boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p A t u v) ≡
    boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p (wk (lift ρ) A) (wk ρ t) (wk ρ u) (wk ρ v)
  wk-boolrec {ρ} {p} {A} {t} {u} {v} =
    wk ρ (boolrec _ _ _ _ _ p A t u v)                                           ≡⟨ wk-liftn 0 ⟩

    boolrec _ _ _ _ _ p A t u v [ toSubst ρ ]                                    ≡⟨ boolrec-[] ⟩

    boolrec _ _ _ _ _ p (A [ toSubst ρ ⇑ ]) (t [ toSubst ρ ]) (u [ toSubst ρ ])
      (v [ toSubst ρ ])                                                          ≡˘⟨ cong₄ (boolrec _ _ _ _ _ _)
                                                                                       (wk-liftn 1) (wk-liftn 0) (wk-liftn 0) (wk-liftn 0) ⟩
    boolrec _ _ _ _ _ p (wk (lift ρ) A) (wk ρ t) (wk ρ u) (wk ρ v)               ∎
