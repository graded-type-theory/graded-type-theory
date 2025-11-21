------------------------------------------------------------------------
-- Booleans, defined using other types
------------------------------------------------------------------------

-- The definitions in this module mostly make no choices about which
-- grades are used. See Definition.Untyped.Bool.Nr and
-- Definition.Untyped.Bool.Greatest-lower-bound for definitions where
-- grades have been suitably chosen for the theory with nr functions
-- and with greatest lower bounds for the natrec rule respectively.

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Bool.OK and
-- Definition.Typed.Properties.Admissible.Bool, and usage rules can be
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

import Definition.Untyped.Bool.OK 𝕄 OKᵍ as B-OK

open import Definition.Untyped M
open import Definition.Untyped.Empty 𝕄
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M

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
  true = prodʷ Boolᵍ₁ (suc zero) (starʷ 0)

opaque

  -- The constructor false.

  false : Term n
  false = prodʷ Boolᵍ₁ zero (starʷ 0)

opaque

  -- A definition that is used in the implementation of boolrec.

  Targetᵇʳ :
    ∀ k → Term (1+ n) → Term (k N.+ n) → Term (k N.+ n) → Term (k N.+ n)
  Targetᵇʳ k A t u = A [ k ][ prodʷ Boolᵍ₁ t u ]↑

opaque

  -- An eliminator for Bool.

  boolrec :
    (boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p : M) →
    Term (1+ n) → Term n → Term n → Term n → Term n
  boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p A t u v =
    prodrec boolrecᵍ-pr Boolᵍ₁ p A v
      (natcase boolrecᵍ-nc₂ boolrecᵍ-nc₃
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Targetᵇʳ 4 A (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec 0 boolrecᵍ-Π p (Targetᵇʳ 4 A zero (var x0))
            (var x0) (wk[ 3 ]′ u))
         (natcase boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Targetᵇʳ 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec 0 boolrecᵍ-Π p
               (Targetᵇʳ 5 A (suc zero) (var x0)) (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ-Π $
             emptyrec-sink (Targetᵇʳ 5 A (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ-Π ⟩
       var x0)

------------------------------------------------------------------------
-- An unfolding lemma

opaque
  unfolding Targetᵇʳ

  -- An unfolding lemma for Targetᵇʳ.

  Targetᵇʳ≡ : Targetᵇʳ k A t u ≡ A [ k ][ prodʷ Boolᵍ₁ t u ]↑
  Targetᵇʳ≡ = refl

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
  unfolding Targetᵇʳ

  -- A substitution lemma for Targetᵇʳ.

  Targetᵇʳ-[⇑] :
    Targetᵇʳ k A t u [ σ ⇑[ k ] ] ≡
    Targetᵇʳ k (A [ σ ⇑ ]) (t [ σ ⇑[ k ] ]) (u [ σ ⇑[ k ] ])
  Targetᵇʳ-[⇑] {A} = [][]↑-commutes A

opaque
  unfolding Targetᵇʳ

  -- A substitution lemma for Targetᵇʳ.

  Targetᵇʳ-+-[⇑] :
    ∀ j {t u} →
    let cast =
          subst₂ Subst (sym $ N.+-assoc j k₂ n) (sym $ N.+-assoc j k₁ n)
    in
    (∀ x → wk[ k₁ ] (var x) [ σ ] ≡ wk[ k₂ ] (var x)) →
    Targetᵇʳ (j N.+ k₁) A t u [ cast (σ ⇑[ j ]) ] ≡
    Targetᵇʳ (j N.+ k₂) A (t [ cast (σ ⇑[ j ]) ]) (u [ cast (σ ⇑[ j ]) ])
  Targetᵇʳ-+-[⇑] {A} _ = [][]↑-commutes-+ A

opaque
  unfolding Targetᵇʳ

  -- A substitution lemma for Targetᵇʳ.

  Targetᵇʳ-[₀⇑] :
    ∀ j {t u} →
    let cast =
          subst₂ Subst (sym $ N.+-assoc j k n) (sym $ N.+-assoc j (1+ k) n)
    in
    Targetᵇʳ (j N.+ 1+ k) A t u [ cast (sgSubst v ⇑[ j ]) ] ≡
    Targetᵇʳ (j N.+ k) A (t [ cast (sgSubst v ⇑[ j ]) ])
      (u [ cast (sgSubst v ⇑[ j ]) ])
  Targetᵇʳ-[₀⇑] {A} _ = [][]↑-[₀⇑] _ A

opaque
  unfolding Targetᵇʳ

  -- A substitution lemma for Targetᵇʳ.

  Targetᵇʳ-[↑⇑] :
    ∀ j {t u} →
    let cast =
          subst₂ Subst (sym $ N.+-assoc j (1+ k) n)
            (sym $ N.+-assoc j (1+ k) n)
    in
    Targetᵇʳ (j N.+ 1+ k) A t u
      [ cast (consSubst (wk1Subst idSubst) v ⇑[ j ]) ] ≡
    Targetᵇʳ (j N.+ 1+ k) A
      (t [ cast (consSubst (wk1Subst idSubst) v ⇑[ j ]) ])
      (u [ cast (consSubst (wk1Subst idSubst) v ⇑[ j ]) ])
  Targetᵇʳ-[↑⇑] {A} _ = [][]↑-[↑⇑] _ A

opaque
  unfolding Targetᵇʳ

  -- A substitution lemma for Targetᵇʳ.

  Targetᵇʳ-[,⇑] :
    ∀ j {t u} →
    let cast =
          subst₂ Subst (sym $ N.+-assoc j k n) (sym $ N.+-assoc j (2+ k) n)
    in
    Targetᵇʳ (j N.+ 2+ k) A t u
      [ cast (consSubst (sgSubst v) w ⇑[ j ]) ] ≡
    Targetᵇʳ (j N.+ k) A
      (t [ cast (consSubst (sgSubst v) w ⇑[ j ]) ])
      (u [ cast (consSubst (sgSubst v) w ⇑[ j ]) ])
  Targetᵇʳ-[,⇑] {A} _ = [][]↑-[,⇑] _ A

opaque
  unfolding boolrec

  -- A substitution lemma for boolrec.

  boolrec-[] :
    boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p A t u v [ σ ] ≡
    boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-nc₃ boolrecᵍ-Π p (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
  boolrec-[] {boolrecᵍ-pr} {boolrecᵍ-nc₁} {boolrecᵍ-nc₂} {boolrecᵍ-nc₃} {boolrecᵍ-Π} {p} {A} {t} {u} {v} {σ} =
    prodrec boolrecᵍ-pr Boolᵍ₁ p A v
      (natcase boolrecᵍ-nc₂ boolrecᵍ-nc₃
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Targetᵇʳ 4 A (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec 0 boolrecᵍ-Π p (Targetᵇʳ 4 A zero (var x0))
            (var x0) (wk[ 3 ]′ u))
         (natcase boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Targetᵇʳ 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec 0 boolrecᵍ-Π p
               (Targetᵇʳ 5 A (suc zero) (var x0)) (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ-Π $
             emptyrec-sink (Targetᵇʳ 5 A (suc (suc (var x1))) (var x0))
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
          (Targetᵇʳ 4 A (var x1) (var x0) [ σ ⇑[ 4 ] ]))
         (lam boolrecᵍ-Π $
          unitrec 0 boolrecᵍ-Π p
            (Targetᵇʳ 4 A zero (var x0) [ σ ⇑[ 4 ] ]) (var x0)
            (wk[ 3 ]′ u [ σ ⇑[ 3 ] ]))
         (natcase boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             (Targetᵇʳ 5 A (suc (var x1)) (var x0) [ σ ⇑[ 5 ] ]))
            (lam boolrecᵍ-Π $
             unitrec 0 boolrecᵍ-Π p
               (Targetᵇʳ 5 A (suc zero) (var x0) [ σ ⇑[ 5 ] ]) (var x0)
               (wk[ 4 ]′ t [ σ ⇑[ 4 ] ]))
            (lam boolrecᵍ-Π $
             emptyrec-sink
               (Targetᵇʳ 5 A (suc (suc (var x1))) (var x0) [ σ ⇑[ 5 ] ])
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ-Π ⟩
       var x0)                                                            ≡⟨ cong (prodrec _ _ _ _ _) $
                                                                             cong (flip (_∘⟨ boolrecᵍ-Π ⟩_) _) $
                                                                             cong₄ (natcase _ _)
                                                                               (cong (Π_,_▷_▹_ _ _ _) Targetᵇʳ-[⇑])
                                                                               (cong (lam _) $
                                                                                cong₃ (unitrec _ _ _)
                                                                                  Targetᵇʳ-[⇑] refl (wk[]′-[⇑] u))
                                                                               (cong₄ (natcase _ _)
                                                                                  (cong (Π_,_▷_▹_ _ _ _) Targetᵇʳ-[⇑])
                                                                                  (cong (lam _) $
                                                                                   cong₃ (unitrec _ _ _)
                                                                                     Targetᵇʳ-[⇑] refl (wk[]′-[⇑] t))
                                                                                  (cong (lam _) $
                                                                                   cong₂ emptyrec-sink Targetᵇʳ-[⇑] refl)
                                                                                  refl)
                                                                               refl ⟩
    prodrec boolrecᵍ-pr Boolᵍ₁ p (A [ σ ⇑ ]) (v [ σ ])
      (natcase boolrecᵍ-nc₂ boolrecᵍ-nc₃
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
          Targetᵇʳ 4 (A [ σ ⇑ ]) (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec 0 boolrecᵍ-Π p
            (Targetᵇʳ 4 (A [ σ ⇑ ]) zero (var x0)) (var x0)
            (wk[ 3 ]′ (u [ σ ])))
         (natcase boolrecᵍ-nc₁ boolrecᵍ-nc₃
            (Π boolrecᵍ-Π , p ▷ OK (suc (var x0)) ▹
             Targetᵇʳ 5 (A [ σ ⇑ ]) (suc (var x1)) (var x0))
            (lam boolrecᵍ-Π $
             unitrec 0 boolrecᵍ-Π p
               (Targetᵇʳ 5 (A [ σ ⇑ ]) (suc zero) (var x0)) (var x0)
               (wk[ 4 ]′ (t [ σ ])))
            (lam boolrecᵍ-Π $
             emptyrec-sink
               (Targetᵇʳ 5 (A [ σ ⇑ ]) (suc (suc (var x1))) (var x0))
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

  -- A weakening lemma for Targetᵇʳ.

  wk-liftn-Targetᵇʳ :
    wk (liftn ρ k) (Targetᵇʳ k A t u) ≡
    Targetᵇʳ k (wk (lift ρ) A) (wk (liftn ρ k) t) (wk (liftn ρ k) u)
  wk-liftn-Targetᵇʳ {ρ} {k} {A} {t} {u} =
    wk (liftn ρ k) (Targetᵇʳ k A t u)                                 ≡⟨ wk-liftn k ⟩

    Targetᵇʳ k A t u [ toSubst ρ ⇑[ k ] ]                             ≡⟨ Targetᵇʳ-[⇑] ⟩

    Targetᵇʳ k (A [ toSubst ρ ⇑ ]) (t [ toSubst ρ ⇑[ k ] ])
      (u [ toSubst ρ ⇑[ k ] ])                                      ≡˘⟨ cong₃ (Targetᵇʳ _) (wk-liftn 1) (wk-liftn k) (wk-liftn k) ⟩

    Targetᵇʳ k (wk (lift ρ) A) (wk (liftn ρ k) t) (wk (liftn ρ k) u)  ∎

opaque
  unfolding Targetᵇʳ

  -- Another weakening lemma for Targetᵇʳ.

  Targetᵇʳ-wk[]′ :
    Targetᵇʳ k A (wk[ k ]′ t) (wk[ k ]′ u) ≡
    wk[ k ]′ (A [ prodʷ Boolᵍ₁ t u ]₀)
  Targetᵇʳ-wk[]′ {k} {A} {t} {u} =
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
