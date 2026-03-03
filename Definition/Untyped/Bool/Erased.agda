------------------------------------------------------------------------
-- Booleans, defined using other types
------------------------------------------------------------------------

-- This variant of the booleans uses erased "proofs".

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Bool.Erased, and
-- usage rules can be found in Graded.Derived.Bool.Erased.

import Graded.Modality
import Graded.Mode

module Definition.Untyped.Bool.Erased
  {a b} {M : Set a} {Mode : Set b}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Graded.Mode Mode 𝕄)
  (𝐌 : IsMode)
  -- It is assumed that the modality has an nr function.
  ⦃ has-nr : Has-nr (Modality.semiring-with-meet 𝕄) ⦄
  where

open Modality 𝕄
open IsMode 𝐌

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Substitution.Primitive
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

open import Definition.Untyped M hiding (_[_]′)
open import Definition.Untyped.Bool.Nr 𝕄 𝐌 as B
  using (OK; OKᵍ; boolrecᵍ-nc₁; boolrecᵍ-nc₂)
open import Definition.Untyped.Empty 𝕄 as UE hiding (module Internal)
open import Definition.Untyped.Erased 𝕄 𝕨 as E
  hiding (module Internal; [_])
open import Definition.Untyped.Nat 𝕄 as UN hiding (module Internal)
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄 hiding (module Internal)
open import Definition.Untyped.Unit 𝕄 hiding (module Internal)

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄 hiding (has-nr)

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Maybe
open import Tools.Nat as N using (Nat; 1+; 2+)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

private variable
  k k₁ k₂ n : Nat
  A t u v w : Term _
  σ         : Subst _ _
  ρ         : Wk _ _
  p         : M

------------------------------------------------------------------------
-- An Agda sketch of the implementation

private module Sketch where

  opaque

    -- The sketch does not make use of Agda's support for erasure,
    -- because (at the time of writing) this formalisation does not
    -- use that feature.

    Erased′ : ∀ {a} → Set a → Set a
    Erased′ A = A

    [_]′ : ∀ {a} {A : Set a} → A → Erased′ A
    [ x ]′ = x

    erasedrec′ :
      ∀ {a p} {A : Set a} (P : Erased′ A → Set p) →
      ((x : A) → P [ x ]′) → (x : Erased′ A) → P x
    erasedrec′ _ f x = f x

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

  OK′ : Nat → Set
  OK′ n =
    natcase′ (λ _ → Set) ⊤
      (natcase′ (λ _ → Set) ⊤ (λ _ → ⊥)) n

  Bool : Set
  Bool = Σ Nat (λ n → Erased′ (OK′ n))

  true : Bool
  true = 1 , [ tt ]′

  false : Bool
  false = 0 , [ tt ]′

  Target′ : ∀ {p} → (Bool → Set p) → (n : Nat) → Erased′ (OK′ n) → Set p
  Target′ P n ok = P (n , ok)

  boolrec : ∀ {p} (P : Bool → Set p) → P true → P false → ∀ b → P b
  boolrec P t f b =
    prodrec′ P b
      (λ n ok →
         natcase′
           (λ n → (ok : Erased′ (OK′ n)) → Target′ P n ok)
           (λ ok →
              erasedrec′ (λ ok → Target′ P 0 ok)
                (λ ok → unitrec′ (λ ok → Target′ P 0 [ ok ]′) ok f) ok)
           (λ n →
              natcase′
                (λ n →
                   (ok : Erased′ (OK′ (1+ n))) → Target′ P (1+ n) ok)
                (λ ok →
                   erasedrec′ (λ ok → Target′ P 1 ok)
                     (λ ok → unitrec′ (λ ok → Target′ P 1 [ ok ]′) ok t)
                     ok)
                (λ n ok →
                   erasedrec′ (λ ok → Target′ P (2+ n) ok)
                     (λ ok → emptyrec′ (Target′ P (2+ n) [ ok ]′) ok)
                     ok)
                n)
           n ok)

------------------------------------------------------------------------
-- Some grades

opaque

  -- A grade used in the implementation of Bool.

  Boolᵍ : M
  Boolᵍ = 𝟘

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-pr : M
  boolrecᵍ-pr = nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ 𝟙

------------------------------------------------------------------------
-- Some lemmas about the grades

opaque
  unfolding boolrecᵍ-pr

  -- If the nr function satisfies Linearity-like-nr-for-𝟘
  -- and Linearity-like-nr-for-𝟙, then boolrecᵍ-pr is equal to 𝟙.

  boolrecᵍ-pr≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-pr ≡ 𝟙
  boolrecᵍ-pr≡ hyp₁ hyp₂ =
    nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ 𝟙        ≡⟨ cong (flip _∧_ _) $ cong (λ p → nr p _ _ _ _) $
                                          B.boolrecᵍ-nc₂≡ hyp₁ hyp₂ ⟩
    nr 𝟙 𝟘 𝟘 𝟘 𝟙 ∧ 𝟙                   ≡⟨ cong (flip _∧_ _) hyp₁ ⟩
    (((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)) ∧ 𝟙  ≡⟨ cong (flip _∧_ _) B.[[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 ⟩
    𝟙 ∧ 𝟙                              ≡⟨ ∧-idem _ ⟩
    𝟙                                  ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-pr

  -- If the modality's zero is well-behaved, then boolrecᵍ-pr is
  -- non-zero.

  boolrecᵍ-pr≢𝟘 :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    boolrecᵍ-pr ≢ 𝟘
  boolrecᵍ-pr≢𝟘 =
    nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ 𝟙 ≡ 𝟘  →⟨ ∧-positiveʳ ⟩
    𝟙 ≡ 𝟘                            →⟨ non-trivial ⟩
    ⊥                                □

------------------------------------------------------------------------
-- Term formers

opaque

  -- A type of booleans.

  Bool : Term n
  Bool = Σʷ 𝟙 , Boolᵍ ▷ ℕ ▹ Erased zeroᵘ (OK (var x0))

opaque

  -- The constructor true.

  true : Term n
  true = prodʷ 𝟙 (suc zero) E.[ starʷ ]

opaque

  -- The constructor false.

  false : Term n
  false = prodʷ 𝟙 zero E.[ starʷ ]

opaque

  -- A definition that is used in the implementation of boolrec.

  Target :
    ∀ k → Term (1+ n) → Term (k N.+ n) → Term (k N.+ n) → Term (k N.+ n)
  Target k A t u = A [ k ][ prodʷ 𝟙 t u ]↑

opaque

  -- An eliminator for Bool.

  boolrec : M → Term (1+ n) → Term n → Term n → Term n → Term n
  boolrec p A t u v =
    prodrec boolrecᵍ-pr 𝟙 p A v
      (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased zeroᵘ (OK (var x0)) ▹
          Target 4 A (var x1) (var x0))
         (lam 𝟙 $
          erasedrec p (Target 4 A zero (var x0))
            (unitrec 𝟘 𝟘 (Target 5 A zero E.[ var x0 ]) (var x0)
               (wk[ 4 ]′ u))
            (var x0))
         (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased zeroᵘ (OK (suc (var x0))) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam 𝟙 $
             erasedrec p (Target 5 A (suc zero) (var x0))
               (unitrec 𝟘 𝟘 (Target 6 A (suc zero) E.[ var x0 ])
                  (var x0) (wk[ 5 ]′ t))
               (var x0))
            (lam 𝟙 $
             erasedrec p (Target 6 A (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target 6 A (suc (suc (var x2))) E.[ var x0 ])
                  (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ 𝟙 ⟩
       var x0)

------------------------------------------------------------------------
-- Variants of the term formers, intended to be used with the internal
-- type-checker

module Internal (R : Type-restrictions 𝕄) where

  open B.Internal 𝐌 R using (OKᵢ)
  open E.Internal 𝐌 R
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
    c                              : I.Constants
    pᵢ p₁ᵢ p₂ᵢ q₁ᵢ q₂ᵢ q₃ᵢ q₄ᵢ q₅ᵢ : I.Termᵍ _
    Aᵢ tᵢ uᵢ vᵢ                    : I.Term _ _
    γ                              : I.Contexts _

  -- A variant of Bool.

  Boolᵢ : (_ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  Boolᵢ Boolᵍ OKᵍ =
    I.Σʷ I.𝟙 , Boolᵍ ▷ I.ℕ ▹ I.Erased I.𝕨 I.zeroᵘ (OKᵢ OKᵍ (I.var x0))

  opaque
    unfolding Bool Erased OK natcase

    -- A translation lemma for Boolᵢ.

    ⌜Boolᵢ⌝ :
      I.⟦ p₁ᵢ ⟧ᵍ γ ≡ Boolᵍ →
      I.⟦ p₂ᵢ ⟧ᵍ γ ≡ OKᵍ →
      I.⌜ Boolᵢ {n = n} p₁ᵢ p₂ᵢ ⌝ γ ≡ Bool
    ⌜Boolᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- A variant of true.

  trueᵢ : (_ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  trueᵢ Boolᵍ OKᵍ =
    I.prod I.𝕨 I.𝟙
      (just (Boolᵍ , I.Erased I.𝕨 I.zeroᵘ (OKᵢ OKᵍ (I.var x0))))
      (I.suc I.zero) (I.box I.𝕨 I.zeroᵘ (I.star I.𝕨))

  opaque
    unfolding true E.[_]

    -- A translation lemma for trueᵢ.

    ⌜trueᵢ⌝ : I.⌜ trueᵢ {n = n} p₁ᵢ p₂ᵢ ⌝ γ ≡ true
    ⌜trueᵢ⌝ = refl

  -- A variant of false.

  falseᵢ : (_ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  falseᵢ Boolᵍ OKᵍ =
    I.prod I.𝕨 I.𝟙
      (just (Boolᵍ , I.Erased I.𝕨 I.zeroᵘ (OKᵢ OKᵍ (I.var x0))))
      I.zero (I.box I.𝕨 I.zeroᵘ (I.star I.𝕨))

  opaque
    unfolding false E.[_]

    -- A translation lemma for falseᵢ.

    ⌜falseᵢ⌝ : I.⌜ falseᵢ {n = n} p₁ᵢ p₂ᵢ ⌝ γ ≡ false
    ⌜falseᵢ⌝ = refl

  -- A variant of Target.

  Targetᵢ :
    ∀ k → I.Term c (1+ n) → I.Term c (k N.+ n) → I.Term c (k N.+ n) →
    I.Term c (k N.+ n)
  Targetᵢ k A t u =
    I.subst A (I.cons (IS.wkSubst k I.id) (I.prod I.𝕨 I.𝟙 nothing t u))

  -- A variant of boolrec.

  boolrecᵢ :
    (_ _ _ _ _ _ : I.Termᵍ (c .I.gs)) → I.Term c (1+ n) →
    (_ _ _ : I.Term c n) → I.Term c n
  boolrecᵢ Boolᵍ OKᵍ boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-pr p A t u v =
    I.prodrec boolrecᵍ-pr I.𝟙 p A v
      (natcaseᵢ boolrecᵍ-nc₂ (Boolᵍ I.+ p)
         (I.Π I.𝟙 , p ▷
            I.Erased I.𝕨 I.zeroᵘ (OKᵢ OKᵍ (I.var x0)) ▹
          Targetᵢ 4 A (I.var x1) (I.var x0))
         (I.lam I.𝟙 nothing $
          erasedrecᵢ p (Targetᵢ 4 A I.zero (I.var x0))
            (I.unitrec I.𝟘 I.𝟘
               (Targetᵢ 5 A I.zero (I.box I.𝕨 I.zeroᵘ (I.var x0)))
               (I.var x0) (IW.wk[ 4 ] u))
            (I.var x0))
         (natcaseᵢ boolrecᵍ-nc₁ (Boolᵍ I.+ p)
            (I.Π I.𝟙 , p ▷
               I.Erased I.𝕨 I.zeroᵘ (OKᵢ OKᵍ (I.suc (I.var x0))) ▹
             Targetᵢ 5 A (I.suc (I.var x1)) (I.var x0))
            (I.lam I.𝟙 nothing $
             erasedrecᵢ p (Targetᵢ 5 A (I.suc I.zero) (I.var x0))
               (I.unitrec I.𝟘 I.𝟘
                  (Targetᵢ 6 A (I.suc I.zero)
                     (I.box I.𝕨 I.zeroᵘ (I.var x0)))
                  (I.var x0) (IW.wk[ 5 ] t))
               (I.var x0))
            (I.lam I.𝟙 nothing $
             erasedrecᵢ p
               (Targetᵢ 6 A (I.suc (I.suc (I.var x2))) (I.var x0))
               (emptyrec-sinkᵢ
                  (Targetᵢ 6 A (I.suc (I.suc (I.var x2)))
                     (I.box I.𝕨 I.zeroᵘ (I.var x0)))
                  (I.var x0))
               (I.var x0))
            (I.var x0))
         (I.var x1) I.∘⟨ I.𝟙 ⟩
       I.var x0)

  opaque
    unfolding
      Erased OK Target boolrec emptyrec-sink erasedrec is-𝕨 natcase
      prodrec⟨_⟩ unitrec⟨_⟩ E.[_]

    -- A translation lemma for boolrecᵢ.

    ⌜boolrecᵢ⌝ :
      I.⟦ q₁ᵢ ⟧ᵍ γ ≡ Boolᵍ →
      I.⟦ q₂ᵢ ⟧ᵍ γ ≡ OKᵍ →
      I.⟦ q₃ᵢ ⟧ᵍ γ ≡ boolrecᵍ-nc₁ →
      I.⟦ q₄ᵢ ⟧ᵍ γ ≡ boolrecᵍ-nc₂ →
      I.⟦ q₅ᵢ ⟧ᵍ γ ≡ boolrecᵍ-pr →
      I.⌜ boolrecᵢ q₁ᵢ q₂ᵢ q₃ᵢ q₄ᵢ q₅ᵢ pᵢ Aᵢ tᵢ uᵢ vᵢ ⌝ γ ≡
      boolrec (I.⟦ pᵢ ⟧ᵍ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ) (I.⌜ uᵢ ⌝ γ)
        (I.⌜ vᵢ ⌝ γ)
    ⌜boolrecᵢ⌝ eq₁ eq₂ eq₃ eq₄ eq₅
      rewrite eq₁ | eq₂ | eq₃ | eq₄ | eq₅ = refl

------------------------------------------------------------------------
-- An unfolding lemma

opaque
  unfolding Target

  -- An unfolding lemma for Target.

  Target≡ : Target k A t u ≡ A [ k ][ prodʷ 𝟙 t u ]↑
  Target≡ = refl

------------------------------------------------------------------------
-- Substitution lemmas

opaque
  unfolding Bool

  -- A substitution lemma for Bool.

  Bool-[] : Bool [ σ ] ≡ Bool
  Bool-[] {σ} =
    (Σʷ 𝟙 , Boolᵍ ▷ ℕ ▹ Erased zeroᵘ (OK (var x0))) [ σ ]  ≡⟨ cong (ΠΣ⟨_⟩_,_▷_▹_ _ _ _ _) Erased-[] ⟩
    Σʷ 𝟙 , Boolᵍ ▷ ℕ ▹ Erased zeroᵘ (OK (var x0) [ σ ⇑ ])  ≡⟨ cong (ΠΣ⟨_⟩_,_▷_▹_ _ _ _ _) $ cong (Erased _) B.OK-[] ⟩
    Σʷ 𝟙 , Boolᵍ ▷ ℕ ▹ Erased zeroᵘ (OK (var x0))          ∎

opaque
  unfolding true

  -- A substitution lemma for true.

  true-[] : true [ σ ] ≡ true
  true-[] = cong (prod _ _ _) []-[]

opaque
  unfolding false

  -- A substitution lemma for false.

  false-[] : false [ σ ] ≡ false
  false-[] = cong (prod _ _ _) []-[]

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
          subst₂ Subst (sym $ N.+-assoc j k n)
            (sym $ N.+-assoc j (1+ k) n)
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
          subst₂ Subst (sym $ N.+-assoc j k n)
            (sym $ N.+-assoc j (2+ k) n)
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
    boolrec p A t u v [ σ ] ≡
    boolrec p (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
  boolrec-[] {p} {A} {t} {u} {v} {σ} =
    prodrec boolrecᵍ-pr 𝟙 p A v
      (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased zeroᵘ (OK (var x0)) ▹
          Target 4 A (var x1) (var x0))
         (lam 𝟙 $
          erasedrec p (Target 4 A zero (var x0))
            (unitrec 𝟘 𝟘 (Target 5 A zero E.[ var x0 ]) (var x0)
               (wk[ 4 ]′ u))
            (var x0))
         (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased zeroᵘ (OK (suc (var x0))) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam 𝟙 $
             erasedrec p (Target 5 A (suc zero) (var x0))
               (unitrec 𝟘 𝟘 (Target 6 A (suc zero) E.[ var x0 ])
                  (var x0) (wk[ 5 ]′ t))
               (var x0))
            (lam 𝟙 $
             erasedrec p (Target 6 A (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target 6 A (suc (suc (var x2))) E.[ var x0 ])
                  (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ 𝟙 ⟩
       var x0)
      [ σ ]                                                             ≡⟨ cong (prodrec _ _ _ _ _) $
                                                                           cong (flip _∘⟨ 𝟙 ⟩_ _) $
                                                                           trans natcase-[] $
                                                                           cong₄ (natcase _ _)
                                                                             (cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                                (trans Erased-[] $
                                                                                 cong (Erased _) B.OK-[])
                                                                                refl)
                                                                             (cong (lam _) erasedrec-[])
                                                                             (trans natcase-[] $
                                                                              cong₄ (natcase _ _)
                                                                                (cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                                   (trans Erased-[] $
                                                                                    cong (Erased _) B.OK-[])
                                                                                   refl)
                                                                                (cong (lam _) erasedrec-[])
                                                                                (cong (lam _) $
                                                                                 trans erasedrec-[] $
                                                                                 cong₂ (erasedrec _ _) emptyrec-sink-[] refl)
                                                                                refl)
                                                                             refl ⟩
    prodrec boolrecᵍ-pr 𝟙 p (A [ σ ⇑ ]) (v [ σ ])
      (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased zeroᵘ (OK (var x0)) ▹
          (Target 4 A (var x1) (var x0) [ σ ⇑[ 4 ] ]))
         (lam 𝟙 $
          erasedrec p (Target 4 A zero (var x0) [ σ ⇑[ 4 ] ])
            (unitrec 𝟘 𝟘 (Target 5 A zero E.[ var x0 ] [ σ ⇑[ 5 ] ])
               (var x0) (wk[ 4 ]′ u [ σ ⇑[ 4 ] ]))
            (var x0))
         (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased zeroᵘ (OK (suc (var x0))) ▹
             (Target 5 A (suc (var x1)) (var x0) [ σ ⇑[ 5 ] ]))
            (lam 𝟙 $
             erasedrec p (Target 5 A (suc zero) (var x0) [ σ ⇑[ 5 ] ])
               (unitrec 𝟘 𝟘
                  (Target 6 A (suc zero) E.[ var x0 ] [ σ ⇑[ 6 ] ])
                  (var x0) (wk[ 5 ]′ t [ σ ⇑[ 5 ] ]))
               (var x0))
            (lam 𝟙 $
             erasedrec p
               (Target 6 A (suc (suc (var x2))) (var x0) [ σ ⇑[ 6 ] ])
               (emptyrec-sink
                  (Target 6 A (suc (suc (var x2))) E.[ var x0 ]
                     [ σ ⇑[ 6 ] ])
                  (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ 𝟙 ⟩
       var x0)                                                          ≡⟨ (cong (prodrec _ _ _ _ _) $
                                                                           cong (flip (_∘⟨ 𝟙 ⟩_) _) $
                                                                           cong₄ (natcase _ _)
                                                                             (cong (ΠΣ⟨_⟩_,_▷_▹_ _ _ _ _) Target-[⇑])
                                                                             (cong (lam _) $
                                                                              cong₃ (erasedrec _)
                                                                                Target-[⇑]
                                                                                (cong₃ (unitrec _ _)
                                                                                   (trans Target-[⇑] $
                                                                                    cong (Target _ _ _) []-[])
                                                                                   refl (wk[]′-[⇑] u))
                                                                                refl)
                                                                             (cong₄ (natcase _ _)
                                                                                (cong (ΠΣ⟨_⟩_,_▷_▹_ _ _ _ _) Target-[⇑])
                                                                                (cong (lam _) $
                                                                                 cong₃ (erasedrec _)
                                                                                   Target-[⇑]
                                                                                   (cong₃ (unitrec _ _)
                                                                                      (trans Target-[⇑] $
                                                                                       cong (Target _ _ _) []-[])
                                                                                      refl (wk[]′-[⇑] t))
                                                                                   refl)
                                                                                (cong (lam _) $
                                                                                 cong₃ (erasedrec _)
                                                                                   Target-[⇑]
                                                                                   (cong₂ emptyrec-sink
                                                                                      (trans Target-[⇑] $
                                                                                       cong (Target _ _ _) []-[])
                                                                                      refl)
                                                                                   refl)
                                                                                refl)
                                                                             refl) ⟩
    prodrec boolrecᵍ-pr 𝟙 p (A [ σ ⇑ ]) (v [ σ ])
      (natcase boolrecᵍ-nc₂ (Boolᵍ + p)
         (Π 𝟙 , p ▷ Erased zeroᵘ (OK (var x0)) ▹
          Target 4 (A [ σ ⇑ ]) (var x1) (var x0))
         (lam 𝟙 $
          erasedrec p (Target 4 (A [ σ ⇑ ]) zero (var x0))
            (unitrec 𝟘 𝟘 (Target 5 (A [ σ ⇑ ]) zero E.[ var x0 ])
               (var x0) (wk[ 4 ]′ (u [ σ ])))
            (var x0))
         (natcase boolrecᵍ-nc₁ (Boolᵍ + p)
            (Π 𝟙 , p ▷ Erased zeroᵘ (OK (suc (var x0))) ▹
             Target 5 (A [ σ ⇑ ]) (suc (var x1)) (var x0))
            (lam 𝟙 $
             erasedrec p (Target 5 (A [ σ ⇑ ]) (suc zero) (var x0))
               (unitrec 𝟘 𝟘
                  (Target 6 (A [ σ ⇑ ]) (suc zero) E.[ var x0 ])
                  (var x0) (wk[ 5 ]′ (t [ σ ])))
               (var x0))
            (lam 𝟙 $
             erasedrec p
               (Target 6 (A [ σ ⇑ ]) (suc (suc (var x2))) (var x0))
               (emptyrec-sink
                  (Target 6 (A [ σ ⇑ ]) (suc (suc (var x2)))
                     E.[ var x0 ])
                  (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ 𝟙 ⟩
       var x0)                                                          ∎

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
    wk[ k ]′ (A [ prodʷ 𝟙 t u ]₀)
  Target-wk[]′ {k} {A} {t} {u} =
    A [ k ][ prodʷ 𝟙 (wk[ k ]′ t) (wk[ k ]′ u) ]↑  ≡⟨⟩
    A [ k ][ wk[ k ]′ (prodʷ 𝟙 t u) ]↑             ≡⟨ [][wk[]′]↑ A ⟩
    wk[ k ]′ (A [ prodʷ 𝟙 t u ]₀)                  ∎

opaque

  -- A weakening lemma for boolrec.

  wk-boolrec :
    wk ρ (boolrec p A t u v) ≡
    boolrec p (wk (lift ρ) A) (wk ρ t) (wk ρ u) (wk ρ v)
  wk-boolrec {ρ} {p} {A} {t} {u} {v} =
    wk ρ (boolrec p A t u v)                                           ≡⟨ wk-liftn 0 ⟩

    boolrec p A t u v [ toSubst ρ ]                                    ≡⟨ boolrec-[] ⟩

    boolrec p (A [ toSubst ρ ⇑ ]) (t [ toSubst ρ ]) (u [ toSubst ρ ])
      (v [ toSubst ρ ])                                                ≡˘⟨ cong₄ (boolrec _)
                                                                             (wk-liftn 1) (wk-liftn 0) (wk-liftn 0) (wk-liftn 0) ⟩
    boolrec p (wk (lift ρ) A) (wk ρ t) (wk ρ u) (wk ρ v)               ∎
