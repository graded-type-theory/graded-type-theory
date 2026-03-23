------------------------------------------------------------------------
-- Binary sums, defined using other types
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions

module Definition.Untyped.Sum
  {ℓ} {M : Set ℓ}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Nat 𝕄
  hiding (module Internal)
open import Definition.Untyped.Properties M
open import Definition.Untyped.Bool.Greatest-lower-bound 𝕄 as UB
  hiding (Target; module Internal)
open import Definition.Untyped.Sup R

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Weakening
import Definition.Typed.Decidable.Internal.Substitution.Primitive

open import Graded.Mode

open import Tools.Bool
  renaming (Bool to Bool′; true to true′; false to false′)
open import Tools.Fin
open import Tools.Function
open import Tools.Level
  renaming (Lift to Lift′; lift to lift′)
open import Tools.Maybe
open import Tools.Nat as N hiding (_⊔_; _+_)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  a b : Universe-level
  k k₁ k₂ n : Nat
  A B P l r t u v w : Term _
  σ : Subst _ _
  ρ : Wk _ _
  q p p₁ p₂ p₃ p₄ : M

------------------------------------------------------------------------
-- An Agda sketch of the implementation

private module Sketch where

  prodrec′ :
    ∀ {a p q} {A : Set a} {P : A → Set p}
    (Q : Σ A P → Set q) → ∀ x → (∀ x y → Q (x , y)) → Q x
  prodrec′ _ (x , y) f = f x y

  boolrec′ :
    ∀ {p} (P : Bool′ → Set p) →
    P true′ → P false′ → ∀ x → P x
  boolrec′ _ _ f false′ = f
  boolrec′ _ t _ true′ = t

  Sum′ : ∀ {a b} → Set a → Set b → Bool′ → Set (a ⊔ b)
  Sum′ {a} {b} A B x =
    boolrec′ (λ _ → Set (a ⊔ b)) (Lift′ b A) (Lift′ a B) x

  Sum : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
  Sum {a} {b} A B = Σ (Lift′ (a ⊔ b) Bool′) λ x → Sum′ A B (Lift′.lower x)

  inl : ∀ {a b} {A : Set a} {B : Set b} → A → Sum A B
  inl a = (lift′ true′) , (lift′ a)

  inr : ∀ {a b} {A : Set a} {B : Set b} → B → Sum A B
  inr b = (lift′ false′) , (lift′ b)

  Target :
    ∀ {a b p} {A : Set a} {B : Set b} →
    (Sum A B → Set p) → (b : Bool′) → Sum′ A B b → Set p
  Target P b s = P (lift′ b , s)

  sumrec :
    ∀ {a b p} {A : Set a} {B : Set b} →
    (P : Sum A B → Set p) →
    ((a : A) → P (inl a)) → ((b : B) → P (inr b)) →
    ∀ x → P x
  sumrec {A} {B} P l r x =
    prodrec′ P x
      λ b ok →
        boolrec′
          (λ b → (ok : Sum′ A B b) → Target P b ok)
          (λ ok → l (Lift′.lower ok))
          (λ ok → r (Lift′.lower ok))
          (Lift′.lower b) ok

------------------------------------------------------------------------
-- Term formers

opaque

  -- A definition that is used in the implemenation of Sum.

  Sum′ : (a b : Lvl n) (A B t : Term n) → Term n
  Sum′ a b A B t =
    boolrec 𝟘
      (wk1 $ U (a supᵘₗ b))
      (Lift b A)
      (Lift a B)
      t

opaque

  -- The binary sum type.
  -- The two grades in the Σ-type are set to 𝟙. The first represents
  -- the uses of the boolean in an element of type Sum a b A B and the
  -- second the number of uses of the boolean in Sum′. Since both of
  -- these are used by boolrec, which is linear in that argument, 𝟙
  -- should be a reasonable choice.

  Sum : (a b : Lvl n) (A B : Term n) → Term n
  Sum a b A B =
    Σʷ 𝟙 , 𝟙 ▷ Lift (a supᵘₗ b) Bool ▹
      Sum′ (wk1 a) (wk1 b) (wk1 A) (wk1 B) (lower (var x0))

opaque

  -- The constructor inl

  inl : Term n → Term n
  inl t = prodʷ 𝟙 (lift true) (lift t)

opaque

  -- The constructor inr

  inr : Term n → Term n
  inr t = prodʷ 𝟙 (lift false) (lift t)

opaque

  -- A definition that is used in the implementation of sumrec.

  Targetˢʳ :
    ∀ k → Term (1+ n) → Term (k N.+ n) → Term (k N.+ n) → Term (k N.+ n)
  Targetˢʳ k A t u = A [ k ][ prodʷ 𝟙 (lift t) u ]↑

opaque

  -- An eliminator for binary sums.

  sumrec :
    (q p : M)
    (a b : Lvl n)
    (A B : Term n)
    (P l r : Term (1+ n)) → Term n → Term n
  sumrec q p a b A B P l r t =
    prodrec p 𝟙 q P t
      (boolrec (q + p)
        (Π p , q ▷ Sum′ (wk[ 3 ]′ a) (wk[ 3 ]′ b) (wk[ 3 ]′ A) (wk[ 3 ]′ B) (var x0)
                         ▹ Targetˢʳ 4 P (var x1) (var x0))
        (lam p (l [ 3 ][ lower (var x0) ]↑))
        (lam p (r [ 3 ][ lower (var x0) ]↑))
        (lower (var x1))
        ∘⟨ p ⟩ var x0)

------------------------------------------------------------------------
-- Variants of the term formers, intended to be used with the internal
-- type-checker

module Internal
  {b} {Mode : Set b}
  (𝐌 : IsMode Mode 𝕄)
  where

  open UB.Internal 𝐌 R

  private
    module I =
      Definition.Typed.Decidable.Internal.Term 𝐌 R
    module IS =
      Definition.Typed.Decidable.Internal.Substitution.Primitive 𝐌 R
    module IW =
      Definition.Typed.Decidable.Internal.Weakening 𝐌 R

  private variable
    c : I.Constants
    Aᵢ Bᵢ tᵢ lᵢ rᵢ Pᵢ : I.Term _ _
    aᵢ bᵢ : I.Lvl _ _
    p₁ᵢ p₂ᵢ p₃ᵢ p₄ᵢ : I.Termᵍ _
    γ : I.Contexts _

  -- A variant of Sum′.

  Sum′ᵢ : (a b : I.Lvl c n) (A B t : I.Term c n) → I.Term c n
  Sum′ᵢ a b A B t =
    boolrecᵢ I.𝟘
      (IW.wk[ 1 ] (I.U (a I.supᵘₗ b)))
      (I.Lift b A)
      (I.Lift a B)
      t

  opaque
    unfolding Sum′

    -- A translation lemma for Sum′ᵢ.

    ⌜Sum′ᵢ⌝ :
      I.⌜ Sum′ᵢ aᵢ bᵢ Aᵢ Bᵢ tᵢ ⌝ γ ≡ Sum′ (I.⌜ aᵢ ⌝ γ) (I.⌜ bᵢ ⌝ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ Bᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
    ⌜Sum′ᵢ⌝ {aᵢ} {bᵢ} {Aᵢ} {Bᵢ} {tᵢ} {γ} =
      ⌜boolrecᵢ⌝ {pᵢ = I.𝟘}
        {Aᵢ = IW.wk[ 1 ] (I.U (aᵢ I.supᵘₗ bᵢ))}
        {tᵢ = I.Lift bᵢ Aᵢ}
        {uᵢ = I.Lift aᵢ Bᵢ}
        {vᵢ = tᵢ}
        {γ = γ}

  -- A variant of Sum

  Sumᵢ : (a b : I.Lvl c n) (A B : I.Term c n) → I.Term c n
  Sumᵢ a b A B =
    I.Σʷ I.𝟙 , I.𝟙 ▷ I.Lift (a I.supᵘₗ b) Boolᵢ ▹
    Sum′ᵢ (IW.wk[ 1 ] a) (IW.wk[ 1 ] b) (IW.wk[ 1 ] A) (IW.wk[ 1 ] B) (I.lower (I.var x0))

  opaque
    unfolding Sum

    -- Atranslation lemma for Sumᵢ.

    ⌜Sumᵢ⌝ :
      I.⌜ Sumᵢ aᵢ bᵢ Aᵢ Bᵢ ⌝ γ ≡ Sum (I.⌜ aᵢ ⌝ γ) (I.⌜ bᵢ ⌝ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ Bᵢ ⌝ γ)
    ⌜Sumᵢ⌝ {aᵢ} {bᵢ} {Aᵢ} {Bᵢ} {γ} =
      cong₂ (Σʷ 𝟙 , 𝟙 ▷_▹_) (cong (Lift _) (⌜Boolᵢ⌝ {γ = γ}))
        (⌜Sum′ᵢ⌝ {aᵢ = IW.wk[ 1 ] aᵢ} {bᵢ = IW.wk[ 1 ] bᵢ}
          {Aᵢ = IW.wk[ 1 ] Aᵢ} {Bᵢ = IW.wk[ 1 ] Bᵢ} {tᵢ = I.lower (I.var x0)} {γ = γ})

  -- A variant of inl.

  inlᵢ : (_ _ : I.Lvl c n) (_ _ _ : I.Term c n) → I.Term c n
  inlᵢ a b A B t =
    I.prod I.𝕨 I.𝟙
      (just (I.𝟙 , Sum′ᵢ (IW.wk (step id) a) (IW.wk (step id) b) (IW.wk (step id) A) (IW.wk (step id) B) (I.lower (I.var x0))))
      (I.lift (just (a I.supᵘₗ b)) trueᵢ) (I.lift (just b) t)

  opaque
    unfolding inl

    -- An unfolding lemma for inlᵢ.

    ⌜inlᵢ⌝ :
      I.⌜ inlᵢ aᵢ bᵢ Aᵢ Bᵢ tᵢ ⌝ γ ≡ inl (I.⌜ tᵢ ⌝ γ)
    ⌜inlᵢ⌝ {γ} =
      cong (flip (prodʷ 𝟙) _) (cong lift (⌜trueᵢ⌝ {γ = γ}))

  -- A variant of inr.

  inrᵢ : (_ _ : I.Lvl c n) (_ _ _ : I.Term c n) → I.Term c n
  inrᵢ a b A B t =
    I.prod I.𝕨 I.𝟙
      (just (I.𝟙 , Sum′ᵢ (IW.wk (step id) a) (IW.wk (step id) b) (IW.wk (step id) A) (IW.wk (step id) B) (I.lower (I.var x0))))
      (I.lift (just (a I.supᵘₗ b)) falseᵢ) (I.lift (just a) t)

  opaque
    unfolding inr

    -- An unfolding lemma for inrᵢ.

    ⌜inrᵢ⌝ :
      I.⌜ inrᵢ aᵢ bᵢ Aᵢ Bᵢ tᵢ ⌝ γ ≡ inr (I.⌜ tᵢ ⌝ γ)
    ⌜inrᵢ⌝ {γ} =
      cong (flip (prodʷ 𝟙) _) (cong lift (⌜falseᵢ⌝ {γ = γ}))

  -- A variant of Targetˢʳ

  Targetˢʳᵢ :
    ∀ k → I.Term c (1+ n) → I.Term c (k N.+ n) → I.Term c (k N.+ n) →
    I.Term c (k N.+ n)
  Targetˢʳᵢ k A t u =
    I.subst A (I.cons (IS.wkSubst k I.id) (I.prod I.𝕨 I.𝟙 nothing (I.lift nothing t) u))

  -- A variant of sumrec.

  sumrecᵢ :
    (_ _ : I.Termᵍ (c .I.gs)) →
    (a b : I.Lvl c n) →
    (A B : I.Term c n) →
    (P l r : I.Term c (1+ n)) →
    I.Term c n → I.Term c n
  sumrecᵢ q p a b A B P l r t =
    I.prodrec p I.𝟙 q P t
      (boolrecᵢ (q I.+ p)
        (I.Π p , q ▷ Sum′ᵢ (IW.wk[ 3 ] a) (IW.wk[ 3 ] b) (IW.wk[ 3 ] A) (IW.wk[ 3 ] B) (I.var x0) ▹ Targetˢʳᵢ 4 P (I.var x1) (I.var x0))
        (I.lam p nothing (I.subst l (I.cons (IS.wkSubst 3 I.id) (I.lower (I.var x0)))))
        (I.lam p nothing (I.subst r (I.cons (IS.wkSubst 3 I.id) (I.lower (I.var x0)))))
        (I.lower (I.var x1))
      I.∘⟨ p ⟩ I.var x0)

  opaque
    unfolding sumrec Targetˢʳ

    -- A translation lemma for sumrecᵢ.

    ⌜sumrecᵢ⌝ :
      I.⟦ p₁ᵢ ⟧ᵍ γ ≡ q →
      I.⟦ p₂ᵢ ⟧ᵍ γ ≡ p →
      I.⌜ sumrecᵢ p₁ᵢ p₂ᵢ aᵢ bᵢ Aᵢ Bᵢ Pᵢ lᵢ rᵢ tᵢ ⌝ γ ≡
      sumrec q p (I.⌜ aᵢ ⌝ γ) (I.⌜ bᵢ ⌝ γ)
        (I.⌜ Aᵢ ⌝ γ) (I.⌜ Bᵢ ⌝ γ) (I.⌜ Pᵢ ⌝ γ)
        (I.⌜ lᵢ ⌝ γ) (I.⌜ rᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ)
    ⌜sumrecᵢ⌝ {p₁ᵢ} {γ} {p₂ᵢ} {aᵢ} {bᵢ} {Aᵢ} {Bᵢ}
      {Pᵢ} {lᵢ} {rᵢ} {tᵢ} eq₁ eq₂  =
        cong₆ prodrec eq₂ refl eq₁ refl refl
          (cong₃ _∘⟨_⟩_
            (trans
              (⌜boolrecᵢ⌝
                {pᵢ = p₁ᵢ I.+ p₂ᵢ}
                {Aᵢ = I.Π p₂ᵢ , p₁ᵢ ▷ Sum′ᵢ (IW.wk[ 3 ] aᵢ) (IW.wk[ 3 ] bᵢ) (IW.wk[ 3 ] Aᵢ) (IW.wk[ 3 ] Bᵢ) (I.var x0) ▹ Targetˢʳᵢ 4 Pᵢ (I.var x1) (I.var x0)}
                {tᵢ = I.lam p₂ᵢ nothing (I.subst lᵢ (I.cons (IS.wkSubst 3 I.id) (I.lower (I.var x0))))}
                {uᵢ = I.lam p₂ᵢ nothing (I.subst rᵢ (I.cons (IS.wkSubst 3 I.id) (I.lower (I.var x0))))}
                {vᵢ = I.lower (I.var x1)} {γ = γ})
              (cong₅ boolrec (+-cong eq₁ eq₂)
                (cong₄ Π_,_▷_▹_ eq₂ eq₁
                  (⌜Sum′ᵢ⌝ {aᵢ = IW.wk[ 3 ] aᵢ} {bᵢ = IW.wk[ 3 ] bᵢ} {Aᵢ = IW.wk[ 3 ] Aᵢ} {Bᵢ = IW.wk[ 3 ] Bᵢ} {tᵢ = I.var x0} {γ = γ})
                  refl)
                (cong (flip lam _) eq₂)
                (cong (flip lam _) eq₂)
                refl))
            eq₂ refl)
