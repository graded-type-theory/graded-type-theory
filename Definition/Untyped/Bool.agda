------------------------------------------------------------------------
-- Booleans, defined using other types
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Bool.OK and
-- Definition.Typed.Properties.Admissible.Bool, and usage rules can be
-- found in Graded.Derived.Bool.

import Graded.Modality

module Definition.Untyped.Bool
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  -- It is assumed that the modality has an nr function.
  ⦃ has-nr : Has-nr (Modality.semiring-with-meet 𝕄) ⦄
  where

private
  open module M = Modality 𝕄 using (𝟘; 𝟙; ω; _+_; _·_; _∧_)

import Definition.Typed.Decidable.Internal.Term
import Definition.Typed.Decidable.Internal.Substitution.Primitive
import Definition.Typed.Decidable.Internal.Weakening
open import Definition.Typed.Restrictions

open import Definition.Untyped M
open import Definition.Untyped.Empty 𝕄 as UE hiding (module Internal)
open import Definition.Untyped.Nat 𝕄 as UN hiding (module Internal)
open import Definition.Untyped.Properties M

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄 hiding (has-nr)
open import Graded.Mode 𝕄

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
  k k₁ k₂ n : Nat
  A t u v w : Term _
  σ         : Subst _ _
  ρ         : Wk _ _
  p         : M

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
-- Some grades

opaque

  -- A grade used in the implementation of OK.

  OKᵍ : M
  OKᵍ = nr 𝟘 𝟘 𝟘 𝟘 𝟙

opaque

  -- A grade used in the implementation of Bool.

  Boolᵍ : M
  Boolᵍ = nr OKᵍ 𝟘 𝟘 𝟘 𝟙

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-Π : M
  boolrecᵍ-Π = nr 𝟘 𝟙 𝟙 𝟘 𝟘

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-nc₁ : M
  boolrecᵍ-nc₁ = nr 𝟘 𝟙 𝟘 𝟘 𝟙

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-nc₂ : M
  boolrecᵍ-nc₂ = nr boolrecᵍ-nc₁ 𝟘 𝟘 𝟘 𝟙

opaque

  -- A function that is used in the implementation of boolrec.

  boolrecᵍ-nc₃ : M → M
  boolrecᵍ-nc₃ p = ⌜ ⌞ boolrecᵍ-Π ⌟ ⌝ · Boolᵍ + p · ω

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-pr : M
  boolrecᵍ-pr = nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π

------------------------------------------------------------------------
-- Some lemmas about the grades

opaque
  unfolding OKᵍ

  -- If the nr function satisfies Linearity-like-nr-for-𝟘,
  -- then OKᵍ is equal to 𝟘 ∧ 𝟙.

  OKᵍ≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    OKᵍ ≡ 𝟘 ∧ 𝟙
  OKᵍ≡ hyp =
    nr 𝟘 𝟘 𝟘 𝟘 𝟙                 ≡⟨ hyp ⟩
    ((𝟙 ∧ 𝟘) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ cong₂ _∧_ (M.+-identityʳ _) (M.+-identityʳ _) ⟩
    ((𝟙 ∧ 𝟘) · 𝟙) ∧ 𝟙            ≡⟨ cong (flip _∧_ _) $ M.·-identityʳ _ ⟩
    (𝟙 ∧ 𝟘) ∧ 𝟙                  ≡⟨ cong (flip _∧_ _) $ M.∧-comm _ _ ⟩
    (𝟘 ∧ 𝟙) ∧ 𝟙                  ≡⟨ M.∧-assoc _ _ _ ⟩
    𝟘 ∧ (𝟙 ∧ 𝟙)                  ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    𝟘 ∧ 𝟙                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding Boolᵍ

  -- If the nr function satisfies Linearity-like-nr-for-𝟘,
  -- then Boolᵍ is equal to 𝟘 ∧ 𝟙.

  Boolᵍ≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    Boolᵍ ≡ 𝟘 ∧ 𝟙
  Boolᵍ≡ hyp =
    nr OKᵍ 𝟘 𝟘 𝟘 𝟙                 ≡⟨ hyp ⟩
    ((𝟙 ∧ OKᵍ) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ cong₂ _∧_ (M.+-identityʳ _) (M.+-identityʳ _) ⟩
    ((𝟙 ∧ OKᵍ) · 𝟙) ∧ 𝟙            ≡⟨ cong (flip _∧_ _) $ M.·-identityʳ _ ⟩
    (𝟙 ∧ OKᵍ) ∧ 𝟙                  ≡⟨ cong (flip _∧_ _) $ M.∧-comm _ _ ⟩
    (OKᵍ ∧ 𝟙) ∧ 𝟙                  ≡⟨ M.∧-assoc _ _ _ ⟩
    OKᵍ ∧ (𝟙 ∧ 𝟙)                  ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    OKᵍ ∧ 𝟙                        ≡⟨ cong (_∧ _) $ OKᵍ≡ hyp ⟩
    (𝟘 ∧ 𝟙) ∧ 𝟙                    ≡⟨ M.∧-assoc _ _ _ ⟩
    𝟘 ∧ (𝟙 ∧ 𝟙)                    ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    𝟘 ∧ 𝟙                          ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-Π

  -- If the nr function satisfies Linearity-like-nr-for-𝟙,
  -- then boolrecᵍ-Π is equal to 𝟙.

  boolrecᵍ-Π≡ :
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-Π ≡ 𝟙
  boolrecᵍ-Π≡ hyp =
    nr 𝟘 𝟙 𝟙 𝟘 𝟘             ≡⟨ hyp ⟩
    (𝟙 + 𝟘) · 𝟘 + ω · 𝟘 + 𝟙  ≡⟨ trans (cong₂ _+_ (M.·-zeroʳ _) (cong (flip _+_ _) $ M.·-zeroʳ _)) $
                                trans (M.+-identityˡ _) $
                                M.+-identityˡ _ ⟩
    𝟙                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-nc₁

  -- If the nr function satisfies Linearity-like-nr-for-𝟙,
  -- then boolrecᵍ-nc₁ is equal to 𝟙.

  boolrecᵍ-nc₁≡ :
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-nc₁ ≡ 𝟙
  boolrecᵍ-nc₁≡ hyp =
    nr 𝟘 𝟙 𝟘 𝟘 𝟙             ≡⟨ hyp ⟩
    (𝟙 + 𝟘) · 𝟙 + ω · 𝟘 + 𝟘  ≡⟨ cong₂ _+_ (cong (flip _·_ _) $ M.+-identityʳ _) (M.+-identityʳ _) ⟩
    𝟙 · 𝟙 + ω · 𝟘            ≡⟨ cong₂ _+_ (M.·-identityˡ _) (M.·-zeroʳ _) ⟩
    𝟙 + 𝟘                    ≡⟨ M.+-identityʳ _ ⟩
    𝟙                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A lemma used below.

  [[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 : ((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘) ≡ 𝟙
  [[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 =
    ((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ cong₂ _∧_ (M.+-identityʳ _) (M.+-identityʳ _) ⟩
    ((𝟙 ∧ 𝟙) · 𝟙) ∧ 𝟙            ≡⟨ cong (flip _∧_ _) $ M.·-identityʳ _ ⟩
    (𝟙 ∧ 𝟙) ∧ 𝟙                  ≡⟨ cong (flip _∧_ _) $ M.∧-comm _ _ ⟩
    (𝟙 ∧ 𝟙) ∧ 𝟙                  ≡⟨ M.∧-assoc _ _ _ ⟩
    𝟙 ∧ (𝟙 ∧ 𝟙)                  ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    𝟙 ∧ 𝟙                        ≡⟨ M.∧-idem _ ⟩
    𝟙                            ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-nc₂

  -- If the nr function satisfies Linearity-like-nr-for-𝟘
  -- and Linearity-like-nr-for-𝟙, then boolrecᵍ-nc₂ is equal to 𝟙.

  boolrecᵍ-nc₂≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-nc₂ ≡ 𝟙
  boolrecᵍ-nc₂≡ hyp₁ hyp₂ =
    nr boolrecᵍ-nc₁ 𝟘 𝟘 𝟘 𝟙      ≡⟨ cong (λ p → nr p _ _ _ _) $ boolrecᵍ-nc₁≡ hyp₂ ⟩
    nr 𝟙 𝟘 𝟘 𝟘 𝟙                 ≡⟨ hyp₁ ⟩
    ((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ [[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 ⟩
    𝟙                            ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-pr

  -- If the nr function satisfies Linearity-like-nr-for-𝟘
  -- and Linearity-like-nr-for-𝟙, then boolrecᵍ-pr is equal to 𝟙.

  boolrecᵍ-pr≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-pr ≡ 𝟙
  boolrecᵍ-pr≡ hyp₁ hyp₂ =
    nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π  ≡⟨ cong₂ _∧_
                                               (cong (λ p → nr p _ _ _ _) $ boolrecᵍ-nc₂≡ hyp₁ hyp₂)
                                               (boolrecᵍ-Π≡ hyp₂) ⟩
    nr 𝟙 𝟘 𝟘 𝟘 𝟙 ∧ 𝟙                      ≡⟨ cong (flip _∧_ _) hyp₁ ⟩
    (((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)) ∧ 𝟙     ≡⟨ cong (flip _∧_ _) [[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 ⟩
    𝟙 ∧ 𝟙                                 ≡⟨ M.∧-idem _ ⟩
    𝟙                                     ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-pr

  -- If the modality's zero is well-behaved, then boolrecᵍ-pr is
  -- non-zero.

  boolrecᵍ-pr≢𝟘 :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M.semiring-with-meet ⦄ →
    boolrecᵍ-pr ≢ 𝟘
  boolrecᵍ-pr≢𝟘 =
    nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π ≡ 𝟘  →⟨ ∧-positiveˡ ⟩
    nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ≡ 𝟘               →⟨ proj₂ ∘→ proj₂ ∘→ nr-positive ⟩
    𝟙 ≡ 𝟘                                     →⟨ non-trivial ⟩
    ⊥                                         □

------------------------------------------------------------------------
-- Term formers

opaque

  -- A definition that is used in the implementation of Bool.

  OK : Term n → Term n
  OK t =
    natcase OKᵍ 𝟘 (U zeroᵘ) Unitʷ
      (natcase 𝟘 𝟘 (U zeroᵘ) Unitʷ Empty (var x0)) t

opaque

  -- A type of booleans.

  Bool : Term n
  Bool = Σʷ ω , Boolᵍ ▷ ℕ ▹ OK (var x0)

opaque

  -- The constructor true.

  true : Term n
  true = prodʷ ω (suc zero) starʷ

opaque

  -- The constructor false.

  false : Term n
  false = prodʷ ω zero starʷ

opaque

  -- A definition that is used in the implementation of boolrec.

  Target :
    ∀ k → Term (1+ n) → Term (k N.+ n) → Term (k N.+ n) → Term (k N.+ n)
  Target k A t u = A [ k ][ prodʷ ω t u ]↑

opaque

  -- An eliminator for Bool.

  boolrec : M → Term (1+ n) → Term n → Term n → Term n → Term n
  boolrec p A t u v =
    prodrec boolrecᵍ-pr ω p A v
      (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 4 A zero (var x0))
            (var x0) (wk[ 3 ]′ u))
         (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
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

module Internal (R : Type-restrictions 𝕄) where

  open UE.Internal R
  open UN.Internal R

  private
    module I =
      Definition.Typed.Decidable.Internal.Term R
    module IS =
      Definition.Typed.Decidable.Internal.Substitution.Primitive R
    module IW =
      Definition.Typed.Decidable.Internal.Weakening R

  private variable
    c                                  : I.Constants
    pᵢ p₁ᵢ p₂ᵢ q₁ᵢ q₂ᵢ q₃ᵢ q₄ᵢ q₅ᵢ q₆ᵢ : I.Termᵍ _
    Aᵢ tᵢ uᵢ vᵢ                        : I.Term _ _
    γ                                  : I.Contexts _

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

  Boolᵢ : (_ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  Boolᵢ Boolᵍ OKᵍ = I.Σʷ I.ω , Boolᵍ ▷ I.ℕ ▹ OKᵢ OKᵍ (I.var x0)

  opaque
    unfolding Bool OK natcase

    -- A translation lemma for Boolᵢ.

    ⌜Boolᵢ⌝ :
      I.⟦ p₁ᵢ ⟧ᵍ γ ≡ Boolᵍ →
      I.⟦ p₂ᵢ ⟧ᵍ γ ≡ OKᵍ →
      I.⌜ Boolᵢ {n = n} p₁ᵢ p₂ᵢ ⌝ γ ≡ Bool
    ⌜Boolᵢ⌝ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

  -- A variant of true.

  trueᵢ : (_ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  trueᵢ Boolᵍ OKᵍ =
    I.prod I.𝕨 I.ω (just (Boolᵍ , OKᵢ OKᵍ (I.var x0))) (I.suc I.zero)
      (I.star I.𝕨)

  opaque
    unfolding true

    -- A translation lemma for trueᵢ.

    ⌜trueᵢ⌝ : I.⌜ trueᵢ {n = n} p₁ᵢ p₂ᵢ ⌝ γ ≡ true
    ⌜trueᵢ⌝ = refl

  -- A variant of false.

  falseᵢ : (_ _ : I.Termᵍ (c .I.gs)) → I.Term c n
  falseᵢ Boolᵍ OKᵍ =
    I.prod I.𝕨 I.ω (just (Boolᵍ , OKᵢ OKᵍ (I.var x0))) I.zero
      (I.star I.𝕨)

  opaque
    unfolding false

    -- A translation lemma for falseᵢ.

    ⌜falseᵢ⌝ : I.⌜ falseᵢ {n = n} p₁ᵢ p₂ᵢ ⌝ γ ≡ false
    ⌜falseᵢ⌝ = refl

  -- A variant of Target.

  Targetᵢ :
    ∀ k → I.Term c (1+ n) → I.Term c (k N.+ n) → I.Term c (k N.+ n) →
    I.Term c (k N.+ n)
  Targetᵢ k A t u =
    I.subst A (I.cons (IS.wkSubst k I.id) (I.prod I.𝕨 I.ω nothing t u))

  -- A variant of boolrec.

  boolrecᵢ :
    (_ _ _ _ _ _ _ : I.Termᵍ (c .I.gs)) → I.Term c (1+ n) →
    (_ _ _ : I.Term c n) → I.Term c n
  boolrecᵢ
    Boolᵍ OKᵍ boolrecᵍ-Π boolrecᵍ-nc₁ boolrecᵍ-nc₂ boolrecᵍ-pr p
    A t u v =
    I.prodrec boolrecᵍ-pr I.ω p A v
      (natcaseᵢ boolrecᵍ-nc₂ boolrecᵍ-nc₃-p
         (I.Π boolrecᵍ-Π , p ▷ OKᵢ OKᵍ (I.var x0) ▹
          Targetᵢ 4 A (I.var x1) (I.var x0))
         (I.lam boolrecᵍ-Π nothing $
          I.unitrec boolrecᵍ-Π p (Targetᵢ 4 A I.zero (I.var x0))
            (I.var x0) (IW.wk[ 3 ] u))
         (natcaseᵢ boolrecᵍ-nc₁ boolrecᵍ-nc₃-p
            (I.Π boolrecᵍ-Π , p ▷ OKᵢ OKᵍ (I.suc (I.var x0)) ▹
             Targetᵢ 5 A (I.suc (I.var x1)) (I.var x0))
            (I.lam boolrecᵍ-Π nothing $
             I.unitrec boolrecᵍ-Π p
               (Targetᵢ 5 A (I.suc I.zero) (I.var x0)) (I.var x0)
                  (IW.wk[ 4 ] t))
            (I.lam boolrecᵍ-Π nothing $
             emptyrec-sinkᵢ
               (Targetᵢ 5 A (I.suc (I.suc (I.var x1))) (I.var x0))
               (I.var x0))
            (I.var x0))
         (I.var x1) I.∘⟨ boolrecᵍ-Π ⟩
       I.var x0)
    where
    boolrecᵍ-nc₃-p = I.⌜⌞ boolrecᵍ-Π ⌟⌝ I.· Boolᵍ I.+ p I.· I.ω

  opaque
    unfolding OK Target boolrec boolrecᵍ-nc₃ emptyrec-sink natcase

    -- A translation lemma for boolrecᵢ.

    ⌜boolrecᵢ⌝ :
      I.⟦ q₁ᵢ ⟧ᵍ γ ≡ Boolᵍ →
      I.⟦ q₂ᵢ ⟧ᵍ γ ≡ OKᵍ →
      I.⟦ q₃ᵢ ⟧ᵍ γ ≡ boolrecᵍ-Π →
      I.⟦ q₄ᵢ ⟧ᵍ γ ≡ boolrecᵍ-nc₁ →
      I.⟦ q₅ᵢ ⟧ᵍ γ ≡ boolrecᵍ-nc₂ →
      I.⟦ q₆ᵢ ⟧ᵍ γ ≡ boolrecᵍ-pr →
      I.⌜ boolrecᵢ q₁ᵢ q₂ᵢ q₃ᵢ q₄ᵢ q₅ᵢ q₆ᵢ pᵢ Aᵢ tᵢ uᵢ vᵢ ⌝ γ ≡
      boolrec (I.⟦ pᵢ ⟧ᵍ γ) (I.⌜ Aᵢ ⌝ γ) (I.⌜ tᵢ ⌝ γ) (I.⌜ uᵢ ⌝ γ)
        (I.⌜ vᵢ ⌝ γ)
    ⌜boolrecᵢ⌝ eq₁ eq₂ eq₃ eq₄ eq₅ eq₆
      rewrite eq₁ | eq₂ | eq₃ | eq₄ | eq₅ | eq₆ = refl

------------------------------------------------------------------------
-- An unfolding lemma

opaque
  unfolding Target

  -- An unfolding lemma for Target.

  Target≡ : Target k A t u ≡ A [ k ][ prodʷ ω t u ]↑
  Target≡ = refl

------------------------------------------------------------------------
-- Substitution lemmas

opaque
  unfolding OK

  -- A substitution lemma for OK.

  OK-[] : OK t [ σ ] ≡ OK (t [ σ ])
  OK-[] =
    trans natcase-[] $
    cong (flip (natcase _ _ _ _) _) natcase-[]

opaque
  unfolding Bool

  -- A substitution lemma for Bool.

  Bool-[] : Bool [ σ ] ≡ Bool
  Bool-[] {σ} =
    (Σʷ ω , Boolᵍ ▷ ℕ ▹ OK (var x0)) [ σ ]    ≡⟨⟩
    Σʷ ω , Boolᵍ ▷ ℕ ▹ (OK (var x0) [ σ ⇑ ])  ≡⟨ cong (Σ⟨_⟩_,_▷_▹_ _ _ _ _) OK-[] ⟩
    Σʷ ω , Boolᵍ ▷ ℕ ▹ OK (var x0)            ∎

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
          subst₂ Subst (sym $ +-assoc j k₂ n) (sym $ +-assoc j k₁ n)
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
          subst₂ Subst (sym $ +-assoc j k n) (sym $ +-assoc j (1+ k) n)
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
          subst₂ Subst (sym $ +-assoc j (1+ k) n)
            (sym $ +-assoc j (1+ k) n)
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
          subst₂ Subst (sym $ +-assoc j k n) (sym $ +-assoc j (2+ k) n)
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
    prodrec boolrecᵍ-pr ω p A v
      (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p (Target 4 A zero (var x0))
            (var x0) (wk[ 3 ]′ u))
         (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
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
    prodrec boolrecᵍ-pr ω p (A [ σ ⇑ ]) (v [ σ ])
      (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
          (Target 4 A (var x1) (var x0) [ σ ⇑[ 4 ] ]))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p
            (Target 4 A zero (var x0) [ σ ⇑[ 4 ] ]) (var x0)
            (wk[ 3 ]′ u [ σ ⇑[ 3 ] ]))
         (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
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
    prodrec boolrecᵍ-pr ω p (A [ σ ⇑ ]) (v [ σ ])
      (natcase boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p)
         (Π boolrecᵍ-Π , p ▷ OK (var x0) ▹
          Target 4 (A [ σ ⇑ ]) (var x1) (var x0))
         (lam boolrecᵍ-Π $
          unitrec boolrecᵍ-Π p
            (Target 4 (A [ σ ⇑ ]) zero (var x0)) (var x0)
            (wk[ 3 ]′ (u [ σ ])))
         (natcase boolrecᵍ-nc₁ (boolrecᵍ-nc₃ p)
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

  -- A weakening lemma for OK.

  wk-OK : wk ρ (OK t) ≡ OK (wk ρ t)
  wk-OK {ρ} {t} =
    wk ρ (OK t)           ≡⟨ wk≡subst _ _ ⟩
    OK t [ toSubst ρ ]    ≡⟨ OK-[] ⟩
    OK (t [ toSubst ρ ])  ≡˘⟨ cong OK $ wk≡subst _ _ ⟩
    OK (wk ρ t)           ∎

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
    wk[ k ]′ (A [ prodʷ ω t u ]₀)
  Target-wk[]′ {k} {A} {t} {u} =
    A [ k ][ prodʷ ω (wk[ k ]′ t) (wk[ k ]′ u) ]↑  ≡⟨⟩
    A [ k ][ wk[ k ]′ (prodʷ ω t u) ]↑             ≡⟨ [][wk[]′]↑ A ⟩
    wk[ k ]′ (A [ prodʷ ω t u ]₀)                  ∎

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
