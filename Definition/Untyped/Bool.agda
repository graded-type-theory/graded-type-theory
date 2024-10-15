------------------------------------------------------------------------
-- Booleans, defined using other types
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Consequences.DerivedRules.Bool, and usage
-- rules can be found in Graded.Derived.Bool.

import Definition.Untyped
import Graded.Modality
import Graded.Modality.Dedicated-nr

module Definition.Untyped.Bool
  {a} {M : Set a}
  (open Definition.Untyped M)
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Graded.Modality.Dedicated-nr 𝕄)
  -- One can define the booleans using either weak or strong Σ and
  -- unit types.
  (s : Strength)
  -- It is assumed that there is a dedicated nr function.
  ⦃ has-nr : Dedicated-nr ⦄
  where

private
  open module M = Modality 𝕄 using (𝟘; 𝟙; _+_; _·_; _∧_)

open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Unit 𝕄

open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

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

  boolrecᵍ₁ : M
  boolrecᵍ₁ = case s of λ where
    𝕨 → 𝟙
    𝕤 → 𝟘

opaque

  -- Another grade that is used in the implementation of boolrec.

  boolrecᵍ₂ : M
  boolrecᵍ₂ = ⌜ ⌞ boolrecᵍ₁ ⌟ ⌝ · Boolᵍ

------------------------------------------------------------------------
-- Some lemmas about the grades

opaque
  unfolding OKᵍ

  -- If the dedicated nr function satisfies Linearity-like-nr-for-𝟘,
  -- then OKᵍ is equal to 𝟘 ∧ 𝟙.

  OKᵍ≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-dedicated-nr →
    OKᵍ ≡ 𝟘 ∧ 𝟙
  OKᵍ≡ hyp =
    nr 𝟘 𝟘 𝟘 𝟘 𝟙                 ≡⟨ hyp ⟩
    ((𝟙 ∧ 𝟘) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ cong₂ _∧_ (M.+-identityʳ _) (M.+-identityʳ _) ⟩
    ((𝟙 ∧ 𝟘) · 𝟙) ∧ 𝟙            ≡⟨ cong (_∧ _) $ M.·-identityʳ _ ⟩
    (𝟙 ∧ 𝟘) ∧ 𝟙                  ≡⟨ cong (_∧ _) $ M.∧-comm _ _ ⟩
    (𝟘 ∧ 𝟙) ∧ 𝟙                  ≡⟨ M.∧-assoc _ _ _ ⟩
    𝟘 ∧ (𝟙 ∧ 𝟙)                  ≡⟨ cong (_ ∧_) $ M.∧-idem _ ⟩
    𝟘 ∧ 𝟙                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding Boolᵍ

  -- If the dedicated nr function satisfies Linearity-like-nr-for-𝟘,
  -- then Boolᵍ is equal to 𝟘 ∧ 𝟙.

  Boolᵍ≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-dedicated-nr →
    Boolᵍ ≡ 𝟘 ∧ 𝟙
  Boolᵍ≡ hyp =
    nr OKᵍ 𝟘 𝟘 𝟘 𝟙                 ≡⟨ hyp ⟩
    ((𝟙 ∧ OKᵍ) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ cong₂ _∧_ (M.+-identityʳ _) (M.+-identityʳ _) ⟩
    ((𝟙 ∧ OKᵍ) · 𝟙) ∧ 𝟙            ≡⟨ cong (_∧ _) $ M.·-identityʳ _ ⟩
    (𝟙 ∧ OKᵍ) ∧ 𝟙                  ≡⟨ cong (_∧ _) $ M.∧-comm _ _ ⟩
    (OKᵍ ∧ 𝟙) ∧ 𝟙                  ≡⟨ M.∧-assoc _ _ _ ⟩
    OKᵍ ∧ (𝟙 ∧ 𝟙)                  ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    OKᵍ ∧ 𝟙                        ≡⟨ cong (_∧ _) $ OKᵍ≡ hyp ⟩
    (𝟘 ∧ 𝟙) ∧ 𝟙                    ≡⟨ M.∧-assoc _ _ _ ⟩
    𝟘 ∧ (𝟙 ∧ 𝟙)                    ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    𝟘 ∧ 𝟙                          ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding Boolᵍ

  -- If the modality's zero is well-behaved, then Boolᵍ ∧ boolrecᵍ₁ is
  -- non-zero.

  Boolᵍ∧boolrecᵍ₁≢𝟘 :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M.semiring-with-meet ⦄ →
    Boolᵍ ∧ boolrecᵍ₁ ≢ 𝟘
  Boolᵍ∧boolrecᵍ₁≢𝟘 =
    nr OKᵍ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ₁ ≡ 𝟘  →⟨ ∧-positiveˡ ⟩
    nr OKᵍ 𝟘 𝟘 𝟘 𝟙 ≡ 𝟘              →⟨ proj₂ ∘→ proj₂ ∘→ nr-positive ⟩
    𝟙 ≡ 𝟘                           →⟨ non-trivial ⟩
    ⊥                               □

opaque
  unfolding boolrecᵍ₁

  -- If the dedicated nr function satisfies Linearity-like-nr-for-𝟘,
  -- then Boolᵍ ∧ boolrecᵍ₁ is equal to 𝟘 ∧ 𝟙.

  Boolᵍ∧boolrecᵍ₁≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-dedicated-nr →
    Boolᵍ ∧ boolrecᵍ₁ ≡ 𝟘 ∧ 𝟙
  Boolᵍ∧boolrecᵍ₁≡ hyp =
    case singleton s of λ where
      (𝕨 , refl) →
        Boolᵍ ∧ 𝟙    ≡⟨ cong (_∧ _) $ Boolᵍ≡ hyp ⟩
        (𝟘 ∧ 𝟙) ∧ 𝟙  ≡⟨ M.∧-assoc _ _ _ ⟩
        𝟘 ∧ (𝟙 ∧ 𝟙)  ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
        𝟘 ∧ 𝟙        ∎
      (𝕤 , refl) →
        Boolᵍ ∧ 𝟘    ≡⟨ cong (_∧ _) $ Boolᵍ≡ hyp ⟩
        (𝟘 ∧ 𝟙) ∧ 𝟘  ≡⟨ M.∧-comm _ _ ⟩
        𝟘 ∧ (𝟘 ∧ 𝟙)  ≡˘⟨ M.∧-assoc _ _ _ ⟩
        (𝟘 ∧ 𝟘) ∧ 𝟙  ≡⟨ cong (_∧ _) $ M.∧-idem _ ⟩
        𝟘 ∧ 𝟙        ∎
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Term formers

opaque

  -- A definition that is used in the implementation of Bool.

  OK : Term n → Term n
  OK t =
    natcase OKᵍ 𝟘 (U 0) (Unit s 0)
      (natcase 𝟘 𝟘 (U 0) (Unit s 0) Empty (var x0)) t

opaque

  -- A type of booleans.

  Bool : Term n
  Bool = Σ⟨ s ⟩ 𝟙 , Boolᵍ ▷ ℕ ▹ OK (var x0)

opaque

  -- The constructor true.

  true : Term n
  true = prod s 𝟙 (suc zero) (star s 0)

opaque

  -- The constructor false.

  false : Term n
  false = prod s 𝟙 zero (star s 0)

opaque

  -- A definition that is used in the implementation of boolrec.

  Target :
    ∀ k → Term (1+ n) → Term (k N.+ n) → Term (k N.+ n) → Term (k N.+ n)
  Target k A t u = A [ k ][ prod s 𝟙 t u ]↑

opaque

  -- An eliminator for Bool.

  boolrec : M → Term (1+ n) → Term n → Term n → Term n → Term n
  boolrec p A t u v =
    prodrec⟨ s ⟩ (Boolᵍ ∧ boolrecᵍ₁) 𝟙 p A v
      (natcase OKᵍ (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A zero (var x0)) (var x0)
            (wk[ 3 ]′ u))
         (natcase 𝟘 (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p (Target 5 A (suc zero) (var x0))
               (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ₁ $
             emptyrec boolrecᵍ₁
               (Target 5 A (suc (suc (var x1))) (var x0)) (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ₁ ⟩
       var x0)

------------------------------------------------------------------------
-- An unfolding lemma

opaque
  unfolding Target

  -- An unfolding lemma for Target.

  Target≡ : Target k A t u ≡ A [ k ][ prod s 𝟙 t u ]↑
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
    (Σ⟨ s ⟩ 𝟙 , Boolᵍ ▷ ℕ ▹ OK (var x0)) [ σ ]    ≡⟨⟩
    Σ⟨ s ⟩ 𝟙 , Boolᵍ ▷ ℕ ▹ (OK (var x0) [ σ ⇑ ])  ≡⟨ cong (Σ⟨_⟩_,_▷_▹_ _ _ _ _) OK-[] ⟩
    Σ⟨ s ⟩ 𝟙 , Boolᵍ ▷ ℕ ▹ OK (var x0)            ∎

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
    prodrec⟨ s ⟩ (Boolᵍ ∧ boolrecᵍ₁) 𝟙 p A v
      (natcase OKᵍ (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹ Target 4 A (var x1) (var x0))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A zero (var x0)) (var x0)
            (wk[ 3 ]′ u))
         (natcase 𝟘 (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
             Target 5 A (suc (var x1)) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p (Target 5 A (suc zero) (var x0))
               (var x0) (wk[ 4 ]′ t))
            (lam boolrecᵍ₁ $
             emptyrec boolrecᵍ₁
               (Target 5 A (suc (suc (var x1))) (var x0)) (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ₁ ⟩
       var x0)
      [ σ ]                                                              ≡⟨ trans prodrec⟨⟩-[] $
                                                                            cong (prodrec⟨ _ ⟩ _ _ _ _ _) $
                                                                            cong (flip _∘⟨ boolrecᵍ₁ ⟩_ _) $
                                                                            trans natcase-[] $
                                                                            cong₄ (natcase _ _)
                                                                              (cong₂ (Π_,_▷_▹_ _ _) OK-[] refl)
                                                                              (cong (lam _) unitrec⟨⟩-[])
                                                                              (trans natcase-[] $
                                                                               cong₄ (natcase _ _)
                                                                                 (cong₂ (Π_,_▷_▹_ _ _) OK-[] refl)
                                                                                 (cong (lam _) unitrec⟨⟩-[]) refl refl)
                                                                              refl ⟩
    prodrec⟨ s ⟩ (Boolᵍ ∧ boolrecᵍ₁) 𝟙 p (A [ σ ⇑ ]) (v [ σ ])
      (natcase OKᵍ (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹
          (Target 4 A (var x1) (var x0) [ σ ⇑[ 4 ] ]))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 4 A zero (var x0) [ σ ⇑[ 4 ] ])
            (var x0) (wk[ 3 ]′ u [ σ ⇑[ 3 ] ]))
         (natcase 𝟘 (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
             (Target 5 A (suc (var x1)) (var x0) [ σ ⇑[ 5 ] ]))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p
               (Target 5 A (suc zero) (var x0) [ σ ⇑[ 5 ] ]) (var x0)
               (wk[ 4 ]′ t [ σ ⇑[ 4 ] ]))
            (lam boolrecᵍ₁ $
             emptyrec boolrecᵍ₁
               (Target 5 A (suc (suc (var x1))) (var x0) [ σ ⇑[ 5 ] ])
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ₁ ⟩
       var x0)                                                           ≡⟨ cong (prodrec⟨ _ ⟩ _ _ _ _ _) $
                                                                            cong (flip (_∘⟨ boolrecᵍ₁ ⟩_) _) $
                                                                            cong₄ (natcase _ _)
                                                                              (cong (Π_,_▷_▹_ _ _ _) Target-[⇑])
                                                                              (cong (lam _) $
                                                                               cong₃ (unitrec⟨ _ ⟩ _ _ _)
                                                                                 Target-[⇑] refl (wk[]′-[⇑] u))
                                                                              (cong₄ (natcase _ _)
                                                                                 (cong (Π_,_▷_▹_ _ _ _) Target-[⇑])
                                                                                 (cong (lam _) $
                                                                                  cong₃ (unitrec⟨ _ ⟩ _ _ _)
                                                                                    Target-[⇑] refl (wk[]′-[⇑] t))
                                                                                 (cong (lam _) $
                                                                                  cong₂ (emptyrec _) Target-[⇑] refl)
                                                                                 refl)
                                                                              refl ⟩
    prodrec⟨ s ⟩ (Boolᵍ ∧ boolrecᵍ₁) 𝟙 p (A [ σ ⇑ ]) (v [ σ ])
      (natcase OKᵍ (boolrecᵍ₂ + p)
         (Π boolrecᵍ₁ , p ▷ OK (var x0) ▹
          Target 4 (A [ σ ⇑ ]) (var x1) (var x0))
         (lam boolrecᵍ₁ $
          unitrec⟨ s ⟩ 0 𝟙 p (Target 4 (A [ σ ⇑ ]) zero (var x0))
            (var x0) (wk[ 3 ]′ (u [ σ ])))
         (natcase 𝟘 (boolrecᵍ₂ + p)
            (Π boolrecᵍ₁ , p ▷ OK (suc (var x0)) ▹
             Target 5 (A [ σ ⇑ ]) (suc (var x1)) (var x0))
            (lam boolrecᵍ₁ $
             unitrec⟨ s ⟩ 0 𝟙 p
               (Target 5 (A [ σ ⇑ ]) (suc zero) (var x0)) (var x0)
               (wk[ 4 ]′ (t [ σ ])))
            (lam boolrecᵍ₁ $
             emptyrec boolrecᵍ₁
               (Target 5 (A [ σ ⇑ ]) (suc (suc (var x1))) (var x0))
               (var x0))
            (var x0))
         (var x1) ∘⟨ boolrecᵍ₁ ⟩
       var x0)                                                           ∎

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
    wk[ k ]′ (A [ prod s 𝟙 t u ]₀)
  Target-wk[]′ {k} {A} {t} {u} =
    A [ k ][ prod s 𝟙 (wk[ k ]′ t) (wk[ k ]′ u) ]↑  ≡⟨⟩
    A [ k ][ wk[ k ]′ (prod s 𝟙 t u) ]↑             ≡⟨ [][wk[]′]↑ A ⟩
    wk[ k ]′ (A [ prod s 𝟙 t u ]₀)                  ∎

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
