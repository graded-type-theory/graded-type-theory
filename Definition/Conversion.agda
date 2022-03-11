-- Algorithmic equality.

{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Tools.Level

module Definition.Conversion {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M′

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


infix 10 _⊢_~_↑_
infix 10 _⊢_~_↓_
infix 10 _⊢_[conv↑]_
infix 10 _⊢_[conv↓]_
infix 10 _⊢_[conv↑]_∷_
infix 10 _⊢_[conv↓]_∷_

private
  variable
    n : Nat
    Γ : Con Term n
    C F H : Term n
    a₀ b₀ g h k l t u v : Term n
    G E : Term (1+ n)
    x y : Fin n
    p p′ p₁ p₂ q q′ r r′ : M

mutual
  -- Neutral equality.
  data _⊢_~_↑_ (Γ : Con Term n) : (k l A : Term n) → Set (a ⊔ ℓ) where

    var-refl      : Γ ⊢ var x ∷ C
                  → x PE.≡ y
                  → Γ ⊢ var x ~ var y ↑ C

    app-cong      : Γ ⊢ k ~ l ↓ Π p , q ▷ F ▹ G
                  → Γ ⊢ t [conv↑] v ∷ F
                  → p ≈ p₁
                  → p ≈ p₂
                  → Γ ⊢ k ∘ p₁ ▷ t ~ l ∘ p₂ ▷ v ↑ G [ t ]

    fst-cong      : Γ ⊢ k ~ l ↓ Σ p ▷ F ▹ G
                  → Γ ⊢ fst k ~ fst l ↑ F

    snd-cong      : Γ ⊢ k ~ l ↓ Σ p ▷ F ▹ G
                  → Γ ⊢ snd k ~ snd l ↑ G [ fst k ]

    natrec-cong   : Γ ∙ ℕ ⊢ F [conv↑] G
                  → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ h [conv↑] g ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ ⊢ k ~ l ↓ ℕ
                  → p ≈ p′
                  → r ≈ r′
                  → Γ ⊢ natrec p r F a₀ h k ~ natrec p′ r′ G b₀ g l ↑ F [ k ]

    Emptyrec-cong : Γ ⊢ F [conv↑] H
                  → Γ ⊢ k ~ l ↓ Empty
                  → p ≈ p′
                  → Γ ⊢ Emptyrec p F k ~ Emptyrec p′ H l ↑ F

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓_ (Γ : Con Term n) (k l B : Term n) : Set (a ⊔ ℓ) where
    inductive
    constructor [~]
    field
      A     : Term n
      D     : Γ ⊢ A ⇒* B
      whnfB : Whnf B
      k~l   : Γ ⊢ k ~ l ↑ A

  -- Type equality.
  record _⊢_[conv↑]_ (Γ : Con Term n) (A B : Term n) : Set (a ⊔ ℓ) where
    inductive
    constructor [↑]
    field
      A′ B′  : Term n
      D      : Γ ⊢ A ⇒* A′
      D′     : Γ ⊢ B ⇒* B′
      whnfA′ : Whnf A′
      whnfB′ : Whnf B′
      A′<>B′ : Γ ⊢ A′ [conv↓] B′

  -- Type equality with types in WHNF.
  data _⊢_[conv↓]_ (Γ : Con Term n) : (A B : Term n) → Set (a ⊔ ℓ) where

    U-refl     : ⊢ Γ → Γ ⊢ U [conv↓] U

    ℕ-refl     : ⊢ Γ → Γ ⊢ ℕ [conv↓] ℕ

    Empty-refl : ⊢ Γ → Γ ⊢ Empty [conv↓] Empty

    Unit-refl  : ⊢ Γ → Γ ⊢ Unit [conv↓] Unit

    ne         : ∀ {K L}
               → Γ ⊢ K ~ L ↓ U
               → Γ ⊢ K [conv↓] L

    Π-cong     : ∀ {F G H E}
               → Γ ⊢ F
               → Γ ⊢ F [conv↑] H
               → Γ ∙ F ⊢ G [conv↑] E
               → p ≈ p′
               → q ≈ q′
               → Γ ⊢ Π p , q ▷ F ▹ G [conv↓] Π p′ , q′ ▷ H ▹ E

    Σ-cong     : ∀ {F G H E}
               → Γ ⊢ F
               → Γ ⊢ F [conv↑] H
               → Γ ∙ F ⊢ G [conv↑] E
               → q ≈ q′
               → Γ ⊢ Σ q ▷ F ▹ G [conv↓] Σ q′ ▷ H ▹ E

  -- Term equality.
  record _⊢_[conv↑]_∷_ (Γ : Con Term n) (t u A : Term n) : Set (a ⊔ ℓ) where
    inductive
    constructor [↑]ₜ
    field
      B t′ u′ : Term n
      D       : Γ ⊢ A ⇒* B
      d       : Γ ⊢ t ⇒* t′ ∷ B
      d′      : Γ ⊢ u ⇒* u′ ∷ B
      whnfB   : Whnf B
      whnft′  : Whnf t′
      whnfu′  : Whnf u′
      t<>u    : Γ ⊢ t′ [conv↓] u′ ∷ B

  -- Term equality with types and terms in WHNF.
  data _⊢_[conv↓]_∷_ (Γ : Con Term n) : (t u A : Term n) → Set (a ⊔ ℓ) where

    ℕ-ins     : Γ ⊢ k ~ l ↓ ℕ
              → Γ ⊢ k [conv↓] l ∷ ℕ

    Empty-ins : Γ ⊢ k ~ l ↓ Empty
              → Γ ⊢ k [conv↓] l ∷ Empty

    Unit-ins  : Γ ⊢ k ~ l ↓ Unit
              → Γ ⊢ k [conv↓] l ∷ Unit

    ne-ins    : ∀ {k l M N}
              → Γ ⊢ k ∷ N
              → Γ ⊢ l ∷ N
              → Neutral N
              → Γ ⊢ k ~ l ↓ M
              → Γ ⊢ k [conv↓] l ∷ N

    univ      : ∀ {A B}
              → Γ ⊢ A ∷ U
              → Γ ⊢ B ∷ U
              → Γ ⊢ A [conv↓] B
              → Γ ⊢ A [conv↓] B ∷ U

    zero-refl : ⊢ Γ → Γ ⊢ zero [conv↓] zero ∷ ℕ

    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv↑] n ∷ ℕ
              → Γ ⊢ suc m [conv↓] suc n ∷ ℕ

    η-eq      : ∀ {f g F G}
              → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
              → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
              → Function f
              → Function g
              → (∀ {p₁ p₂}
                 → p ≈ p₁
                 → p ≈ p₂
                 → Γ ∙ F ⊢ wk1 f ∘ p₁ ▷ var x0 [conv↑] wk1 g ∘ p₂ ▷ var x0 ∷ G)
              → Γ ⊢ f [conv↓] g ∷ Π p , q ▷ F ▹ G

    Σ-η       : Γ ⊢ k ∷ Σ p ▷ F ▹ G
              → Γ ⊢ l ∷ Σ p ▷ F ▹ G
              → Product k
              → Product l
              → Γ ⊢ fst k [conv↑] fst l ∷ F
              → Γ ⊢ snd k [conv↑] snd l ∷ G [ fst k ]
              → Γ ⊢ k [conv↓] l ∷ Σ p ▷ F ▹ G

    η-unit    : ∀ {k l}
              → Γ ⊢ k ∷ Unit
              → Γ ⊢ l ∷ Unit
              → Whnf k
              → Whnf l
              → Γ ⊢ k [conv↓] l ∷ Unit

star-refl : ⊢ Γ → Γ ⊢ star [conv↓] star ∷ Unit
star-refl ⊢Γ = η-unit (starⱼ ⊢Γ) (starⱼ ⊢Γ) starₙ starₙ
