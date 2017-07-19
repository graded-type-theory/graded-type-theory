{-# OPTIONS --without-K #-}

module Definition.Conversion where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Nat
import Tools.PropositionalEquality as PE


infix 10 _⊢_~_↑_
infix 10 _⊢_~_↓_
infix 10 _⊢_[conv↑]_
infix 10 _⊢_[conv↓]_
infix 10 _⊢_[conv↑]_∷_
infix 10 _⊢_[conv↓]_∷_

mutual
  data _⊢_~_↑_ (Γ : Con Term) : (k l A : Term) → Set where
    var       : ∀ {x y A}
              → Γ ⊢ var x ∷ A
              → x PE.≡ y
              → Γ ⊢ var x ~ var y ↑ A
    app       : ∀ {k l t v F G}
              → Γ ⊢ k ~ l ↓ Πₑ F ▹ G
              → Γ ⊢ t [conv↑] v ∷ F
              → Γ ⊢ k ∘ₑ t ~ l ∘ₑ v ↑ G [ t ]
    natrec    : ∀ {k l h g a₀ b₀ F G}
              → Γ ∙ ℕₑ ⊢ F [conv↑] G
              → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zeroₑ ]
              → Γ ⊢ h [conv↑] g ∷ Πₑ ℕₑ ▹ (F ▹▹ F [ sucₑ (var zero) ]↑)
              → Γ ⊢ k ~ l ↓ ℕₑ
              → Γ ⊢ natrecₑ F a₀ h k ~ natrecₑ G b₀ g l ↑ F [ k ]

  record _⊢_~_↓_ (Γ : Con Term) (k l B : Term) : Set where
    inductive
    constructor [~]
    field
      A     : Term
      D     : Γ ⊢ A ⇒* B
      whnfB : Whnf B
      k~l   : Γ ⊢ k ~ l ↑ A

  record _⊢_[conv↑]_ (Γ : Con Term) (A B : Term) : Set where
    inductive
    constructor [↑]
    field
      A' B'  : Term
      D      : Γ ⊢ A ⇒* A'
      D'     : Γ ⊢ B ⇒* B'
      whnfA' : Whnf A'
      whnfB' : Whnf B'
      A'<>B' : Γ ⊢ A' [conv↓] B'

  data _⊢_[conv↓]_ (Γ : Con Term) : (A B : Term) → Set where
    U-refl    : ⊢ Γ → Γ ⊢ Uₑ [conv↓] Uₑ
    ℕ-refl    : ⊢ Γ → Γ ⊢ ℕₑ [conv↓] ℕₑ
    ne        : ∀ {K L}
              → Γ ⊢ K ~ L ↓ Uₑ
              → Γ ⊢ K [conv↓] L
    Π-cong    : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F [conv↑] H
              → Γ ∙ F ⊢ G [conv↑] E
              → Γ ⊢ Πₑ F ▹ G [conv↓] Πₑ H ▹ E

  record _⊢_[conv↑]_∷_ (Γ : Con Term) (t u A : Term) : Set where
    inductive
    constructor [↑]ₜ
    field
      B t' u' : Term
      D       : Γ ⊢ A ⇒* B
      d       : Γ ⊢ t ⇒* t' ∷ B
      d'      : Γ ⊢ u ⇒* u' ∷ B
      whnfB   : Whnf B
      whnft'  : Whnf t'
      whnfu'  : Whnf u'
      t<>u    : Γ ⊢ t' [conv↓] u' ∷ B

  data _⊢_[conv↓]_∷_ (Γ : Con Term) : (t u A : Term) → Set where
    ℕ-ins     : ∀ {k l}
              → Γ ⊢ k ~ l ↓ ℕₑ
              → Γ ⊢ k [conv↓] l ∷ ℕₑ
    ne-ins    : ∀ {k l M N}
              → Γ ⊢ k ∷ N
              → Γ ⊢ l ∷ N
              → Neutral N
              → Γ ⊢ k ~ l ↓ M
              → Γ ⊢ k [conv↓] l ∷ N
    univ      : ∀ {A B}
              → Γ ⊢ A ∷ Uₑ
              → Γ ⊢ B ∷ Uₑ
              → Γ ⊢ A [conv↓] B
              → Γ ⊢ A [conv↓] B ∷ Uₑ
    zero-refl : ⊢ Γ → Γ ⊢ zeroₑ [conv↓] zeroₑ ∷ ℕₑ
    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv↑] n ∷ ℕₑ
              → Γ ⊢ sucₑ m [conv↓] sucₑ n ∷ ℕₑ
    fun-ext   : ∀ {f g F G}
              → Γ ⊢ F
              → Γ ⊢ f ∷ Πₑ F ▹ G
              → Γ ⊢ g ∷ Πₑ F ▹ G
              → Whnf f
              → Whnf g
              → Γ ∙ F ⊢ wk1 f ∘ₑ var zero [conv↑] wk1 g ∘ₑ var zero ∷ G
              → Γ ⊢ f [conv↓] g ∷ Πₑ F ▹ G
