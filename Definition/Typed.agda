{-# OPTIONS --without-K --safe  #-}

module Definition.Typed where

open import Definition.Untyped hiding (_∷_)
open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Usage

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

infixl 30 _∙_
infix 30 Πⱼ_▹_
infix 30 Σⱼ_▹_
infix 30 ⟦_⟧ⱼ_▹_


private
  variable
    n m : Nat
    M : Set
    𝕄 : Modality M
    Γ  : Con (Term M) n
    A B C F H : Term M n
    a b f g t u v : Term M n
    G E : Term M (1+ n)
    x : Fin n
    p q r : M
    γ δ η θ : Conₘ 𝕄 n
    γ′ γ″ δ′ η′ θ′ : Conₘ 𝕄 n


-- Well-typed variables
data _∷_∈_ : (x : Fin n) (A : Term M n) (Γ : Con (Term M) n) → Set₁ where
  here  :                       x0 ∷ wk1 A ∈ (Γ ∙ A)
  there : (h : x ∷ A ∈ Γ) → (x +1) ∷ wk1 A ∈ (Γ ∙ B)


mutual
  -- Well-formed context
  data ⊢_ {M : Set} : Con (Term M) n → Set₁ where
    ε   : ⊢ ε
    _∙_ : ⊢ Γ
        → Γ ⊢ A
        → ⊢ Γ ∙ A

  -- Well-formed type
  data _⊢_ (Γ : Con (Term M) n) : Term M n → Set₁ where
    Uⱼ     : ⊢ Γ → Γ ⊢ U
    ℕⱼ     : ⊢ Γ → Γ ⊢ ℕ
    Emptyⱼ : ⊢ Γ → Γ ⊢ Empty
    Unitⱼ  : ⊢ Γ → Γ ⊢ Unit
    Πⱼ_▹_  : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → Γ     ⊢ Π p , q ▷ F ▹ G
    Σⱼ_▹_  : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → Γ     ⊢ Σ p ▷ F ▹ G
    univ   : Γ ⊢ A ∷ U
           → Γ ⊢ A

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con (Term M) n) : Term M n → Term M n → Set₁ where
    Πⱼ_▹_     : ∀ {F G}
              → Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → Γ     ⊢ Π p , q ▷ F ▹ G ∷ U
    Σⱼ_▹_     : ∀ {F G}
              → Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → Γ     ⊢ Σ p ▷ F ▹ G ∷ U
    ℕⱼ        : ⊢ Γ → Γ ⊢ ℕ ∷ U
    Emptyⱼ    : ⊢ Γ → Γ ⊢ Empty ∷ U
    Unitⱼ     : ⊢ Γ → Γ ⊢ Unit ∷ U

    var       : ∀ {A x}
              → ⊢ Γ
              → x ∷ A ∈ Γ
              → Γ ⊢ var x ∷ A

    lamⱼ      : ∀ {F G t}
              → Γ     ⊢ F
              → Γ ∙ F ⊢ t ∷ G
              → Γ     ⊢ lam p t ∷ Π p , q ▷ F ▹ G
    _∘ⱼ_      : ∀ {g a F G}
              → Γ ⊢     g ∷ Π p , q ▷ F ▹ G
              → Γ ⊢     a ∷ F
              → Γ ⊢ p ▷ g ∘ a ∷ G [ a ]

    prodⱼ     : ∀ {F G t u}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ F
              → Γ ⊢ u ∷ G [ t ]
              → Γ ⊢ prod t u ∷ Σ p ▷ F ▹ G
    fstⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σ p ▷ F ▹ G
              → Γ ⊢ fst t ∷ F
    sndⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σ p ▷ F ▹ G
              → Γ ⊢ snd t ∷ G [ fst t ]
    prodrecⱼ  : ∀ {t u F G A}
              → Γ ⊢ t ∷ Σ p ▷ F ▹ G
              → Γ ∙ F ∙ G ⊢ u ∷ A
              → Γ ⊢ prodrec q A t u ∷ A [ snd t ][ fst t ]

    zeroⱼ     : ⊢ Γ
              → Γ ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {n}
              → Γ ⊢       n ∷ ℕ
              → Γ ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {G s z n}
              → Γ ∙ ℕ     ⊢ G
              → Γ         ⊢ z ∷ G [ zero ]
              → Γ ∙ ℕ ∙ G ⊢ s ∷ wk1 (G [ suc (var x0) ]↑)
              → Γ         ⊢ n ∷ ℕ
              → Γ         ⊢ natrec p q G z s n ∷ G [ n ]

    Emptyrecⱼ : ∀ {A e}
              → Γ ⊢ A → Γ ⊢ e ∷ Empty → Γ ⊢ Emptyrec p A e ∷ A

    starⱼ     : ⊢ Γ → Γ ⊢ star ∷ Unit

    conv      : ∀ {t A B}
              → Γ ⊢ t ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t ∷ B

  -- Type equality
  data _⊢_≡_ (Γ : Con (Term M) n) : Term M n → Term M n → Set₁ where
    univ   : ∀ {A B}
           → Γ ⊢ A ≡ B ∷ U
           → Γ ⊢ A ≡ B
    refl   : ∀ {A}
           → Γ ⊢ A
           → Γ ⊢ A ≡ A
    sym    : ∀ {A B}
           → Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ A
    trans  : ∀ {A B C}
           → Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ C
           → Γ ⊢ A ≡ C
    Π-cong : ∀ {F H G E}
           → Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → Γ     ⊢ Π p , q ▷ F ▹ G ≡ Π p , q ▷ H ▹ E
    Σ-cong : ∀ {F H G E}
           → Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → Γ     ⊢ Σ p ▷ F ▹ G ≡ Σ p ▷ H ▹ E

  -- Term equality
  data _⊢_≡_∷_ (Γ : Con (Term M) n) : Term M n → Term M n → Term M n → Set₁ where
    refl          : ∀ {t A}
                  → Γ ⊢ t ∷ A
                  → Γ ⊢ t ≡ t ∷ A
    sym           : ∀ {t u A}
                  → Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ t ∷ A
    trans         : ∀ {t u r A}
                  → Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ r ∷ A
                  → Γ ⊢ t ≡ r ∷ A
    conv          : ∀ {A B t u}
                  → Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ A ≡ B
                  → Γ ⊢ t ≡ u ∷ B
    Π-cong        : ∀ {E F G H}
                  → Γ     ⊢ F
                  → Γ     ⊢ F ≡ H       ∷ U
                  → Γ ∙ F ⊢ G ≡ E       ∷ U
                  → Γ     ⊢ Π p , q ▷ F ▹ G ≡ Π p , q ▷ H ▹ E ∷ U
    Σ-cong        : ∀ {E F G H}
                  → Γ     ⊢ F
                  → Γ     ⊢ F ≡ H       ∷ U
                  → Γ ∙ F ⊢ G ≡ E       ∷ U
                  → Γ     ⊢ Σ p ▷ F ▹ G ≡ Σ p ▷ H ▹ E ∷ U
    app-cong      : ∀ {a b f g F G}
                  → Γ ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
                  → Γ ⊢ a ≡ b ∷ F
                  → Γ ⊢ p ▷ f ∘ a ≡ p ▷ g ∘ b ∷ G [ a ]
    β-red         : ∀ {a t F G}
                  → Γ     ⊢ F
                  → Γ ∙ F ⊢ t ∷ G
                  → Γ     ⊢ a ∷ F
                  → Γ     ⊢ p ▷ (lam p t) ∘ a ≡ t [ a ] ∷ G [ a ]
    η-eq          : ∀ {f g F G}
                  → Γ     ⊢ F
                  → Γ     ⊢ f ∷ Π p , q ▷ F ▹ G
                  → Γ     ⊢ g ∷ Π p , q ▷ F ▹ G
                  → Γ ∙ F ⊢ p ▷ wk1 f ∘ var x0 ≡ p ▷ wk1 g ∘ var x0 ∷ G
                  → Γ     ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
    fst-cong      : ∀ {t t' F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t' ∷ Σ p ▷ F ▹ G
                  → Γ ⊢ fst t ≡ fst t' ∷ F
    snd-cong      : ∀ {t t' F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t' ∷ Σ p ▷ F ▹ G
                  → Γ ⊢ snd t ≡ snd t' ∷ G [ fst t ]
    Σ-β₁          : ∀ {F G t u}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]
                  → Γ ⊢ fst (prod t u) ≡ t ∷ F
    Σ-β₂          : ∀ {F G t u}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]
                  → Γ ⊢ snd (prod t u) ≡ u ∷ G [ fst (prod t u) ]
    Σ-η           : ∀ {t u F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ Σ p ▷ F ▹ G
                  → Γ ⊢ u ∷ Σ p ▷ F ▹ G
                  → Γ ⊢ fst t ≡ fst u ∷ F
                  → Γ ⊢ snd t ≡ snd u ∷ G [ fst t ]
                  → Γ ⊢ t ≡ u ∷ Σ p ▷ F ▹ G
    prodrec-cong  : ∀ {t t′ u u′ F G A}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ Σ p ▷ F ▹ G
                  → Γ ∙ F ∙ G ⊢ u ≡ u′ ∷ A
                  → Γ ⊢ (prodrec q A t u) ≡ (prodrec q A t′ u′) ∷ A [ snd t ][ fst t ]
    prodrec-β     : ∀ {t t′ u F G A}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ t′ ∷ G [ t ]
                  → Γ ∙ F ∙ G ⊢ u ∷ A
                  → Γ ⊢ (prodrec p A (prod t t′) u) ≡ u [ snd (prod t t′) ][ fst (prod t t′) ] ∷ A [ snd (prod t t′) ][ fst (prod t t′) ]
    suc-cong      : ∀ {m n}
                  → Γ ⊢ m ≡ n ∷ ℕ
                  → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {z z′ s s′ n n′ F F′}
                  → Γ ∙ ℕ     ⊢ F ≡ F′
                  → Γ         ⊢ z ≡ z′ ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ s ≡ s′ ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ         ⊢ n ≡ n′ ∷ ℕ
                  → Γ         ⊢ natrec p q F z s n ≡ natrec p q F′ z′ s′ n′ ∷ F [ n ]
    natrec-zero   : ∀ {z s F}
                  → Γ ∙ ℕ ⊢ F
                  → Γ     ⊢ z ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ     ⊢ natrec p q F z s zero ≡ z ∷ F [ zero ]
    natrec-suc    : ∀ {n z s F}
                  → Γ     ⊢ n ∷ ℕ
                  → Γ ∙ ℕ ⊢ F
                  → Γ     ⊢ z ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ     ⊢ natrec p r F z s (suc n) ≡ s [ natrec p r F z s n ][ n ]
                                        ∷ F [ suc n ]
    Emptyrec-cong : ∀ {A A' e e'}
                  → Γ ⊢ A ≡ A'
                  → Γ ⊢ e ≡ e' ∷ Empty
                  → Γ ⊢ Emptyrec p A e ≡ Emptyrec p A' e' ∷ A
    η-unit        : ∀ {e e'}
                  → Γ ⊢ e ∷ Unit
                  → Γ ⊢ e' ∷ Unit
                  → Γ ⊢ e ≡ e' ∷ Unit


_⊢_▸_ : {𝕄 : Modality M} (Γ : Con (Term M) n) (A : Term M n) (γ : Conₘ 𝕄 n) → Set₁
Γ ⊢ A ▸ γ = (Γ ⊢ A) × (γ ▸ A)

_⊢_▸_∷_◂_ : {𝕄 : Modality M} (Γ : Con (Term M) n) (γ : Conₘ 𝕄 n) (t A : Term M n) (δ : Conₘ 𝕄 n) → Set₁
Γ ⊢ γ ▸ t ∷ A ◂ δ = (Γ ⊢ t ∷ A) × (γ ▸ t) × (δ ▸ A)

-- _⊢_≡_◂_ : {𝕄 : Modality M} (Γ : Con (Term M) n) (A B : Term M n) (γ : Conₘ 𝕄 n) → Set₁
-- Γ ⊢ A ≡ B ◂ γ = (Γ ⊢ A ≡ B) × (γ ▸ A) × (γ ▸ B)
--
-- _⊢_▸_≡_∷_◂_ : {𝕄 : Modality M} (Γ : Con (Term M) n) (γ : Conₘ 𝕄 n) (t u A : Term M n) (δ : Conₘ 𝕄 n) → Set₁
-- Γ ⊢ γ ▸ t ≡ u ∷ A ◂ δ = Γ ⊢ t ≡ u ∷ A × γ ▸ t × γ ▸ u × δ ▸ A


-- Term reduction
data _⊢_⇒_∷_ (Γ : Con (Term M) n) : Term M n → Term M n → Term M n → Set₁ where
  conv           : ∀ {A B t u}
                 → Γ ⊢ t ⇒ u ∷ A
                 → Γ ⊢ A ≡ B
                 → Γ ⊢ t ⇒ u ∷ B
  app-subst      : ∀ {A B t u a}
                 → Γ ⊢ t ⇒ u ∷ Π p , q ▷ A ▹ B
                 → Γ ⊢ a ∷ A
                 → Γ ⊢ p ▷ t ∘ a ⇒ p ▷ u ∘ a ∷ B [ a ]
  β-red          : ∀ {A B a t}
                 → Γ     ⊢ A
                 → Γ ∙ A ⊢ t ∷ B
                 → Γ     ⊢ a ∷ A
                 → Γ     ⊢ p ▷ (lam p t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  fst-subst      : ∀ {t t' F G}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ t' ∷ Σ p ▷ F ▹ G
                 → Γ ⊢ fst t ⇒ fst t' ∷ F
  snd-subst      : ∀ {t t' F G}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ t' ∷ Σ p ▷ F ▹ G
                 → Γ ⊢ snd t ⇒ snd t' ∷ G [ fst t ]
  Σ-β₁           : ∀ {F G t u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]
                 → Γ ⊢ fst (prod t u) ⇒ t ∷ F
  Σ-β₂           : ∀ {F G t u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]
                 -- TODO(WN): Prove that 𝔍 ∷ G [ t ] is admissible
                 → Γ ⊢ snd (prod t u) ⇒ u ∷ G [ fst (prod t u) ]

  prodrec-subst  : ∀ {t t′ F G A}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ F ∙ G ⊢ u ∷ A
                 → Γ ⊢ t ⇒ t′ ∷ Σ p ▷ F ▹ G
                 → Γ ⊢ prodrec p A t u ⇒ prodrec p A t′ u ∷ A [ snd t ][ fst t ]
  prodrec-β      : ∀ {A F G t t′ u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ t′ ∷ G [ t ]
                 → Γ ∙ F ∙ G ⊢ u ∷ A
                 → Γ ⊢ prodrec p A (prod t t′) u ⇒ u [ snd (prod t t′) ][ fst (prod t t′) ] ∷ A [ snd (prod t t′) ][ fst (prod t t′) ]

  natrec-subst   : ∀ {z s n n′ F}
                 → Γ ∙ ℕ     ⊢ F
                 → Γ         ⊢ z ∷ F [ zero ]
                 → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                 → Γ         ⊢ n ⇒ n′ ∷ ℕ
                 → Γ         ⊢ natrec p q F z s n ⇒ natrec p q F z s n′ ∷ F [ n ]
  natrec-zero    : ∀ {z s F}
                 → Γ ∙ ℕ     ⊢ F
                 → Γ         ⊢ z ∷ F [ zero ]
                 → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                 → Γ         ⊢ natrec p q F z s zero ⇒ z ∷ F [ zero ]
  natrec-suc     : ∀ {n z s F}
                 → Γ         ⊢ n ∷ ℕ
                 → Γ ∙ ℕ     ⊢ F
                 → Γ         ⊢ z ∷ F [ zero ]
                 → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                 → Γ         ⊢ natrec p r F z s (suc n) ⇒
                               s [ natrec p r F z s n ][ n ] ∷ F [ suc n ]
  Emptyrec-subst : ∀ {n n′ A}
                 → Γ ⊢ A
                 → Γ     ⊢ n ⇒ n′ ∷ Empty
                 → Γ     ⊢ Emptyrec p A n ⇒ Emptyrec p A n′ ∷ A

-- Type reduction
data _⊢_⇒_ (Γ : Con (Term M) n) : Term M n → Term M n → Set₁ where
  univ : ∀ {A B}
       → Γ ⊢ A ⇒ B ∷ U
       → Γ ⊢ A ⇒ B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con (Term M) n) : Term M n → Term M n → Term M n → Set₁ where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con (Term M) n) : Term M n → Term M n → Set₁ where
  id  : ∀ {A}
      → Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : ∀ {A A′ B}
      → Γ ⊢ A  ⇒  A′
      → Γ ⊢ A′ ⇒* B
      → Γ ⊢ A  ⇒* B

-- Type reduction to whnf
_⊢_↘_ : (Γ : Con (Term M) n) → Term M n → Term M n → Set₁
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con (Term M) n) → Term M n → Term M n → Term M n → Set₁
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type eqaulity with well-formed types
_⊢_:≡:_ : (Γ : Con (Term M) n) → Term M n → Term M n → Set₁
Γ ⊢ A :≡: B = Γ ⊢ A × Γ ⊢ B × (Γ ⊢ A ≡ B)

-- Term equality with well-formed terms
_⊢_:≡:_∷_ : (Γ : Con (Term M) n) → Term M n → Term M n → Term M n → Set₁
Γ ⊢ t :≡: u ∷ A = (Γ ⊢ t ∷ A) × (Γ ⊢ u ∷ A) × (Γ ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_ (Γ : Con (Term M) n) (A B : Term M n) : Set₁ where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con (Term M) n) (t u A : Term M n) : Set₁ where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A
    ⊢u : Γ ⊢ u ∷ A
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ (Δ : Con (Term M) m) : (σ : Subst {M} m n) (Γ : Con (Term M) n) → Set₁ where
  id  : ∀ {σ} → Δ ⊢ˢ σ ∷ ε
  _,_ : ∀ {A σ}
      → Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢  head σ ∷ subst (tail σ) A
      → Δ ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ (Δ : Con (Term M) m) : (σ σ′ : Subst {M} m n) (Γ : Con (Term M) n) → Set₁ where
  id  : ∀ {σ σ′} → Δ ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : ∀ {A σ σ′}
      → Δ ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ ⊢  head σ ≡ head σ′ ∷ subst (tail σ) A
      → Δ ⊢ˢ      σ ≡ σ′      ∷ Γ ∙ A

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.

⟦_⟧ⱼ_▹_ : (W : BindingType M) → ∀ {F G}
     → Γ     ⊢ F
     → Γ ∙ F ⊢ G
     → Γ     ⊢ ⟦ W ⟧ F ▹ G
⟦ BΠ p q ⟧ⱼ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ p ⟧ⱼ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

⟦_⟧ⱼᵤ_▹_ : (W : BindingType M) → ∀ {F G}
     → Γ     ⊢ F ∷ U
     → Γ ∙ F ⊢ G ∷ U
     → Γ     ⊢ ⟦ W ⟧ F ▹ G ∷ U
⟦ BΠ p q ⟧ⱼᵤ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ p ⟧ⱼᵤ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G
