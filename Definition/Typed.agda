{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation

module Definition.Typed {ℓ ℓ′} (M′ : Setoid ℓ ℓ′) where

open Setoid M′ using (_≈_) renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)

open import Tools.Fin
open import Tools.Nat
open import Tools.Product hiding (_,_)
import Tools.PropositionalEquality as PE


infixl 30 _∙_
infix 30 Πⱼ_▹_
infix 30 Σⱼ_▹_
infix 30 ⟦_⟧ⱼ_▹_

private
  variable
    n k : Nat
    Γ  : Con Term n
    A B C F H : Term n
    a b f g t u v : Term n
    G E : Term (1+ n)
    x : Fin n
    p q r p′ q′ r′ p₁ p₂ q₁ q₂ : M
    m : SigmaMode

-- Well-typed variables
data _∷_∈_  : {n : Nat} (x : Fin n) (A : Term n) (Γ : Con Term n) → Set ℓ where
  here  :                       x0 ∷ wk1 A ∈ (Γ ∙ A)
  there : (h : x ∷ A ∈ Γ) → (x +1) ∷ wk1 A ∈ (Γ ∙ B)


mutual
  -- Well-formed context
  data ⊢_ : Con Term n → Set (ℓ ⊔ ℓ′) where
    ε   : ⊢ ε
    _∙_ : ⊢ Γ
        → Γ ⊢ A
        → ⊢ Γ ∙ A

  -- Well-formed type
  data _⊢_ (Γ : Con Term n) : Term n → Set (ℓ ⊔ ℓ′) where
    Uⱼ     : ⊢ Γ → Γ ⊢ U
    ℕⱼ     : ⊢ Γ → Γ ⊢ ℕ
    Emptyⱼ : ⊢ Γ → Γ ⊢ Empty
    Unitⱼ  : ⊢ Γ → Γ ⊢ Unit
    Πⱼ_▹_  : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → Γ     ⊢ Π p , q ▷ F ▹ G
    Σⱼ_▹_  : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → Γ     ⊢ Σ⟨ m ⟩ q ▷ F ▹ G
    univ   : Γ ⊢ A ∷ U
           → Γ ⊢ A

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con Term n) : Term n → Term n → Set (ℓ ⊔ ℓ′) where
    Πⱼ_▹_     : ∀ {F G}
              → Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → Γ     ⊢ Π p , q ▷ F ▹ G ∷ U
    Σⱼ_▹_     : ∀ {F G}
              → Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → Γ     ⊢ Σ⟨ m ⟩ q ▷ F ▹ G ∷ U
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
              → Γ ⊢ g ∘⟨ p ⟩ a ∷ G [ a ]

    prodⱼ     : ∀ {F G t u}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ F
              → Γ ⊢ u ∷ G [ t ]
              → Γ ⊢ prod m t u ∷ Σ⟨ m ⟩ q ▷ F ▹ G
    fstⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σₚ q ▷ F ▹ G
              → Γ ⊢ fst t ∷ F
    sndⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σₚ q ▷ F ▹ G
              → Γ ⊢ snd t ∷ G [ fst t ]
    prodrecⱼ  : ∀ {t u F G A}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ∙ (Σᵣ q ▷ F ▹ G) ⊢ A
              → Γ ⊢ t ∷ Σᵣ q ▷ F ▹ G
              → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑²
              → Γ ⊢ prodrec p q′ A t u ∷ A [ t ]
    zeroⱼ     : ⊢ Γ
              → Γ ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {n}
              → Γ ⊢     n ∷ ℕ
              → Γ ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {G s z n}
              → Γ ∙ ℕ     ⊢ G
              → Γ         ⊢ z ∷ G [ zero ]
              → Γ ∙ ℕ ∙ G ⊢ s ∷ wk1 (G [ suc (var x0) ]↑)
              → Γ         ⊢ n ∷ ℕ
              → Γ         ⊢ natrec p q r G z s n ∷ G [ n ]

    Emptyrecⱼ : ∀ {A e}
              → Γ ⊢ A → Γ ⊢ e ∷ Empty → Γ ⊢ Emptyrec p A e ∷ A

    starⱼ     : ⊢ Γ → Γ ⊢ star ∷ Unit

    conv      : ∀ {t A B}
              → Γ ⊢ t ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t ∷ B

  -- Type equality
  data _⊢_≡_ (Γ : Con Term n) : Term n → Term n → Set (ℓ ⊔ ℓ′) where
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
           → p ≈ p′
           → q ≈ q′
           → Γ     ⊢ Π p , q ▷ F ▹ G ≡ Π p′ , q′ ▷ H ▹ E
    Σ-cong : ∀ {F H G E}
           → Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → q ≈ q′
           → Γ     ⊢ Σ⟨ m ⟩ q ▷ F ▹ G ≡ Σ⟨ m ⟩ q′ ▷ H ▹ E

  -- Term equality
  data _⊢_≡_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set (ℓ ⊔ ℓ′) where
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
                  → p ≈ p′
                  → q ≈ q′
                  → Γ     ⊢ Π p , q ▷ F ▹ G ≡ Π p′ , q′ ▷ H ▹ E ∷ U
    Σ-cong        : ∀ {E F G H}
                  → Γ     ⊢ F
                  → Γ     ⊢ F ≡ H       ∷ U
                  → Γ ∙ F ⊢ G ≡ E       ∷ U
                  → q ≈ q′
                  → Γ     ⊢ Σ⟨ m ⟩ q ▷ F ▹ G ≡ Σ⟨ m ⟩ q′ ▷ H ▹ E ∷ U
    app-cong      : ∀ {a b f g F G}
                  → Γ ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
                  → Γ ⊢ a ≡ b ∷ F
                  → p ≈ p₁
                  → p ≈ p₂
                  → Γ ⊢ f ∘⟨ p₁ ⟩ a ≡ g ∘⟨ p₂ ⟩ b ∷ G [ a ]
    β-red         : ∀ {a t F G}
                  → Γ     ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ F ⊢ t ∷ G
                  → Γ     ⊢ a ∷ F
                  → p ≈ p′
                  → Γ     ⊢ lam p t ∘⟨ p′ ⟩ a ≡ t [ a ] ∷ G [ a ]
    η-eq          : ∀ {f g F G}
                  → Γ     ⊢ F
                  → Γ     ⊢ f ∷ Π p , q ▷ F ▹ G
                  → Γ     ⊢ g ∷ Π p , q ▷ F ▹ G
                  → (∀ {p₁ p₂}
                     → p ≈ p₁
                     → p ≈ p₂
                     → Γ ∙ F ⊢ wk1 f ∘⟨ p₁ ⟩ var x0 ≡ wk1 g ∘⟨ p₂ ⟩ var x0 ∷ G)
                  → Γ     ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
    fst-cong      : ∀ {t t' F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t' ∷ Σₚ q ▷ F ▹ G
                  → Γ ⊢ fst t ≡ fst t' ∷ F
    snd-cong      : ∀ {t t' F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t' ∷ Σₚ q ▷ F ▹ G
                  → Γ ⊢ snd t ≡ snd t' ∷ G [ fst t ]
    prod-cong     : ∀ {F G t t′ u u′}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ F
                  → Γ ⊢ u ≡ u′ ∷ G [ t ]
                  → Γ ⊢ prod m t u ≡ prod m t′ u′ ∷ Σ⟨ m ⟩ q ▷ F ▹ G
    Σ-β₁          : ∀ {F G t u}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]
                  → Γ ⊢ prodₚ t u ∷ Σₚ q ▷ F ▹ G
                  → Γ ⊢ fst (prodₚ t u) ≡ t ∷ F
    Σ-β₂          : ∀ {F G t u}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]
                  → Γ ⊢ prodₚ t u ∷ Σₚ q ▷ F ▹ G
                  → Γ ⊢ snd (prodₚ t u) ≡ u ∷ G [ fst (prodₚ t u) ]
    Σ-η           : ∀ {t u F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ Σₚ q ▷ F ▹ G
                  → Γ ⊢ u ∷ Σₚ q ▷ F ▹ G
                  → Γ ⊢ fst t ≡ fst u ∷ F
                  → Γ ⊢ snd t ≡ snd u ∷ G [ fst t ]
                  → Γ ⊢ t ≡ u ∷ Σₚ q ▷ F ▹ G
    prodrec-cong  : ∀ {t t′ u u′ F G A A′}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ (Σᵣ q ▷ F ▹ G) ⊢ A ≡ A′
                  → Γ ⊢ t ≡ t′ ∷ Σᵣ q ▷ F ▹ G
                  → Γ ∙ F ∙ G ⊢ u ≡ u′ ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑²
                  → p ≈ p′
                  → q₁ ≈ q₂
                  → Γ ⊢ prodrec p q₁ A t u ≡ prodrec p′ q₂ A′ t′ u′ ∷ A [ t ]
    prodrec-β     : ∀ {t t′ u F G A}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ (Σᵣ q ▷ F ▹ G) ⊢ A
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ t′ ∷ G [ t ]
                  → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑²
                  → Γ ⊢ (prodrec p q′ A (prodᵣ t t′) u) ≡
                        u [ t , t′ ] ∷ A [ prodᵣ t t′ ]
    suc-cong      : ∀ {m n}
                  → Γ ⊢ m ≡ n ∷ ℕ
                  → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {z z′ s s′ n n′ F F′}
                  → Γ ∙ ℕ     ⊢ F
                  → Γ ∙ ℕ     ⊢ F ≡ F′
                  → Γ         ⊢ z ≡ z′ ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ s ≡ s′ ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ         ⊢ n ≡ n′ ∷ ℕ
                  → p ≈ p′
                  → q ≈ q′
                  → r ≈ r′
                  → Γ         ⊢ natrec p q r F z s n ≡ natrec p′ q′ r′ F′ z′ s′ n′ ∷ F [ n ]
    natrec-zero   : ∀ {z s F}
                  → Γ ∙ ℕ ⊢ F
                  → Γ     ⊢ z ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ     ⊢ natrec p q r F z s zero ≡ z ∷ F [ zero ]
    natrec-suc    : ∀ {n z s F}
                  → Γ     ⊢ n ∷ ℕ
                  → Γ ∙ ℕ ⊢ F
                  → Γ     ⊢ z ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ     ⊢ natrec p q r F z s (suc n) ≡ s [ n , natrec p q r F z s n ]
                                        ∷ F [ suc n ]
    Emptyrec-cong : ∀ {A A' e e'}
                  → Γ ⊢ A ≡ A'
                  → Γ ⊢ e ≡ e' ∷ Empty
                  → p ≈ p′
                  → Γ ⊢ Emptyrec p A e ≡ Emptyrec p′ A' e' ∷ A
    η-unit        : ∀ {e e'}
                  → Γ ⊢ e ∷ Unit
                  → Γ ⊢ e' ∷ Unit
                  → Γ ⊢ e ≡ e' ∷ Unit


-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set (ℓ ⊔ ℓ′) where
  conv           : ∀ {A B t u}
                 → Γ ⊢ t ⇒ u ∷ A
                 → Γ ⊢ A ≡ B
                 → Γ ⊢ t ⇒ u ∷ B
  app-subst      : ∀ {A B t u a}
                 → Γ ⊢ t ⇒ u ∷ Π p , q ▷ A ▹ B
                 → Γ ⊢ a ∷ A
                 → Γ ⊢ t ∘⟨ p ⟩ a ⇒ u ∘⟨ p ⟩ a ∷ B [ a ]
  β-red          : ∀ {A B a t}
                 → Γ     ⊢ A
                 → Γ ∙ A ⊢ B
                 → Γ ∙ A ⊢ t ∷ B
                 → Γ     ⊢ a ∷ A
                 → p ≈ p′
                 → Γ     ⊢ lam p t ∘⟨ p′ ⟩ a ⇒ t [ a ] ∷ B [ a ]
  fst-subst      : ∀ {t t' F G}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ t' ∷ Σₚ q ▷ F ▹ G
                 → Γ ⊢ fst t ⇒ fst t' ∷ F
  snd-subst      : ∀ {t t' F G}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ t' ∷ Σₚ q ▷ F ▹ G
                 → Γ ⊢ snd t ⇒ snd t' ∷ G [ fst t ]
  Σ-β₁           : ∀ {F G t u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]
                 → Γ ⊢ (prodₚ t u) ∷ Σₚ q ▷ F ▹ G
                 → Γ ⊢ fst (prodₚ t u) ⇒ t ∷ F
  Σ-β₂           : ∀ {F G t u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]
                 → Γ ⊢ (prodₚ t u) ∷ Σₚ q ▷ F ▹ G
                 -- TODO(WN): Prove that 𝔍 ∷ G [ t ] is admissible
                 → Γ ⊢ snd (prodₚ t u) ⇒ u ∷ G [ fst (prodₚ t u) ]
  prodrec-subst  : ∀ {t t′ F G A}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ (Σᵣ q ▷ F ▹ G) ⊢ A
                 → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑²
                 → Γ ⊢ t ⇒ t′ ∷ Σᵣ q ▷ F ▹ G
                 → Γ ⊢ prodrec p q′ A t u ⇒ prodrec p q′ A t′ u ∷ A [ t ]
  prodrec-β      : ∀ {A F G t t′ u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ (Σᵣ q ▷ F ▹ G) ⊢ A
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ t′ ∷ G [ t ]
                 → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ (var (x0 +1)) (var x0) ]↑²
                 → Γ ⊢ prodrec p q′ A (prodᵣ t t′) u ⇒
                       u [ t , t′ ] ∷ A [ prodᵣ t t′ ]
  natrec-subst   : ∀ {z s n n′ F}
                 → Γ ∙ ℕ     ⊢ F
                 → Γ         ⊢ z ∷ F [ zero ]
                 → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                 → Γ         ⊢ n ⇒ n′ ∷ ℕ
                 → Γ         ⊢ natrec p q r F z s n ⇒ natrec p q r F z s n′ ∷ F [ n ]
  natrec-zero    : ∀ {z s F}
                 → Γ ∙ ℕ     ⊢ F
                 → Γ         ⊢ z ∷ F [ zero ]
                 → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                 → Γ         ⊢ natrec p q r F z s zero ⇒ z ∷ F [ zero ]
  natrec-suc     : ∀ {n z s F}
                 → Γ         ⊢ n ∷ ℕ
                 → Γ ∙ ℕ     ⊢ F
                 → Γ         ⊢ z ∷ F [ zero ]
                 → Γ ∙ ℕ ∙ F ⊢ s ∷ wk1 (F [ suc (var x0) ]↑)
                 → Γ         ⊢ natrec p q r F z s (suc n) ⇒
                               s [ n , natrec p q r F z s n ] ∷ F [ suc n ]
  Emptyrec-subst : ∀ {n n′ A}
                 → Γ ⊢ A
                 → Γ     ⊢ n ⇒ n′ ∷ Empty
                 → Γ     ⊢ Emptyrec p A n ⇒ Emptyrec p A n′ ∷ A

-- Type reduction
data _⊢_⇒_ (Γ : Con Term n) : Term n → Term n → Set (ℓ ⊔ ℓ′) where
  univ : ∀ {A B}
       → Γ ⊢ A ⇒ B ∷ U
       → Γ ⊢ A ⇒ B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set (ℓ ⊔ ℓ′) where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con Term n) : Term n → Term n → Set (ℓ ⊔ ℓ′) where
  id  : ∀ {A}
      → Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : ∀ {A A′ B}
      → Γ ⊢ A  ⇒  A′
      → Γ ⊢ A′ ⇒* B
      → Γ ⊢ A  ⇒* B

-- Type reduction to whnf
_⊢_↘_ : (Γ : Con Term n) → Term n → Term n → Set (ℓ ⊔ ℓ′)
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set (ℓ ⊔ ℓ′)
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type equality with well-formed types
_⊢_:≡:_ : (Γ : Con Term n) → Term n → Term n → Set (ℓ ⊔ ℓ′)
Γ ⊢ A :≡: B = Γ ⊢ A × Γ ⊢ B × (Γ ⊢ A ≡ B)

-- Term equality with well-formed terms
_⊢_:≡:_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set (ℓ ⊔ ℓ′)
Γ ⊢ t :≡: u ∷ A = (Γ ⊢ t ∷ A) × (Γ ⊢ u ∷ A) × (Γ ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_ (Γ : Con Term n) (A B : Term n) : Set (ℓ ⊔ ℓ′) where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term n) (t u A : Term n) : Set (ℓ ⊔ ℓ′) where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A
    ⊢u : Γ ⊢ u ∷ A
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ (Δ : Con Term k) : (σ : Subst k n) (Γ : Con Term n) → Set (ℓ ⊔ ℓ′) where
  id  : ∀ {σ} → Δ ⊢ˢ σ ∷ ε
  _,_ : ∀ {A σ}
      → Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢  head σ ∷ subst (tail σ) A
      → Δ ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ (Δ : Con Term k) : (σ σ′ : Subst k n) (Γ : Con Term n) → Set (ℓ ⊔ ℓ′) where
  id  : ∀ {σ σ′} → Δ ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : ∀ {A σ σ′}
      → Δ ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ ⊢  head σ ≡ head σ′ ∷ subst (tail σ) A
      → Δ ⊢ˢ      σ ≡ σ′      ∷ Γ ∙ A

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.

⟦_⟧ⱼ_▹_ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F
     → Γ ∙ F ⊢ G
     → Γ     ⊢ ⟦ W ⟧ F ▹ G
⟦ BΠ p q ⟧ⱼ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ m q ⟧ⱼ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

⟦_⟧ⱼᵤ_▹_ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F ∷ U
     → Γ ∙ F ⊢ G ∷ U
     → Γ     ⊢ ⟦ W ⟧ F ▹ G ∷ U
⟦ BΠ p q ⟧ⱼᵤ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ m q ⟧ⱼᵤ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G
