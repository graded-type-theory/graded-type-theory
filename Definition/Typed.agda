------------------------------------------------------------------------
-- Typing and reduction relations
------------------------------------------------------------------------

module Definition.Typed {ℓ} (M : Set ℓ) where

open import Definition.Untyped M hiding (_∷_)

open import Tools.Fin
open import Tools.Nat
open import Tools.Product hiding (_,_)
open import Tools.PropositionalEquality as PE using (_≈_)


infixl 30 _∙_
infix 30 ΠΣⱼ_▹_
infix 30 ⟦_⟧ⱼ_▹_

private
  variable
    n k : Nat
    Γ  : Con Term n
    A B C F H : Term n
    a f g t u v : Term n
    G E : Term (1+ n)
    x : Fin n
    p p′ q q′ r : M
    b : BinderMode
    m : SigmaMode

-- Well-typed variables
data _∷_∈_  : {n : Nat} (x : Fin n) (A : Term n) (Γ : Con Term n) → Set ℓ where
  here  :                       x0 ∷ wk1 A ∈ (Γ ∙ A)
  there : (h : x ∷ A ∈ Γ) → (x +1) ∷ wk1 A ∈ (Γ ∙ B)


mutual
  -- Well-formed context
  data ⊢_ : Con Term n → Set ℓ where
    ε   : ⊢ ε
    _∙_ : ⊢ Γ
        → Γ ⊢ A
        → ⊢ Γ ∙ A

  -- Well-formed type
  data _⊢_ (Γ : Con Term n) : Term n → Set ℓ where
    Uⱼ     : ⊢ Γ → Γ ⊢ U
    ℕⱼ     : ⊢ Γ → Γ ⊢ ℕ
    Emptyⱼ : ⊢ Γ → Γ ⊢ Empty
    Unitⱼ  : ⊢ Γ → Γ ⊢ Unit
    ΠΣⱼ_▹_ : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
    univ   : Γ ⊢ A ∷ U
           → Γ ⊢ A

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
    ΠΣⱼ_▹_    : ∀ {F G}
              → Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷ U
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
              → Γ ⊢ prod m p t u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
    fstⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G
              → Γ ⊢ fst p t ∷ F
    sndⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G
              → Γ ⊢ snd p t ∷ G [ fst p t ]
    prodrecⱼ  : ∀ {t u F G A}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A
              → Γ ⊢ t ∷ Σᵣ p , q ▷ F ▹ G
              → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
              → Γ ⊢ prodrec r p q′ A t u ∷ A [ t ]
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
  data _⊢_≡_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
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
    ΠΣ-cong
           : ∀ {F H G E}
           → Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡ ΠΣ⟨ b ⟩ p , q ▷ H ▹ E

  -- Term equality
  data _⊢_≡_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
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
    ΠΣ-cong       : ∀ {E F G H}
                  → Γ     ⊢ F
                  → Γ     ⊢ F ≡ H ∷ U
                  → Γ ∙ F ⊢ G ≡ E ∷ U
                  → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡
                            ΠΣ⟨ b ⟩ p , q ▷ H ▹ E ∷ U
    app-cong      : ∀ {a b f g F G}
                  → Γ ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
                  → Γ ⊢ a ≡ b ∷ F
                  → Γ ⊢ f ∘⟨ p ⟩ a ≡ g ∘⟨ p ⟩ b ∷ G [ a ]
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
                  → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 ≡ wk1 g ∘⟨ p ⟩ var x0 ∷ G
                  → Γ     ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
    fst-cong      : ∀ {t t' F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t' ∷ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ fst p t ≡ fst p t' ∷ F
    snd-cong      : ∀ {t t' F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t' ∷ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ snd p t ≡ snd p t' ∷ G [ fst p t ]
    prod-cong     : ∀ {F G t t′ u u′}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ F
                  → Γ ⊢ u ≡ u′ ∷ G [ t ]
                  → Γ ⊢ prod m p t u ≡ prod m p t′ u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
    Σ-β₁          : ∀ {F G t u}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]
                  → p ≈ p′
                  → Γ ⊢ fst p (prodₚ p′ t u) ≡ t ∷ F
    Σ-β₂          : ∀ {F G t u}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]
                  → p ≈ p′
                  → Γ ⊢ snd p (prodₚ p′ t u) ≡ u ∷ G [ fst p (prodₚ p′ t u) ]
    Σ-η           : ∀ {t u F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ u ∷ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ fst p t ≡ fst p u ∷ F
                  → Γ ⊢ snd p t ≡ snd p u ∷ G [ fst p t ]
                  → Γ ⊢ t ≡ u ∷ Σₚ p , q ▷ F ▹ G
    prodrec-cong  : ∀ {t t′ u u′ F G A A′}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A ≡ A′
                  → Γ ⊢ t ≡ t′ ∷ Σᵣ p , q ▷ F ▹ G
                  → Γ ∙ F ∙ G ⊢ u ≡ u′ ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
                  → Γ ⊢ prodrec r p q′ A t u ≡ prodrec r p q′ A′ t′ u′ ∷ A [ t ]
    prodrec-β     : ∀ {t t′ u F G A}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ t′ ∷ G [ t ]
                  → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
                  → p ≈ p′
                  → Γ ⊢ prodrec r p q′ A (prodᵣ p′ t t′) u ≡
                        u [ t , t′ ] ∷ A [ prodᵣ p′ t t′ ]
    suc-cong      : ∀ {m n}
                  → Γ ⊢ m ≡ n ∷ ℕ
                  → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {z z′ s s′ n n′ F F′}
                  → Γ ∙ ℕ     ⊢ F
                  → Γ ∙ ℕ     ⊢ F ≡ F′
                  → Γ         ⊢ z ≡ z′ ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ s ≡ s′ ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ         ⊢ n ≡ n′ ∷ ℕ
                  → Γ         ⊢ natrec p q r F z s n ≡ natrec p q r F′ z′ s′ n′ ∷ F [ n ]
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
                  → Γ ⊢ Emptyrec p A e ≡ Emptyrec p A' e' ∷ A
    η-unit        : ∀ {e e'}
                  → Γ ⊢ e ∷ Unit
                  → Γ ⊢ e' ∷ Unit
                  → Γ ⊢ e ≡ e' ∷ Unit


-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
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
                 → Γ ⊢ t ⇒ t' ∷ Σₚ p , q ▷ F ▹ G
                 → Γ ⊢ fst p t ⇒ fst p t' ∷ F
  snd-subst      : ∀ {t t' F G}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ t' ∷ Σₚ p , q ▷ F ▹ G
                 → Γ ⊢ snd p t ⇒ snd p t' ∷ G [ fst p t ]
  Σ-β₁           : ∀ {F G t u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]
                 → p ≈ p′
                 → Γ ⊢ fst p (prodₚ p′ t u) ⇒ t ∷ F
  Σ-β₂           : ∀ {F G t u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]
                 -- TODO(WN): Prove that 𝔍 ∷ G [ t ] is admissible
                 → p ≈ p′
                 → Γ ⊢ snd p (prodₚ p′ t u) ⇒ u ∷ G [ fst p (prodₚ p′ t u) ]
  prodrec-subst  : ∀ {t t′ F G A}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A
                 → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
                 → Γ ⊢ t ⇒ t′ ∷ Σᵣ p , q ▷ F ▹ G
                 → Γ ⊢ prodrec r p q′ A t u ⇒ prodrec r p q′ A t′ u ∷ A [ t ]
  prodrec-β      : ∀ {A F G t t′ u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ t′ ∷ G [ t ]
                 → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
                 → p ≈ p′
                 → Γ ⊢ prodrec r p q′ A (prodᵣ p′ t t′) u ⇒
                       u [ t , t′ ] ∷ A [ prodᵣ p′ t t′ ]
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
data _⊢_⇒_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
  univ : ∀ {A B}
       → Γ ⊢ A ⇒ B ∷ U
       → Γ ⊢ A ⇒ B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
  id  : ∀ {A}
      → Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : ∀ {A A′ B}
      → Γ ⊢ A  ⇒  A′
      → Γ ⊢ A′ ⇒* B
      → Γ ⊢ A  ⇒* B

-- Type reduction to whnf
_⊢_↘_ : (Γ : Con Term n) → Term n → Term n → Set ℓ
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set ℓ
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type equality with well-formed types
_⊢_:≡:_ : (Γ : Con Term n) → Term n → Term n → Set ℓ
Γ ⊢ A :≡: B = Γ ⊢ A × Γ ⊢ B × (Γ ⊢ A ≡ B)

-- Term equality with well-formed terms
_⊢_:≡:_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set ℓ
Γ ⊢ t :≡: u ∷ A = (Γ ⊢ t ∷ A) × (Γ ⊢ u ∷ A) × (Γ ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_ (Γ : Con Term n) (A B : Term n) : Set ℓ where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term n) (t u A : Term n) : Set ℓ where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A
    ⊢u : Γ ⊢ u ∷ A
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ (Δ : Con Term k) : (σ : Subst k n) (Γ : Con Term n) → Set ℓ where
  id  : ∀ {σ} → Δ ⊢ˢ σ ∷ ε
  _,_ : ∀ {A σ}
      → Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢  head σ ∷ subst (tail σ) A
      → Δ ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ (Δ : Con Term k) : (σ σ′ : Subst k n) (Γ : Con Term n) → Set ℓ where
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
⟦ BΠ p q   ⟧ⱼ ⊢F ▹ ⊢G = ΠΣⱼ ⊢F ▹ ⊢G
⟦ BΣ m p q ⟧ⱼ ⊢F ▹ ⊢G = ΠΣⱼ ⊢F ▹ ⊢G

⟦_⟧ⱼᵤ_▹_ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F ∷ U
     → Γ ∙ F ⊢ G ∷ U
     → Γ     ⊢ ⟦ W ⟧ F ▹ G ∷ U
⟦ BΠ p q   ⟧ⱼᵤ ⊢F ▹ ⊢G = ΠΣⱼ ⊢F ▹ ⊢G
⟦ BΣ m p q ⟧ⱼᵤ ⊢F ▹ ⊢G = ΠΣⱼ ⊢F ▹ ⊢G
