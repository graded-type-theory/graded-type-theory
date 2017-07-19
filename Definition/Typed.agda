{-# OPTIONS --without-K #-}

module Definition.Typed where

open import Tools.Nat
open import Tools.Product
open import Definition.Untyped

infixl 30 _∙_
infix 30 Π_▹_


-- Context member existance at location
data _∷_∈_ : (x : Nat) (A : Term) (Γ : Con Term) → Set where
  here  : ∀ {Γ A}                     →     0 ∷ wk1 A ∈ (Γ ∙ A)
  there : ∀ {Γ A B n} (h : n ∷ A ∈ Γ) → suc n ∷ wk1 A ∈ (Γ ∙ B)

mutual
  -- Well-formed context
  data ⊢_ : Con Term → Set where
    ε   : ⊢ ε
    _∙_ : ∀ {Γ A}
        → ⊢ Γ
        → Γ ⊢ A
        → ⊢ Γ ∙ A

  -- Well-formed type
  data _⊢_ (Γ : Con Term) : Term → Set where
    ℕ    : ⊢ Γ → Γ ⊢ ℕₑ
    U    : ⊢ Γ → Γ ⊢ Uₑ
    Π_▹_ : ∀ {F G}
         → Γ     ⊢ F
         → Γ ∙ F ⊢ G
         → Γ     ⊢ Πₑ F ▹ G
    univ : ∀ {A}
         → Γ ⊢ A ∷ Uₑ
         → Γ ⊢ A

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con Term) : Term → Term → Set where
    ℕ      : ⊢ Γ → Γ ⊢ ℕₑ ∷ Uₑ
    Π_▹_   : ∀ {F G}
           → Γ     ⊢ F ∷ Uₑ
           → Γ ∙ F ⊢ G ∷ Uₑ
           → Γ     ⊢ Πₑ F ▹ G ∷ Uₑ
    var    : ∀ {A x}
           → ⊢ Γ
           → x ∷ A ∈ Γ
           → Γ ⊢ var x ∷ A
    lam    : ∀ {F G t}
           → Γ     ⊢ F
           → Γ ∙ F ⊢ t ∷ G
           → Γ     ⊢ lamₑ t ∷ Πₑ F ▹ G
    _∘_    : ∀ {g a F G}
           → Γ ⊢     g ∷ Πₑ F ▹ G
           → Γ ⊢     a ∷ F
           → Γ ⊢ g ∘ₑ a ∷ G [ a ]
    zero   : ⊢ Γ
           → Γ ⊢ zeroₑ ∷ ℕₑ
    suc    : ∀ {n}
           → Γ ⊢     n ∷ ℕₑ
           → Γ ⊢ sucₑ n ∷ ℕₑ
    natrec : ∀ {G s z n}
           → Γ ∙ ℕₑ ⊢ G
           → Γ     ⊢ z ∷ G [ zeroₑ ]
           → Γ     ⊢ s ∷ Πₑ ℕₑ ▹ (G ▹▹ G [ sucₑ (var zero) ]↑)
           → Γ     ⊢ n ∷ ℕₑ
           → Γ     ⊢ natrecₑ G z s n ∷ G [ n ]
    conv   : ∀ {t A B}
           → Γ ⊢ t ∷ A
           → Γ ⊢ A ≡ B
           → Γ ⊢ t ∷ B

  -- Type equality
  data _⊢_≡_ (Γ : Con Term) : Term → Term → Set where
    univ   : ∀ {A B}
           → Γ ⊢ A ≡ B ∷ Uₑ
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
           → Γ     ⊢ Πₑ F ▹ G ≡ Πₑ H ▹ E

  -- Term equality
  data _⊢_≡_∷_ (Γ : Con Term) : Term → Term → Term → Set where
    refl        : ∀ {t A}
                → Γ ⊢ t ∷ A
                → Γ ⊢ t ≡ t ∷ A
    sym         : ∀ {t u A}
                → Γ ⊢ t ≡ u ∷ A
                → Γ ⊢ u ≡ t ∷ A
    trans       : ∀ {t u r A}
                → Γ ⊢ t ≡ u ∷ A
                → Γ ⊢ u ≡ r ∷ A
                → Γ ⊢ t ≡ r ∷ A
    conv        : ∀ {A B t u}
                → Γ ⊢ t ≡ u ∷ A
                → Γ ⊢ A ≡ B
                → Γ ⊢ t ≡ u ∷ B
    Π-cong      : ∀ {E F G H}
                → Γ     ⊢ F
                → Γ     ⊢ F ≡ H       ∷ Uₑ
                → Γ ∙ F ⊢ G ≡ E       ∷ Uₑ
                → Γ     ⊢ Πₑ F ▹ G ≡ Πₑ H ▹ E ∷ Uₑ
    app-cong    : ∀ {a b f g F G}
                → Γ ⊢ f ≡ g ∷ Πₑ F ▹ G
                → Γ ⊢ a ≡ b ∷ F
                → Γ ⊢ f ∘ₑ a ≡ g ∘ₑ b ∷ G [ a ]
    β-red       : ∀ {a t F G}
                → Γ     ⊢ F
                → Γ ∙ F ⊢ t ∷ G
                → Γ     ⊢ a ∷ F
                → Γ     ⊢ (lamₑ t) ∘ₑ a ≡ t [ a ] ∷ G [ a ]
    fun-ext     : ∀ {f g F G}
                → Γ     ⊢ F
                → Γ     ⊢ f ∷ Πₑ F ▹ G
                → Γ     ⊢ g ∷ Πₑ F ▹ G
                → Γ ∙ F ⊢ wk1 f ∘ₑ var zero ≡ wk1 g ∘ₑ var zero ∷ G
                → Γ     ⊢ f ≡ g ∷ Πₑ F ▹ G
    suc-cong    : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕₑ
                → Γ ⊢ sucₑ m ≡ sucₑ n ∷ ℕₑ
    natrec-cong : ∀ {z z' s s' n n' F F'}
                → Γ ∙ ℕₑ ⊢ F ≡ F'
                → Γ     ⊢ z ≡ z' ∷ F [ zeroₑ ]
                → Γ     ⊢ s ≡ s' ∷ Πₑ ℕₑ ▹ (F ▹▹ F [ sucₑ (var zero) ]↑)
                → Γ     ⊢ n ≡ n' ∷ ℕₑ
                → Γ     ⊢ natrecₑ F z s n ≡ natrecₑ F' z' s' n' ∷ F [ n ]
    natrec-zero : ∀ {z s F}
                → Γ ∙ ℕₑ ⊢ F
                → Γ     ⊢ z ∷ F [ zeroₑ ]
                → Γ     ⊢ s ∷ Πₑ ℕₑ ▹ (F ▹▹ F [ sucₑ (var zero) ]↑)
                → Γ     ⊢ natrecₑ F z s zeroₑ ≡ z ∷ F [ zeroₑ ]
    natrec-suc  : ∀ {n z s F}
                → Γ     ⊢ n ∷ ℕₑ
                → Γ ∙ ℕₑ ⊢ F
                → Γ     ⊢ z ∷ F [ zeroₑ ]
                → Γ     ⊢ s ∷ Πₑ ℕₑ ▹ (F ▹▹ F [ sucₑ (var zero) ]↑)
                → Γ     ⊢ natrecₑ F z s (sucₑ n) ≡ (s ∘ₑ n) ∘ₑ (natrecₑ F z s n)
                        ∷ F [ sucₑ n ]

-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  conv         : ∀ {A B t u}
               → Γ ⊢ t ⇒ u ∷ A
               → Γ ⊢ A ≡ B
               → Γ ⊢ t ⇒ u ∷ B
  app-subst    : ∀ {A B t u a}
               → Γ ⊢ t ⇒ u ∷ Πₑ A ▹ B
               → Γ ⊢ a ∷ A
               → Γ ⊢ t ∘ₑ a ⇒ u ∘ₑ a ∷ B [ a ]
  β-red        : ∀ {A B a t}
               → Γ     ⊢ A
               → Γ ∙ A ⊢ t ∷ B
               → Γ     ⊢ a ∷ A
               → Γ     ⊢ (lamₑ t) ∘ₑ a ⇒ t [ a ] ∷ B [ a ]
  natrec-subst : ∀ {z s n n' F}
               → Γ ∙ ℕₑ ⊢ F
               → Γ     ⊢ z ∷ F [ zeroₑ ]
               → Γ     ⊢ s ∷ Πₑ ℕₑ ▹ (F ▹▹ F [ sucₑ (var zero) ]↑)
               → Γ     ⊢ n ⇒ n' ∷ ℕₑ
               → Γ     ⊢ natrecₑ F z s n ⇒ natrecₑ F z s n' ∷ F [ n ]
  natrec-zero  : ∀ {z s F}
               → Γ ∙ ℕₑ ⊢ F
               → Γ     ⊢ z ∷ F [ zeroₑ ]
               → Γ     ⊢ s ∷ Πₑ ℕₑ ▹ (F ▹▹ F [ sucₑ (var zero) ]↑)
               → Γ     ⊢ natrecₑ F z s zeroₑ ⇒ z ∷ F [ zeroₑ ]
  natrec-suc   : ∀ {n z s F}
               → Γ     ⊢ n ∷ ℕₑ
               → Γ ∙ ℕₑ ⊢ F
               → Γ     ⊢ z ∷ F [ zeroₑ ]
               → Γ     ⊢ s ∷ Πₑ ℕₑ ▹ (F ▹▹ F [ sucₑ (var zero) ]↑)
               → Γ     ⊢ natrecₑ F z s (sucₑ n) ⇒ (s ∘ₑ n) ∘ₑ (natrecₑ F z s n)
                       ∷ F [ sucₑ n ]

-- Type reduction
data _⊢_⇒_ (Γ : Con Term) : Term → Term → Set where
  univ : ∀ {A B}
       → Γ ⊢ A ⇒ B ∷ Uₑ
       → Γ ⊢ A ⇒ B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t' u}
      → Γ ⊢ t  ⇒  t' ∷ A
      → Γ ⊢ t' ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con Term) : Term → Term → Set where
  id  : ∀ {A}
      → Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : ∀ {A A' B}
      → Γ ⊢ A  ⇒  A'
      → Γ ⊢ A' ⇒* B
      → Γ ⊢ A  ⇒* B

-- Type reduction to whnf
_⊢_↘_ : (Γ : Con Term) → Term → Term → Set
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type eqaulity with well-formed types
_⊢_:≡:_ : (Γ : Con Term) → Term → Term → Set
Γ ⊢ A :≡: B = Γ ⊢ A × Γ ⊢ B × (Γ ⊢ A ≡ B)

-- Term equality with well-formed terms
_⊢_:≡:_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t :≡: u ∷ A = Γ ⊢ t ∷ A × Γ ⊢ u ∷ A × (Γ ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_ (Γ : Con Term) (A B : Term) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

open _⊢_:⇒*:_ using () renaming (D to red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term) (t u A : Term) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A
    ⊢u : Γ ⊢ u ∷ A
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ) public

-- Well-formed substitutions.
data _⊢ₛ_∷_ (Δ : Con Term) (σ : Subst) : (Γ : Con Term) → Set where
  id : Δ ⊢ₛ σ ∷ ε
  _,_ : ∀ {Γ A}
      → Δ ⊢ₛ tail σ ∷ Γ
      → Δ ⊢ head σ ∷ subst (tail σ) A
      → Δ ⊢ₛ σ ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _⊢ₛ_≡_∷_ (Δ : Con Term) (σ σ' : Subst) : (Γ : Con Term) → Set where
  id : Δ ⊢ₛ σ ≡ σ' ∷ ε
  _,_ : ∀ {Γ A}
      → Δ ⊢ₛ tail σ ≡ tail σ' ∷ Γ
      → Δ ⊢ head σ ≡ head σ' ∷ subst (tail σ) A
      → Δ ⊢ₛ σ ≡ σ' ∷ Γ ∙ A

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.
