{-# OPTIONS  --safe #-}

module Definition.Typed where

open import Definition.Untyped hiding (_∷_)
open import Definition.Modality
open import Definition.Modality.Context

open import Tools.Fin
open import Tools.Nat
open import Tools.Product

infixl 30 _∙_
infix 30 Πⱼ_▹_
infix 30 Σⱼ_▹_
-- infix 30 ⟦_⟧ⱼ_▹_


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
    γ δ η θ : ConM 𝕄 n
    γ′ γ″ δ′ η′ θ′ : ConM 𝕄 n

  _▶_≈_ : (𝕄 : Modality M) (p q : M) → Set
  𝕄 ▶ p ≈ q = Modality._≈_ 𝕄 p q



-- Well-typed variables
data _∷_∈_ : (x : Fin n) (A : Term M n) (Γ : Con (Term M) n) → Set₁ where
  here  :                       x0 ∷ wk1 A ∈ (Γ ∙ A)
  there : (h : x ∷ A ∈ Γ) → (x +1) ∷ wk1 A ∈ (Γ ∙ B)

-- Well-usage of variables
data _◂_∈_ : (x : Fin n) (p : M) (γ : ConM 𝕄 n) → Set₁ where
  here  :                       x0 ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q

data _▸_ {n : Nat} {𝕄 : Modality M} : (γ : ConM 𝕄 n) → Term M n → Set₁ where
  Uₘ        : 𝟘ᶜ ▸ U
  ℕₘ        : 𝟘ᶜ ▸ ℕ
  Emptyₘ    : 𝟘ᶜ ▸ Empty
  Unitₘ     : 𝟘ᶜ ▸ Unit
  Πₘ        : γ ▸ F
            → (δ ∙ p) ▸ G
            → 𝕄 ▶ p ≈ r
            → (γ +ᶜ δ) ▸ Π q , r ▷ F ▹ G
  Σₘ        : γ ▸ F
            → (δ ∙ p) ▸ G
            → 𝕄 ▶ p ≈ q
            → (γ +ᶜ δ) ▸ Σ q ▷ F ▹ G

  var       : x ◂ (Modality.𝟙 𝕄) ∈ γ
            → γ ▸ var x

  lamₘ      : ∀ {t}
            → (γ ∙ p) ▸ t
            → γ ▸ lam p t
  _∘ₘ_      : γ ▸ t
            → δ ▸ u
            → (γ +ᶜ p ·ᶜ δ) ▸ (p ▷ t ∘ u)

  prodₘ     : γ ▸ t
            → δ ▸ u
            → (γ +ᶜ δ) ▸ prod t u
  fstₘ      : γ ▸ t
            → γ ▸ fst t
  sndₘ      : γ ▸ t
            → γ ▸ snd t

  zeroₘ     : 𝟘ᶜ ▸ zero
  sucₘ      : γ ▸ t
            → γ ▸ suc t
  natrec-zeroₘ : ∀ {G z s}
               → γ ▸ z
               → γ ▸ natrec G z s zero
--  natrec-sucₘ  : ∀ {G z s n}
--               → (γ ∙ q ∙ p) ▸ s
--               → δ ▸ n
--               → η ▸ natrec G z s n
--               → (γ +ᶜ q ·ᶜ δ +ᶜ p ·ᶜ η) ▸ natrec G z s (suc n)
 {- natrecₘ   : ∀ {G z s n}
            → (γ ∙ p) ▸ G
            → δ ▸ z
            → η ▸ s
            → θ ▸ n
            → (γ +ᶜ δ +ᶜ η +ᶜ θ) ▸ natrec G z s n
-}

  Emptyrecₘ : δ ▸ A
            → γ ▸ t
            → (γ +ᶜ δ) ▸ (Emptyrec p A t)

  starₘ     : 𝟘ᶜ ▸ star

  sub       : γ ▸ t
            → δ ≤ᶜ γ
            → δ ▸ t

mutual
  -- Well-formed context
  data ⊢_ {M : Set} : Con (Term M) n → Set₁ where
    ε   : ⊢ ε
    _∙_ : ⊢ Γ
        → Γ ⊢ A
        → ⊢ Γ ∙ A

  data _⊢_◂_ {𝕄 : Modality M} (Γ : Con (Term M) n) : (A : Term M n) (γ : ConM 𝕄 n) → Set₁ where
    Uⱼ     : ⊢ Γ
           → Γ ⊢ U ◂ 𝟘ᶜ
    ℕⱼ     : ⊢ Γ
           → Γ ⊢ ℕ ◂ 𝟘ᶜ
    Emptyⱼ : ⊢ Γ
           → Γ ⊢ Empty ◂ 𝟘ᶜ
    Unitⱼ  : ⊢ Γ
           → Γ ⊢ Unit ◂ 𝟘ᶜ
    Πⱼ_▹_  : Γ     ⊢ F ◂ γ
           → Γ ∙ F ⊢ G ◂ (δ ∙ q)
           → Γ     ⊢ (Π p , q ▷ F ▹ G) ◂ (γ +ᶜ δ)
    Σⱼ_▹_  : Γ     ⊢ F ◂ γ
           → Γ ∙ F ⊢ G ◂ (δ ∙ p)
           → Γ     ⊢ (Σ p ▷ F ▹ G) ◂ (γ +ᶜ δ)
    univ   : Γ ⊢ γ ▸ A ∷ U ◂ δ
           → Γ ⊢ A ◂ γ
    sub    : Γ ⊢ A ◂ γ
           → δ ≤ᶜ γ
           → Γ ⊢ A ◂ δ

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

  data _⊢_▸_∷_◂_ {𝕄 : Modality M} (Γ : Con (Term M) n) :
       (γ : ConM 𝕄 n) (t A : Term M n) (δ : ConM 𝕄 n) → Set₁ where
    Πⱼ_▹_     : Γ     ⊢ γ         ▸                 F ∷ U ◂ 𝟘ᶜ
              → Γ ∙ F ⊢ (γ′ ∙ q)  ▸                 G ∷ U ◂ 𝟘ᶜ
              → Γ     ⊢ (γ +ᶜ γ′) ▸ (Π p , q ▷ F ▹ G) ∷ U ◂ 𝟘ᶜ 
    Σⱼ_▹_     : Γ     ⊢ γ         ▸                 F ∷ U ◂ 𝟘ᶜ
              → Γ ∙ F ⊢ (γ′ ∙ p)  ▸                 G ∷ U ◂ 𝟘ᶜ
              → Γ     ⊢ (γ +ᶜ γ′) ▸     (Σ p ▷ F ▹ G) ∷ U ◂ 𝟘ᶜ
    ℕⱼ        : ⊢ Γ
              → Γ ⊢ 𝟘ᶜ ▸ ℕ ∷ U ◂ 𝟘ᶜ
    Emptyⱼ    : ⊢ Γ
              → Γ ⊢ 𝟘ᶜ ▸ Empty ∷ U ◂ 𝟘ᶜ
    Unitⱼ     : ⊢ Γ
              → Γ ⊢ 𝟘ᶜ ▸ Unit ∷ U ◂ 𝟘ᶜ

    var       : ⊢ Γ
              → x ∷ A ∈ Γ
              → x ◂ Modality.𝟙 𝕄 ∈ γ
              → Γ ⊢ A ◂ δ
              → Γ ⊢ γ ▸ var x ∷ A ◂ δ

    lamⱼ      : Γ     ⊢ F ◂ δ
              → Γ ∙ F ⊢ (γ′ ∙ p) ▸ t ∷ G ◂ (δ′ ∙ q)
              → Γ ⊢ γ′ ▸ lam p t ∷ (Π p , q ▷ F ▹ G) ◂ (δ +ᶜ δ′)
    _∘ⱼ_      : Γ ⊢ γ ▸ g ∷ (Π p , q ▷ F ▹ G) ◂ (δ +ᶜ δ′)
              → Γ ⊢ γ′ ▸ a ∷ F ◂ δ′
              → Γ ⊢ γ +ᶜ p ·ᶜ γ′ ▸ p ▷ g ∘ a ∷ G [ a ] ◂ (δ +ᶜ q ·ᶜ γ′)

    prodⱼ     : Γ ⊢ F ◂ δ
              → Γ ∙ F ⊢ G ◂ (δ′ ∙ p)
              → Γ ⊢ γ  ▸ t ∷ F       ◂ δ
              → Γ ⊢ γ′ ▸ u ∷ G [ t ] ◂ δ′
              → Γ ⊢ (γ +ᶜ γ′) ▸ prod t u ∷ (Σ p ▷ F ▹ G) ◂ (δ +ᶜ δ′)
    fstⱼ      : Γ ⊢ F ◂ δ
              → Γ ∙ F ⊢ G ◂ (δ′ ∙ p)
              → Γ ⊢ γ ▸ t ∷ (Σ p ▷ F ▹ G) ◂ (δ +ᶜ δ′) 
              → Γ ⊢ γ ▸ fst t ∷ F ◂ δ
    sndⱼ      : Γ ⊢ F ◂ δ
              → Γ ∙ F ⊢ G ◂ (δ′ ∙ p)
              → Γ ⊢ γ ▸ t ∷ (Σ p ▷ F ▹ G) ◂ (δ +ᶜ δ′)
              → Γ ⊢ γ ▸ snd t ∷ G [ fst t ] ◂ δ′

    zeroⱼ     : ⊢ Γ
              → Γ ⊢ 𝟘ᶜ ▸ zero ∷ ℕ ◂ 𝟘ᶜ
    sucⱼ      : Γ ⊢ γ ▸ t ∷ ℕ ◂ δ
              → Γ ⊢ γ ▸ suc t ∷ ℕ ◂ δ
   {- natrecⱼ   : ∀ {s z n}
              → Γ ∙ ℕ ⊢ G ◂ (δ ∙ {!!})
              → Γ ⊢ γ ▸ z ∷ G [ zero ] ◂ δ
              → Γ ⊢ γ′ ▸ s ∷ (Π p , q ▷ ℕ ▹ (r ▷ G ▹▹ G [ suc (var x0) ]↑)) ◂ {!!}
              → Γ ⊢ {!!} ▸ n ∷ ℕ ◂ 𝟘ᶜ
              → Γ ⊢ {!!} ▸ natrec G z s n ∷ G [ n ] ◂ δ -}

    Emptyrecⱼ : Γ ⊢ A ◂ δ
              → Γ ⊢ γ ▸ t ∷ Empty ◂ 𝟘ᶜ
              → Γ ⊢ (γ +ᶜ δ) ▸ Emptyrec p A t ∷ A ◂ δ

    starⱼ     : ⊢ Γ
              → Γ ⊢ 𝟘ᶜ ▸ star ∷ Unit ◂ 𝟘ᶜ

    conv      : Γ ⊢ γ ▸ t ∷ A ◂ δ
              → Γ ⊢ δ ▸ A ≡ B ◂ δ′
              → Γ ⊢ γ ▸ t ∷ B ◂ δ′

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
              → Γ     ⊢ lam p t ∷ Π q , r ▷ F ▹ G
    _∘ⱼ_      : ∀ {g a F G}
              → Γ ⊢     g ∷ Π p , q ▷ F ▹ G
              → Γ ⊢     a ∷ F
              → Γ ⊢ r ▷ g ∘ a ∷ G [ a ]

    prodⱼ     : ∀ {F G t u}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ F
              → Γ ⊢ u ∷ G [ t ]
              → Γ ⊢ prod t u ∷ Σ p ▷ F ▹ G
    fstⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σ p  ▷ F ▹ G
              → Γ ⊢ fst t ∷ F
    sndⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σ p ▷ F ▹ G
              → Γ ⊢ snd t ∷ G [ fst t ]

    zeroⱼ     : ⊢ Γ
              → Γ ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {n}
              → Γ ⊢       n ∷ ℕ
              → Γ ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {G s z n}
              → Γ ∙ ℕ ⊢ G
              → Γ       ⊢ z ∷ G [ zero ]
              → Γ       ⊢ s ∷ Π p , q ▷ ℕ ▹ (_▷_▹▹_ {𝕄 = 𝕄} r G (G [ suc (var x0) ]↑))
              -- (r ▷ G ▹▹ G [ suc (var x0) ]↑)
              → Γ       ⊢ n ∷ ℕ
              → Γ       ⊢ natrec G z s n ∷ G [ n ]

    Emptyrecⱼ : ∀ {A e}
              → Γ ⊢ A → Γ ⊢ e ∷ Empty → Γ ⊢ Emptyrec p A e ∷ A

    starⱼ     : ⊢ Γ → Γ ⊢ star ∷ Unit

    conv      : ∀ {t A B}
              → Γ ⊢ t ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t ∷ B

  data _⊢_▸_≡_◂_ (Γ : Con (Term M) n) : (γ : ConM 𝕄 n) (A B : Term M n) (δ : ConM 𝕄 n) → Set₁ where
    univ   : Γ ⊢ γ ▸ A ≡ B ◂ δ ∷ U ◂ 𝟘ᶜ
           → Γ ⊢ γ ▸ A ≡ B ◂ δ
    refl   : Γ ⊢ A ◂ γ
           → Γ ⊢ γ ▸ A ≡ A ◂ γ
    sym    : Γ ⊢ γ ▸ A ≡ B ◂ δ
           → Γ ⊢ δ ▸ B ≡ A ◂ γ
    trans  : Γ ⊢ γ ▸ A ≡ B ◂ δ
           → Γ ⊢ δ ▸ B ≡ C ◂ η
           → Γ ⊢ γ ▸ A ≡ C ◂ η
    Π-cong : Γ     ⊢ F ◂ γ
           → Γ     ⊢ γ ▸ F ≡ H ◂ γ′
           → Γ ∙ F ⊢ (δ ∙ q) ▸ G ≡ E ◂ (δ′ ∙ q)
           → Γ     ⊢ (γ +ᶜ δ) ▸ (Π p , q ▷ F ▹ G) ≡ (Π p , q ▷ H ▹ E) ◂ (γ′ +ᶜ δ′)
    Σ-cong : Γ     ⊢ F ◂ γ
           → Γ     ⊢ γ ▸ F ≡ H ◂ γ′
           → Γ ∙ F ⊢ (δ ∙ p) ▸ G ≡ E ◂ (δ′ ∙ p)
           → Γ     ⊢ (γ +ᶜ δ) ▸ (Σ p ▷ F ▹ G) ≡ (Σ p  ▷ H ▹ E) ◂ (γ′ +ᶜ δ′)
           
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

  data _⊢_▸_≡_◂_∷_◂_ (Γ : Con (Term M) n) : (γ : ConM 𝕄 n) (t u : Term M n)
                     (δ : ConM 𝕄 n) (A : Term M n) (η : ConM 𝕄 n) → Set₁ where

    refl          : Γ ⊢ γ  ▸ t ∷ A ◂ δ
                  → Γ ⊢ γ  ▸ t ≡ t ◂ γ  ∷ A ◂ δ
    sym           : Γ ⊢ γ  ▸ t ≡ u ◂ γ′ ∷ A ◂ δ
                  → Γ ⊢ γ′ ▸ u ≡ t ◂ γ  ∷ A ◂ δ
    trans         : Γ ⊢ γ  ▸ t ≡ u ◂ γ′ ∷ A ◂ δ
                  → Γ ⊢ γ′ ▸ u ≡ r ◂ γ″ ∷ A ◂ δ
                  → Γ ⊢ γ  ▸ t ≡ r ◂ γ″ ∷ A ◂ δ
    conv          : Γ ⊢ γ  ▸ t ≡ u ◂ γ′ ∷ A ◂ δ
                  → Γ ⊢ δ  ▸ A ≡ B ◂ δ′
                  → Γ ⊢ γ  ▸ t ≡ u ◂ γ′ ∷ B ◂ δ′
    Π-cong        : Γ     ⊢ F ◂ γ
                  → Γ     ⊢ γ ▸ F ≡ H ◂ δ ∷ U ◂ 𝟘ᶜ
                  → Γ ∙ F ⊢ (γ′ ∙ q) ▸ G ≡ E ◂ (δ′ ∙ q) ∷ U ◂ 𝟘ᶜ
                  → Γ     ⊢ (γ +ᶜ γ′) ▸ (Π p , q ▷ F ▹ G) ≡ (Π p , q ▷ H ▹ E) ◂ (δ +ᶜ δ′) ∷ U ◂ 𝟘ᶜ
    Σ-cong        : Γ     ⊢ F ◂ γ
                  → Γ     ⊢ γ  ▸ F ≡ H ◂ δ  ∷ U ◂ 𝟘ᶜ
                  → Γ ∙ F ⊢ (γ′ ∙ p) ▸ G ≡ E ◂ (δ′ ∙ p) ∷ U ◂ 𝟘ᶜ
                  → Γ     ⊢ (γ +ᶜ γ′) ▸ (Σ p ▷ F ▹ G) ≡ (Σ p ▷ H ▹ E) ◂ (δ +ᶜ δ′) ∷ U ◂ 𝟘ᶜ
    app-cong      : Γ ⊢ γ  ▸ f ≡ g ◂ δ  ∷ (Π p , q ▷ F ▹ G) ◂ (η +ᶜ η′)
                  → Γ ⊢ γ′ ▸ a ≡ b ◂ δ′ ∷ F ◂ η′
                  → Γ ⊢ (γ +ᶜ p ·ᶜ γ′) ▸ (p ▷ f ∘ a) ≡ (p ▷ g ∘ b) ◂ (δ +ᶜ p ·ᶜ δ′) ∷ G [ a ] ◂ η
    β-red         : Γ     ⊢ F ◂ δ
                  → Γ ∙ F ⊢ (γ′ ∙ p) ▸ t ∷ G ◂ (δ′ ∙ q)
                  → Γ     ⊢ γ ▸ a ∷ F ◂ δ
                  → Γ     ⊢ (γ′ +ᶜ p ·ᶜ γ) ▸ (p ▷ (lam p t) ∘ a) ≡ t [ a ] ◂ γ′ ∷ G [ a ] ◂ δ′ 
    η-eq          : Γ     ⊢ F ◂ δ
                  → Γ     ⊢ γ  ▸ f ∷ Π p , q ▷ F ▹ G ◂ (δ +ᶜ δ′)
                  → Γ     ⊢ γ′ ▸ g ∷ Π p , q ▷ F ▹ G ◂ (δ +ᶜ δ′)
                  → Γ ∙ F ⊢ (γ ∙ p) ▸ (p ▷ wk1 f ∘ var x0) ≡ (p ▷ wk1 g ∘ var x0) ◂ (γ′ ∙ p) ∷ G ◂ (δ′ ∙ q)
                  → Γ     ⊢ γ ▸ f ≡ g ◂ γ′ ∷ Π p , q ▷ F ▹ G ◂ (δ +ᶜ δ′)
    fst-cong      : Γ ⊢ F ◂ δ
                  → Γ ∙ F ⊢ G ◂ (δ′ ∙ p)
                  → Γ ⊢ γ ▸ t ≡ u ◂ γ′ ∷ Σ p ▷ F ▹ G ◂ (δ +ᶜ δ′)
                  → Γ ⊢ γ ▸ fst t ≡ fst u ◂ γ′ ∷ F ◂ δ
    snd-cong      : Γ ⊢ F ◂ δ
                  → Γ ∙ F ⊢ G ◂ (δ′ ∙ p)
                  → Γ ⊢ γ ▸ t ≡ u ◂ γ′ ∷ Σ p ▷ F ▹ G ◂ (δ +ᶜ δ′)
                  → Γ ⊢ γ ▸ snd t ≡ snd u ◂ γ′ ∷ G [ fst t ] ◂ δ′
    Σ-β₁          : Γ ⊢ F ◂ δ
                  → Γ ∙ F ⊢ G ◂ (δ′ ∙ q)
                  → Γ ⊢ γ ▸ t ∷ F ◂ δ
                  → Γ ⊢ γ′ ▸ u ∷ G [ t ] ◂ δ′
                  → Γ ⊢ (γ +ᶜ γ′) ▸ fst (prod t u) ≡ t ◂ γ ∷ F ◂ δ
    Σ-β₂          : Γ ⊢ F ◂ δ
                  → Γ ∙ F ⊢ G ◂ (δ′ ∙ q)
                  → Γ ⊢ γ ▸ t ∷ F ◂ δ
                  → Γ ⊢ γ′ ▸ u ∷ G [ t ] ◂ δ′
                  → Γ ⊢ (γ +ᶜ γ′) ▸ snd (prod t u) ≡ u ◂ γ′ ∷ G [ fst (prod t u) ] ◂ δ′
    Σ-η           : Γ ⊢ F ◂ δ
                  → Γ ∙ F ⊢ G ◂ (δ′ ∙ p)
                  → Γ ⊢ γ  ▸ t ∷ (Σ p ▷ F ▹ G) ◂ (δ +ᶜ δ′)
                  → Γ ⊢ γ′ ▸ u ∷ (Σ p ▷ F ▹ G) ◂ (δ +ᶜ δ′)
                  → Γ ⊢ γ ▸ fst t ≡ fst u ◂ γ′ ∷ F ◂ δ
                  → Γ ⊢ γ ▸ snd t ≡ snd u ◂ γ′ ∷ G [ fst t ] ◂ γ′
                  → Γ ⊢ γ ▸ t ≡ u ◂ γ′ ∷ (Σ p ▷ F ▹ G) ◂ (δ +ᶜ δ′)
    suc-cong      : Γ ⊢ γ ▸ t ≡ u ◂ δ ∷ ℕ ◂ 𝟘ᶜ
                  → Γ ⊢ γ ▸ suc t ≡ suc u ◂ δ ∷ ℕ ◂ 𝟘ᶜ
    natrec-cong   : ∀ {z z′ s s′ n n′ F F′}
                  → Γ ∙ ℕ ⊢ (γ ∙ p) ▸ F ≡ F′ ◂ (γ′ ∙ p)
                  → Γ     ⊢ δ ▸ z ≡ z′ ◂ δ′ ∷ F [ zero ] ◂ γ
                  → Γ     ⊢ η ▸ s ≡ s′ ◂ η′ ∷ (Π p , q ▷ ℕ ▹ (_▷_▹▹_ {𝕄 = 𝕄} r F (F [ suc (var x0) ]↑))) ◂ (γ +ᶜ γ)
                  --(r ▷ F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢ θ ▸ n ≡ n′ ◂ θ′ ∷ ℕ ◂ 𝟘ᶜ
                  → Γ     ⊢ (γ +ᶜ δ +ᶜ η +ᶜ θ) ▸ natrec F z s n ≡ natrec F′ z′ s′ n′ ◂ (γ′ +ᶜ δ′ +ᶜ η′ +ᶜ θ′) ∷ F [ n ] ◂ γ
    natrec-zero   : ∀ {z s F}
                  → Γ ∙ ℕ ⊢ F ◂ (γ ∙ p)
                  → Γ     ⊢ δ ▸ z ∷ F [ zero ] ◂ γ
                  → Γ     ⊢ η ▸ s ∷ (Π p , q ▷ ℕ ▹ (_▷_▹▹_ {𝕄 = 𝕄} r F (F [ suc (var x0) ]↑))) ◂ (γ +ᶜ γ)
                  -- (r ▷ F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢  (γ +ᶜ δ +ᶜ γ) ▸ natrec F z s zero ≡ z ◂ δ ∷ F [ zero ] ◂ γ
    natrec-suc    : ∀ {n z s F}
                  → Γ     ⊢ γ ▸ n ∷ ℕ ◂ 𝟘ᶜ
                  → Γ ∙ ℕ ⊢ F ◂ (δ ∙ p)
                  → Γ     ⊢ η ▸ z ∷ F [ zero ] ◂ δ
                  → Γ     ⊢ θ ▸ s ∷ (Π p , q ▷ ℕ ▹ (_▷_▹▹_ {𝕄 = 𝕄} r F (F [ suc (var x0) ]↑))) ◂ (δ +ᶜ δ)
                  -- (r ▷ F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢ (δ +ᶜ η +ᶜ θ +ᶜ γ) ▸ natrec F z s (suc n) ≡ r ▷ (p ▷ s ∘ n) ∘ (natrec F z s n) ◂ (δ +ᶜ η +ᶜ θ +ᶜ γ) -- ?
                                        ∷ F [ suc n ] ◂ δ
    Emptyrec-cong : ∀ {A A' e e'}
                  → Γ ⊢ δ ▸ A ≡ A' ◂ δ′
                  → Γ ⊢ γ ▸ e ≡ e' ◂ γ′ ∷ Empty ◂ 𝟘ᶜ
                  → Γ ⊢ (γ +ᶜ δ) ▸ Emptyrec p A e ≡ Emptyrec p A' e' ◂ (γ′ +ᶜ δ′) ∷ A ◂ δ
    η-unit        : ∀ {e e'}
                  → Γ ⊢ γ ▸ e ∷ Unit ◂ 𝟘ᶜ
                  → Γ ⊢ δ ▸ e' ∷ Unit ◂ 𝟘ᶜ
                  → Γ ⊢ γ ▸ e ≡ e' ◂ δ ∷ Unit ◂ 𝟘ᶜ
    

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
    suc-cong      : ∀ {m n}
                  → Γ ⊢ m ≡ n ∷ ℕ
                  → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {z z′ s s′ n n′ F F′}
                  → Γ ∙ ℕ ⊢ F ≡ F′
                  → Γ     ⊢ z ≡ z′ ∷ F [ zero ]
                  → Γ     ⊢ s ≡ s′ ∷ Π p , q ▷ ℕ ▹ (_▷_▹▹_ {𝕄 = 𝕄} r F (F [ suc (var x0) ]↑))
                  --(r ▷ F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢ n ≡ n′ ∷ ℕ
                  → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ]
    natrec-zero   : ∀ {z s F}
                  → Γ ∙ ℕ ⊢ F
                  → Γ     ⊢ z ∷ F [ zero ]
                  → Γ     ⊢ s ∷ Π p , q ▷ ℕ ▹ (_▷_▹▹_ {𝕄 = 𝕄} r F (F [ suc (var x0) ]↑))
                  -- (r ▷ F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢ natrec F z s zero ≡ z ∷ F [ zero ]
    natrec-suc    : ∀ {n z s F}
                  → Γ     ⊢ n ∷ ℕ
                  → Γ ∙ ℕ ⊢ F
                  → Γ     ⊢ z ∷ F [ zero ]
                  → Γ     ⊢ s ∷ Π p , q ▷ ℕ ▹ (_▷_▹▹_ {𝕄 = 𝕄} r F (F [ suc (var x0) ]↑))
                  -- (r ▷ F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢ natrec F z s (suc n) ≡ r ▷ (p ▷ s ∘ n) ∘ (natrec F z s n)
                                        ∷ F [ suc n ]
    Emptyrec-cong : ∀ {A A' e e'}
                  → Γ ⊢ A ≡ A'
                  → Γ ⊢ e ≡ e' ∷ Empty
                  → Γ ⊢ Emptyrec p A e ≡ Emptyrec p A' e' ∷ A
    η-unit        : ∀ {e e'}
                  → Γ ⊢ e ∷ Unit
                  → Γ ⊢ e' ∷ Unit
                  → Γ ⊢ e ≡ e' ∷ Unit

{-
mutual

  thm : Γ ⊢ t ◂ γ → γ ▸ t
  thm (Uⱼ x) = Uₘ
  thm (ℕⱼ x) = ℕₘ
  thm (Emptyⱼ x) = Emptyₘ
  thm (Unitⱼ x) = Unitₘ
  thm (Πⱼ j ▹ j₁) = Πₘ (thm j) (thm j₁)
  thm (Σⱼ j ▹ j₁) = Σₘ (thm j) (thm j₁)
  thm (sub j x) = sub (thm j) x
  thm (univ x) = thm3 x

  thm2 : Γ ⊢ t ◂ γ → Γ ⊢ t
  thm2 (Uⱼ x) = Uⱼ x
  thm2 (ℕⱼ x) = ℕⱼ x
  thm2 (Emptyⱼ x) = Emptyⱼ x
  thm2 (Unitⱼ x) = Unitⱼ x
  thm2 (Πⱼ j ▹ j₁) = Πⱼ thm2 j ▹ thm2 j₁
  thm2 (Σⱼ j ▹ j₁) = Σⱼ thm2 j ▹ thm2 j₁
  thm2 (sub j x) = thm2 j
  thm2 (univ x) = univ (thm4 x)

  thm3 : Γ ⊢ γ ▸ t ∷ A ◂ δ → γ ▸ t
  thm3 (Πⱼ j ▹ j₁) = Πₘ (thm3 j) (thm3 j₁)
  thm3 (Σⱼ j ▹ j₁) = Σₘ (thm3 j) (thm3 j₁)
  thm3 (ℕⱼ x) = ℕₘ
  thm3 (Emptyⱼ x) = Emptyₘ
  thm3 (Unitⱼ x) = Unitₘ
  thm3 (var x x₁ x₂ x₃) = var x₂
  thm3 (lamⱼ x j) = lamₘ (thm3 j)
  thm3 (j ∘ⱼ j₁) = thm3 j ∘ₘ thm3 j₁
  thm3 (prodⱼ x x₁ j j₁) = prodₘ (thm3 j) (thm3 j₁)
  thm3 (fstⱼ x x₁ j) = fstₘ (thm3 j)
  thm3 (sndⱼ x x₁ j) = sndₘ (thm3 j)
  thm3 (zeroⱼ x) = zeroₘ
  thm3 (sucⱼ j) = sucₘ (thm3 j)
  thm3 (Emptyrecⱼ x j) = Emptyrecₘ (thm x) (thm3 j)
  thm3 (starⱼ x) = starₘ
  thm3 (conv x x₁) = thm3 x

  thm3' : Γ ⊢ γ ▸ t ∷ A ◂ δ → δ ▸ A
  thm3' (Πⱼ j ▹ j₁) = thm3' j
  thm3' (Σⱼ j ▹ j₁) = thm3' j
  thm3' (ℕⱼ x) = Uₘ
  thm3' (Emptyⱼ x) = Uₘ
  thm3' (Unitⱼ x) = Uₘ
  thm3' (var x x₁ x₂ x₃) = thm x₃
  thm3' (lamⱼ x j) = Πₘ (thm x) (thm3' j)
  thm3' (j ∘ⱼ j₁) = {!!}
  thm3' (prodⱼ x x₁ j j₁) = Σₘ (thm3' j) (thm x₁)
  thm3' (fstⱼ x x₁ j) = thm x
  thm3' (sndⱼ x x₁ j) = {!!}
  thm3' (zeroⱼ x) = ℕₘ
  thm3' (sucⱼ j) = thm3' j
  thm3' (Emptyrecⱼ x j) = thm x
  thm3' (starⱼ x) = Unitₘ
  thm3' (conv j x) = proj₂ (thm5 x)

  thm4 : Γ ⊢ γ ▸ t ∷ A ◂ δ → Γ ⊢ t ∷ A
  thm4 (Πⱼ j ▹ j₁) = Πⱼ (thm4 j) ▹ (thm4 j₁)
  thm4 (Σⱼ j ▹ j₁) = Σⱼ (thm4 j) ▹  (thm4 j₁)
  thm4 (ℕⱼ x) = ℕⱼ x
  thm4 (Emptyⱼ x) = Emptyⱼ x
  thm4 (Unitⱼ x) = Unitⱼ x
  thm4 (var x x₁ x₂ x₃) = var x x₁
  thm4 (lamⱼ x j) = lamⱼ (thm2 x) (thm4 j)
  thm4 (j ∘ⱼ j₁) = thm4 j ∘ⱼ thm4 j₁
  thm4 (prodⱼ x x₁ j j₁) = prodⱼ (thm2 x) (thm2 x₁) (thm4 j) (thm4 j₁)
  thm4 (fstⱼ x x₁ j) = fstⱼ (thm2 x) (thm2 x₁) (thm4 j)
  thm4 (sndⱼ x x₁ j) = sndⱼ (thm2 x) (thm2 x₁) (thm4 j)
  thm4 (zeroⱼ x) = zeroⱼ x
  thm4 (sucⱼ j) = sucⱼ (thm4 j)
  thm4 (Emptyrecⱼ x j) = Emptyrecⱼ (thm2 x) (thm4 j)
  thm4 (starⱼ x) = starⱼ x
  thm4 (conv x x₁) = conv (thm4 x) (thm6 x₁)

  thm5 : Γ ⊢ γ ▸ A ≡ B ◂ δ → (γ ▸ A) × (δ ▸ B)
  thm5 (refl x) = (thm x) , (thm x)
  thm5 (sym j) = (proj₂ (thm5 j)) , (proj₁ (thm5 j))
  thm5 (trans j j₁) = (proj₁ (thm5 j)) , (proj₂ (thm5 j₁))
  thm5 (Π-cong x j j₁) = (Πₘ (proj₁ (thm5 j)) (proj₁ (thm5 j₁))) ,
                         (Πₘ (proj₂ (thm5 j)) (proj₂ (thm5 j₁)))
  thm5 (Σ-cong x j j₁) = (Σₘ (proj₁ (thm5 j)) (proj₁ (thm5 j₁))) ,
                         (Σₘ (proj₂ (thm5 j)) (proj₂ (thm5 j₁)))
  thm5 (univ x) = proj₁ (thm7 x) , proj₁ (proj₂ (thm7 x))

  thm6 : Γ ⊢ γ ▸ A ≡ B ◂ δ → Γ ⊢ A ≡ B
  thm6 (refl x) = refl (thm2 x)
  thm6 (sym j) = sym (thm6 j)
  thm6 (trans j j₁) = trans (thm6 j) (thm6 j₁)
  thm6 (Π-cong x j j₁) = Π-cong (thm2 x) (thm6 j) (thm6 j₁)
  thm6 (Σ-cong x j j₁) = Σ-cong (thm2 x) (thm6 j) (thm6 j₁)
  thm6 (univ x) = univ (thm8 x)

  thm7 : Γ ⊢ γ ▸ t ≡ u ◂ δ ∷ A ◂ η → γ ▸ t × δ ▸ u × η ▸ A
  thm7 (refl x) = ( thm3 x) , (thm3 x , thm3' x)
  thm7 (sym j) = (proj₁ (proj₂ (thm7 j))) , ((proj₁ (thm7 j)) , (proj₂ (proj₂ (thm7 j))))
  thm7 (trans j j₁) = (proj₁ (thm7 j)) , ((proj₁ (proj₂ (thm7 j₁))) , (proj₂ (proj₂ (thm7 j))))
  thm7 (conv j x) = (proj₁ (thm7 j)) , ((proj₁ (proj₂ (thm7 j))) , proj₂ (thm5 x))
  thm7 (Π-cong x j j₁) = Πₘ (thm x) (proj₁ (thm7 j₁)) , (Πₘ (proj₁ (proj₂ (thm7 j))) (proj₁ (proj₂ (thm7 j₁))) , Uₘ)
  thm7 (Σ-cong x j j₁) = Σₘ (thm x) (proj₁ (thm7 j₁)) , (Σₘ (proj₁ (proj₂ (thm7 j))) (proj₁ (proj₂ (thm7 j₁))) , Uₘ)
  thm7 (app-cong j j₁) = ((proj₁ (thm7 j)) ∘ₘ (proj₁ (thm7 j₁))) , (((proj₁ (proj₂ (thm7 j))) ∘ₘ (proj₁ (proj₂ (thm7 j₁)))) , {!!})
  thm7 (β-red x x₁ x₂) = ((lamₘ (thm3 x₁)) ∘ₘ (thm3 x₂)) , ({!!} , {!!})
  thm7 (η-eq x x₁ x₂ x₃) = (thm3 x₁) , ((thm3 x₂) , (thm3' x₁))
  thm7 (fst-cong x x₁ x₂) = (fstₘ (proj₁ (thm7 x₂))) , ((fstₘ (proj₁ (proj₂ (thm7 x₂)))) , (thm x))
  thm7 (snd-cong x x₁ x₂) = (sndₘ (proj₁ (thm7 x₂))) , ((sndₘ (proj₁ (proj₂ (thm7 x₂)))) , {!!})
  thm7 (Σ-β₁ x x₁ x₂ x₃) = (fstₘ (prodₘ (thm3 x₂) (thm3 x₃))) , ((thm3 x₂) , (thm3' x₂))
  thm7 (Σ-β₂ x x₁ x₂ x₃) = (sndₘ (prodₘ (thm3 x₂) (thm3 x₃))) , ((thm3 x₃) , {!!})
  thm7 (Σ-η x x₁ x₂ x₃ j j₁) = (thm3 x₂) , ((thm3 x₃) , (thm3' x₂))
  thm7 (suc-cong j) = sucₘ (proj₁ (thm7 j)) , (sucₘ (proj₁ (proj₂ (thm7 j))) , ℕₘ)
  thm7 (natrec-cong x j j₁ j₂) = {!!} ,
    --natrecₘ (proj₁ (thm5 x)) (proj₁ (thm7 j)) (proj₁ (thm7 j₁)) (proj₁ (thm7 j₂)) ,
                                 --(natrecₘ (proj₂ (thm5 x)) (proj₁ (proj₂ (thm7 j))) (proj₁ (proj₂ (thm7 j₁))) ( proj₁ (proj₂ (thm7 j₂))) ,
                                 {!!} ,
                                 {!!}
  thm7 (natrec-zero x x₁ x₂) = {!natrecₘ!} , (thm3 x₁ , thm3' x₁)
  thm7 (natrec-suc x x₁ x₂ x₃) = {!!}
  --natrecₘ (thm x₁) (thm3 x₂) (thm3 x₃) (sucₘ (thm3 x)) , ({!!} , {!!})
  thm7 (Emptyrec-cong x j) = Emptyrecₘ (proj₁ (thm5 x)) (proj₁ (thm7 j)) , (Emptyrecₘ (proj₂ (thm5 x)) (proj₁ (proj₂ (thm7 j))) , proj₁ (thm5 x))
  thm7 (η-unit x x₁) = thm3 x , (thm3 x₁ , Unitₘ)

  thm8 : {𝕄 : Modality M} → Γ ⊢ γ ▸ t ≡ u ◂ δ ∷ A ◂ η → Γ ⊢ t ≡ u ∷ A
  thm8 (refl x) = refl (thm4 x)
  thm8 (sym j) = sym (thm8 j)
  thm8 (trans j j₁) = trans (thm8 j) (thm8 j₁)
  thm8 (conv j x) = conv (thm8 j) (thm6 x)
  thm8 (Π-cong x j j₁) = Π-cong (thm2 x) (thm8 j) (thm8 j₁)
  thm8 (Σ-cong x j j₁) = Σ-cong (thm2 x) (thm8 j) (thm8 j₁)
  thm8 (app-cong j j₁) = app-cong (thm8 j) (thm8 j₁)
  thm8 (β-red x x₁ x₂) = β-red (thm2 x) (thm4 x₁) (thm4 x₂)
  thm8 (η-eq x x₁ x₂ x₃) = η-eq (thm2 x) (thm4 x₁) (thm4 x₂) (thm8 x₃)
  thm8 (fst-cong x x₁ x₂) = fst-cong (thm2 x) (thm2 x₁) (thm8 x₂)
  thm8 (snd-cong x x₁ x₂) = snd-cong (thm2 x) (thm2 x₁) (thm8 x₂)
  thm8 (Σ-β₁ x x₁ x₂ x₃) = Σ-β₁ (thm2 x) (thm2 x₁) (thm4 x₂) (thm4 x₃)
  thm8 (Σ-β₂ x x₁ x₂ x₃) = Σ-β₂ (thm2 x) (thm2 x₁) (thm4 x₂) (thm4 x₃)
  thm8 (Σ-η x x₁ x₂ x₃ j j₁) = Σ-η (thm2 x) (thm2 x₁) (thm4 x₂) (thm4 x₃) (thm8 j) (thm8 j₁)
  thm8 (suc-cong j) = suc-cong (thm8 j)
  thm8 (natrec-cong x j j₁ j₂) = natrec-cong (thm6 x) (thm8 j) (thm8 j₁) (thm8 j₂)
  thm8 (natrec-zero x x₁ x₂) = natrec-zero (thm2 x) (thm4 x₁) (thm4 x₂)
  thm8 (natrec-suc x x₁ x₂ x₃) = natrec-suc (thm4 x) (thm2 x₁) (thm4 x₂) (thm4 x₃)
  thm8 (Emptyrec-cong x j) = Emptyrec-cong (thm6 x) (thm8 j)
  thm8 (η-unit x x₁) = η-unit (thm4 x) (thm4 x₁)
-}  
{-
-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set where
  conv           : ∀ {A B t u}
                 → Γ ⊢ t ⇒ u ∷ A
                 → Γ ⊢ A ≡ B
                 → Γ ⊢ t ⇒ u ∷ B
  -- app-subst      : ∀ {A B t u a}
  --                → Γ ⊢ t ⇒ u ∷ Π A ▹ B
  --                → Γ ⊢ a ∷ A
  --                → Γ ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ]
  -- β-red          : ∀ {A B a t}
  --                → Γ     ⊢ A
  --                → Γ ∙ A ⊢ t ∷ B
  --                → Γ     ⊢ a ∷ A
  --                → Γ     ⊢ (lam t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  -- fst-subst      : ∀ {t t' F G}
  --                → Γ ⊢ F
  --                → Γ ∙ F ⊢ G
  --                → Γ ⊢ t ⇒ t' ∷ Σ F ▹ G
  --                → Γ ⊢ fst t ⇒ fst t' ∷ F
  -- snd-subst      : ∀ {t t' F G}
  --                → Γ ⊢ F
  --                → Γ ∙ F ⊢ G
  --                → Γ ⊢ t ⇒ t' ∷ Σ F ▹ G
  --                → Γ ⊢ snd t ⇒ snd t' ∷ G [ fst t ]
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
  -- natrec-subst   : ∀ {z s n n′ F}
  --                → Γ ∙ ℕ ⊢ F
  --                → Γ     ⊢ z ∷ F [ zero ]
  --                → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                → Γ     ⊢ n ⇒ n′ ∷ ℕ
  --                → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ]
  -- natrec-zero    : ∀ {z s F}
  --                → Γ ∙ ℕ ⊢ F
  --                → Γ     ⊢ z ∷ F [ zero ]
  --                → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                → Γ     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ]
  -- natrec-suc     : ∀ {n z s F}
  --                → Γ     ⊢ n ∷ ℕ
  --                → Γ ∙ ℕ ⊢ F
  --                → Γ     ⊢ z ∷ F [ zero ]
  --                → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n) ∷ F [ suc n ]
  -- Emptyrec-subst : ∀ {n n′ A}
  --                → Γ ⊢ A
  --                → Γ     ⊢ n ⇒ n′ ∷ Empty
  --                → Γ     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∷ A

-- Type reduction
data _⊢_⇒_ (Γ : Con Term n) : Term n → Term n → Set where
  univ : ∀ {A B}
       → Γ ⊢ A ⇒ B ∷ U
       → Γ ⊢ A ⇒ B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con Term n) : Term n → Term n → Set where
  id  : ∀ {A}
      → Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : ∀ {A A′ B}
      → Γ ⊢ A  ⇒  A′
      → Γ ⊢ A′ ⇒* B
      → Γ ⊢ A  ⇒* B

-- Type reduction to whnf
_⊢_↘_ : (Γ : Con Term n) → Term n → Term n → Set
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type eqaulity with well-formed types
_⊢_:≡:_ : (Γ : Con Term n) → Term n → Term n → Set
Γ ⊢ A :≡: B = Γ ⊢ A × Γ ⊢ B × (Γ ⊢ A ≡ B)

-- Term equality with well-formed terms
_⊢_:≡:_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set
Γ ⊢ t :≡: u ∷ A = (Γ ⊢ t ∷ A) × (Γ ⊢ u ∷ A) × (Γ ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_ (Γ : Con Term n) (A B : Term n) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term n) (t u A : Term n) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A
    ⊢u : Γ ⊢ u ∷ A
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ (Δ : Con Term m) : (σ : Subst m n) (Γ : Con Term n) → Set where
  id  : ∀ {σ} → Δ ⊢ˢ σ ∷ ε
  _,_ : ∀ {A σ}
      → Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢  head σ ∷ subst (tail σ) A
      → Δ ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ (Δ : Con Term m) : (σ σ′ : Subst m n) (Γ : Con Term n) → Set where
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
⟦ BΠ ⟧ⱼ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ ⟧ⱼ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

⟦_⟧ⱼᵤ_▹_ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F ∷ U
     → Γ ∙ F ⊢ G ∷ U
     → Γ     ⊢ ⟦ W ⟧ F ▹ G ∷ U
⟦ BΠ ⟧ⱼᵤ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ ⟧ⱼᵤ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G
-}
