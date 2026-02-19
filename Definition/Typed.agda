------------------------------------------------------------------------
-- Typing and reduction relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed.Variant

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Sup R
open import Definition.Untyped.Whnf M type-variant

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
import Tools.Vec as Vec

infix 24 ∙_

private
  variable
    m n α : Nat
    ∇ ∇′ : DCon (Term 0) _
    φ φ′ : Unfolding _
    ω : Opacity _
    Γ : Con Term _
    A A₁ A₂ A′ B B₁ B₂ C E F F′ G H : Term _
    a f g l l₁ l₂ l₂′ l₃ l′ n′ s s′ t t₁ t₂ t′ u u₁ u₂ u′ v v₁ v₂ v′ w w₁ w₂ w′ z z′ :
      Term _
    σ σ′ : Subst _ _
    x : Fin _
    p p′ q q′ r : M
    b : BinderMode
    k : Strength

-- Well-typed variables
data _∷_∈_ : (x : Fin n) (A : Term n) (Γ : Con Term n) → Set ℓ where
  here  :                 x0 ∷ wk1 A ∈ Γ ∙ A
  there : x ∷ A ∈ Γ → (x +1) ∷ wk1 A ∈ Γ ∙ B

opaque
  unfolding _⊔ᵒ_

  infixl 5 _⊔ᵒᵗ_

  -- Definition context unfolding.

  _⊔ᵒᵗ_ : Unfolding n → Unfolding n → Unfolding n
  _⊔ᵒᵗ_ with unfolding-mode
  … | explicit   = λ φ _ → φ
  … | transitive = _⊔ᵒ_

opaque

  -- Transparentisation.

  Trans : Unfolding n → DCon (Term 0) n → DCon (Term 0) n
  Trans _ ε =
    ε
  Trans φ (∇ ∙⟨ tra ⟩[ t ∷ A ]) =
    Trans (Vec.tail φ) ∇ ∙⟨ tra ⟩[ t ∷ A ]
  Trans (φ ⁰) (∇ ∙⟨ ω ⟩[ t ∷ A ]) =
    Trans φ ∇ ∙⟨ ω ⟩[ t ∷ A ]
  Trans (φ ¹) (∇ ∙⟨ opa φ′ ⟩[ t ∷ A ]) =
    Trans (φ ⊔ᵒᵗ φ′) ∇ ∙⟨ tra ⟩[ t ∷ A ]

mutual

  -- Well-formed definition contexts.

  infix 4 »_

  data »_ : DCon (Term 0) m → Set ℓ where
    ε          : » ε
    ∙ᵒ⟨_⟩[_∷_] : Opacity-allowed
               → Trans φ ∇ » ε ⊢ t ∷ A
               → ∇ » ε ⊢ A
               → » ∇ ∙⟨ opa φ ⟩[ t ∷ A ]
    ∙ᵗ[_]      : ∇ » ε ⊢ t ∷ A
               → » ∇ ∙⟨ tra ⟩[ t ∷ A ]

  -- Well-formed contexts.

  infix 4 _»⊢_

  data _»⊢_ (∇ : DCon (Term 0) m) : Con Term n → Set ℓ where
    ε  : » ∇       → ∇ »⊢ ε
    ∙_ : ∇ » Γ ⊢ A → ∇ »⊢ Γ ∙ A

  pattern εε = ε ε

  -- A variant of _»⊢_.

  infix 4 ⊢_

  ⊢_ : Cons m n → Set ℓ
  ⊢ ∇ » Γ = ∇ »⊢ Γ

  -- Well-formed types.

  infix 4 _⊢_

  data _⊢_ (Γ : Cons m n) : Term n → Set ℓ where
    Levelⱼ : Level-is-not-small
           → ⊢ Γ
           → Γ ⊢ Level
    univ   : Γ ⊢ A ∷ U l
           → Γ ⊢ A
    Liftⱼ  : Γ ⊢ l₂ ∷Level
           → Γ ⊢ A
           → Γ ⊢ Lift l₂ A
    ΠΣⱼ    : Γ »∙ A ⊢ B
           → ΠΣ-allowed b p q
           → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
    Idⱼ    : Γ ⊢ A
           → Γ ⊢ t ∷ A
           → Γ ⊢ u ∷ A
           → Γ ⊢ Id A t u

  -- Well-typed terms.

  infix 4 _⊢_∷_

  data _⊢_∷_ (Γ : Cons m n) : Term n → Term n → Set ℓ where
    conv      : Γ ⊢ t ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t ∷ B

    var       : ⊢ Γ
              → x ∷ A ∈ Γ .vars
              → Γ ⊢ var x ∷ A
    defn      : ⊢ Γ
              → α ↦∷ A′ ∈ Γ .defs
              → A PE.≡ wk wk₀ A′
              → Γ ⊢ defn α ∷ A

    Levelⱼ    : ⊢ Γ → Level-is-small → Γ ⊢ Level ∷ U zeroᵘ
    zeroᵘⱼ    : Level-allowed
              → ⊢ Γ
              → Γ ⊢ zeroᵘ ∷ Level
    sucᵘⱼ     : Γ ⊢ l ∷ Level
              → Γ ⊢ sucᵘ l ∷ Level
    supᵘⱼ     : Γ ⊢ l₁ ∷ Level
              → Γ ⊢ l₂ ∷ Level
              → Γ ⊢ l₁ supᵘ l₂ ∷ Level

    Uⱼ        : Γ ⊢ l ∷Level
              → Γ ⊢ U l ∷ U (sucᵘ l)

    Liftⱼ     : Γ ⊢ l₁ ∷Level
              → Γ ⊢ l₂ ∷Level
              → Γ ⊢ A ∷ U l₁
              → Γ ⊢ Lift l₂ A ∷ U (l₁ supᵘₗ l₂)
    liftⱼ     : Γ ⊢ l₂ ∷Level
              → Γ ⊢ A
              → Γ ⊢ t ∷ A
              → Γ ⊢ lift t ∷ Lift l₂ A
    lowerⱼ    : Γ ⊢ t ∷ Lift l₂ A
              → Γ ⊢ lower t ∷ A

    Emptyⱼ    : ⊢ Γ → Γ ⊢ Empty ∷ U zeroᵘ
    emptyrecⱼ : Γ ⊢ A → Γ ⊢ t ∷ Empty → Γ ⊢ emptyrec p A t ∷ A

    Unitⱼ     : ⊢ Γ → Unit-allowed k → Γ ⊢ Unit k ∷ U zeroᵘ
    starⱼ     : ⊢ Γ
              → Unit-allowed k
              → Γ ⊢ star k ∷ Unit k
    unitrecⱼ  : Γ »∙ Unitʷ ⊢ A
              → Γ ⊢ t ∷ Unitʷ
              → Γ ⊢ u ∷ A [ starʷ ]₀
              → Unitʷ-allowed
              → Γ ⊢ unitrec p q A t u ∷ A [ t ]₀

    ΠΣⱼ       : Γ ⊢ l ∷Level
              → Γ ⊢ F ∷ U l
              → Γ »∙ F ⊢ G ∷ U (wk1 l)
              → ΠΣ-allowed b p q
              → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷ U l

    lamⱼ      : Γ »∙ F ⊢ G
              → Γ »∙ F ⊢ t ∷ G
              → Π-allowed p q
              → Γ ⊢ lam p t ∷ Π p , q ▷ F ▹ G
    _∘ⱼ_      : Γ ⊢ t ∷ Π p , q ▷ F ▹ G
              → Γ ⊢ u ∷ F
              → Γ ⊢ t ∘⟨ p ⟩ u ∷ G [ u ]₀

    prodⱼ     : Γ »∙ F ⊢ G
              → Γ ⊢ t ∷ F
              → Γ ⊢ u ∷ G [ t ]₀
              → Σ-allowed k p q
              → Γ ⊢ prod k p t u ∷ Σ⟨ k ⟩ p , q ▷ F ▹ G
    fstⱼ      : Γ »∙ F ⊢ G
              → Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G
              → Γ ⊢ fst p t ∷ F
    sndⱼ      : Γ »∙ F ⊢ G
              → Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G
              → Γ ⊢ snd p t ∷ G [ fst p t ]₀
    prodrecⱼ  : Γ »∙ (Σʷ p , q′ ▷ F ▹ G) ⊢ A
              → Γ ⊢ t ∷ Σʷ p , q′ ▷ F ▹ G
              → Γ »∙ F »∙ G ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑²
              → Σʷ-allowed p q′
              → Γ ⊢ prodrec r p q A t u ∷ A [ t ]₀

    ℕⱼ        : ⊢ Γ → Γ ⊢ ℕ ∷ U zeroᵘ
    zeroⱼ     : ⊢ Γ
              → Γ ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {n}
              → Γ ⊢     n ∷ ℕ
              → Γ ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {n}
              → Γ ⊢ z ∷ A [ zero ]₀
              → Γ »∙ ℕ »∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
              → Γ ⊢ n ∷ ℕ
              → Γ ⊢ natrec p q r A z s n ∷ A [ n ]₀

    Idⱼ       : Γ ⊢ A ∷ U l
              → Γ ⊢ t ∷ A
              → Γ ⊢ u ∷ A
              → Γ ⊢ Id A t u ∷ U l
    rflⱼ      : Γ ⊢ t ∷ A
              → Γ ⊢ rfl ∷ Id A t t
    Jⱼ        : Γ ⊢ t ∷ A
              → Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B
              → Γ ⊢ u ∷ B [ t , rfl ]₁₀
              → Γ ⊢ v ∷ A
              → Γ ⊢ w ∷ Id A t v
              → Γ ⊢ J p q A t B u v w ∷ B [ v , w ]₁₀
    Kⱼ        : Γ »∙ Id A t t ⊢ B
              → Γ ⊢ u ∷ B [ rfl ]₀
              → Γ ⊢ v ∷ Id A t t
              → K-allowed
              → Γ ⊢ K p A t B u v ∷ B [ v ]₀
    []-congⱼ  : Γ ⊢ l ∷Level
              → Γ ⊢ A
              → Γ ⊢ t ∷ A
              → Γ ⊢ u ∷ A
              → Γ ⊢ v ∷ Id A t u
              → []-cong-allowed k
              → let open Erased k in
                Γ ⊢ []-cong k l A t u v ∷
                  Id (Erased l A) ([ t ]) ([ u ])

  -- Well-formed level terms.

  infix 4 _⊢_∷Level

  data _⊢_∷Level (Γ : Cons m n) : Term n → Set ℓ where
    term    : Level-allowed
            → Γ ⊢ t ∷ Level
            → Γ ⊢ t ∷Level
    literal : ¬ Level-allowed
            → ⊢ Γ
            → Level-literal t
            → Γ ⊢ t ∷Level

  -- Type equality.

  infix 4 _⊢_≡_

  data _⊢_≡_ (Γ : Cons m n) : Term n → Term n → Set ℓ where
    refl   : Γ ⊢ A
           → Γ ⊢ A ≡ A
    sym    : Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ A
    trans  : Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ C
           → Γ ⊢ A ≡ C
    U-cong : Γ ⊢ l₁ ≡ l₂ ∷ Level
           → Γ ⊢ U l₁ ≡ U l₂
    univ   : Γ ⊢ A ≡ B ∷ U l
           → Γ ⊢ A ≡ B
    Lift-cong
           : Γ ⊢ l₂ ≡ l₂′ ∷Level
           → Γ ⊢ A ≡ B
           → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B
    ΠΣ-cong
           : Γ ⊢ F ≡ H
           → Γ »∙ F ⊢ G ≡ E
           → ΠΣ-allowed b p q
           → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡ ΠΣ⟨ b ⟩ p , q ▷ H ▹ E
    Id-cong
           : Γ ⊢ A₁ ≡ A₂
           → Γ ⊢ t₁ ≡ t₂ ∷ A₁
           → Γ ⊢ u₁ ≡ u₂ ∷ A₁
           → Γ ⊢ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂

  -- Term equality.

  infix 4 _⊢_≡_∷_

  data _⊢_≡_∷_ (Γ : Cons m n) : Term n → Term n → Term n → Set ℓ where
    conv          : Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ A ≡ B
                  → Γ ⊢ t ≡ u ∷ B

    refl          : Γ ⊢ t ∷ A
                  → Γ ⊢ t ≡ t ∷ A
    sym           : Γ ⊢ A
                  → Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ t ∷ A
    trans         : Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ v ∷ A
                  → Γ ⊢ t ≡ v ∷ A

    δ-red         : ⊢ Γ
                  → α ↦ t′ ∷ A′ ∈ Γ .defs
                  → A PE.≡ wk wk₀ A′
                  → t PE.≡ wk wk₀ t′
                  → Γ ⊢ defn α ≡ t ∷ A

    sucᵘ-cong     : ∀ {t t'}
                  → Γ ⊢ t ≡ t' ∷ Level
                  → Γ ⊢ sucᵘ t ≡ sucᵘ t' ∷ Level
    supᵘ-cong     : ∀ {t t' u u'}
                  → Γ ⊢ t ≡ t' ∷ Level
                  → Γ ⊢ u ≡ u' ∷ Level
                  → Γ ⊢ t supᵘ u ≡ t' supᵘ u' ∷ Level
    supᵘ-zeroˡ    : Γ ⊢ l ∷ Level
                  → Γ ⊢ zeroᵘ supᵘ l ≡ l ∷ Level
    supᵘ-sucᵘ     : Γ ⊢ l₁ ∷ Level
                  → Γ ⊢ l₂ ∷ Level
                  → Γ ⊢ sucᵘ l₁ supᵘ sucᵘ l₂ ≡ sucᵘ (l₁ supᵘ l₂) ∷ Level
    supᵘ-assoc    : Γ ⊢ l₁ ∷ Level
                  → Γ ⊢ l₂ ∷ Level
                  → Γ ⊢ l₃ ∷ Level
                  → Γ ⊢ (l₁ supᵘ l₂) supᵘ l₃ ≡ l₁ supᵘ (l₂ supᵘ l₃) ∷ Level
    supᵘ-comm     : Γ ⊢ l₁ ∷ Level
                  → Γ ⊢ l₂ ∷ Level
                  → Γ ⊢ l₁ supᵘ l₂ ≡ l₂ supᵘ l₁ ∷ Level
    supᵘ-idem     : Γ ⊢ l ∷ Level
                  → Γ ⊢ l supᵘ l ≡ l ∷ Level
    supᵘ-sub      : Γ ⊢ l ∷ Level
                  → Γ ⊢ l supᵘ sucᵘ l ≡ sucᵘ l ∷ Level

    U-cong        : Γ ⊢ l₁ ≡ l₂ ∷ Level
                  → Γ ⊢ U l₁ ≡ U l₂ ∷ U (sucᵘ l₁)

    Lift-cong     : Γ ⊢ l₁ ∷Level
                  → Γ ⊢ l₂ ∷Level
                  → Γ ⊢ l₂ ≡ l₂′ ∷Level
                  → Γ ⊢ A ≡ B ∷ U l₁
                  → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₁ supᵘₗ l₂)
    lower-cong    : Γ ⊢ t ≡ u ∷ Lift l₂ A
                  → Γ ⊢ lower t ≡ lower u ∷ A
    Lift-β        : Γ ⊢ A
                  → Γ ⊢ t ∷ A
                  → Γ ⊢ lower (lift t) ≡ t ∷ A
    Lift-η        : Γ ⊢ l₂ ∷Level
                  → Γ ⊢ A
                  → Γ ⊢ t ∷ Lift l₂ A
                  → Γ ⊢ u ∷ Lift l₂ A
                  → Γ ⊢ lower t ≡ lower u ∷ A
                  → Γ ⊢ t ≡ u ∷ Lift l₂ A

    emptyrec-cong : Γ ⊢ A ≡ B
                  → Γ ⊢ t ≡ u ∷ Empty
                  → Γ ⊢ emptyrec p A t ≡ emptyrec p B u ∷ A

    η-unit        : Γ ⊢ t ∷ Unit k
                  → Γ ⊢ t′ ∷ Unit k
                  → Unit-with-η k
                  → Γ ⊢ t ≡ t′ ∷ Unit k

    unitrec-cong  : Γ »∙ Unitʷ ⊢ A ≡ A′
                  → Γ ⊢ t ≡ t′ ∷ Unitʷ
                  → Γ ⊢ u ≡ u′ ∷ A [ starʷ ]₀
                  → Unitʷ-allowed
                  → ¬ Unitʷ-η
                  → Γ ⊢ unitrec p q A t u ≡ unitrec p q A′ t′ u′ ∷
                      A [ t ]₀
    unitrec-β     : Γ »∙ Unitʷ ⊢ A
                  → Γ ⊢ u ∷ A [ starʷ ]₀
                  → Unitʷ-allowed
                  → ¬ Unitʷ-η
                  → Γ ⊢ unitrec p q A starʷ u ≡ u ∷ A [ starʷ ]₀
    unitrec-β-η   : Γ »∙ Unitʷ ⊢ A
                  → Γ ⊢ t ∷ Unitʷ
                  → Γ ⊢ u ∷ A [ starʷ ]₀
                  → Unitʷ-allowed
                  → Unitʷ-η
                  → Γ ⊢ unitrec p q A t u ≡ u ∷ A [ t ]₀

    ΠΣ-cong       : Γ ⊢ l ∷Level
                  → Γ ⊢ F ≡ H ∷ U l
                  → Γ »∙ F ⊢ G ≡ E ∷ U (wk1 l)
                  → ΠΣ-allowed b p q
                  → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡
                      ΠΣ⟨ b ⟩ p , q ▷ H ▹ E ∷ U l

    app-cong      : ∀ {b}
                  → Γ ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
                  → Γ ⊢ a ≡ b ∷ F
                  → Γ ⊢ f ∘⟨ p ⟩ a ≡ g ∘⟨ p ⟩ b ∷ G [ a ]₀
    β-red         : Γ »∙ F ⊢ G
                  → Γ »∙ F ⊢ t ∷ G
                  → Γ ⊢ a ∷ F
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Π-allowed p q
                  → Γ ⊢ lam p t ∘⟨ p′ ⟩ a ≡ t [ a ]₀ ∷ G [ a ]₀
    η-eq          : Γ »∙ F ⊢ G
                  → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
                  → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
                  → Γ »∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 ≡ wk1 g ∘⟨ p ⟩ var x0 ∷ G
                  → Π-allowed p q
                  → Γ ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G

    prod-cong     : Γ »∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ F
                  → Γ ⊢ u ≡ u′ ∷ G [ t ]₀
                  → Σ-allowed k p q
                  → Γ ⊢ prod k p t u ≡ prod k p t′ u′ ∷ Σ⟨ k ⟩ p , q ▷ F ▹ G

    fst-cong      : Γ »∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ Σˢ p , q ▷ F ▹ G
                  → Γ ⊢ fst p t ≡ fst p t′ ∷ F
    Σ-β₁          : Γ »∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]₀
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Σˢ-allowed p q
                  → Γ ⊢ fst p (prodˢ p′ t u) ≡ t ∷ F
    snd-cong      : Γ »∙ F ⊢ G
                  → Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ F ▹ G
                  → Γ ⊢ snd p t ≡ snd p u ∷ G [ fst p t ]₀
    Σ-β₂          : Γ »∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]₀
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Σˢ-allowed p q
                  → Γ ⊢ snd p (prodˢ p′ t u) ≡ u ∷ G [ t ]₀
    Σ-η           : Γ »∙ F ⊢ G
                  → Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G
                  → Γ ⊢ u ∷ Σˢ p , q ▷ F ▹ G
                  → Γ ⊢ fst p t ≡ fst p u ∷ F
                  → Γ ⊢ snd p t ≡ snd p u ∷ G [ fst p t ]₀
                  → Σˢ-allowed p q
                  → Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ F ▹ G

    prodrec-cong  : Γ »∙ Σʷ p , q′ ▷ F ▹ G ⊢ A ≡ A′
                  → Γ ⊢ t ≡ t′ ∷ Σʷ p , q′ ▷ F ▹ G
                  → Γ »∙ F »∙ G ⊢ u ≡ u′ ∷
                      A [ prodʷ p (var x1) (var x0) ]↑²
                  → Σʷ-allowed p q′
                  → Γ ⊢ prodrec r p q A t u ≡ prodrec r p q A′ t′ u′ ∷ A [ t ]₀
    prodrec-β     : Γ »∙ Σʷ p , q′ ▷ F ▹ G ⊢ A
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ t′ ∷ G [ t ]₀
                  → Γ »∙ F »∙ G ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑²
                  → p PE.≡ p′
                  → Σʷ-allowed p q′
                  → Γ ⊢ prodrec r p q A (prodʷ p′ t t′) u ≡
                        u [ t , t′ ]₁₀ ∷ A [ prodʷ p′ t t′ ]₀

    suc-cong      : ∀ {n}
                  → Γ ⊢ t ≡ n ∷ ℕ
                  → Γ ⊢ suc t ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {n}
                  → Γ »∙ ℕ ⊢ A ≡ A′
                  → Γ ⊢ z ≡ z′ ∷ A [ zero ]₀
                  → Γ »∙ ℕ »∙ A ⊢ s ≡ s′ ∷ A [ suc (var x1) ]↑²
                  → Γ ⊢ n ≡ n′ ∷ ℕ
                  → Γ ⊢ natrec p q r A z s n ≡
                      natrec p q r A′ z′ s′ n′ ∷ A [ n ]₀
    natrec-zero   : Γ ⊢ z ∷ A [ zero ]₀
                  → Γ »∙ ℕ »∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                  → Γ ⊢ natrec p q r A z s zero ≡ z ∷ A [ zero ]₀
    natrec-suc    : ∀ {n}
                  → Γ ⊢ z ∷ A [ zero ]₀
                  → Γ »∙ ℕ »∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                  → Γ ⊢ n ∷ ℕ
                  → Γ ⊢ natrec p q r A z s (suc n) ≡
                      s [ n , natrec p q r A z s n ]₁₀ ∷ A [ suc n ]₀

    Id-cong       : Γ ⊢ A₁ ≡ A₂ ∷ U l
                  → Γ ⊢ t₁ ≡ t₂ ∷ A₁
                  → Γ ⊢ u₁ ≡ u₂ ∷ A₁
                  → Γ ⊢ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U l
    J-cong        : Γ ⊢ A₁ ≡ A₂
                  → Γ ⊢ t₁ ∷ A₁
                  → Γ ⊢ t₁ ≡ t₂ ∷ A₁
                  → Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂
                  → Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀
                  → Γ ⊢ v₁ ≡ v₂ ∷ A₁
                  → Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁
                  → Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ≡
                        J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷ B₁ [ v₁ , w₁ ]₁₀
    J-β           : Γ ⊢ t ∷ A
                  → Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B
                  → Γ ⊢ u ∷ B [ t , rfl ]₁₀
                  → t PE.≡ t′
                  → Γ ⊢ J p q A t B u t′ rfl ≡ u ∷ B [ t , rfl ]₁₀
    K-cong        : Γ ⊢ A₁ ≡ A₂
                  → Γ ⊢ t₁ ≡ t₂ ∷ A₁
                  → Γ »∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂
                  → Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀
                  → Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁
                  → K-allowed
                  → Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ≡ K p A₂ t₂ B₂ u₂ v₂ ∷
                      B₁ [ v₁ ]₀
    K-β           : Γ »∙ Id A t t ⊢ B
                  → Γ ⊢ u ∷ B [ rfl ]₀
                  → K-allowed
                  → Γ ⊢ K p A t B u rfl ≡ u ∷ B [ rfl ]₀
    []-cong-cong  : Γ ⊢ l₁ ≡ l₂ ∷Level
                  → Γ ⊢ A₁ ≡ A₂
                  → Γ ⊢ t₁ ≡ t₂ ∷ A₁
                  → Γ ⊢ u₁ ≡ u₂ ∷ A₁
                  → Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁
                  → []-cong-allowed k
                  → let open Erased k in
                    Γ ⊢ []-cong k l₁ A₁ t₁ u₁ v₁ ≡
                      []-cong k l₂ A₂ t₂ u₂ v₂ ∷
                      Id (Erased l₁ A₁) ([ t₁ ]) ([ u₁ ])
    []-cong-β     : Γ ⊢ l ∷Level
                  → Γ ⊢ t ∷ A
                  → t PE.≡ t′
                  → []-cong-allowed k
                  → let open Erased k in
                    Γ ⊢ []-cong k l A t t′ rfl ≡ rfl ∷
                      Id (Erased l A) ([ t ]) ([ t′ ])
    equality-reflection
                  : Equality-reflection
                  → Γ ⊢ Id A t u
                  → Γ ⊢ v ∷ Id A t u
                  → Γ ⊢ t ≡ u ∷ A

  -- Level term equality.

  infix 4 _⊢_≡_∷Level

  data _⊢_≡_∷Level (Γ : Cons m n) : (_ _ : Term n) → Set ℓ where
    term    : Level-allowed
            → Γ ⊢ t ≡ u ∷ Level
            → Γ ⊢ t ≡ u ∷Level
    literal : ¬ Level-allowed
            → ⊢ Γ
            → Level-literal t
            → Γ ⊢ t ≡ t ∷Level

-- Term reduction.

infix 4 _⊢_⇒_∷_

data _⊢_⇒_∷_ (Γ : Cons m n) : Term n → Term n → Term n → Set ℓ where
  conv           : Γ ⊢ t ⇒ u ∷ A
                 → Γ ⊢ A ≡ B
                 → Γ ⊢ t ⇒ u ∷ B

  δ-red          : ⊢ Γ
                 → α ↦ t′ ∷ A′ ∈ Γ .defs
                 → A PE.≡ wk wk₀ A′
                 → t PE.≡ wk wk₀ t′
                 → Γ ⊢ defn α ⇒ t ∷ A

  supᵘ-substˡ    : Γ ⊢ t ⇒ t′ ∷ Level
                 → Γ ⊢ u ∷ Level
                 → Γ ⊢ t supᵘ u ⇒ t′ supᵘ u ∷ Level
  supᵘ-substʳ    : Γ ⊢ t ∷ Level
                 → Γ ⊢ u ⇒ u′ ∷ Level
                 → Γ ⊢ sucᵘ t supᵘ u ⇒ sucᵘ t supᵘ u′ ∷ Level
  supᵘ-zeroˡ     : Γ ⊢ l ∷ Level
                 → Γ ⊢ zeroᵘ supᵘ l ⇒ l ∷ Level
  supᵘ-zeroʳ     : Γ ⊢ l ∷ Level
                 → Γ ⊢ sucᵘ l supᵘ zeroᵘ ⇒ sucᵘ l ∷ Level
  supᵘ-sucᵘ      : Γ ⊢ l₁ ∷ Level
                 → Γ ⊢ l₂ ∷ Level
                 → Γ ⊢ sucᵘ l₁ supᵘ sucᵘ l₂ ⇒ sucᵘ (l₁ supᵘ l₂) ∷ Level

  lower-subst    : Γ ⊢ t ⇒ u ∷ Lift l₂ A
                 → Γ ⊢ lower t ⇒ lower u ∷ A
  Lift-β         : Γ ⊢ A
                 → Γ ⊢ t ∷ A
                 → Γ ⊢ lower (lift t) ⇒ t ∷ A

  emptyrec-subst : ∀ {n}
                 → Γ ⊢ A
                 → Γ     ⊢ n ⇒ n′ ∷ Empty
                 → Γ     ⊢ emptyrec p A n ⇒ emptyrec p A n′ ∷ A

  unitrec-subst : Γ »∙ Unitʷ ⊢ A
                → Γ ⊢ u ∷ A [ starʷ ]₀
                → Γ ⊢ t ⇒ t′ ∷ Unitʷ
                → Unitʷ-allowed
                → ¬ Unitʷ-η
                → Γ ⊢ unitrec p q A t u ⇒ unitrec p q A t′ u ∷
                    A [ t ]₀
  unitrec-β     : Γ »∙ Unitʷ ⊢ A
                → Γ ⊢ u ∷ A [ starʷ ]₀
                → Unitʷ-allowed
                → ¬ Unitʷ-η
                → Γ ⊢ unitrec p q A starʷ u ⇒ u ∷ A [ starʷ ]₀
  unitrec-β-η   : Γ »∙ Unitʷ ⊢ A
                → Γ ⊢ t ∷ Unitʷ
                → Γ ⊢ u ∷ A [ starʷ ]₀
                → Unitʷ-allowed
                → Unitʷ-η
                → Γ ⊢ unitrec p q A t u ⇒ u ∷ A [ t ]₀

  app-subst      : Γ ⊢ t ⇒ u ∷ Π p , q ▷ F ▹ G
                 → Γ ⊢ a ∷ F
                 → Γ ⊢ t ∘⟨ p ⟩ a ⇒ u ∘⟨ p ⟩ a ∷ G [ a ]₀
  β-red          : Γ »∙ F ⊢ G
                 → Γ »∙ F ⊢ t ∷ G
                 → Γ ⊢ a ∷ F
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Π-allowed p q
                 → Γ ⊢ lam p t ∘⟨ p′ ⟩ a ⇒ t [ a ]₀ ∷ G [ a ]₀

  fst-subst      : Γ »∙ F ⊢ G
                 → Γ ⊢ t ⇒ u ∷ Σˢ p , q ▷ F ▹ G
                 → Γ ⊢ fst p t ⇒ fst p u ∷ F
  Σ-β₁           : Γ »∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]₀
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Σˢ-allowed p q
                 → Γ ⊢ fst p (prodˢ p′ t u) ⇒ t ∷ F
  snd-subst      : Γ »∙ F ⊢ G
                 → Γ ⊢ t ⇒ u ∷ Σˢ p , q ▷ F ▹ G
                 → Γ ⊢ snd p t ⇒ snd p u ∷ G [ fst p t ]₀
  Σ-β₂           : Γ »∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]₀
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Σˢ-allowed p q
                 → Γ ⊢ snd p (prodˢ p′ t u) ⇒ u ∷ G [ t ]₀

  prodrec-subst  : Γ »∙ Σʷ p , q′ ▷ F ▹ G ⊢ A
                 → Γ »∙ F »∙ G ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑²
                 → Γ ⊢ t ⇒ t′ ∷ Σʷ p , q′ ▷ F ▹ G
                 → Σʷ-allowed p q′
                 → Γ ⊢ prodrec r p q A t u ⇒ prodrec r p q A t′ u ∷ A [ t ]₀
  prodrec-β      : Γ »∙ Σʷ p , q′ ▷ F ▹ G ⊢ A
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ t′ ∷ G [ t ]₀
                 → Γ »∙ F »∙ G ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑²
                 → p PE.≡ p′
                 → Σʷ-allowed p q′
                 → Γ ⊢ prodrec r p q A (prodʷ p′ t t′) u ⇒
                       u [ t , t′ ]₁₀ ∷ A [ prodʷ p′ t t′ ]₀

  natrec-subst   : ∀ {n}
                 → Γ ⊢ z ∷ A [ zero ]₀
                 → Γ »∙ ℕ »∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ ⊢ n ⇒ n′ ∷ ℕ
                 → Γ ⊢ natrec p q r A z s n ⇒ natrec p q r A z s n′ ∷
                     A [ n ]₀
  natrec-zero    : Γ ⊢ z ∷ A [ zero ]₀
                 → Γ »∙ ℕ »∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ ⊢ natrec p q r A z s zero ⇒ z ∷ A [ zero ]₀
  natrec-suc     : ∀ {n}
                 → Γ ⊢ z ∷ A [ zero ]₀
                 → Γ »∙ ℕ »∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ ⊢ n ∷ ℕ
                 → Γ ⊢ natrec p q r A z s (suc n) ⇒
                     s [ n , natrec p q r A z s n ]₁₀ ∷ A [ suc n ]₀

  J-subst        : Γ ⊢ t ∷ A
                 → Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B
                 → Γ ⊢ u ∷ B [ t , rfl ]₁₀
                 → Γ ⊢ v ∷ A
                 → Γ ⊢ w₁ ⇒ w₂ ∷ Id A t v
                 → Γ ⊢ J p q A t B u v w₁ ⇒ J p q A t B u v w₂ ∷
                     B [ v , w₁ ]₁₀
  J-β            : Γ ⊢ t ∷ A
                 → Γ ⊢ t′ ∷ A
                 → Γ ⊢ t ≡ t′ ∷ A
                 → Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B
                 → Γ ⊢ B [ t , rfl ]₁₀ ≡ B [ t′ , rfl ]₁₀
                 → Γ ⊢ u ∷ B [ t , rfl ]₁₀
                 → Γ ⊢ J p q A t B u t′ rfl ⇒ u ∷ B [ t , rfl ]₁₀
  K-subst        : Γ »∙ Id A t t ⊢ B
                 → Γ ⊢ u ∷ B [ rfl ]₀
                 → Γ ⊢ v₁ ⇒ v₂ ∷ Id A t t
                 → K-allowed
                 → Γ ⊢ K p A t B u v₁ ⇒ K p A t B u v₂ ∷ B [ v₁ ]₀
  K-β            : Γ »∙ Id A t t ⊢ B
                 → Γ ⊢ u ∷ B [ rfl ]₀
                 → K-allowed
                 → Γ ⊢ K p A t B u rfl ⇒ u ∷ B [ rfl ]₀
  []-cong-subst  : Γ ⊢ l ∷Level
                 → Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u
                 → []-cong-allowed k
                 → let open Erased k in
                   Γ ⊢ []-cong k l A t u v₁ ⇒ []-cong k l A t u v₂ ∷
                     Id (Erased l A) ([ t ]) ([ u ])
  []-cong-β      : Γ ⊢ l ∷Level
                 → Γ ⊢ t ≡ t′ ∷ A
                 → []-cong-allowed k
                 → let open Erased k in
                   Γ ⊢ []-cong k l A t t′ rfl ⇒ rfl ∷
                     Id (Erased l A) ([ t ]) ([ t′ ])

-- Type reduction.

infix 4 _⊢_⇒_

data _⊢_⇒_ (Γ : Cons m n) : Term n → Term n → Set ℓ where
  univ   : Γ ⊢ A ⇒ B ∷ U l
         → Γ ⊢ A ⇒ B

-- A kind of reflexive transitive closure for _⊢_⇒_∷_.

infix 4 _⊢_⇒*_∷_

data _⊢_⇒*_∷_ (Γ : Cons m n) : Term n → Term n → Term n → Set ℓ where
  id  : Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- A kind of reflexive transitive closure for _⊢_⇒_.

infix 4 _⊢_⇒*_

data _⊢_⇒*_ (Γ : Cons m n) : Term n → Term n → Set ℓ where
  id  : Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : Γ ⊢ A  ⇒  A′
      → Γ ⊢ A′ ⇒* B
      → Γ ⊢ A  ⇒* B

-- Reduction of types to WHNF.

infix 4 _⊢_↘_

_⊢_↘_ : Cons m n → Term n → Term n → Set ℓ
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf (Γ .defs) B

-- Reduction of terms to WHNF.

infix 4 _⊢_↘_∷_

_⊢_↘_∷_ : Cons m n → Term n → Term n → Term n → Set ℓ
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf (Γ .defs) u

-- The natural order on levels

_⊢_≤_∷Level : (Γ : Cons m n) (t u : Term n) → Set ℓ
Γ ⊢ t ≤ u ∷Level = Γ ⊢ t supᵘ u ≡ u ∷ Level

-- A variant of _⊢_≤_∷Level, expressed using _supᵘₗ_ and _⊢_≡_∷Level.

infix 4 _⊢_≤ₗ_∷Level

_⊢_≤ₗ_∷Level : Cons m n → (_ _ : Term n) → Set ℓ
Γ ⊢ l₁ ≤ₗ l₂ ∷Level = Γ ⊢ l₁ supᵘₗ l₂ ≡ l₂ ∷Level

-- A context pair Γ is consistent if the empty type is not inhabited
-- in Γ.

Consistent : Cons m n → Set ℓ
Consistent Γ = ∀ t → ¬ Γ ⊢ t ∷ Empty
