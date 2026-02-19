------------------------------------------------------------------------
-- A combination of typing and usage for the erasure modality with
-- modes
------------------------------------------------------------------------

-- Given certain assumptions the combined type and usage system is
-- logically equivalent to the usual type and usage systems, see
-- Graded.Modality.Instances.Erasure.Combined.Equivalent.

open import Tools.Bool
open import Tools.Level using (lzero)

open import Definition.Typed.Restrictions

open import Graded.Modality.Variant lzero
open import Graded.Modality.Instances.Erasure.Modality
open import Graded.Usage.Restrictions

module Graded.Modality.Instances.Erasure.Combined
  (TR : Type-restrictions (ErasureModality (𝟘ᵐ-allowed-if true)))
  (UR : Usage-restrictions (ErasureModality (𝟘ᵐ-allowed-if true)))
  where

open Type-restrictions TR
open Usage-restrictions UR

private

  -- The modality used in this module.

  𝕄 : Modality
  𝕄 = ErasureModality (𝟘ᵐ-allowed-if true)

open import Graded.Context 𝕄
open import Graded.Modality.Instances.Erasure
open import Graded.Mode 𝕄
open import Graded.Usage.Erased-matches

open import Definition.Typed TR using (_∷_∈_; Trans)
open import Definition.Untyped Erasure
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Sup TR

open import Tools.Fin
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private variable
  α k m n                                 : Nat
  x                                       : Fin _
  ∇ ∇′                                    : DCon _ _
  φ                                       : Unfolding _
  Γ                                       : Cons _ _
  A A′ A₁ A₂ A₃ B B₁ B₂ C C₁ C₂
    l l₁ l₁₁ l₁₂ l₂ l₂₁ l₂₂ l₃
    t t′ t₁ t₂ t₃ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  σ                                       : Subst _ _
  s                                       : Strength
  b                                       : BinderMode
  δ δ₁ δ₂                                 : Conₘ _
  o p p′ q q′ r r′ r₁ r₂                  : Erasure

mutual

  infix 24 ∙_
  infix  4 »_ ⊢_ _⊢_ _▸_⊢[_]_ _⊢_∷_ _⊢_∷Level _▸_⊢_∷[_]_ _⊢_≡_ _⊢_≡_∷_
           _⊢_≡_∷Level

  -- Well-formed definition contexts.

  data »_ : DCon (Term 0) m → Set where
    ε  : » ε
    ∙ᵒ : Opacity-allowed →
         » ∇ →
         Trans φ ∇ » ε ⊢ t ∷ A →
         ∇ » ε ⊢ A →
         » ∇ ∙⟨ opa φ ⟩[ t ∷ A ]
    ∙ᵗ : » ∇ →
         ∇ » ε ⊢ t ∷ A →
         » ∇ ∙⟨ tra ⟩[ t ∷ A ]

  -- Well-formed context pairs.

  data ⊢_ : Cons m n → Set where
    ε  : » ∇ → ⊢ ∇ » ε
    ∙_ : Γ ⊢ A → ⊢ Γ »∙ A

  -- A variant of _▸_⊢[_]_.

  _⊢_ : Cons m n → Term n → Set
  Γ ⊢ A = 𝟘ᶜ ▸ Γ ⊢[ 𝟘 ] A

  -- Well-formed types.

  data _▸_⊢[_]_ (γ : Conₘ n) (Γ : Cons m n) (r : Erasure) :
         Term n → Set where
    Level : Level-is-not-small →
            ⊢ Γ →
            γ ▸ Γ ⊢[ r ] Level
    univ  : γ ▸ Γ ⊢ A ∷[ r ] U l →
            γ ▸ Γ ⊢[ r ] A
    Lift  : Γ ⊢ l ∷Level →
            γ ▸ Γ ⊢[ r ] A →
            γ ▸ Γ ⊢[ r ] Lift l A
    ΠΣ    : ΠΣ-allowed b p q →
            γ ▸ Γ ⊢[ r · p ] A →
            γ ∙ q ▸ Γ »∙ A ⊢[ r ] B →
            γ ▸ Γ ⊢[ r ] ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
    Id    : (Id-erased → δ PE.≡ 𝟘ᶜ × r′ PE.≡ 𝟘) →
            (¬ Id-erased → δ PE.≡ γ × r′ PE.≡ r) →
            δ ▸ Γ ⊢[ r′ ] A →
            δ ▸ Γ ⊢ t ∷[ r′ ] A →
            δ ▸ Γ ⊢ u ∷[ r′ ] A →
            γ ▸ Γ ⊢[ r ] Id A t u

  -- A variant of _▸_⊢_∷[_]_.

  _⊢_∷_ : Cons m n → Term n → Term n → Set
  Γ ⊢ t ∷ A = 𝟘ᶜ ▸ Γ ⊢ t ∷[ 𝟘 ] A

  -- Well-typed terms.

  data _▸_⊢_∷[_]_ (γ : Conₘ n) (Γ : Cons m n) :
         Term n → Erasure → Term n → Set where
    conv : γ ▸ Γ ⊢ t ∷[ p ] A₁ →
           Γ ⊢ A₁ ≡ A₂ →
           γ ▸ Γ ⊢ t ∷[ p ] A₂

    var  : γ ⟨ x ⟩ ≤ p →
           ⊢ Γ →
           x ∷ A ∈ Γ .vars →
           γ ▸ Γ ⊢ var x ∷[ p ] A
    defn : ⊢ Γ →
           α ↦∷ A′ ∈ Γ .defs →
           A PE.≡ wk wk₀ A′ →
           γ ▸ Γ ⊢ defn α ∷[ p ] A

    Level : Level-is-small →
            ⊢ Γ →
            γ ▸ Γ ⊢ Level ∷[ p ] U zeroᵘ
    zeroᵘ : Level-allowed →
            ⊢ Γ →
            γ ▸ Γ ⊢ zeroᵘ ∷[ p ] Level
    sucᵘ  : γ ▸ Γ ⊢ l ∷[ p ] Level →
            γ ▸ Γ ⊢ sucᵘ l ∷[ p ] Level
    ⊢supᵘ : γ ▸ Γ ⊢ l₁ ∷[ p ] Level →
            γ ▸ Γ ⊢ l₂ ∷[ p ] Level →
            γ ▸ Γ ⊢ l₁ supᵘ l₂ ∷[ p ] Level

    U : Γ ⊢ l ∷Level →
        γ ▸ Γ ⊢ U l ∷[ p ] U (sucᵘ l)

    Lift  : Γ ⊢ l₂ ∷Level →
            γ ▸ Γ ⊢ A ∷[ p ] U l₁ →
            γ ▸ Γ ⊢ Lift l₂ A ∷[ p ] U (l₁ supᵘₗ l₂)
    lift  : Γ ⊢ l ∷Level →
            γ ▸ Γ ⊢ t ∷[ p ] A →
            γ ▸ Γ ⊢ lift t ∷[ p ] Lift l A
    lower : γ ▸ Γ ⊢ t ∷[ p ] Lift l A →
            γ ▸ Γ ⊢ lower t ∷[ p ] A

    Empty    : ⊢ Γ →
               γ ▸ Γ ⊢ Empty ∷[ p ] U zeroᵘ
    emptyrec : Emptyrec-allowed ⌞ q ⌟ p →
               Γ ⊢ A →
               γ ▸ Γ ⊢ t ∷[ q · p ] Empty →
               γ ▸ Γ ⊢ emptyrec p A t ∷[ q ] A

    Unit     : Unit-allowed s →
               ⊢ Γ →
               γ ▸ Γ ⊢ Unit s ∷[ p ] U zeroᵘ
    star     : Unit-allowed s →
               ⊢ Γ →
               γ ▸ Γ ⊢ star s ∷[ p ] Unit s
    unitrec  : Unitrec-allowed ⌞ r ⌟ p q →
               Γ »∙ Unitʷ ⊢ A →
               γ ▸ Γ ⊢ t ∷[ r · p ] Unitʷ →
               γ ▸ Γ ⊢ u ∷[ r ] A [ starʷ ]₀ →
               γ ▸ Γ ⊢ unitrec p q A t u ∷[ r ] A [ t ]₀

    ΠΣ       : ΠΣ-allowed b p q →
               γ ▸ Γ ⊢ A ∷[ r · p ] U l →
               γ ∙ q ▸ Γ »∙ A ⊢ B ∷[ r ] U (wk1 l) →
               γ ▸ Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷[ r ] U l

    lam      : Π-allowed p q →
               γ ∙ p ▸ Γ »∙ A ⊢ t ∷[ r ] B →
               γ ▸ Γ ⊢ lam p t ∷[ r ] Π p , q ▷ A ▹ B
    app      : γ ▸ Γ ⊢ t ∷[ r ] Π p , q ▷ A ▹ B →
               γ ▸ Γ ⊢ u ∷[ r · p ] A →
               γ ▸ Γ ⊢ t ∘⟨ p ⟩ u ∷[ r ] B [ u ]₀

    prod     : Σ-allowed s p q →
               Γ »∙ A ⊢ B →
               γ ▸ Γ ⊢ t ∷[ r · p ] A →
               γ ▸ Γ ⊢ u ∷[ r ] B [ t ]₀ →
               γ ▸ Γ ⊢ prod s p t u ∷[ r ] Σ⟨ s ⟩ p , q ▷ A ▹ B
    fst      : p ≤ r →
               γ ▸ Γ ⊢ t ∷[ r ] Σˢ p , q ▷ A ▹ B →
               γ ▸ Γ ⊢ fst p t ∷[ r ] A
    snd      : γ ▸ Γ ⊢ t ∷[ r ] Σˢ p , q ▷ A ▹ B →
               γ ▸ Γ ⊢ snd p t ∷[ r ] B [ fst p t ]₀
    prodrec  : Prodrec-allowed ⌞ o ⌟ r p q →
               Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
               γ ▸ Γ ⊢ t ∷[ o · r ] Σʷ p , q′ ▷ A ▹ B →
               γ ∙ r · p ∙ r ▸ Γ »∙ A »∙ B ⊢ u ∷[ o ]
                 C [ prodʷ p (var x1) (var x0) ]↑² →
               γ ▸ Γ ⊢ prodrec r p q C t u ∷[ o ] C [ t ]₀

    ℕ        : ⊢ Γ →
               γ ▸ Γ ⊢ ℕ ∷[ p ] U zeroᵘ
    zero     : ⊢ Γ →
               γ ▸ Γ ⊢ zero ∷[ p ] ℕ
    suc      : γ ▸ Γ ⊢ t ∷[ p ] ℕ →
               γ ▸ Γ ⊢ suc t ∷[ p ] ℕ
    natrec   : Γ »∙ ℕ ⊢ A →
               γ ▸ Γ ⊢ t ∷[ o ] A [ zero ]₀ →
               γ ∙ p ∙ r ▸ Γ »∙ ℕ »∙ A ⊢ u ∷[ o ] A [ suc (var x1) ]↑² →
               γ ▸ Γ ⊢ v ∷[ o ] ℕ →
               γ ▸ Γ ⊢ natrec p q r A t u v ∷[ o ] A [ v ]₀

    Id       : (Id-erased → δ PE.≡ 𝟘ᶜ × p′ PE.≡ 𝟘) →
               (¬ Id-erased → δ PE.≡ γ × p′ PE.≡ p) →
               δ ▸ Γ ⊢ A ∷[ p′ ] U l →
               δ ▸ Γ ⊢ t ∷[ p′ ] A →
               δ ▸ Γ ⊢ u ∷[ p′ ] A →
               γ ▸ Γ ⊢ Id A t u ∷[ p ] U l
    rfl      : Γ ⊢ t ∷ A →
               γ ▸ Γ ⊢ rfl ∷[ p ] Id A t t
    J        : (erased-matches-for-J ⌞ r ⌟ ≤ᵉᵐ some →
                (erased-matches-for-J ⌞ r ⌟ PE.≡ some →
                 ¬ (p PE.≡ 𝟘 × q PE.≡ 𝟘)) →
                δ₁ PE.≡ γ ∙ p ∙ q × δ₂ PE.≡ γ ×
                r₁ PE.≡ r × r₂ PE.≡ r) →
               (erased-matches-for-J ⌞ r ⌟ PE.≡ some →
                p PE.≡ 𝟘 → q PE.≡ 𝟘 →
                δ₁ PE.≡ γ ∙ 𝟘 ∙ 𝟘 × δ₂ PE.≡ 𝟘ᶜ ×
                r₁ PE.≡ r × r₂ PE.≡ 𝟘) →
               (erased-matches-for-J ⌞ r ⌟ PE.≡ all →
                δ₁ PE.≡ 𝟘ᶜ × δ₂ PE.≡ 𝟘ᶜ ×
                r₁ PE.≡ 𝟘 × r₂ PE.≡ 𝟘) →
               Γ ⊢ A →
               δ₂ ▸ Γ ⊢ t ∷[ r₂ ] A →
               δ₁ ▸ Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢[ r₁ ] B →
               γ ▸ Γ ⊢ u ∷[ r ] B [ t , rfl ]₁₀ →
               δ₂ ▸ Γ ⊢ v ∷[ r₂ ] A →
               δ₂ ▸ Γ ⊢ w ∷[ r₂ ] Id A t v →
               γ ▸ Γ ⊢ J p q A t B u v w ∷[ r ] B [ v , w ]₁₀
    K        : (erased-matches-for-K ⌞ r ⌟ ≤ᵉᵐ some →
                (erased-matches-for-K ⌞ r ⌟ PE.≡ some → p PE.≢ 𝟘) →
                δ₁ PE.≡ γ ∙ p × δ₂ PE.≡ γ ×
                r₁ PE.≡ r × r₂ PE.≡ r) →
               (erased-matches-for-K ⌞ r ⌟ PE.≡ some →
                p PE.≡ 𝟘 →
                δ₁ PE.≡ γ ∙ 𝟘 × δ₂ PE.≡ 𝟘ᶜ ×
                r₁ PE.≡ r × r₂ PE.≡ 𝟘) →
               (erased-matches-for-K ⌞ r ⌟ PE.≡ all →
                δ₁ PE.≡ 𝟘ᶜ × δ₂ PE.≡ 𝟘ᶜ ×
                r₁ PE.≡ 𝟘 × r₂ PE.≡ 𝟘) →
               K-allowed →
               Γ ⊢ A →
               δ₂ ▸ Γ ⊢ t ∷[ r₂ ] A →
               δ₁ ▸ Γ »∙ Id A t t ⊢[ r₁ ] B →
               γ ▸ Γ ⊢ u ∷[ r ] B [ rfl ]₀ →
               δ₂ ▸ Γ ⊢ v ∷[ r₂ ] Id A t t →
               γ ▸ Γ ⊢ K p A t B u v ∷[ r ] B [ v ]₀
    []-cong  : []-cong-allowed s →
               []-cong-allowed-mode s ⌞ p ⌟ →
               Γ ⊢ l ∷Level →
               Γ ⊢ A →
               Γ ⊢ t ∷ A →
               Γ ⊢ u ∷ A →
               Γ ⊢ v ∷ Id A t u →
               let open Erased s in
               γ ▸ Γ ⊢ []-cong s l A t u v ∷[ p ]
                 Id (Erased l A) [ t ] ([ u ])

  -- Well-typed levels.

  data _⊢_∷Level (Γ : Cons m n) (l : Term n) : Set where
    term    : Level-allowed → Γ ⊢ l ∷ Level → Γ ⊢ l ∷Level
    literal : ¬ Level-allowed → ⊢ Γ → Level-literal l → Γ ⊢ l ∷Level

  -- Type equality.

  data _⊢_≡_ (Γ : Cons m n) : Term n → Term n → Set where
    refl      : Γ ⊢ A →
                Γ ⊢ A ≡ A
    sym       : Γ ⊢ A₁ ≡ A₂ →
                Γ ⊢ A₂ ≡ A₁
    trans     : Γ ⊢ A₁ ≡ A₂ →
                Γ ⊢ A₂ ≡ A₃ →
                Γ ⊢ A₁ ≡ A₃
    U-cong    : Γ ⊢ l₁ ≡ l₂ ∷ Level →
                Γ ⊢ U l₁ ≡ U l₂
    univ      : Γ ⊢ A₁ ≡ A₂ ∷ U l →
                Γ ⊢ A₁ ≡ A₂
    Lift-cong : Γ ⊢ l₁ ≡ l₂ ∷Level →
                Γ ⊢ A₁ ≡ A₂ →
                Γ ⊢ Lift l₁ A₁ ≡ Lift l₂ A₂
    ΠΣ-cong   : ΠΣ-allowed b p q →
                Γ ⊢ A₁ ≡ A₂ →
                Γ »∙ A₁ ⊢ B₁ ≡ B₂ →
                Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂
    Id-cong   : Γ ⊢ A₁ ≡ A₂ →
                Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
                Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
                Γ ⊢ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂

  -- Term equality.

  data _⊢_≡_∷_ (Γ : Cons m n) : Term n → Term n → Term n → Set where
    conv : Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
           Γ ⊢ A₁ ≡ A₂ →
           Γ ⊢ t₁ ≡ t₂ ∷ A₂

    refl  : Γ ⊢ t ∷ A →
            Γ ⊢ t ≡ t ∷ A
    sym   : Γ ⊢ t₁ ≡ t₂ ∷ A →
            Γ ⊢ t₂ ≡ t₁ ∷ A
    trans : Γ ⊢ t₁ ≡ t₂ ∷ A →
            Γ ⊢ t₂ ≡ t₃ ∷ A →
            Γ ⊢ t₁ ≡ t₃ ∷ A

    δ-red : ⊢ Γ →
            α ↦ t′ ∷ A′ ∈ Γ .defs →
            A PE.≡ wk wk₀ A′ →
            t PE.≡ wk wk₀ t′ →
            Γ ⊢ defn α ≡ t ∷ A

    sucᵘ-cong  : Γ ⊢ l₁ ≡ l₂ ∷ Level →
                 Γ ⊢ sucᵘ l₁ ≡ sucᵘ l₂ ∷ Level
    supᵘ-cong  : Γ ⊢ l₁₁ ≡ l₂₁ ∷ Level →
                 Γ ⊢ l₁₂ ≡ l₂₂ ∷ Level →
                 Γ ⊢ l₁₁ supᵘ l₁₂ ≡ l₂₁ supᵘ l₂₂ ∷ Level
    supᵘ-zeroˡ : Γ ⊢ l ∷ Level →
                 Γ ⊢ zeroᵘ supᵘ l ≡ l ∷ Level
    supᵘ-sucᵘ  : Γ ⊢ l₁ ∷ Level →
                 Γ ⊢ l₂ ∷ Level →
                 Γ ⊢ sucᵘ l₁ supᵘ sucᵘ l₂ ≡ sucᵘ (l₁ supᵘ l₂) ∷ Level
    supᵘ-assoc : Γ ⊢ l₁ ∷ Level →
                 Γ ⊢ l₂ ∷ Level →
                 Γ ⊢ l₃ ∷ Level →
                 Γ ⊢ (l₁ supᵘ l₂) supᵘ l₃ ≡ l₁ supᵘ (l₂ supᵘ l₃) ∷ Level
    supᵘ-comm  : Γ ⊢ l₁ ∷ Level →
                 Γ ⊢ l₂ ∷ Level →
                 Γ ⊢ l₁ supᵘ l₂ ≡ l₂ supᵘ l₁ ∷ Level
    supᵘ-idem  : Γ ⊢ l ∷ Level →
                 Γ ⊢ l supᵘ l ≡ l ∷ Level
    supᵘ-sub   : Γ ⊢ l ∷ Level →
                 Γ ⊢ l supᵘ sucᵘ l ≡ sucᵘ l ∷ Level

    U-cong : Γ ⊢ l₁ ≡ l₂ ∷ Level →
             Γ ⊢ U l₁ ≡ U l₂ ∷ U (sucᵘ l₁)

    Lift-cong  : Γ ⊢ l₂₁ ≡ l₂₂ ∷Level →
                 Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
                 Γ ⊢ Lift l₂₁ A₁ ≡ Lift l₂₂ A₂ ∷ U (l₁ supᵘₗ l₂₁)
    lower-cong : Γ ⊢ t₁ ≡ t₂ ∷ Lift l A →
                 Γ ⊢ lower t₁ ≡ lower t₂ ∷ A
    Lift-β     : Γ ⊢ t ∷ A →
                 Γ ⊢ lower (lift t) ≡ t ∷ A
    Lift-η     : Γ ⊢ t₁ ∷ Lift l A →
                 Γ ⊢ t₂ ∷ Lift l A →
                 Γ ⊢ lower t₁ ≡ lower t₂ ∷ A →
                 Γ ⊢ t₁ ≡ t₂ ∷ Lift l A

    emptyrec-cong : Γ ⊢ A₁ ≡ A₂ →
                    Γ ⊢ t₁ ≡ t₂ ∷ Empty →
                    Γ ⊢ emptyrec p A₁ t₁ ≡ emptyrec p A₂ t₂ ∷ A₁

    η-unit : Unit-with-η s →
             Γ ⊢ t₁ ∷ Unit s →
             Γ ⊢ t₂ ∷ Unit s →
             Γ ⊢ t₁ ≡ t₂ ∷ Unit s

    unitrec-cong : ¬ Unitʷ-η →
                   Γ »∙ Unitʷ ⊢ A₁ ≡ A₂ →
                   Γ ⊢ t₁ ≡ t₂ ∷ Unitʷ →
                   Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ starʷ ]₀ →
                   Γ ⊢ unitrec p q A₁ t₁ u₁ ≡ unitrec p q A₂ t₂ u₂ ∷
                     A₁ [ t₁ ]₀
    unitrec-β    : ¬ Unitʷ-η →
                   Γ »∙ Unitʷ ⊢ A →
                   Γ ⊢ t ∷ A [ starʷ ]₀ →
                   Γ ⊢ unitrec p q A starʷ t ≡ t ∷ A [ starʷ ]₀
    unitrec-β-η  : Unitʷ-η →
                   Γ »∙ Unitʷ ⊢ A →
                   Γ ⊢ t ∷ Unitʷ →
                   Γ ⊢ u ∷ A [ starʷ ]₀ →
                   Γ ⊢ unitrec p q A t u ≡ u ∷ A [ t ]₀

    ΠΣ-cong : ΠΣ-allowed b p q →
              Γ ⊢ A₁ ≡ A₂ ∷ U l →
              Γ »∙ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk1 l) →
              Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷
                U l

    app-cong : Γ ⊢ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B →
               Γ ⊢ u₁ ≡ u₂ ∷ A →
               Γ ⊢ t₁ ∘⟨ p ⟩ u₁ ≡ t₂ ∘⟨ p ⟩ u₂ ∷ B [ u₁ ]₀
    β-red    : Π-allowed p q →
               Γ »∙ A ⊢ t ∷ B →
               Γ ⊢ u ∷ A →
               Γ ⊢ lam p t ∘⟨ p ⟩ u ≡ t [ u ]₀ ∷ B [ u ]₀
    η-eq     : Γ ⊢ t₁ ∷ Π p , q ▷ A ▹ B →
               Γ ⊢ t₂ ∷ Π p , q ▷ A ▹ B →
               Γ »∙ A ⊢ wk1 t₁ ∘⟨ p ⟩ var x0 ≡ wk1 t₂ ∘⟨ p ⟩ var x0 ∷
                 B →
               Γ ⊢ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B

    prod-cong : Σ-allowed s p q →
                Γ »∙ A ⊢ B →
                Γ ⊢ t₁ ≡ t₂ ∷ A →
                Γ ⊢ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
                Γ ⊢ prod s p t₁ u₁ ≡ prod s p t₂ u₂ ∷
                  Σ⟨ s ⟩ p , q ▷ A ▹ B

    fst-cong : Γ ⊢ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B →
               Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A
    Σ-β₁     : Σˢ-allowed p q →
               Γ »∙ A ⊢ B →
               Γ ⊢ t ∷ A →
               Γ ⊢ u ∷ B [ t ]₀ →
               Γ ⊢ fst p (prodˢ p t u) ≡ t ∷ A
    snd-cong : Γ ⊢ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B →
               Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀
    Σ-β₂     : Σˢ-allowed p q →
               Γ »∙ A ⊢ B →
               Γ ⊢ t ∷ A →
               Γ ⊢ u ∷ B [ t ]₀ →
               Γ ⊢ snd p (prodˢ p t u) ≡ u ∷ B [ t ]₀
    Σ-η      : Γ ⊢ t₁ ∷ Σˢ p , q ▷ A ▹ B →
               Γ ⊢ t₂ ∷ Σˢ p , q ▷ A ▹ B →
               Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A →
               Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀ →
               Γ ⊢ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B

    prodrec-cong : Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C₁ ≡ C₂ →
                   Γ ⊢ t₁ ≡ t₂ ∷ Σʷ p , q′ ▷ A ▹ B →
                   Γ »∙ A »∙ B ⊢ u₁ ≡ u₂ ∷
                     C₁ [ prodʷ p (var x1) (var x0) ]↑² →
                   Γ ⊢ prodrec r p q C₁ t₁ u₁ ≡ prodrec r p q C₂ t₂ u₂ ∷
                     C₁ [ t₁ ]₀
    prodrec-β    : Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
                   Γ ⊢ t ∷ A →
                   Γ ⊢ u ∷ B [ t ]₀ →
                   Γ »∙ A »∙ B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
                   Γ ⊢ prodrec r p q C (prodʷ p t u) v ≡ v [ t , u ]₁₀ ∷
                     C [ prodʷ p t u ]₀

    suc-cong    : Γ ⊢ t₁ ≡ t₂ ∷ ℕ →
                  Γ ⊢ suc t₁ ≡ suc t₂ ∷ ℕ
    natrec-cong : Γ »∙ ℕ ⊢ A₁ ≡ A₂ →
                  Γ ⊢ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
                  Γ »∙ ℕ »∙ A₁ ⊢ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
                  Γ ⊢ v₁ ≡ v₂ ∷ ℕ →
                  Γ ⊢
                    natrec p q r A₁ t₁ u₁ v₁ ≡
                    natrec p q r A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
    natrec-zero : Γ ⊢ t ∷ A [ zero ]₀ →
                  Γ »∙ ℕ »∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
                  Γ ⊢ natrec p q r A t u zero ≡ t ∷ A [ zero ]₀
    natrec-suc   : Γ ⊢ t ∷ A [ zero ]₀ →
                   Γ »∙ ℕ »∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
                   Γ ⊢ v ∷ ℕ →
                   Γ ⊢
                     natrec p q r A t u (suc v) ≡
                     u [ v , natrec p q r A t u v ]₁₀ ∷ A [ suc v ]₀

    Id-cong             : Γ ⊢ A₁ ≡ A₂ ∷ U l →
                          Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
                          Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
                          Γ ⊢ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U l
    J-cong              : Γ ⊢ A₁ ≡ A₂ →
                          Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
                          Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢
                            B₁ ≡ B₂ →
                          Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
                          Γ ⊢ v₁ ≡ v₂ ∷ A₁ →
                          Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ →
                          Γ ⊢
                            J p q A₁ t₁ B₁ u₁ v₁ w₁ ≡
                            J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷ B₁ [ v₁ , w₁ ]₁₀
    J-β                 : Γ ⊢ t ∷ A →
                          Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
                          Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
                          Γ ⊢ J p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀
    K-cong              : K-allowed →
                          Γ ⊢ A₁ ≡ A₂ →
                          Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
                          Γ »∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂ →
                          Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀ →
                          Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ →
                          Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ≡ K p A₂ t₂ B₂ u₂ v₂ ∷
                            B₁ [ v₁ ]₀
    K-β                 : K-allowed →
                          Γ »∙ Id A t t ⊢ B →
                          Γ ⊢ u ∷ B [ rfl ]₀ →
                          Γ ⊢ K p A t B u rfl ≡ u ∷ B [ rfl ]₀
    []-cong-cong        : []-cong-allowed s →
                          Γ ⊢ l₁ ≡ l₂ ∷Level →
                          Γ ⊢ A₁ ≡ A₂ →
                          Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
                          Γ ⊢ u₁ ≡ u₂ ∷ A₁ →
                          Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ →
                          let open Erased s in
                          Γ ⊢
                            []-cong s l₁ A₁ t₁ u₁ v₁ ≡
                            []-cong s l₂ A₂ t₂ u₂ v₂ ∷
                            Id (Erased l₁ A₁) [ t₁ ] ([ u₁ ])
    []-cong-β           : []-cong-allowed s →
                          Γ ⊢ l ∷Level →
                          Γ ⊢ t ∷ A →
                          let open Erased s in
                          Γ ⊢ []-cong s l A t t rfl ≡ rfl ∷
                            Id (Erased l A) [ t ] ([ t ])
    equality-reflection : Equality-reflection →
                          Γ ⊢ v ∷ Id A t u →
                          Γ ⊢ t ≡ u ∷ A

  -- Level equality.

  data _⊢_≡_∷Level (Γ : Cons m n) (l₁ l₂ : Term n) : Set where
    term    : Level-allowed → Γ ⊢ l₁ ≡ l₂ ∷ Level → Γ ⊢ l₁ ≡ l₂ ∷Level
    literal : ¬ Level-allowed → ⊢ Γ → Level-literal l₁ → l₁ PE.≡ l₂ →
              Γ ⊢ l₁ ≡ l₂ ∷Level

pattern literal! not-ok ⊢Γ l-lit = literal not-ok ⊢Γ l-lit PE.refl

-- Well-formed substitutions.

infixl 24 _∙_
infix   4 _▸_⊢ˢʷ_∷[_]_

data _▸_⊢ˢʷ_∷[_]_ (δ : Conₘ m) (Δ : Cons k m) :
       Subst m n → Erasure → Con Term n → Set where
  ε   : ⊢ Δ → δ ▸ Δ ⊢ˢʷ σ ∷[ p ] ε
  _∙_ : ∀ {Γ} → δ ▸ Δ ⊢ˢʷ tail σ ∷[ p ] Γ →
        δ ▸ Δ ⊢ head σ ∷[ p ] A [ tail σ ] →
        δ ▸ Δ ⊢ˢʷ σ ∷[ p ] Γ ∙ A
