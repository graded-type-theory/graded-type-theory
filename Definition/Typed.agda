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

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant

import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Fin
open import Tools.Nat
open import Tools.Product hiding (_,_)
import Tools.PropositionalEquality as PE
open import Tools.Relation


infixl 24 _∙_

private
  variable
    n : Nat
    Γ : Con Term _
    A A₁ A₂ A′ B B₁ B₂ C E F F′ G H : Term _
    a f g m n′ s s′ t t₁ t₂ t′ u u₁ u₂ u′ v v₁ v₂ v′ w w₁ w₂ w′ z z′ :
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
    Unitⱼ  : ⊢ Γ → Unit-allowed k → Γ ⊢ Unit k
    ΠΣⱼ    : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → ΠΣ-allowed b p q
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
    Idⱼ    : Γ ⊢ t ∷ A
           → Γ ⊢ u ∷ A
           → Γ ⊢ Id A t u
    univ   : Γ ⊢ A ∷ U
           → Γ ⊢ A

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
    ΠΣⱼ       : Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → ΠΣ-allowed b p q
              → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷ U
    ℕⱼ        : ⊢ Γ → Γ ⊢ ℕ ∷ U
    Emptyⱼ    : ⊢ Γ → Γ ⊢ Empty ∷ U
    Unitⱼ     : ⊢ Γ → Unit-allowed k → Γ ⊢ Unit k ∷ U

    conv      : Γ ⊢ t ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t ∷ B

    var       : ⊢ Γ
              → x ∷ A ∈ Γ
              → Γ ⊢ var x ∷ A

    lamⱼ      : Γ     ⊢ F
              → Γ ∙ F ⊢ t ∷ G
              → Π-allowed p q
              → Γ     ⊢ lam p t ∷ Π p , q ▷ F ▹ G
    _∘ⱼ_      : Γ ⊢ t ∷ Π p , q ▷ F ▹ G
              → Γ ⊢ u ∷ F
              → Γ ⊢ t ∘⟨ p ⟩ u ∷ G [ u ]₀

    prodⱼ     : Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ F
              → Γ ⊢ u ∷ G [ t ]₀
              → Σ-allowed k p q
              → Γ ⊢ prod k p t u ∷ Σ⟨ k ⟩ p , q ▷ F ▹ G
    fstⱼ      : Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G
              → Γ ⊢ fst p t ∷ F
    sndⱼ      : Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G
              → Γ ⊢ snd p t ∷ G [ fst p t ]₀
    prodrecⱼ  : Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ∙ (Σʷ p , q′ ▷ F ▹ G) ⊢ A
              → Γ ⊢ t ∷ Σʷ p , q′ ▷ F ▹ G
              → Γ ∙ F ∙ G ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑²
              → Σʷ-allowed p q′
              → Γ ⊢ prodrec r p q A t u ∷ A [ t ]₀
    zeroⱼ     : ⊢ Γ
              → Γ ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {n}
              → Γ ⊢     n ∷ ℕ
              → Γ ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {n}
              → Γ ∙ ℕ     ⊢ A
              → Γ         ⊢ z ∷ A [ zero ]₀
              → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
              → Γ         ⊢ n ∷ ℕ
              → Γ         ⊢ natrec p q r A z s n ∷ A [ n ]₀

    emptyrecⱼ : Γ ⊢ A → Γ ⊢ t ∷ Empty → Γ ⊢ emptyrec p A t ∷ A

    starⱼ     : ⊢ Γ → Unit-allowed k → Γ ⊢ star k ∷ Unit k
    unitrecⱼ  : Γ ∙ Unitʷ ⊢ A
              → Γ ⊢ t ∷ Unitʷ
              → Γ ⊢ u ∷ A [ starʷ ]₀
              → Unitʷ-allowed
              → Γ ⊢ unitrec p q A t u ∷ A [ t ]₀

    Idⱼ       : Γ ⊢ A ∷ U
              → Γ ⊢ t ∷ A
              → Γ ⊢ u ∷ A
              → Γ ⊢ Id A t u ∷ U
    rflⱼ      : Γ ⊢ t ∷ A
              → Γ ⊢ rfl ∷ Id A t t
    Jⱼ        : Γ ⊢ A
              → Γ ⊢ t ∷ A
              → Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B
              → Γ ⊢ u ∷ B [ t , rfl ]₁₀
              → Γ ⊢ v ∷ A
              → Γ ⊢ w ∷ Id A t v
              → Γ ⊢ J p q A t B u v w ∷ B [ v , w ]₁₀
    Kⱼ        : Γ ⊢ t ∷ A
              → Γ ∙ Id A t t ⊢ B
              → Γ ⊢ u ∷ B [ rfl ]₀
              → Γ ⊢ v ∷ Id A t t
              → K-allowed
              → Γ ⊢ K p A t B u v ∷ B [ v ]₀
    []-congⱼ  : Γ ⊢ t ∷ A
              → Γ ⊢ u ∷ A
              → Γ ⊢ v ∷ Id A t u
              → []-cong-allowed k
              → let open Erased k in
                Γ ⊢ []-cong k A t u v ∷
                  Id (Erased A) ([ t ]) ([ u ])

  -- Type equality
  data _⊢_≡_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
    univ   : Γ ⊢ A ≡ B ∷ U
           → Γ ⊢ A ≡ B
    refl   : Γ ⊢ A
           → Γ ⊢ A ≡ A
    sym    : Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ A
    trans  : Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ C
           → Γ ⊢ A ≡ C
    ΠΣ-cong
           : Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → ΠΣ-allowed b p q
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡ ΠΣ⟨ b ⟩ p , q ▷ H ▹ E
    Id-cong
           : Γ ⊢ A₁ ≡ A₂
           → Γ ⊢ t₁ ≡ t₂ ∷ A₁
           → Γ ⊢ u₁ ≡ u₂ ∷ A₁
           → Γ ⊢ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂

  -- Term equality
  data _⊢_≡_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
    refl          : Γ ⊢ t ∷ A
                  → Γ ⊢ t ≡ t ∷ A
    sym           : Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ t ∷ A
    trans         : Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ v ∷ A
                  → Γ ⊢ t ≡ v ∷ A
    conv          : Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ A ≡ B
                  → Γ ⊢ t ≡ u ∷ B
    ΠΣ-cong       : Γ     ⊢ F
                  → Γ     ⊢ F ≡ H ∷ U
                  → Γ ∙ F ⊢ G ≡ E ∷ U
                  → ΠΣ-allowed b p q
                  → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡
                            ΠΣ⟨ b ⟩ p , q ▷ H ▹ E ∷ U
    app-cong      : ∀ {b}
                  → Γ ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
                  → Γ ⊢ a ≡ b ∷ F
                  → Γ ⊢ f ∘⟨ p ⟩ a ≡ g ∘⟨ p ⟩ b ∷ G [ a ]₀
    β-red         : Γ     ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ F ⊢ t ∷ G
                  → Γ     ⊢ a ∷ F
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Π-allowed p q
                  → Γ     ⊢ lam p t ∘⟨ p′ ⟩ a ≡ t [ a ]₀ ∷ G [ a ]₀
    η-eq          : Γ     ⊢ F
                  → Γ     ⊢ f ∷ Π p , q ▷ F ▹ G
                  → Γ     ⊢ g ∷ Π p , q ▷ F ▹ G
                  → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 ≡ wk1 g ∘⟨ p ⟩ var x0 ∷ G
                  → Γ     ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
    fst-cong      : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ Σˢ p , q ▷ F ▹ G
                  → Γ ⊢ fst p t ≡ fst p t′ ∷ F
    snd-cong      : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ F ▹ G
                  → Γ ⊢ snd p t ≡ snd p u ∷ G [ fst p t ]₀
    Σ-β₁          : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]₀
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Σˢ-allowed p q
                  → Γ ⊢ fst p (prodˢ p′ t u) ≡ t ∷ F
    Σ-β₂          : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]₀
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Σˢ-allowed p q
                  → Γ ⊢ snd p (prodˢ p′ t u) ≡ u ∷ G [ fst p (prodˢ p′ t u) ]₀
    Σ-η           : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G
                  → Γ ⊢ u ∷ Σˢ p , q ▷ F ▹ G
                  → Γ ⊢ fst p t ≡ fst p u ∷ F
                  → Γ ⊢ snd p t ≡ snd p u ∷ G [ fst p t ]₀
                  → Γ ⊢ t ≡ u ∷ Σˢ p , q ▷ F ▹ G
    prod-cong     : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ F
                  → Γ ⊢ u ≡ u′ ∷ G [ t ]₀
                  → Σ-allowed k p q
                  → Γ ⊢ prod k p t u ≡ prod k p t′ u′ ∷ Σ⟨ k ⟩ p , q ▷ F ▹ G
    prodrec-cong  : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ (Σʷ p , q′ ▷ F ▹ G) ⊢ A ≡ A′
                  → Γ ⊢ t ≡ t′ ∷ Σʷ p , q′ ▷ F ▹ G
                  → Γ ∙ F ∙ G ⊢ u ≡ u′ ∷ A [ prodʷ p (var x1) (var x0) ]↑²
                  → Σʷ-allowed p q′
                  → Γ ⊢ prodrec r p q A t u ≡ prodrec r p q A′ t′ u′ ∷ A [ t ]₀
    prodrec-β     : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ (Σʷ p , q′ ▷ F ▹ G) ⊢ A
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ t′ ∷ G [ t ]₀
                  → Γ ∙ F ∙ G ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑²
                  → p PE.≡ p′
                  → Σʷ-allowed p q′
                  → Γ ⊢ prodrec r p q A (prodʷ p′ t t′) u ≡
                        u [ t , t′ ]₁₀ ∷ A [ prodʷ p′ t t′ ]₀
    suc-cong      : ∀ {n}
                  → Γ ⊢ m ≡ n ∷ ℕ
                  → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {n}
                  → Γ ∙ ℕ     ⊢ A
                  → Γ ∙ ℕ     ⊢ A ≡ A′
                  → Γ         ⊢ z ≡ z′ ∷ A [ zero ]₀
                  → Γ ∙ ℕ ∙ A ⊢ s ≡ s′ ∷ A [ suc (var x1) ]↑²
                  → Γ         ⊢ n ≡ n′ ∷ ℕ
                  → Γ         ⊢ natrec p q r A z s n ≡
                                natrec p q r A′ z′ s′ n′ ∷
                                A [ n ]₀
    natrec-zero   : Γ ∙ ℕ     ⊢ A
                  → Γ         ⊢ z ∷ A [ zero ]₀
                  → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                  → Γ         ⊢ natrec p q r A z s zero ≡ z ∷ A [ zero ]₀
    natrec-suc    : ∀ {n}
                  → Γ ∙ ℕ     ⊢ A
                  → Γ         ⊢ z ∷ A [ zero ]₀
                  → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                  → Γ         ⊢ n ∷ ℕ
                  → Γ         ⊢ natrec p q r A z s (suc n) ≡
                                s [ n , natrec p q r A z s n ]₁₀ ∷
                                A [ suc n ]₀
    emptyrec-cong : Γ ⊢ A ≡ B
                  → Γ ⊢ t ≡ u ∷ Empty
                  → Γ ⊢ emptyrec p A t ≡ emptyrec p B u ∷ A
    unitrec-cong  : Γ ∙ Unitʷ ⊢ A ≡ A′
                  → Γ ⊢ t ≡ t′ ∷ Unitʷ
                  → Γ ⊢ u ≡ u′ ∷ A [ starʷ ]₀
                  → Unitʷ-allowed
                  → Γ ⊢ unitrec p q A t u ≡ unitrec p q A′ t′ u′ ∷ A [ t ]₀
    unitrec-β     : Γ ∙ Unitʷ ⊢ A
                  → Γ ⊢ u ∷ A [ starʷ ]₀
                  → Unitʷ-allowed
                  → ¬ Unitʷ-η
                  → Γ ⊢ unitrec p q A starʷ u ≡ u ∷ A [ starʷ ]₀
    unitrec-β-η   : Γ ∙ Unitʷ ⊢ A
                  → Γ ⊢ t ∷ Unitʷ
                  → Γ ⊢ u ∷ A [ starʷ ]₀
                  → Unitʷ-allowed
                  → Unitʷ-η
                  → Γ ⊢ unitrec p q A t u ≡ u ∷ A [ t ]₀
    η-unit        : Γ ⊢ t ∷ Unit k
                  → Γ ⊢ t′ ∷ Unit k
                  → Unit-with-η k
                  → Γ ⊢ t ≡ t′ ∷ Unit k
    Id-cong       : Γ ⊢ A₁ ≡ A₂ ∷ U
                  → Γ ⊢ t₁ ≡ t₂ ∷ A₁
                  → Γ ⊢ u₁ ≡ u₂ ∷ A₁
                  → Γ ⊢ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U
    J-cong        : Γ ⊢ A₁
                  → Γ ⊢ A₁ ≡ A₂
                  → Γ ⊢ t₁ ∷ A₁
                  → Γ ⊢ t₁ ≡ t₂ ∷ A₁
                  → Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≡ B₂
                  → Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀
                  → Γ ⊢ v₁ ≡ v₂ ∷ A₁
                  → Γ ⊢ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁
                  → Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ≡
                        J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷ B₁ [ v₁ , w₁ ]₁₀
    K-cong        : Γ ⊢ A₁ ≡ A₂
                  → Γ ⊢ t₁ ∷ A₁
                  → Γ ⊢ t₁ ≡ t₂ ∷ A₁
                  → Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ ≡ B₂
                  → Γ ⊢ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀
                  → Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁
                  → K-allowed
                  → Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ≡ K p A₂ t₂ B₂ u₂ v₂ ∷
                      B₁ [ v₁ ]₀
    []-cong-cong  : Γ ⊢ A₁ ≡ A₂
                  → Γ ⊢ t₁ ≡ t₂ ∷ A₁
                  → Γ ⊢ u₁ ≡ u₂ ∷ A₁
                  → Γ ⊢ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁
                  → []-cong-allowed k
                  → let open Erased k in
                    Γ ⊢ []-cong k A₁ t₁ u₁ v₁ ≡ []-cong k A₂ t₂ u₂ v₂ ∷
                      Id (Erased A₁) ([ t₁ ]) ([ u₁ ])
    J-β           : Γ ⊢ A
                  → Γ ⊢ t ∷ A
                  → Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B
                  → Γ ⊢ u ∷ B [ t , rfl ]₁₀
                  → t PE.≡ t′
                  → Γ ⊢ J p q A t B u t′ rfl ≡ u ∷ B [ t , rfl ]₁₀
    K-β           : Γ ⊢ t ∷ A
                  → Γ ∙ Id A t t ⊢ B
                  → Γ ⊢ u ∷ B [ rfl ]₀
                  → K-allowed
                  → Γ ⊢ K p A t B u rfl ≡ u ∷ B [ rfl ]₀
    []-cong-β     : Γ ⊢ t ∷ A
                  → t PE.≡ t′
                  → []-cong-allowed k
                  → let open Erased k in
                    Γ ⊢ []-cong k A t t′ rfl ≡ rfl ∷
                      Id (Erased A) ([ t ]) ([ t′ ])


-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
  conv           : Γ ⊢ t ⇒ u ∷ A
                 → Γ ⊢ A ≡ B
                 → Γ ⊢ t ⇒ u ∷ B
  app-subst      : Γ ⊢ t ⇒ u ∷ Π p , q ▷ F ▹ G
                 → Γ ⊢ a ∷ F
                 → Γ ⊢ t ∘⟨ p ⟩ a ⇒ u ∘⟨ p ⟩ a ∷ G [ a ]₀
  β-red          : Γ     ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ F ⊢ t ∷ G
                 → Γ     ⊢ a ∷ F
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Π-allowed p q
                 → Γ     ⊢ lam p t ∘⟨ p′ ⟩ a ⇒ t [ a ]₀ ∷ G [ a ]₀
  fst-subst      : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ u ∷ Σˢ p , q ▷ F ▹ G
                 → Γ ⊢ fst p t ⇒ fst p u ∷ F
  snd-subst      : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ u ∷ Σˢ p , q ▷ F ▹ G
                 → Γ ⊢ snd p t ⇒ snd p u ∷ G [ fst p t ]₀
  Σ-β₁           : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]₀
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Σˢ-allowed p q
                 → Γ ⊢ fst p (prodˢ p′ t u) ⇒ t ∷ F
  Σ-β₂           : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]₀
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Σˢ-allowed p q
                 → Γ ⊢ snd p (prodˢ p′ t u) ⇒ u ∷ G [ fst p (prodˢ p′ t u) ]₀
  prodrec-subst  : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ (Σʷ p , q′ ▷ F ▹ G) ⊢ A
                 → Γ ∙ F ∙ G ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑²
                 → Γ ⊢ t ⇒ t′ ∷ Σʷ p , q′ ▷ F ▹ G
                 → Σʷ-allowed p q′
                 → Γ ⊢ prodrec r p q A t u ⇒ prodrec r p q A t′ u ∷ A [ t ]₀
  prodrec-β      : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ (Σʷ p , q′ ▷ F ▹ G) ⊢ A
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ t′ ∷ G [ t ]₀
                 → Γ ∙ F ∙ G ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑²
                 → p PE.≡ p′
                 → Σʷ-allowed p q′
                 → Γ ⊢ prodrec r p q A (prodʷ p′ t t′) u ⇒
                       u [ t , t′ ]₁₀ ∷ A [ prodʷ p′ t t′ ]₀
  natrec-subst   : ∀ {n}
                 → Γ ∙ ℕ     ⊢ A
                 → Γ         ⊢ z ∷ A [ zero ]₀
                 → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ         ⊢ n ⇒ n′ ∷ ℕ
                 → Γ         ⊢ natrec p q r A z s n ⇒
                               natrec p q r A z s n′ ∷
                               A [ n ]₀
  natrec-zero    : Γ ∙ ℕ     ⊢ A
                 → Γ         ⊢ z ∷ A [ zero ]₀
                 → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ         ⊢ natrec p q r A z s zero ⇒ z ∷ A [ zero ]₀
  natrec-suc     : ∀ {n}
                 → Γ ∙ ℕ     ⊢ A
                 → Γ         ⊢ z ∷ A [ zero ]₀
                 → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ         ⊢ n ∷ ℕ
                 → Γ         ⊢ natrec p q r A z s (suc n) ⇒
                               s [ n , natrec p q r A z s n ]₁₀ ∷
                               A [ suc n ]₀
  emptyrec-subst : ∀ {n}
                 → Γ ⊢ A
                 → Γ     ⊢ n ⇒ n′ ∷ Empty
                 → Γ     ⊢ emptyrec p A n ⇒ emptyrec p A n′ ∷ A
  unitrec-subst : Γ ∙ Unitʷ ⊢ A
                → Γ ⊢ u ∷ A [ starʷ ]₀
                → Γ ⊢ t ⇒ t′ ∷ Unitʷ
                → Unitʷ-allowed
                → ¬ Unitʷ-η
                → Γ ⊢ unitrec p q A t u ⇒ unitrec p q A t′ u ∷ A [ t ]₀
  unitrec-β     : Γ ∙ Unitʷ ⊢ A
                → Γ ⊢ u ∷ A [ starʷ ]₀
                → Unitʷ-allowed
                → ¬ Unitʷ-η
                → Γ ⊢ unitrec p q A starʷ u ⇒ u ∷ A [ starʷ ]₀
  unitrec-β-η   : Γ ∙ Unitʷ ⊢ A
                → Γ ⊢ t ∷ Unitʷ
                → Γ ⊢ u ∷ A [ starʷ ]₀
                → Unitʷ-allowed
                → Unitʷ-η
                → Γ ⊢ unitrec p q A t u ⇒ u ∷ A [ t ]₀
  J-subst        : Γ ⊢ A
                 → Γ ⊢ t ∷ A
                 → Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B
                 → Γ ⊢ u ∷ B [ t , rfl ]₁₀
                 → Γ ⊢ v ∷ A
                 → Γ ⊢ w₁ ⇒ w₂ ∷ Id A t v
                 → Γ ⊢ J p q A t B u v w₁ ⇒ J p q A t B u v w₂ ∷
                     B [ v , w₁ ]₁₀
  K-subst        : Γ ⊢ A
                 → Γ ⊢ t ∷ A
                 → Γ ∙ Id A t t ⊢ B
                 → Γ ⊢ u ∷ B [ rfl ]₀
                 → Γ ⊢ v₁ ⇒ v₂ ∷ Id A t t
                 → K-allowed
                 → Γ ⊢ K p A t B u v₁ ⇒ K p A t B u v₂ ∷ B [ v₁ ]₀
  []-cong-subst  : Γ ⊢ A
                 → Γ ⊢ t ∷ A
                 → Γ ⊢ u ∷ A
                 → Γ ⊢ v₁ ⇒ v₂ ∷ Id A t u
                 → []-cong-allowed k
                 → let open Erased k in
                   Γ ⊢ []-cong k A t u v₁ ⇒ []-cong k A t u v₂ ∷
                     Id (Erased A) ([ t ]) ([ u ])
  J-β            : Γ ⊢ A
                 → Γ ⊢ t ∷ A
                 → Γ ⊢ t′ ∷ A
                 → Γ ⊢ t ≡ t′ ∷ A
                 → Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B
                 → Γ ⊢ B [ t , rfl ]₁₀ ≡ B [ t′ , rfl ]₁₀
                 → Γ ⊢ u ∷ B [ t , rfl ]₁₀
                 → Γ ⊢ J p q A t B u t′ rfl ⇒ u ∷ B [ t , rfl ]₁₀
  K-β            : Γ ⊢ t ∷ A
                 → Γ ∙ Id A t t ⊢ B
                 → Γ ⊢ u ∷ B [ rfl ]₀
                 → K-allowed
                 → Γ ⊢ K p A t B u rfl ⇒ u ∷ B [ rfl ]₀
  []-cong-β      : Γ ⊢ A
                 → Γ ⊢ t ∷ A
                 → Γ ⊢ t′ ∷ A
                 → Γ ⊢ t ≡ t′ ∷ A
                 → []-cong-allowed k
                 → let open Erased k in
                   Γ ⊢ []-cong k A t t′ rfl ⇒ rfl ∷
                     Id (Erased A) ([ t ]) ([ t′ ])

-- Type reduction
data _⊢_⇒_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
  univ : Γ ⊢ A ⇒ B ∷ U
       → Γ ⊢ A ⇒ B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
  id  : Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
  id  : Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : Γ ⊢ A  ⇒  A′
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
data _⊢ˢ_∷_ {k} (Δ : Con Term k) :
       (σ : Subst k n) (Γ : Con Term n) → Set ℓ where
  id  : Δ ⊢ˢ σ ∷ ε
  _,_ : Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢  head σ ∷ A [ tail σ ]
      → Δ ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ {k} (Δ : Con Term k) :
       (σ σ′ : Subst k n) (Γ : Con Term n) → Set ℓ where
  id  : Δ ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : Δ ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ ⊢  head σ ≡ head σ′ ∷ A [ tail σ ]
      → Δ ⊢ˢ      σ ≡ σ′      ∷ Γ ∙ A

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.

⟦_⟧ⱼ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F
     → Γ ∙ F ⊢ G
     → BindingType-allowed W
     → Γ     ⊢ ⟦ W ⟧ F ▹ G
⟦ BΠ _ _   ⟧ⱼ = ΠΣⱼ
⟦ BΣ _ _ _ ⟧ⱼ = ΠΣⱼ

⟦_⟧ⱼᵤ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F ∷ U
     → Γ ∙ F ⊢ G ∷ U
     → BindingType-allowed W
     → Γ     ⊢ ⟦ W ⟧ F ▹ G ∷ U
⟦ BΠ _ _   ⟧ⱼᵤ = ΠΣⱼ
⟦ BΣ _ _ _ ⟧ⱼᵤ = ΠΣⱼ

-- A context Γ is consistent if the empty type is not inhabited in Γ.

Consistent : Con Term n → Set ℓ
Consistent Γ = ∀ t → ¬ Γ ⊢ t ∷ Empty
