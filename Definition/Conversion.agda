------------------------------------------------------------------------
-- Algorithmic equality.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
  hiding (_∷_) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Typed R

open import Graded.Derived.Erased.Untyped 𝕄 as Erased using (Erased)

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
    A₁ A₂ B₁ B₂ C F H G E : Term n
    a₀ b₀ g h k l t t₁ t₂ u u₁ u₂ v v₁ v₂ w₁ w₂ : Term n
    x y : Fin n
    p p′ p″ p₁ p₂ q q′ q″ q₁ q₂ r r′ : M
    b : BinderMode

mutual
  -- Neutral equality.
  data _⊢_~_↑_ (Γ : Con Term n) : (k l A : Term n) → Set a where

    var-refl      : Γ ⊢ var x ∷ C
                  → x PE.≡ y
                  → Γ ⊢ var x ~ var y ↑ C

    app-cong      : Γ ⊢ k ~ l ↓ Π p , q ▷ F ▹ G
                  → Γ ⊢ t [conv↑] v ∷ F
                  → Γ ⊢ k ∘⟨ p ⟩ t ~ l ∘⟨ p ⟩ v ↑ G [ t ]₀

    fst-cong      : Γ ⊢ k ~ l ↓ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ fst p k ~ fst p l ↑ F

    snd-cong      : Γ ⊢ k ~ l ↓ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ snd p k ~ snd p l ↑ G [ fst p k ]₀

    natrec-cong   : Γ ∙ ℕ ⊢ F [conv↑] G
                  → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zero ]₀
                  → Γ ∙ ℕ ∙ F ⊢ h [conv↑] g ∷ F [ suc (var x1) ]↑²
                  → Γ ⊢ k ~ l ↓ ℕ
                  → Γ ⊢ natrec p q r F a₀ h k ~ natrec p q r G b₀ g l ↑ F [ k ]₀

    prodrec-cong  : Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ C [conv↑] E
                  → Γ ⊢ g ~ h ↓ Σᵣ p , q ▷ F ▹ G
                  → Γ ∙ F ∙ G ⊢ u [conv↑] v ∷ C [ prodᵣ p (var x1) (var x0) ]↑²
                  → Γ ⊢ prodrec r p q′ C g u ~ prodrec r p q′ E h v ↑ C [ g ]₀

    emptyrec-cong : Γ ⊢ F [conv↑] H
                  → Γ ⊢ k ~ l ↓ Empty
                  → Γ ⊢ emptyrec p F k ~ emptyrec p H l ↑ F

    J-cong        : Γ ⊢ A₁ [conv↑] A₂
                  → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁
                  → Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ [conv↑] B₂
                  → Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ t₁ , rfl ]₁₀
                  → Γ ⊢ v₁ [conv↑] v₂ ∷ A₁
                  → Γ ⊢ w₁ ~ w₂ ↓ C
                  → Γ ⊢ C ≡ Id A₁ t₁ v₁
                  → Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ~
                        J p q A₂ t₂ B₂ u₂ v₂ w₂ ↑ B₁ [ v₁ , w₁ ]₁₀

    K-cong        : Γ ⊢ A₁ [conv↑] A₂
                  → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁
                  → Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ [conv↑] B₂
                  → Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ rfl ]₀
                  → Γ ⊢ v₁ ~ v₂ ↓ C
                  → Γ ⊢ C ≡ Id A₁ t₁ t₁
                  → K-allowed
                  → Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ~ K p A₂ t₂ B₂ u₂ v₂ ↑
                      B₁ [ v₁ ]₀

    []-cong-cong  : ∀ {B}
                  → Γ ⊢ A₁ [conv↑] A₂
                  → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁
                  → Γ ⊢ u₁ [conv↑] u₂ ∷ A₁
                  → Γ ⊢ v₁ ~ v₂ ↓ B
                  → Γ ⊢ B ≡ Id A₁ t₁ u₁
                  → []-cong-allowed
                  → Γ ⊢ []-cong A₁ t₁ u₁ v₁ ~ []-cong A₂ t₂ u₂ v₂ ↑
                      Id (Erased A₁) Erased.[ t₁ ] Erased.[ u₁ ]

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓_ (Γ : Con Term n) (k l B : Term n) : Set a where
    inductive
    constructor [~]
    field
      A     : Term n
      D     : Γ ⊢ A ⇒* B
      whnfB : Whnf B
      k~l   : Γ ⊢ k ~ l ↑ A

  -- Type equality.
  record _⊢_[conv↑]_ (Γ : Con Term n) (A B : Term n) : Set a where
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
  data _⊢_[conv↓]_ (Γ : Con Term n) : (A B : Term n) → Set a where

    U-refl     : ⊢ Γ → Γ ⊢ U [conv↓] U

    ℕ-refl     : ⊢ Γ → Γ ⊢ ℕ [conv↓] ℕ

    Empty-refl : ⊢ Γ → Γ ⊢ Empty [conv↓] Empty

    Unit-refl  : ⊢ Γ → Unit-allowed → Γ ⊢ Unit [conv↓] Unit

    ne         : ∀ {K L}
               → Γ ⊢ K ~ L ↓ U
               → Γ ⊢ K [conv↓] L

    ΠΣ-cong    : ∀ {F G H E}
               → Γ ⊢ F
               → Γ ⊢ F [conv↑] H
               → Γ ∙ F ⊢ G [conv↑] E
               → ΠΣ-allowed b p q
               → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G [conv↓] ΠΣ⟨ b ⟩ p , q ▷ H ▹ E

    Id-cong    : Γ ⊢ A₁ [conv↑] A₂
               → Γ ⊢ t₁ [conv↑] t₂ ∷ A₁
               → Γ ⊢ u₁ [conv↑] u₂ ∷ A₁
               → Γ ⊢ Id A₁ t₁ u₁ [conv↓] Id A₂ t₂ u₂

  -- Term equality.
  record _⊢_[conv↑]_∷_ (Γ : Con Term n) (t u A : Term n) : Set a where
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
  data _⊢_[conv↓]_∷_ (Γ : Con Term n) : (t u A : Term n) → Set a where

    ℕ-ins     : Γ ⊢ k ~ l ↓ ℕ
              → Γ ⊢ k [conv↓] l ∷ ℕ

    Empty-ins : Γ ⊢ k ~ l ↓ Empty
              → Γ ⊢ k [conv↓] l ∷ Empty

    Unit-ins  : Γ ⊢ k ~ l ↓ Unit
              → Γ ⊢ k [conv↓] l ∷ Unit

    Σᵣ-ins    : Γ ⊢ k ∷ Σᵣ p , q ▷ F ▹ G
              → Γ ⊢ l ∷ Σᵣ p , q ▷ F ▹ G
              → Γ ⊢ k ~ l ↓ Σᵣ p′ , q′ ▷ H ▹ E
              → Γ ⊢ k [conv↓] l ∷ Σᵣ p , q ▷ F ▹ G

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

    prod-cong : ∀ {F G t t′ u u′}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t [conv↑] t′ ∷ F
              → Γ ⊢ u [conv↑] u′ ∷ G [ t ]₀
              → Σᵣ-allowed p q
              → Γ ⊢ prodᵣ p t u [conv↓] prodᵣ p t′ u′ ∷ Σᵣ p , q ▷ F ▹ G

    η-eq      : ∀ {f g F G}
              → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
              → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
              → Function f
              → Function g
              → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 [conv↑] wk1 g ∘⟨ p ⟩ var x0 ∷ G
              → Γ ⊢ f [conv↓] g ∷ Π p , q ▷ F ▹ G

    Σ-η       : Γ ⊢ k ∷ Σₚ p , q ▷ F ▹ G
              → Γ ⊢ l ∷ Σₚ p , q ▷ F ▹ G
              → Product k
              → Product l
              → Γ ⊢ fst p k [conv↑] fst p l ∷ F
              → Γ ⊢ snd p k [conv↑] snd p l ∷ G [ fst p k ]₀
              → Γ ⊢ k [conv↓] l ∷ Σₚ p , q ▷ F ▹ G

    η-unit    : ∀ {k l}
              → Γ ⊢ k ∷ Unit
              → Γ ⊢ l ∷ Unit
              → Whnf k
              → Whnf l
              → Γ ⊢ k [conv↓] l ∷ Unit

    Id-ins    : ∀ {A A′ t′ u′}
              → Γ ⊢ v₁ ∷ Id A t u
              → Γ ⊢ v₁ ~ v₂ ↓ Id A′ t′ u′
              → Γ ⊢ v₁ [conv↓] v₂ ∷ Id A t u

    rfl-refl  : ∀ {A}
              → Γ ⊢ t ≡ u ∷ A
              → Γ ⊢ rfl [conv↓] rfl ∷ Id A t u

star-refl : ⊢ Γ → Unit-allowed → Γ ⊢ star [conv↓] star ∷ Unit
star-refl ⊢Γ ok = η-unit (starⱼ ⊢Γ ok) (starⱼ ⊢Γ ok) starₙ starₙ

-- An inversion lemma for prod-cong.

prod-cong⁻¹ :
  ∀ {t′ u′} →
  Γ ⊢ prodᵣ p t u [conv↓] prodᵣ p′ t′ u′ ∷ Σᵣ p″ , q ▷ F ▹ G →
  p PE.≡ p′ ×
  p PE.≡ p″ ×
  Γ ⊢ F ×
  Γ ∙ F ⊢ G ×
  (Γ ⊢ t [conv↑] t′ ∷ F) ×
  (Γ ⊢ u [conv↑] u′ ∷ G [ t ]₀) ×
  Σᵣ-allowed p q
prod-cong⁻¹ (prod-cong F G t u ok) =
  PE.refl , PE.refl , F , G , t , u , ok

-- An inversion lemma for J-cong.

J-cong⁻¹ :
  Γ ⊢ J p₁ q₁ A₁ t₁ B₁ u₁ v₁ w₁ ~ J p₂ q₂ A₂ t₂ B₂ u₂ v₂ w₂ ↑ C →
  ∃ λ D →
  p₁ PE.≡ p₂ ×
  q₁ PE.≡ q₂ ×
  (Γ ⊢ A₁ [conv↑] A₂) ×
  Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ ×
  (Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ [conv↑] B₂) ×
  Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ t₁ , rfl ]₁₀ ×
  Γ ⊢ v₁ [conv↑] v₂ ∷ A₁ ×
  Γ ⊢ w₁ ~ w₂ ↓ D ×
  Γ ⊢ D ≡ Id A₁ t₁ v₁ ×
  C PE.≡ B₁ [ v₁ , w₁ ]₁₀
J-cong⁻¹ (J-cong A t B u v w D) =
  _ , PE.refl , PE.refl , A , t , B , u , v , w , D , PE.refl

-- An inversion lemma for K-cong.

K-cong⁻¹ :
  Γ ⊢ K p₁ A₁ t₁ B₁ u₁ v₁ ~ K p₂ A₂ t₂ B₂ u₂ v₂ ↑ C →
  ∃ λ D →
  p₁ PE.≡ p₂ ×
  (Γ ⊢ A₁ [conv↑] A₂) ×
  Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ ×
  (Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ [conv↑] B₂) ×
  Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ rfl ]₀ ×
  Γ ⊢ v₁ ~ v₂ ↓ D ×
  Γ ⊢ D ≡ Id A₁ t₁ t₁ ×
  K-allowed ×
  C PE.≡ B₁ [ v₁ ]₀
K-cong⁻¹ (K-cong A t B u v D ok) =
  _ , PE.refl , A , t , B , u , v , D , ok , PE.refl
