------------------------------------------------------------------------
-- A variant of Definition.Typed.Inversion with fewer dependencies
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Inversion.Primitive
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Size R

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
import Tools.PropositionalEquality as PE
open import Tools.Product
open import Tools.Size
open import Tools.Size.Instances

private variable
  α         : Nat
  Γ         : Cons _ _
  A B C t u : Term _
  b         : BinderMode
  l         : Universe-level
  s         : Strength
  p q       : M
  sz        : Size

------------------------------------------------------------------------
-- Inversion for U

opaque

  -- Inversion for U.

  inversion-U : Γ ⊢ U l ∷ A → Γ ⊢ A ≡ U (1+ l)
  inversion-U (Uⱼ ⊢Γ)       = refl (Uⱼ ⊢Γ)
  inversion-U (conv ⊢U B≡A) = trans (sym B≡A) (inversion-U ⊢U)

------------------------------------------------------------------------
-- Inversion for U

------------------------------------------------------------------------
-- Inversion for Empty

opaque

  -- Inversion for Empty.

  inversion-Empty : Γ ⊢ Empty ∷ A → Γ ⊢ A ≡ U 0
  inversion-Empty (Emptyⱼ ⊢Γ)      = refl (Uⱼ ⊢Γ)
  inversion-Empty (conv ⊢Empty eq) =
    trans (sym eq) (inversion-Empty ⊢Empty)

opaque

  -- Inversion for emptyrec.

  inversion-emptyrec :
    Γ ⊢ emptyrec p A t ∷ B →
    (Γ ⊢ A) × Γ ⊢ t ∷ Empty × Γ ⊢ B ≡ A
  inversion-emptyrec (emptyrecⱼ ⊢A ⊢t) =
    ⊢A , ⊢t , refl ⊢A
  inversion-emptyrec (conv ⊢er eq) =
    let a , b , c = inversion-emptyrec ⊢er
    in  a , b , trans (sym eq) c

------------------------------------------------------------------------
-- Inversion for Unit

opaque

  -- Inversion for Unit.

  inversion-Unit-U : Γ ⊢ Unit s l ∷ A → Γ ⊢ A ≡ U l × Unit-allowed s
  inversion-Unit-U (Unitⱼ ⊢Γ ok)    = refl (Uⱼ ⊢Γ) , ok
  inversion-Unit-U (conv ⊢Unit B≡A) =
    let B≡U , ok = inversion-Unit-U ⊢Unit in
    trans (sym B≡A) B≡U , ok

opaque

  -- Inversion for Unit.

  inversion-Unit : Γ ⊢ Unit s l → Unit-allowed s
  inversion-Unit = λ where
    (Unitⱼ _ ok) → ok
    (univ ⊢Unit) →
      let _ , ok = inversion-Unit-U ⊢Unit in
      ok

opaque

  -- Inversion for star.

  inversion-star :
    Γ ⊢ star s l ∷ A → Γ ⊢ A ≡ Unit s l × Unit-allowed s
  inversion-star (starⱼ ⊢Γ ok)   = refl (Unitⱼ ⊢Γ ok) , ok
  inversion-star (conv ⊢star eq) =
    let a , b = inversion-star ⊢star in
    trans (sym eq) a , b

------------------------------------------------------------------------
-- Inversion for ℕ

opaque

  -- Inversion for ℕ.

  inversion-ℕ : Γ ⊢ ℕ ∷ A → Γ ⊢ A ≡ U 0
  inversion-ℕ (ℕⱼ ⊢Γ)      = refl (Uⱼ ⊢Γ)
  inversion-ℕ (conv ⊢ℕ eq) = trans (sym eq) (inversion-ℕ ⊢ℕ)

opaque

  -- Inversion for zero.

  inversion-zero : Γ ⊢ zero ∷ A → Γ ⊢ A ≡ ℕ
  inversion-zero (zeroⱼ ⊢Γ)      = refl (ℕⱼ ⊢Γ)
  inversion-zero (conv ⊢zero eq) = trans (sym eq) (inversion-zero ⊢zero)

opaque

  -- Inversion for suc.

  inversion-suc : Γ ⊢ suc t ∷ A → Γ ⊢ t ∷ ℕ × Γ ⊢ A ≡ ℕ
  inversion-suc (sucⱼ ⊢t)      = ⊢t , refl (ℕⱼ (wfTerm ⊢t))
  inversion-suc (conv ⊢suc eq) =
    let a , b = inversion-suc ⊢suc in
    a , trans (sym eq) b

------------------------------------------------------------------------
-- Inversion for Id

opaque
  unfolding size-⊢∷

  -- An inversion lemma for Id.

  inversion-Id-⊢∷ :
    (⊢Id : Γ ⊢ Id A t u ∷ B) →
    (∃ λ (⊢A : Γ ⊢ A ∷ B) → size-⊢∷ ⊢A <ˢ size-⊢∷ ⊢Id) ×
    (∃ λ (⊢t : Γ ⊢ t ∷ A) → size-⊢∷ ⊢t <ˢ size-⊢∷ ⊢Id) ×
    (∃ λ (⊢u : Γ ⊢ u ∷ A) → size-⊢∷ ⊢u <ˢ size-⊢∷ ⊢Id)
  inversion-Id-⊢∷ (Idⱼ ⊢A ⊢t ⊢u) = (⊢A , !) , (⊢t , !) , (⊢u , !)
  inversion-Id-⊢∷ (conv ⊢Id ≡U)  =
    let (⊢A , A<) , (⊢t , t<) , (⊢u , u<) = inversion-Id-⊢∷ ⊢Id in
    (conv ⊢A ≡U , A< ↙⊕ ◻) , (⊢t , ↙ <ˢ→≤ˢ t<) , (⊢u , ↙ <ˢ→≤ˢ u<)

opaque

  -- Inversion for Id.

  inversion-Id-U :
    Γ ⊢ Id A t u ∷ B →
    ∃ λ l → Γ ⊢ A ∷ U l × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A × Γ ⊢ B ≡ U l
  inversion-Id-U = λ where
    (Idⱼ ⊢A ⊢t ⊢u) → _ , ⊢A , ⊢t , ⊢u , refl (Uⱼ (wfTerm ⊢A))
    (conv ⊢Id C≡B) →
      case inversion-Id-U ⊢Id of λ {
        (_ , ⊢A , ⊢t , ⊢u , C≡U) →
      _ , ⊢A , ⊢t , ⊢u , trans (sym C≡B) C≡U }

opaque

  -- A variant of inversion-Id-U.

  inversion-Id∷U :
    Γ ⊢ Id A t u ∷ U l →
    Γ ⊢ A ∷ U l × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  inversion-Id∷U ⊢Id =
    let _ , ⊢A , ⊢t , ⊢u , ≡U = inversion-Id-U ⊢Id in
    conv ⊢A (sym ≡U) , ⊢t , ⊢u

opaque
  unfolding size-⊢

  -- An inversion lemma for Id.

  inversion-Id-⊢ :
    (⊢Id : Γ ⊢ Id A t u) →
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢ ⊢Id) ×
    (∃ λ (⊢t : Γ ⊢ t ∷ A) → size-⊢∷ ⊢t <ˢ size-⊢ ⊢Id) ×
    (∃ λ (⊢u : Γ ⊢ u ∷ A) → size-⊢∷ ⊢u <ˢ size-⊢ ⊢Id)
  inversion-Id-⊢ (Idⱼ ⊢A ⊢t ⊢u) = (⊢A , !) , (⊢t , !) , (⊢u , !)
  inversion-Id-⊢ (univ ⊢Id)     =
    let (⊢A , A<) , (⊢t , t<) , (⊢u , u<) = inversion-Id-⊢∷ ⊢Id in
    (univ ⊢A , A< ↙⊕ ◻) , (⊢t , ↙ <ˢ→≤ˢ t<) , (⊢u , ↙ <ˢ→≤ˢ u<)

opaque
  unfolding size-⊢

  -- A variant of inversion-Id-⊢.

  inversion-Id-⊢-<ˢ :
    (∃ λ (⊢Id : Γ ⊢ Id A t u) → size-⊢ ⊢Id <ˢ sz) →
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ sz) ×
    (∃ λ (⊢t : Γ ⊢ t ∷ A) → size-⊢∷ ⊢t <ˢ sz) ×
    (∃ λ (⊢u : Γ ⊢ u ∷ A) → size-⊢∷ ⊢u <ˢ sz)
  inversion-Id-⊢-<ˢ (⊢Id , lt) =
    let (⊢A , A<) , (⊢t , t<) , (⊢u , u<) = inversion-Id-⊢ ⊢Id in
    (⊢A , <ˢ-trans A< lt) , (⊢t , <ˢ-trans t< lt) ,
    (⊢u , <ˢ-trans u< lt)

opaque

  -- Inversion for Id.

  inversion-Id :
    Γ ⊢ Id A t u →
    (Γ ⊢ A) × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  inversion-Id ⊢Id =
    let (⊢A , _) , (⊢t , _) , (⊢u , _) = inversion-Id-⊢ ⊢Id in
    ⊢A , ⊢t , ⊢u

------------------------------------------------------------------------
-- Inversion for Π and Σ

opaque
  unfolding size-⊢∷

  -- An inversion lemma for ΠΣ⟨_⟩_,_▷_▹_.

  inversion-ΠΣ-⊢∷ :
    (⊢ΠΣ : Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ C) →
    ∃₂ λ l₁ l₂ →
    (∃ λ (⊢A : Γ ⊢ A ∷ U l₁) → size-⊢∷ ⊢A <ˢ size-⊢∷ ⊢ΠΣ) ×
    (∃ λ (⊢B : Γ »∙ A ⊢ B ∷ U l₂) → size-⊢∷ ⊢B <ˢ size-⊢∷ ⊢ΠΣ) ×
    Γ ⊢ C ≡ U (l₁ ⊔ᵘ l₂) ×
    ΠΣ-allowed b p q
  inversion-ΠΣ-⊢∷ (ΠΣⱼ ⊢A ⊢B ok) =
    _ , _ , (⊢A , !) , (⊢B , !) , refl (Uⱼ (wfTerm ⊢A)) , ok
  inversion-ΠΣ-⊢∷ (conv ⊢ΠΣ eq₁) =
    let _ , _ , (⊢A , A<) , (⊢B , B<) , eq₂ , ok =
          inversion-ΠΣ-⊢∷ ⊢ΠΣ
    in
    _ , _ , (⊢A , ↙ <ˢ→≤ˢ A<) , (⊢B , ↙ <ˢ→≤ˢ B<) ,
    trans (sym eq₁) eq₂ , ok

opaque

  -- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

  inversion-ΠΣ-U :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ C →
    ∃₂ λ l₁ l₂ →
      Γ ⊢ A ∷ U l₁ × Γ »∙ A ⊢ B ∷ U l₂ × Γ ⊢ C ≡ U (l₁ ⊔ᵘ l₂) ×
      ΠΣ-allowed b p q
  inversion-ΠΣ-U ⊢ΠΣ =
    let _ , _ , (⊢A , _) , (⊢B , _) , C≡ , ok = inversion-ΠΣ-⊢∷ ⊢ΠΣ in
    _ , _ , ⊢A , ⊢B , C≡ , ok

opaque
  unfolding size-⊢

  -- An inversion lemma for ΠΣ⟨_⟩_,_▷_▹_.

  inversion-ΠΣ-⊢ :
    (⊢ΠΣ : Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) →
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢ ⊢ΠΣ) ×
    (∃ λ (⊢B : Γ »∙ A ⊢ B) → size-⊢ ⊢B <ˢ size-⊢ ⊢ΠΣ) ×
    ΠΣ-allowed b p q
  inversion-ΠΣ-⊢ (ΠΣⱼ ⊢B ok) =
    let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B in
    (⊢A , <ˢ-trans A< !) , (⊢B , ↙ ◻) , ok
  inversion-ΠΣ-⊢ (univ ⊢ΠΣ) =
    let _ , _ , (⊢A , A<) , (⊢B , B<) , _ , ok = inversion-ΠΣ-⊢∷ ⊢ΠΣ in
    (univ ⊢A , A< ↙⊕ ◻) , (univ ⊢B , B< ↙⊕ ◻) , ok

opaque
  unfolding size-⊢

  -- A variant of inversion-ΠΣ-⊢.

  inversion-ΠΣ-⊢-<ˢ :
    (∃ λ (⊢ΠΣ : Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) → size-⊢ ⊢ΠΣ <ˢ sz) →
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ sz) ×
    (∃ λ (⊢B : Γ »∙ A ⊢ B) → size-⊢ ⊢B <ˢ sz) ×
    ΠΣ-allowed b p q
  inversion-ΠΣ-⊢-<ˢ (⊢ΠΣ , lt) =
    let (⊢A , A<) , (⊢B , B<) , ok = inversion-ΠΣ-⊢ ⊢ΠΣ in
    (⊢A , <ˢ-trans A< lt) , (⊢B , <ˢ-trans B< lt) , ok

opaque

  -- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

  inversion-ΠΣ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊢ A × Γ »∙ A ⊢ B × ΠΣ-allowed b p q
  inversion-ΠΣ ⊢ΠΣ =
    let (⊢A , _) , (⊢B , _) , ok = inversion-ΠΣ-⊢ ⊢ΠΣ in
    ⊢A , ⊢B , ok

opaque

  -- Inversion for prod.

  inversion-prod :
    Γ ⊢ prod s p t u ∷ A →
    ∃₃ λ B C q →
      (Γ ⊢ B) × (Γ »∙ B ⊢ C) ×
      Γ ⊢ t ∷ B × Γ ⊢ u ∷ C [ t ]₀ ×
      Γ ⊢ A ≡ Σ⟨ s ⟩ p , q ▷ B ▹ C ×
      Σ-allowed s p q
  inversion-prod (prodⱼ ⊢C ⊢t ⊢u ok) =
    _ , _ , _ , ⊢∙→⊢ (wf ⊢C) , ⊢C , ⊢t , ⊢u , refl (ΠΣⱼ ⊢C ok) , ok
  inversion-prod (conv ⊢prod eq) =
    let a , b , c , d , e , f , g , h , i = inversion-prod ⊢prod in
    a , b , c , d , e , f , g , trans (sym eq) h , i

opaque

  -- Inversion for fst.

  inversion-fst :
    Γ ⊢ fst p t ∷ A →
    ∃₃ λ B C q →
      (Γ ⊢ B) × (Γ »∙ B ⊢ C) ×
      Γ ⊢ t ∷ Σˢ p , q ▷ B ▹ C ×
      Γ ⊢ A ≡ B
  inversion-fst (fstⱼ ⊢C ⊢t) =
    let ⊢B = ⊢∙→⊢ (wf ⊢C) in
    _ , _ , _ , ⊢B , ⊢C , ⊢t , refl ⊢B
  inversion-fst (conv ⊢fst eq) =
    let a , b , c , d , e , f , g = inversion-fst ⊢fst in
    a , b , c , d , e , f , trans (sym eq) g
