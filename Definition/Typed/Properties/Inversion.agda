------------------------------------------------------------------------
-- Some inversion lemmas related to _⊢_ and _⊢_∷_
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Inversion
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Size R

open import Definition.Untyped M

open import Tools.Product
open import Tools.Size
open import Tools.Size.Instances

private variable
  Γ         : Con Term _
  A B C t u : Term _
  b         : BinderMode
  p q       : M
  s         : Size

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
    (∃ λ (⊢Id : Γ ⊢ Id A t u) → size-⊢ ⊢Id <ˢ s) →
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) ×
    (∃ λ (⊢t : Γ ⊢ t ∷ A) → size-⊢∷ ⊢t <ˢ s) ×
    (∃ λ (⊢u : Γ ⊢ u ∷ A) → size-⊢∷ ⊢u <ˢ s)
  inversion-Id-⊢-<ˢ (⊢Id , lt) =
    let (⊢A , A<) , (⊢t , t<) , (⊢u , u<) = inversion-Id-⊢ ⊢Id in
    (⊢A , <ˢ-trans A< lt) , (⊢t , <ˢ-trans t< lt) ,
    (⊢u , <ˢ-trans u< lt)

opaque
  unfolding size-⊢∷

  -- An inversion lemma for ΠΣ⟨_⟩_,_▷_▹_.

  inversion-ΠΣ-⊢∷ :
    (⊢ΠΣ : Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ C) →
    ∃₂ λ l₁ l₂ →
    (∃ λ (⊢A : Γ ⊢ A ∷ U l₁) → size-⊢∷ ⊢A <ˢ size-⊢∷ ⊢ΠΣ) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B ∷ U l₂) → size-⊢∷ ⊢B <ˢ size-⊢∷ ⊢ΠΣ) ×
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
  unfolding size-⊢

  -- An inversion lemma for ΠΣ⟨_⟩_,_▷_▹_.

  inversion-ΠΣ-⊢ :
    (⊢ΠΣ : Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) →
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢ ⊢ΠΣ) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B) → size-⊢ ⊢B <ˢ size-⊢ ⊢ΠΣ) ×
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
    (∃ λ (⊢ΠΣ : Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) → size-⊢ ⊢ΠΣ <ˢ s) →
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ s) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B) → size-⊢ ⊢B <ˢ s) ×
    ΠΣ-allowed b p q
  inversion-ΠΣ-⊢-<ˢ (⊢ΠΣ , lt) =
    let (⊢A , A<) , (⊢B , B<) , ok = inversion-ΠΣ-⊢ ⊢ΠΣ in
    (⊢A , <ˢ-trans A< lt) , (⊢B , <ˢ-trans B< lt) , ok
