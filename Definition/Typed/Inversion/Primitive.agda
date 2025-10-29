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
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Size R

open import Definition.Untyped M

open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Relation
open import Tools.Size
open import Tools.Size.Instances

private variable
  Γ           : Con Term _
  A B C t u l : Term _
  b           : BinderMode
  s           : Strength
  p q         : M
  sz          : Size

------------------------------------------------------------------------
-- Inversion for Level

opaque

  -- Inversion for Level.

  inversion-Level : Γ ⊢ Level ∷ A → Γ ⊢ A ≡ U zeroᵘ × Level-is-small
  inversion-Level (Levelⱼ ⊢Γ ok)    = refl (Uⱼ (zeroᵘⱼ ⊢Γ)) , ok
  inversion-Level (conv ⊢Level eq) =
    let a , ok = inversion-Level ⊢Level
    in trans (sym eq) a , ok

opaque

  -- Level is not in any universe unless Level-is-small.

  ¬Level-is-small→¬Level∷U
    : ¬ Level-is-small → ¬ ∃ λ t → ε ⊢ Level ∷ U t
  ¬Level-is-small→¬Level∷U ¬small (t , Level∷Ut) = ¬small
    (inversion-Level Level∷Ut .proj₂)

opaque

  -- Inversion for zeroᵘ.

  inversion-zeroᵘ : Γ ⊢ zeroᵘ ∷ A → Γ ⊢ A ≡ Level
  inversion-zeroᵘ (zeroᵘⱼ ⊢Γ)      = refl (Levelⱼ′ ⊢Γ)
  inversion-zeroᵘ (conv ⊢zeroᵘ eq) = trans (sym eq) (inversion-zeroᵘ ⊢zeroᵘ)

opaque

  -- Inversion for sucᵘ.

  inversion-sucᵘ : Γ ⊢ sucᵘ t ∷ A → Γ ⊢ t ∷ Level × Γ ⊢ A ≡ Level
  inversion-sucᵘ (sucᵘⱼ ⊢t)      = ⊢t , refl (Levelⱼ′ (wfTerm ⊢t))
  inversion-sucᵘ (conv ⊢sucᵘ eq) =
    let a , b = inversion-sucᵘ ⊢sucᵘ in
    a , trans (sym eq) b

opaque

  -- Inversion for supᵘ.

  inversion-supᵘ : Γ ⊢ t supᵘ u ∷ A → Γ ⊢ t ∷ Level × Γ ⊢ u ∷ Level × Γ ⊢ A ≡ Level
  inversion-supᵘ (supᵘⱼ ⊢t ⊢u)   = ⊢t , ⊢u , refl (Levelⱼ′ (wfTerm ⊢t))
  inversion-supᵘ (conv ⊢supᵘ eq) =
    let a , b , c = inversion-supᵘ ⊢supᵘ in
    a , b , trans (sym eq) c

------------------------------------------------------------------------
-- Inversion for U

opaque

  -- Inversion for U.

  inversion-U : Γ ⊢ U t ∷ A → Γ ⊢ A ≡ U (sucᵘ t)
  inversion-U (Uⱼ ⊢t)       = refl (Uⱼ (sucᵘⱼ ⊢t))
  inversion-U (conv ⊢U B≡A) = trans (sym B≡A) (inversion-U ⊢U)

  inversion-U∷-Level : Γ ⊢ U l ∷ A → Γ ⊢ l ∷ Level
  inversion-U∷-Level (Uⱼ ⊢l) = ⊢l
  inversion-U∷-Level (conv ⊢U _) = inversion-U∷-Level ⊢U

  inversion-U-Level : Γ ⊢ U l → Γ ⊢ l ∷ Level
  inversion-U-Level (Uⱼ ⊢l) = ⊢l
  inversion-U-Level (univ ⊢U) = inversion-U∷-Level ⊢U

------------------------------------------------------------------------
-- Inversion for Lift

opaque

  inversion-Lift∷ : Γ ⊢ Lift t A ∷ B → ∃ λ k₁ → Γ ⊢ t ∷ Level × Γ ⊢ A ∷ U k₁ × Γ ⊢ B ≡ U (k₁ supᵘ t)
  inversion-Lift∷ (conv x x₁) =
    let _ , ⊢t , ⊢A , B≡ = inversion-Lift∷ x
    in _ , ⊢t , ⊢A , trans (sym x₁) B≡
  inversion-Lift∷ (Liftⱼ x x₁ x₂) = _ , x₁ , x₂ , refl (Uⱼ (supᵘⱼ x x₁))

  inversion-Lift : Γ ⊢ Lift t A → Γ ⊢ t ∷ Level × Γ ⊢ A
  inversion-Lift (univ x) =
    let _ , ⊢t , ⊢A , B≡ = inversion-Lift∷ x
    in ⊢t , univ ⊢A
  inversion-Lift (Liftⱼ x x₁) = x , x₁

  inversion-lift : Γ ⊢ lift t ∷ A → ∃₂ λ l B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Lift l B
  inversion-lift (conv a x) =
    let _ , _ , ⊢t , A≡Lift = inversion-lift a
    in _ , _ , ⊢t , trans (sym x) A≡Lift
  inversion-lift (liftⱼ a₁ a₂ a₃) = _ , _ , a₃ , refl (Liftⱼ a₁ a₂)

------------------------------------------------------------------------
-- Inversion for Empty

opaque

  -- Inversion for Empty.

  inversion-Empty : Γ ⊢ Empty ∷ A → Γ ⊢ A ≡ U zeroᵘ
  inversion-Empty (Emptyⱼ ⊢Γ)      = refl (Uⱼ (zeroᵘⱼ ⊢Γ))
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

  inversion-Unit-U : Γ ⊢ Unit s ∷ A → Γ ⊢ A ≡ U zeroᵘ × Unit-allowed s
  inversion-Unit-U (Unitⱼ ⊢Γ ok)    = refl (Uⱼ (zeroᵘⱼ ⊢Γ)) , ok
  inversion-Unit-U (conv ⊢Unit B≡A) =
    let B≡U , ok = inversion-Unit-U ⊢Unit in
    trans (sym B≡A) B≡U , ok

opaque

  -- Inversion for Unit.

  inversion-Unit : Γ ⊢ Unit s → Unit-allowed s
  inversion-Unit = λ where
    (Unitⱼ _ ok) → ok
    (univ ⊢Unit) →
      let _ , ok = inversion-Unit-U ⊢Unit in
      ok

opaque

  -- Inversion for star.

  inversion-star :
    Γ ⊢ star s ∷ A → Γ ⊢ A ≡ Unit s × Unit-allowed s
  inversion-star (starⱼ ⊢Γ ok)   = refl (Unitⱼ ⊢Γ ok) , ok
  inversion-star (conv ⊢star eq) =
    let a , b = inversion-star ⊢star in
    trans (sym eq) a , b

------------------------------------------------------------------------
-- Inversion for ℕ

opaque

  -- Inversion for ℕ.

  inversion-ℕ : Γ ⊢ ℕ ∷ A → Γ ⊢ A ≡ U zeroᵘ
  inversion-ℕ (ℕⱼ ⊢Γ)      = refl (Uⱼ (zeroᵘⱼ ⊢Γ))
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
    ∃ λ l →
    Γ ⊢ l ∷ Level ×
    (∃ λ (⊢A : Γ ⊢ A ∷ U l) → size-⊢∷ ⊢A <ˢ size-⊢∷ ⊢ΠΣ) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B ∷ U (wk1 l)) → size-⊢∷ ⊢B <ˢ size-⊢∷ ⊢ΠΣ) ×
    Γ ⊢ C ≡ U l ×
    ΠΣ-allowed b p q
  inversion-ΠΣ-⊢∷ (ΠΣⱼ ⊢l ⊢A ⊢B ok) =
    _ , ⊢l , (⊢A , !) , (⊢B , !) , refl (Uⱼ ⊢l) , ok
  inversion-ΠΣ-⊢∷ (conv ⊢ΠΣ eq₁) =
    let _ , ⊢l , (⊢A , A<) , (⊢B , B<) , eq₂ , ok =
          inversion-ΠΣ-⊢∷ ⊢ΠΣ
    in
    _ , ⊢l , (⊢A , ↙ <ˢ→≤ˢ A<) , (⊢B , ↙ <ˢ→≤ˢ B<) ,
    trans (sym eq₁) eq₂ , ok

opaque

  -- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

  inversion-ΠΣ-U :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ C →
    ∃ λ l →
      Γ ⊢ l ∷ Level ×
      Γ ⊢ A ∷ U l × Γ ∙ A ⊢ B ∷ U (wk1 l) × Γ ⊢ C ≡ U l ×
      ΠΣ-allowed b p q
  inversion-ΠΣ-U ⊢ΠΣ =
    let _ , ⊢l , (⊢A , _) , (⊢B , _) , C≡ , ok = inversion-ΠΣ-⊢∷ ⊢ΠΣ in
    _ , ⊢l , ⊢A , ⊢B , C≡ , ok

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
    (∃ λ (⊢ΠΣ : Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) → size-⊢ ⊢ΠΣ <ˢ sz) →
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ sz) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B) → size-⊢ ⊢B <ˢ sz) ×
    ΠΣ-allowed b p q
  inversion-ΠΣ-⊢-<ˢ (⊢ΠΣ , lt) =
    let (⊢A , A<) , (⊢B , B<) , ok = inversion-ΠΣ-⊢ ⊢ΠΣ in
    (⊢A , <ˢ-trans A< lt) , (⊢B , <ˢ-trans B< lt) , ok

opaque

  -- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

  inversion-ΠΣ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊢ A × Γ ∙ A ⊢ B × ΠΣ-allowed b p q
  inversion-ΠΣ ⊢ΠΣ =
    let (⊢A , _) , (⊢B , _) , ok = inversion-ΠΣ-⊢ ⊢ΠΣ in
    ⊢A , ⊢B , ok

opaque

  -- Inversion for prod.

  inversion-prod :
    Γ ⊢ prod s p t u ∷ A →
    ∃₃ λ B C q →
      (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
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
      (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
      Γ ⊢ t ∷ Σˢ p , q ▷ B ▹ C ×
      Γ ⊢ A ≡ B
  inversion-fst (fstⱼ ⊢C ⊢t) =
    let ⊢B = ⊢∙→⊢ (wf ⊢C) in
    _ , _ , _ , ⊢B , ⊢C , ⊢t , refl ⊢B
  inversion-fst (conv ⊢fst eq) =
    let a , b , c , d , e , f , g = inversion-fst ⊢fst in
    a , b , c , d , e , f , trans (sym eq) g
