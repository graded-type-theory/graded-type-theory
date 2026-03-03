------------------------------------------------------------------------
-- Sets of natural numbers with addition and multiplication are not
-- modalities, given certain assumptions
------------------------------------------------------------------------

module Graded.Modality.Instances.Set where

import Tools.Algebra
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat as ℕ using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

open import Graded.Modality

private variable
  a     : Level
  S     : Set _
  xs ys : S
  n     : Nat

-- A specification of sets of natural numbers with addition and
-- multiplication.

record Is-set-+· (S : Set a) : Set (lsuc a) where
  no-eta-equality

  infixr 45 _·_
  infixr 40 _+_
  infix  10 _∈_

  field
    -- The membership relation.
    _∈_ : Nat → S → Set a

    -- Addition.
    _+_ : S → S → S
    ∈+⇔ : n ∈ xs + ys ⇔ ∃₂ λ l m → l ℕ.+ m ≡ n × l ∈ xs × m ∈ ys

    -- Multiplication.
    _·_ : S → S → S
    ∈·⇔ : n ∈ xs · ys ⇔ ∃₂ λ l m → l ℕ.* m ≡ n × l ∈ xs × m ∈ ys

-- Some lemmas that apply to instances of Is-set-+· with the sets ∅
-- and {0}.

module ∅-𝟘
  {a} {S : Set a}
  (set : Is-set-+· S)
  (open Is-set-+· set)
  (∅ : S)
  (∈∅⇔ : ∀ {n} → n ∈ ∅ ⇔ ⊥)
  (𝟘 : S)
  (∈𝟘⇔ : ∀ {n} → n ∈ 𝟘 ⇔ n ≡ 0)
  where

  open Tools.Algebra S

  -- There is no right identity for addition which is also a right
  -- zero for multiplication.

  no-right-zero :
    ¬ ∃ λ zero → RightIdentity zero _+_ × RightZero zero _·_
  no-right-zero (zero , +-identityʳ , ·-zeroʳ) =
              $⟨ refl ⟩
    0 ≡ 0     ⇔˘⟨ zero-contains-exactly-zero ⟩→
    0 ∈ zero  ⇔⟨ zero-is-empty ⟩→
    ⊥         □
    where
    zero-contains-exactly-zero : n ∈ zero ⇔ n ≡ 0
    zero-contains-exactly-zero {n = n} =
      n ∈ zero                                     ⇔⟨ (λ n∈zero → 0 , n , refl , refl , n∈zero)
                                                    , (λ { (.0 , .n , refl , refl , n∈zero) → n∈zero })
                                                    ⟩
      (∃₂ λ l m → l ℕ.+ m ≡ n × l ≡ 0 × m ∈ zero)  ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                        ∈𝟘⇔ ×-cong-⇔ id⇔) ⟩
      (∃₂ λ l m → l ℕ.+ m ≡ n × l ∈ 𝟘 × m ∈ zero)  ⇔˘⟨ ∈+⇔ ⟩
      n ∈ 𝟘 + zero                                 ≡⟨ cong (_ ∈_) (+-identityʳ _) ⟩⇔
      n ∈ 𝟘                                        ⇔⟨ ∈𝟘⇔ ⟩
      n ≡ 0                                        □⇔

    zero-is-empty : n ∈ zero ⇔ ⊥
    zero-is-empty {n = n} =
      n ∈ zero                                     ≡˘⟨ cong (_ ∈_) (·-zeroʳ _) ⟩⇔
      n ∈ ∅ · zero                                 ⇔⟨ ∈·⇔ ⟩
      (∃₂ λ l m → l ℕ.* m ≡ n × l ∈ ∅ × m ∈ zero)  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                       ∈∅⇔ ×-cong-⇔ id⇔) ⟩
      (∃₂ λ l m → l ℕ.* m ≡ n × ⊥ × m ∈ zero)      ⇔⟨ ⊥-elim ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ , ⊥-elim ⟩
      ⊥                                            □⇔

  -- There is no modality for which the modality's implementations of
  -- addition and multiplication match those of the set.

  no-modality :
    (modality : Modality S) →
    Modality._+_ modality ≡ _+_ →
    Modality._·_ modality ≡ _·_ →
    ⊥
  no-modality modality@record{} refl refl =
    no-right-zero (_ , +-identityʳ , ·-zeroʳ)
    where
    open Modality modality

-- Some lemmas that apply to instances of Is-set-+· with the sets {1}
-- and {1, 2}.

module 𝟙-𝟚
  {a} {S : Set a}
  (set : Is-set-+· S)
  (open Is-set-+· set)
  (𝟙 : S)
  (∈𝟙⇔ : ∀ {n} → n ∈ 𝟙 ⇔ n ≡ 1)
  (𝟙∪𝟚 : S)
  (∈𝟙∪𝟚⇔ : ∀ {n} → n ∈ 𝟙∪𝟚 ⇔ (n ≡ 1 ⊎ n ≡ 2))
  where

  open Tools.Algebra S

  -- A set that contains exactly 2.

  𝟚 : S
  𝟚 = 𝟙 + 𝟙

  -- The set 𝟚 contains exactly 2.

  ∈𝟚⇔ : n ∈ 𝟚 ⇔ n ≡ 2
  ∈𝟚⇔ {n = n} =
    n ∈ 𝟙 + 𝟙                                 ⇔⟨ ∈+⇔ ⟩
    (∃₂ λ l m → l ℕ.+ m ≡ n × l ∈ 𝟙 × m ∈ 𝟙)  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                  ∈𝟙⇔ ×-cong-⇔ ∈𝟙⇔) ⟩
    (∃₂ λ l m → l ℕ.+ m ≡ n × l ≡ 1 × m ≡ 1)  ⇔⟨ (λ { (.1 , .1 , refl , refl , refl) → refl })
                                               , (λ { refl → 1 , 1 , refl , refl , refl })
                                               ⟩
    n ≡ 2                                     □⇔

  private

    -- Some lemmas used below.

    ∈𝟙∪𝟚·𝟙⇔ : n ∈ 𝟙∪𝟚 · 𝟙 ⇔ (n ≡ 1 ⊎ n ≡ 2)
    ∈𝟙∪𝟚·𝟙⇔ {n = n} =
      n ∈ 𝟙∪𝟚 · 𝟙                                         ⇔⟨ ∈·⇔ ⟩
      (∃₂ λ l m → l ℕ.* m ≡ n × l ∈ 𝟙∪𝟚 × m ∈ 𝟙)          ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                              ∈𝟙∪𝟚⇔ ×-cong-⇔ ∈𝟙⇔) ⟩
      (∃₂ λ l m → l ℕ.* m ≡ n × (l ≡ 1 ⊎ l ≡ 2) × m ≡ 1)  ⇔⟨ (λ { (l , .1 , eq , hyp , refl) →
                                                                  subst (λ n → n ≡ 1 ⊎ n ≡ 2)
                                                                    (trans (sym (ℕ.*-identityʳ _)) eq)
                                                                    hyp })
                                                           , (λ hyp → n , 1 , ℕ.*-identityʳ _ , hyp , refl)
                                                           ⟩
      n ≡ 1 ⊎ n ≡ 2                                       □⇔

    ∈𝟙∪𝟚·𝟙+𝟙∪𝟚·𝟙⇔ :
      n ∈ 𝟙∪𝟚 · 𝟙 + 𝟙∪𝟚 · 𝟙 ⇔ (n ≡ 2 ⊎ n ≡ 3 ⊎ n ≡ 4)
    ∈𝟙∪𝟚·𝟙+𝟙∪𝟚·𝟙⇔ {n = n} =
      n ∈ 𝟙∪𝟚 · 𝟙 + 𝟙∪𝟚 · 𝟙                                         ⇔⟨ ∈+⇔ ⟩
      (∃₂ λ l m → l ℕ.+ m ≡ n × l ∈ 𝟙∪𝟚 · 𝟙 × m ∈ 𝟙∪𝟚 · 𝟙)          ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                        ∈𝟙∪𝟚·𝟙⇔ ×-cong-⇔ ∈𝟙∪𝟚·𝟙⇔) ⟩
      (∃₂ λ l m → l ℕ.+ m ≡ n × (l ≡ 1 ⊎ l ≡ 2) × (m ≡ 1 ⊎ m ≡ 2))  ⇔⟨ (λ where
                                                                          (.1 , .1 , refl , inj₁ refl , inj₁ refl) → inj₁ refl
                                                                          (.1 , .2 , refl , inj₁ refl , inj₂ refl) → inj₂ (inj₁ refl)
                                                                          (.2 , .1 , refl , inj₂ refl , inj₁ refl) → inj₂ (inj₁ refl)
                                                                          (.2 , .2 , refl , inj₂ refl , inj₂ refl) → inj₂ (inj₂ refl))
                                                                     , (λ where
                                                                          (inj₁ refl)        → 1 , 1 , refl , inj₁ refl , inj₁ refl
                                                                          (inj₂ (inj₁ refl)) → 1 , 2 , refl , inj₁ refl , inj₂ refl
                                                                          (inj₂ (inj₂ refl)) → 2 , 2 , refl , inj₂ refl , inj₂ refl)
                                                                     ⟩
      n ≡ 2 ⊎ n ≡ 3 ⊎ n ≡ 4                                         □⇔

    ∈𝟙∪𝟚·𝟚⇔ : n ∈ 𝟙∪𝟚 · 𝟚 ⇔ (n ≡ 2 ⊎ n ≡ 4)
    ∈𝟙∪𝟚·𝟚⇔ {n = n} =
      n ∈ 𝟙∪𝟚 · 𝟚                                         ⇔⟨ ∈·⇔ ⟩
      (∃₂ λ l m → l ℕ.* m ≡ n × l ∈ 𝟙∪𝟚 × m ∈ 𝟚)          ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                              ∈𝟙∪𝟚⇔ ×-cong-⇔ ∈𝟚⇔) ⟩
      (∃₂ λ l m → l ℕ.* m ≡ n × (l ≡ 1 ⊎ l ≡ 2) × m ≡ 2)  ⇔⟨ (λ where
                                                                (.1 , .2 , refl , inj₁ refl , refl) → inj₁ refl
                                                                (.2 , .2 , refl , inj₂ refl , refl) → inj₂ refl)
                                                           , (λ where
                                                                (inj₁ refl) → 1 , 2 , refl , inj₁ refl , refl
                                                                (inj₂ refl) → 2 , 2 , refl , inj₂ refl , refl)
                                                           ⟩
      (n ≡ 2 ⊎ n ≡ 4)                                     □⇔


  -- The number 3 is a member of 𝟙∪𝟚 · 𝟙 + 𝟙∪𝟚 · 𝟙.

  3∈𝟙∪𝟚·𝟙+𝟙∪𝟚·𝟙 : 3 ∈ 𝟙∪𝟚 · 𝟙 + 𝟙∪𝟚 · 𝟙
  3∈𝟙∪𝟚·𝟙+𝟙∪𝟚·𝟙 = ∈𝟙∪𝟚·𝟙+𝟙∪𝟚·𝟙⇔ .proj₂ (inj₂ (inj₁ refl))

  -- The number 3 is not a member of 𝟙∪𝟚 · 𝟚.

  3∉𝟙∪𝟚·𝟚 : ¬ 3 ∈ 𝟙∪𝟚 · 𝟚
  3∉𝟙∪𝟚·𝟚 =
    3 ∈ 𝟙∪𝟚 · 𝟚    ⇔⟨ ∈𝟙∪𝟚·𝟚⇔ ⟩→
    3 ≡ 2 ⊎ 3 ≡ 4  →⟨ (λ { (inj₁ ()); (inj₂ ()) }) ⟩
    ⊥              □

  -- Multiplication does not distribute from the left over addition.

  ¬-·-distribˡ-+ : ¬ _·_ DistributesOverˡ _+_
  ¬-·-distribˡ-+ ·-distribˡ-+ =
                           $⟨ 3∈𝟙∪𝟚·𝟙+𝟙∪𝟚·𝟙 ⟩
    3 ∈ 𝟙∪𝟚 · 𝟙 + 𝟙∪𝟚 · 𝟙  ≡⟨ cong (_ ∈_) (sym (·-distribˡ-+ _ _ _)) ⟩→
    3 ∈ 𝟙∪𝟚 · 𝟚            →⟨ 3∉𝟙∪𝟚·𝟚 ⟩
    ⊥                      □

  -- There is no modality for which the modality's implementations of
  -- addition and multiplication match those of the set.

  no-modality :
    (modality : Modality S) →
    Modality._+_ modality ≡ _+_ →
    Modality._·_ modality ≡ _·_ →
    ⊥
  no-modality modality@record{} refl refl = ¬-·-distribˡ-+ ·-distribˡ-+
    where
    open Modality modality

-- Some lemmas that apply to instances of Is-set-+· with a union
-- operation and the set {1}.

module ∪-𝟙
  {a} {S : Set a}
  (set : Is-set-+· S)
  (open Is-set-+· set)
  (_∪_ : S → S → S)
  (∈∪⇔ : ∀ {n xs ys} → n ∈ xs ∪ ys ⇔ (n ∈ xs ⊎ n ∈ ys))
  (𝟙 : S)
  (∈𝟙⇔ : ∀ {n} → n ∈ 𝟙 ⇔ n ≡ 1)
  where

  open Tools.Algebra S

  private

    𝟙∪𝟚 : S
    𝟙∪𝟚 = 𝟙 ∪ (𝟙 + 𝟙)

    ∈𝟙∪𝟚⇔ : n ∈ 𝟙∪𝟚 ⇔ (n ≡ 1 ⊎ n ≡ 2)
    ∈𝟙∪𝟚⇔ {n = n} =
      n ∈ 𝟙 ∪ (𝟙 + 𝟙)                                   ⇔⟨ ∈∪⇔ ⟩
      n ∈ 𝟙 ⊎ n ∈ 𝟙 + 𝟙                                 ⇔⟨ ∈𝟙⇔ ⊎-cong-⇔ ∈+⇔ ⟩
      n ≡ 1 ⊎ (∃₂ λ l m → l ℕ.+ m ≡ n × l ∈ 𝟙 × m ∈ 𝟙)  ⇔⟨ (id⇔ ⊎-cong-⇔ Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                            ∈𝟙⇔ ×-cong-⇔ ∈𝟙⇔) ⟩
      n ≡ 1 ⊎ (∃₂ λ l m → l ℕ.+ m ≡ n × l ≡ 1 × m ≡ 1)  ⇔⟨ id⇔
                                                             ⊎-cong-⇔
                                                           ( (λ { (.1 , .1 , refl , refl , refl) → refl })
                                                           , (λ { refl → 1 , 1 , refl , refl , refl })
                                                           ) ⟩
      n ≡ 1 ⊎ n ≡ 2                                     □⇔

  open 𝟙-𝟚 set 𝟙 ∈𝟙⇔ 𝟙∪𝟚 ∈𝟙∪𝟚⇔ public

  -- An ordering relation.

  _≤_ : S → S → Set a
  xs ≤ ys = xs ≡ xs ∪ ys

  -- If xs ≤ ys and n ∈ ys, then x ∈ xs.

  ≤∈→∈ : xs ≤ ys → n ∈ ys → n ∈ xs
  ≤∈→∈ {xs = xs} {ys = ys} {n = n} xs≤ys =
    n ∈ ys       →⟨ ∈∪⇔ .proj₂ ∘→ inj₂ ⟩
    n ∈ xs ∪ ys  ≡⟨ cong (_ ∈_) (sym xs≤ys) ⟩→
    n ∈ xs       □

  -- Multiplication does not sub-distribute (in a certain sense) from
  -- the left over addition.

  ¬-·-sub-distribˡ-+ : ¬ _·_ SubDistributesOverˡ _+_ by _≤_
  ¬-·-sub-distribˡ-+ ·-sub-distribˡ-+ =
                           $⟨ 3∈𝟙∪𝟚·𝟙+𝟙∪𝟚·𝟙 ⟩
    3 ∈ 𝟙∪𝟚 · 𝟙 + 𝟙∪𝟚 · 𝟙  →⟨ ≤∈→∈ (·-sub-distribˡ-+ _ _ _) ⟩
    3 ∈ 𝟙∪𝟚 · 𝟚            →⟨ 3∉𝟙∪𝟚·𝟚 ⟩
    ⊥                      □
