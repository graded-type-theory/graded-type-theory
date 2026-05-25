------------------------------------------------------------------------
-- Some definitions related to quotients
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Quotient
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (Eq : EqRelSet R)
  where

open EqRelSet Eq
open Type-restrictions R

open import Definition.LogicalRelation _ ⦃ eqrel = Eq ⦄
open import Definition.LogicalRelation.Weakening.Restricted
  _ ⦃ eqrel = Eq ⦄

open import Definition.Typed R
open import Definition.Typed.Properties R

open import Definition.Untyped M
open import Definition.Untyped.Neutral.Atomic M type-variant

open import Tools.Empty
open import Tools.Function
import Tools.Level as L
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation hiding (Rel)
open import Tools.Sum

open Symmetric-transitive-closure

private variable
  m n           : Nat
  ℓ             : Universe-level
  Γ             : Cons _ _
  A t t′ u u′ v : Term _
  t′-q u′-q     : Quotientᵃₗ _ _

-- A part of the definition of well-formed equality for quotients.

⊩Quot-related :
  (ℓ : Universe-level) (Γ : Cons m n) ({A} _ _ : Term n) →
  Γ ⊢ʷᵏʳ id ∷ Γ → Γ ⊩′⟨ ℓ ⟩Quot A → Set a
⊩Quot-related ℓ Γ t u id-Γ ⊩A =
  Symmetric-transitive-closure
    (λ t u →
       ∃ λ (⊩t : Γ ⊩⟨ ℓ ⟩ t ∷ wk id Data / ⊩Data id-Γ) →
       ∃ λ (⊩u : Γ ⊩⟨ ℓ ⟩ u ∷ wk id Data / ⊩Data id-Γ) →
       ∃ λ v →
       Γ ⊩⟨ ℓ ⟩ v ∷ wk (liftn id 2) Rel [ t , u ]₁₀ / ⊩Rel id-Γ ⊩t ⊩u)
    t u
  where
  open _⊩ₗQuot_ ⊩A

-- A view of parts of _⊩ₗQuot_≡_∷_/_.

data Quot-view
       {Γ : Cons m n} (⊢Γ : ⊢ Γ) (⊩A : Γ ⊩′⟨ ℓ ⟩Quot A) :
       (t : Term n) → Quotientᵃₗ (Γ .defs) t →
       (u : Term n) → Quotientᵃₗ (Γ .defs) u → Set a where
  equal :
    let open _⊩ₗQuot_ ⊩A
        id-Γ = ⊢ʷᵏʳid ⊢Γ
    in
    (t≡u : Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ wk id Data / ⊩Data id-Γ) →
    Quot-view ⊢Γ ⊩A (class t) class (class u) class
  related :
    (ok : Equality-reflection)
    (rel : ⊩Quot-related ℓ Γ t u (⊢ʷᵏʳid ⊢Γ) ⊩A) →
    Quot-view ⊢Γ ⊩A (class t) class (class u) class
  ne :
    let open _⊩ₗQuot_ ⊩A in
    (t-n : Neutralᵃₗ (Γ .defs) t)
    (u-n : Neutralᵃₗ (Γ .defs) u)
    (t~u : Γ ⊢ t ~ u ∷ Quot Data Rel) →
    Quot-view ⊢Γ ⊩A t (ne t-n) u (ne u-n)

opaque

  -- The view is inhabited.

  Quot-view-inhabited :
    (⊩A : Γ ⊩′⟨ ℓ ⟩Quot A) →
    let open _⊩ₗQuot_ ⊩A in
    ((t′ , u′ , t⇒*t′ , _ , t′-quot , u′-quot , _) :
     Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / Quot ⊩A) →
    Quot-view (wf (subset* ⇒*Quot)) ⊩A t′ t′-quot u′ u′-quot
  Quot-view-inhabited _ (_ , _ , _ , _ , class , class , inj₁ t″≡u″) =
    equal t″≡u″
  Quot-view-inhabited
    _ (_ , _ , _ , _ , class , class , inj₂ (ok , rel)) =
    related ok rel
  Quot-view-inhabited _ (_ , _ , _ , _ , ne t′-ne , ne u′-ne , t′~u′) =
    ne t′-ne u′-ne t′~u′
  Quot-view-inhabited _ (_ , _ , _ , _ , class , ne _ , ())
  Quot-view-inhabited _ (_ , _ , _ , _ , ne _ , class , ())

opaque

  -- The quotient view can be used to fill in parts of the data for
  -- well-formed equality between quotient terms.

  Quot-view-inhabited⁻¹′ :
    {⊢Γ : ⊢ Γ} (⊩A : Γ ⊩′⟨ ℓ ⟩Quot A) →
    let open _⊩ₗQuot_ ⊩A in
    (t⇒*t′ : Γ ⊢ t ⇒* t′ ∷ Quot Data Rel)
    (u⇒*u′ : Γ ⊢ u ⇒* u′ ∷ Quot Data Rel)
    (t′-q : Quotientᵃₗ (Γ .defs) t′)
    (u′-q : Quotientᵃₗ (Γ .defs) u′) →
    Quot-view ⊢Γ ⊩A t′ t′-q u′ u′-q →
    Quotientᵃ-rec t′-q
      (λ t″ →
         Quotientᵃ-rec u′-q
           (λ u″ →
              Γ ⊩⟨ ℓ ⟩ t″ ≡ u″ ∷ wk id Data / ⊩Data (⊢ʷᵏʳid ⊢Γ) ⊎
              Equality-reflection ×
              ⊩Quot-related ℓ Γ t″ u″ (⊢ʷᵏʳid ⊢Γ) ⊩A)
           (L.Lift _ ⊥))
      (Quotientᵃ-rec u′-q
         (λ _ → L.Lift _ ⊥)
         (Γ ⊢ t′ ~ u′ ∷ Quot Data Rel))
  Quot-view-inhabited⁻¹′ _ _ _ _ _ (equal t≡u)      = inj₁ t≡u
  Quot-view-inhabited⁻¹′ _ _ _ _ _ (related ok rel) =
    inj₂ (ok , rel)
  Quot-view-inhabited⁻¹′ _ _ _ _ _ (ne t-n u-n t~u) =
    t~u

opaque

  -- Given a suitable instance of Quot-view one can prove that
  -- Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Quot ⊩A holds.

  Quot-view-inhabited⁻¹ :
    (⊩A : Γ ⊩′⟨ ℓ ⟩Quot A) →
    let open _⊩ₗQuot_ ⊩A in
    (t⇒*t′ : Γ ⊢ t ⇒* t′ ∷ Quot Data Rel)
    (u⇒*u′ : Γ ⊢ u ⇒* u′ ∷ Quot Data Rel) →
    Quot-view (wf (subset* ⇒*Quot)) ⊩A t′ t′-q u′ u′-q →
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A / Quot ⊩A
  Quot-view-inhabited⁻¹ {t′-q} {u′-q} _ t⇒*t′ u⇒*u′ ok =
    _ , _ , t⇒*t′ , u⇒*u′ , t′-q , u′-q ,
    Quot-view-inhabited⁻¹′ _ t⇒*t′ u⇒*u′ _ _ ok

-- A unary variant of Quot-view.
--
-- Note that there is no counterpart to the constructor
-- Quot-view.related.

data Quot-view₁
       {Γ : Cons m n} (⊢Γ : ⊢ Γ) (⊩A : Γ ⊩′⟨ ℓ ⟩Quot A) :
       (t : Term n) → Quotientᵃₗ (Γ .defs) t → Set a where
  class :
    let open _⊩ₗQuot_ ⊩A
        id-Γ = ⊢ʷᵏʳid ⊢Γ
    in
    (⊩t : Γ ⊩⟨ ℓ ⟩ t ∷ wk id Data / ⊩Data id-Γ) →
    Quot-view₁ ⊢Γ ⊩A (class t) class
  ne :
    let open _⊩ₗQuot_ ⊩A in
    (t-n : Neutralᵃₗ (Γ .defs) t)
    (t~ : Γ ⊢~ t ∷ Quot Data Rel) →
    Quot-view₁ ⊢Γ ⊩A t (ne t-n)

opaque

  -- A variant of Quot-view₁⇔ (which is defined below).

  Quot-view₁⇔′ :
    {⊢Γ : ⊢ Γ} {⊩A : Γ ⊩′⟨ ℓ ⟩Quot A}
    ({t-q} t-q′ : Quotientᵃₗ (Γ .defs) t) →
    let open _⊩ₗQuot_ ⊩A
        id-Γ = ⊢ʷᵏʳid ⊢Γ
    in
    Quot-view₁ ⊢Γ ⊩A t t-q ⇔
    Quotientᵃ-rec t-q
      (λ t′ →
         Quotientᵃ-rec t-q′
           (λ t″ →
              Γ ⊩⟨ ℓ ⟩ t′ ≡ t″ ∷ wk id Data / ⊩Data id-Γ ⊎
              Equality-reflection ×
              ⊩Quot-related ℓ Γ t′ t″ (⊢ʷᵏʳid ⊢Γ) ⊩A)
           (L.Lift _ ⊥))
      (Quotientᵃ-rec t-q′
         (λ _ → L.Lift _ ⊥)
         (Γ ⊢ t ~ t ∷ Quot Data Rel))
  Quot-view₁⇔′ {Γ} {ℓ} {⊢Γ} {⊩A} {t-q} t-q′ =
    lemma₁ t-q′ , lemma₂ _ t-q′
    where
    open _⊩ₗQuot_ ⊩A

    id-Γ : Γ ⊢ʷᵏʳ id ∷ Γ
    id-Γ = ⊢ʷᵏʳid ⊢Γ

    lemma₁ :
      ({t-q} t-q′ : Quotientᵃₗ (Γ .defs) t) →
      Quot-view₁ ⊢Γ ⊩A t t-q →
      Quotientᵃ-rec t-q
        (λ t′ →
           Quotientᵃ-rec t-q′
             (λ t″ →
                Γ ⊩⟨ ℓ ⟩ t′ ≡ t″ ∷ wk id Data / ⊩Data id-Γ ⊎
                Equality-reflection ×
                ⊩Quot-related ℓ Γ t′ t″ (⊢ʷᵏʳid ⊢Γ) ⊩A)
             (L.Lift _ ⊥))
        (Quotientᵃ-rec t-q′
           (λ _ → L.Lift _ ⊥)
           (Γ ⊢ t ~ t ∷ Quot Data Rel))
    lemma₁ class          (class ⊩t)       = inj₁ ⊩t
    lemma₁ class          (ne (ne () _) _)
    lemma₁ (ne (ne () _)) (class _)
    lemma₁ (ne _)         (ne _ t~)        = t~

    lemma₂ :
      (t-q t-q′ : Quotientᵃₗ (Γ .defs) t) →
      Quotientᵃ-rec t-q
        (λ t′ →
           Quotientᵃ-rec t-q′
             (λ t″ →
                Γ ⊩⟨ ℓ ⟩ t′ ≡ t″ ∷ wk id Data / ⊩Data id-Γ ⊎
                Equality-reflection ×
                ⊩Quot-related ℓ Γ t′ t″ (⊢ʷᵏʳid ⊢Γ) ⊩A)
             (L.Lift _ ⊥))
        (Quotientᵃ-rec t-q′
           (λ _ → L.Lift _ ⊥)
           (Γ ⊢ t ~ t ∷ Quot Data Rel)) →
      Quot-view₁ ⊢Γ ⊩A t t-q
    lemma₂ class  (ne _) ()
    lemma₂ (ne _) class  ()
    lemma₂ (ne n) (ne _) t~               = ne n t~
    lemma₂ class  class  (inj₁ ⊩t)        = class ⊩t
    lemma₂ class  class  (inj₂ (_ , rel)) =
      class $ proj₁ $
      Symmetric-transitive-closure-elim-×
        (λ (⊩t , ⊩u , _) → ⊩t , ⊩u) rel

opaque

  -- The relation Quot-view₁ is pointwise logically equivalent to a
  -- certain relation (given a certain assumption).

  Quot-view₁⇔ :
    {⊢Γ : ⊢ Γ} {⊩A : Γ ⊩′⟨ ℓ ⟩Quot A} {t-q : Quotientᵃₗ (Γ .defs) t} →
    let open _⊩ₗQuot_ ⊩A
        id-Γ = ⊢ʷᵏʳid ⊢Γ
    in
    Quot-view₁ ⊢Γ ⊩A t t-q ⇔
    Quotientᵃ-rec t-q
      (λ t′ →
         Quotientᵃ-rec t-q
           (λ t″ →
              Γ ⊩⟨ ℓ ⟩ t′ ≡ t″ ∷ wk id Data / ⊩Data id-Γ ⊎
              Equality-reflection ×
              ⊩Quot-related ℓ Γ t′ t″ (⊢ʷᵏʳid ⊢Γ) ⊩A)
           (L.Lift _ ⊥))
      (Quotientᵃ-rec t-q
         (λ _ → L.Lift _ ⊥)
         (Γ ⊢ t ~ t ∷ Quot Data Rel))
  Quot-view₁⇔ {t-q} = Quot-view₁⇔′ t-q

-- Unary term reducibility for quotients.

infix 4 _⊩⟨_⟩Quot_∷_/_

record _⊩⟨_⟩Quot_∷_/_ (Γ : Cons m n) (ℓ : Universe-level) (t A : Term n)
         (⊩A : Γ ⊩′⟨ ℓ ⟩Quot A) : Set a where
  no-eta-equality
  pattern
  constructor Quot
  open _⊩ₗQuot_ ⊩A
  field
    {w}  : Term n
    ⇒*w  : Γ ⊢ t ⇒* w ∷ Quot Data Rel
    w-q  : Quotientᵃₗ (Γ .defs) w
    prop : Quot-view₁ (wf (subset* ⇒*Quot)) ⊩A w w-q

opaque

  -- The relation _⊩⟨_⟩Quot_∷_/_ is pointwise logically equivalent to
  -- the diagonal of a certain relation.

  ⊩Quot∷⇔⊩Quot≡∷ :
    (⊩A : Γ ⊩′⟨ ℓ ⟩Quot A) →
    Γ ⊩⟨ ℓ ⟩Quot t ∷ A / ⊩A ⇔
    LogRel._⊩ₗQuot_≡_∷_/_ ℓ kit′ Γ t t A ⊩A
  ⊩Quot∷⇔⊩Quot≡∷ _ =
      (λ ⊩t →
         let open _⊩⟨_⟩Quot_∷_/_ ⊩t in
         _ , _ , ⇒*w , ⇒*w , w-q , w-q ,
         Quot-view₁⇔ .proj₁ prop)
    , (λ (u , v , t⇒u , t⇒v , u-q , v-q , rest) →
         record
           { ⇒*w  = t⇒u
           ; w-q  = u-q
           ; prop =
               case whrDet*Term (t⇒u , Quotientᵃ→Whnf u-q)
                      (t⇒v , Quotientᵃ→Whnf v-q) of λ {
                 PE.refl →
               Quot-view₁⇔′ v-q .proj₂ rest }
           })
