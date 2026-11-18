------------------------------------------------------------------------
-- The predicates No-[]-cong-Quot and No-[]-cong-Quot′
------------------------------------------------------------------------

module Definition.Untyped.No-box-cong-Quot {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Empty
open import Tools.Function
import Tools.Level as L
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.Relation
open import Tools.Unit

private variable
  A B : Set a
  n   : Nat
  k   : Term-kind

-- If the type is inhabited, then the term does not contain any
-- occurrences of []-cong or quotient primitives.

No-[]-cong-Quot′ : Set a → Term[ k ] n → Set a
No-[]-cong-Quot′ _ (var _)                 = L.Lift _ ⊤
No-[]-cong-Quot′ _ (defn _)                = L.Lift _ ⊤
No-[]-cong-Quot′ _ Level                   = L.Lift _ ⊤
No-[]-cong-Quot′ _ zeroᵘ                   = L.Lift _ ⊤
No-[]-cong-Quot′ X (sucᵘ t)                = No-[]-cong-Quot′ X t
No-[]-cong-Quot′ X (t supᵘ u)              = No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X u
No-[]-cong-Quot′ _ (ωᵘ+ _)                 = L.Lift _ ⊤
No-[]-cong-Quot′ X (level t)               = No-[]-cong-Quot′ X t
No-[]-cong-Quot′ X (U l)                   = No-[]-cong-Quot′ X l
No-[]-cong-Quot′ X (Lift l A)              = No-[]-cong-Quot′ X l ×
                                             No-[]-cong-Quot′ X A
No-[]-cong-Quot′ X (lift t)                = No-[]-cong-Quot′ X t
No-[]-cong-Quot′ X (lower t)               = No-[]-cong-Quot′ X t
No-[]-cong-Quot′ _ Empty                   = L.Lift _ ⊤
No-[]-cong-Quot′ X (emptyrec _ A t)        = No-[]-cong-Quot′ X A ×
                                             No-[]-cong-Quot′ X t
No-[]-cong-Quot′ _ (Unit _)                = L.Lift _ ⊤
No-[]-cong-Quot′ _ (star _)                = L.Lift _ ⊤
No-[]-cong-Quot′ X (unitrec _ _ A t u)     = No-[]-cong-Quot′ X A ×
                                             No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X u
No-[]-cong-Quot′ X (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) = No-[]-cong-Quot′ X A ×
                                             No-[]-cong-Quot′ X B
No-[]-cong-Quot′ X (lam _ t)               = No-[]-cong-Quot′ X t
No-[]-cong-Quot′ X (t ∘⟨ _ ⟩ u)            = No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X u
No-[]-cong-Quot′ X (prod _ _ t u)          = No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X u
No-[]-cong-Quot′ X (fst _ t)               = No-[]-cong-Quot′ X t
No-[]-cong-Quot′ X (snd _ t)               = No-[]-cong-Quot′ X t
No-[]-cong-Quot′ X (prodrec _ _ _ A t u)   = No-[]-cong-Quot′ X A ×
                                             No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X u
No-[]-cong-Quot′ _ ℕ                       = L.Lift _ ⊤
No-[]-cong-Quot′ _ zero                    = L.Lift _ ⊤
No-[]-cong-Quot′ X (suc t)                 = No-[]-cong-Quot′ X t
No-[]-cong-Quot′ X (natrec _ _ _ A t u v)  = No-[]-cong-Quot′ X A ×
                                             No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X u ×
                                             No-[]-cong-Quot′ X v
No-[]-cong-Quot′ X (Id A t u)              = No-[]-cong-Quot′ X A ×
                                             No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X u
No-[]-cong-Quot′ _ rfl                     = L.Lift _ ⊤
No-[]-cong-Quot′ X (J _ _ A t B u v w)     = No-[]-cong-Quot′ X A ×
                                             No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X B ×
                                             No-[]-cong-Quot′ X u ×
                                             No-[]-cong-Quot′ X v ×
                                             No-[]-cong-Quot′ X w
No-[]-cong-Quot′ X (K _ A t B u v)         = No-[]-cong-Quot′ X A ×
                                             No-[]-cong-Quot′ X t ×
                                             No-[]-cong-Quot′ X B ×
                                             No-[]-cong-Quot′ X u ×
                                             No-[]-cong-Quot′ X v
No-[]-cong-Quot′ X ([]-cong _ _ _ _ _ _)   = ¬ X
No-[]-cong-Quot′ X (Quot _ _)              = ¬ X
No-[]-cong-Quot′ X (class _)               = ¬ X
No-[]-cong-Quot′ X (resp _ _ _ _ _)        = ¬ X
No-[]-cong-Quot′ X (set _ _ _ _ _ _)       = ¬ X
No-[]-cong-Quot′ X (qrec _ _ _ _ _)        = ¬ X

-- The term does not contain any occurrences of []-cong or quotient
-- primitives.

No-[]-cong-Quot : Term[ k ] n → Set a
No-[]-cong-Quot = No-[]-cong-Quot′ (L.Lift _ ⊤)

opaque

  -- A characterisation lemma for No-[]-cong-Quot′.
  --
  -- An advantage of No-[]-cong-Quot′ A t over A → No-[]-cong-Quot t
  -- is that there is no function space that gets in the way when one
  -- "extracts components" (for instance when one obtains values of
  -- the types No-[]-cong-Quot′ A t and No-[]-cong-Quot′ A u from a
  -- value of type No-[]-cong-Quot′ A (prod s p t u)).

  No-[]-cong-Quot′⇔ :
    (t : Term[ k ] n) →
    No-[]-cong-Quot′ A t ⇔ (A → No-[]-cong-Quot t)
  No-[]-cong-Quot′⇔ (var _) =
    _
  No-[]-cong-Quot′⇔ (defn _) =
    _
  No-[]-cong-Quot′⇔ Level =
    _
  No-[]-cong-Quot′⇔ zeroᵘ =
    _
  No-[]-cong-Quot′⇔ (sucᵘ t) =
    No-[]-cong-Quot′⇔ t
  No-[]-cong-Quot′⇔ (t supᵘ u) =
    (λ (t′ , u′) x →
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂ (proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (ωᵘ+ _) =
    _
  No-[]-cong-Quot′⇔ (level t) =
    No-[]-cong-Quot′⇔ t
  No-[]-cong-Quot′⇔ (U l) =
    No-[]-cong-Quot′⇔ l
  No-[]-cong-Quot′⇔ (Lift l A) =
    (λ (l′ , A′) x →
       No-[]-cong-Quot′⇔ l .proj₁ l′ x ,
       No-[]-cong-Quot′⇔ A .proj₁ A′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ l .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ A .proj₂ (proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (lift t) =
    No-[]-cong-Quot′⇔ t
  No-[]-cong-Quot′⇔ (lower t) =
    No-[]-cong-Quot′⇔ t
  No-[]-cong-Quot′⇔ Empty =
    _
  No-[]-cong-Quot′⇔ (emptyrec _ A t) =
    (λ (A′ , t′) x →
       No-[]-cong-Quot′⇔ A .proj₁ A′ x ,
       No-[]-cong-Quot′⇔ t .proj₁ t′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ A .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ t .proj₂ (proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (Unit _) =
    _
  No-[]-cong-Quot′⇔ (star _) =
    _
  No-[]-cong-Quot′⇔ (unitrec _ _ A t u) =
    (λ (A′ , t′ , u′) x →
       No-[]-cong-Quot′⇔ A .proj₁ A′ x ,
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ A .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂ (proj₂ ∘→ proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) =
    (λ (A′ , B′) x →
       No-[]-cong-Quot′⇔ A .proj₁ A′ x ,
       No-[]-cong-Quot′⇔ B .proj₁ B′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ A .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ B .proj₂ (proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (lam _ t) =
    No-[]-cong-Quot′⇔ t
  No-[]-cong-Quot′⇔ (t ∘⟨ _ ⟩ u) =
    (λ (t′ , u′) x →
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂ (proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (prod _ _ t u) =
    (λ (t′ , u′) x →
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂ (proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (fst _ t) =
    No-[]-cong-Quot′⇔ t
  No-[]-cong-Quot′⇔ (snd _ t) =
    No-[]-cong-Quot′⇔ t
  No-[]-cong-Quot′⇔ (prodrec _ _ _ A t u) =
    (λ (A′ , t′ , u′) x →
       No-[]-cong-Quot′⇔ A .proj₁ A′ x ,
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ A .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂ (proj₂ ∘→ proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ ℕ =
    _
  No-[]-cong-Quot′⇔ zero =
    _
  No-[]-cong-Quot′⇔ (suc t) =
    No-[]-cong-Quot′⇔ t
  No-[]-cong-Quot′⇔ (natrec _ _ _ A t u v) =
    (λ (A′ , t′ , u′ , v′) x →
       No-[]-cong-Quot′⇔ A .proj₁ A′ x ,
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x ,
       No-[]-cong-Quot′⇔ v .proj₁ v′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ A .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂ (proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ v .proj₂ (proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (Id A t u) =
    (λ (A′ , t′ , u′) x →
       No-[]-cong-Quot′⇔ A .proj₁ A′ x ,
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ A .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂ (proj₂ ∘→ proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ rfl =
    _
  No-[]-cong-Quot′⇔ (J _ _ A t B u v w) =
    (λ (A′ , t′ , B′ , u′ , v′ , w′) x →
       No-[]-cong-Quot′⇔ A .proj₁ A′ x ,
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ B .proj₁ B′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x ,
       No-[]-cong-Quot′⇔ v .proj₁ v′ x ,
       No-[]-cong-Quot′⇔ w .proj₁ w′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ A .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ B .proj₂ (proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂
         (proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ v .proj₂
         (proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ w .proj₂
         (proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ (K _ A t B u v) =
    (λ (A′ , t′ , B′ , u′ , v′) x →
       No-[]-cong-Quot′⇔ A .proj₁ A′ x ,
       No-[]-cong-Quot′⇔ t .proj₁ t′ x ,
       No-[]-cong-Quot′⇔ B .proj₁ B′ x ,
       No-[]-cong-Quot′⇔ u .proj₁ u′ x ,
       No-[]-cong-Quot′⇔ v .proj₁ v′ x) ,
    (λ f →
       No-[]-cong-Quot′⇔ A .proj₂ (proj₁ ∘→ f) ,
       No-[]-cong-Quot′⇔ t .proj₂ (proj₁ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ B .proj₂ (proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ u .proj₂
         (proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ f) ,
       No-[]-cong-Quot′⇔ v .proj₂
         (proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ f))
  No-[]-cong-Quot′⇔ ([]-cong _ _ _ _ _ _) =
    (λ f x _ → f x) , (λ f x → f x _)
  No-[]-cong-Quot′⇔ (Quot _ _) =
    (λ f x _ → f x) , (λ f x → f x _)
  No-[]-cong-Quot′⇔ (class _) =
    (λ f x _ → f x) , (λ f x → f x _)
  No-[]-cong-Quot′⇔ (resp _ _ _ _ _) =
    (λ f x _ → f x) , (λ f x → f x _)
  No-[]-cong-Quot′⇔ (set _ _ _ _ _ _) =
    (λ f x _ → f x) , (λ f x → f x _)
  No-[]-cong-Quot′⇔ (qrec _ _ _ _ _) =
    (λ f x _ → f x) , (λ f x → f x _)

opaque

  -- If A is not inhabited, then No-[]-cong-Quot′ A t holds.

  ¬→No-[]-cong-Quot′ : ¬ A → (t : Term[ k ] n) → No-[]-cong-Quot′ A t
  ¬→No-[]-cong-Quot′ {A} ¬A t =
    No-[]-cong-Quot′⇔ t .proj₂ (⊥-elim ∘→ ¬A)

opaque

  -- A map function for No-[]-cong-Quot′.

  map-No-[]-cong-Quot′ :
    (A → B) → (t : Term[ k ] n) →
    No-[]-cong-Quot′ B t → No-[]-cong-Quot′ A t
  map-No-[]-cong-Quot′ {A} {B} f t =
    No-[]-cong-Quot′ B t     →⟨ No-[]-cong-Quot′⇔ t .proj₁ ⟩
    (B → No-[]-cong-Quot t)  →⟨ _∘→ f ⟩
    (A → No-[]-cong-Quot t)  →⟨ No-[]-cong-Quot′⇔ t .proj₂ ⟩
    No-[]-cong-Quot′ A t     □
