------------------------------------------------------------------------
-- Decidability of bi-directional typechecking (given certain
-- assumptions)
------------------------------------------------------------------------

open import Definition.Typechecking.Decidable.Assumptions
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typechecking.Decidable
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as
open Type-restrictions R

open import Definition.Typechecking R
open import Definition.Typechecking.Soundness R
open import Definition.Typechecking.Deterministic R
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.NeTypeEq R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Decidable.Equality R _≟_
open import Definition.Typed.Decidable.Reduction R _≟_
open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Neutral M type-variant as U

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation as Dec
open import Tools.Sum

private
  variable
    P : Set a
    n : Nat
    Γ : Con Term n
    l t u v w A B : Term n
    p q r : M

dec⇉-var : (x : Fin n) → ∃ λ A → x ∷ A ∈ Γ
dec⇉-var {Γ = ε}     ()
dec⇉-var {Γ = Γ ∙ A} x0     = _ , here
dec⇉-var {Γ = Γ ∙ B} (x +1) =
  let A , x∷A∈Γ = dec⇉-var x
  in  _ , there x∷A∈Γ

dec⇇-var : (x : Fin n) → Γ ⊢ A → Dec (Γ ⊢ var x ⇇ A)
dec⇇-var x ⊢A =
  let B , x∷B∈Γ = dec⇉-var x
  in  case decEq (syntacticVar x∷B∈Γ (wf ⊢A)) ⊢A of λ where
    (yes B≡A) → yes (infᶜ (varᵢ x∷B∈Γ) B≡A)
    (no B≢A) → no λ where
      (infᶜ (varᵢ x) x₁) → case det∈ x x∷B∈Γ of λ where
        PE.refl → B≢A x₁

mutual

  -- It is decidable whether Checkable-type A holds.

  dec-Checkable-type : (A : Term n) → Dec (Checkable-type A)
  dec-Checkable-type A = helper A (dec-Checkable A)
    where
    helper : (A : Term n) → Dec (Checkable A) → Dec (Checkable-type A)
    helper (Lift l A) _ =
      case dec-Checkable-level l ×-dec dec-Checkable-type A of λ where
        (yes (l , A)) → yes (Liftᶜ l A)
        (no not) → no λ where
          (Liftᶜ l A) → not (l , A)
          (checkᶜ (infᶜ (Liftᵢ l A))) → not (l , checkᶜ (infᶜ A))
    helper (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) _ =
      case dec-Checkable-type A ×-dec dec-Checkable-type B of λ where
        (yes (A , B)) → yes (ΠΣᶜ A B)
        (no not)      → no λ where
          (ΠΣᶜ A B)                 → not (A , B)
          (checkᶜ (infᶜ (ΠΣᵢ A B))) →
            not (checkᶜ (infᶜ A) , checkᶜ B)
    helper (Id A t u) _ =
      case dec-Checkable-type A ×-dec dec-Checkable t ×-dec
           dec-Checkable u of λ where
        (yes (A , t , u)) → yes (Idᶜ A t u)
        (no not)          → no λ where
          (Idᶜ A t u)                 → not (A , t , u)
          (checkᶜ (infᶜ (Idᵢ A t u))) → not (checkᶜ (infᶜ A) , t , u)
    helper A@(var _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper Level = λ where
      (yes A) → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper zeroᵘ = λ where
      (yes A) → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper (sucᵘ _) = λ where
      (yes A) → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper (_ supᵘ _) = λ where
      (yes A) → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper (lift _) = λ where
      (yes A) → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper (lower _) = λ where
      (yes A) → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(U _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(lam _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(_ ∘⟨ _ ⟩ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(prod! _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(fst _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(snd _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(prodrec _ _ _ _ _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@Empty = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(emptyrec _ _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@Unit! = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@star! = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(unitrec _ _ _ _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@ℕ = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@zero = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(suc _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(natrec _ _ _ _ _ _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@rfl = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(J _ _ _ _ _ _ _ -) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@(K _ _ _ _ _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }
    helper A@([]-cong _ _ _ _ _ _) = λ where
      (yes A)  → yes (checkᶜ A)
      (no not) → no λ { (checkᶜ A) → not A }

  -- Decidability of terms being inferable

  dec-Inferable : (t : Term n) → Dec (Inferable t)
  dec-Inferable (var _) =
    yes varᵢ
  dec-Inferable Level =
    yes Levelᵢ
  dec-Inferable zeroᵘ =
    yes zeroᵘᵢ
  dec-Inferable (sucᵘ t) =
    case dec-Checkable t of λ where
      (yes t)  → yes (sucᵘᵢ t)
      (no not) → no λ { (sucᵘᵢ t) → not t }
  dec-Inferable (t supᵘ u) =
    case dec-Checkable t ×-dec dec-Checkable u of λ where
      (yes (t , u))  → yes (supᵘᵢ t u)
      (no not) → no λ { (supᵘᵢ t u) → not (t , u) }
  dec-Inferable (U l) =
    case dec-Checkable-level l of λ where
      (yes l) → yes (Uᵢ l)
      (no not) → no λ { (Uᵢ x) → not x }
  dec-Inferable (Lift l A) =
    case dec-Checkable-level l ×-dec dec-Inferable A of λ where
      (yes (l , A)) → yes (Liftᵢ l A)
      (no not) → no λ { (Liftᵢ l A) → not (l , A) }
  dec-Inferable (lift t) =
    no λ ()
  dec-Inferable (lower t) =
    case dec-Inferable t of λ where
      (yes t)  → yes (lowerᵢ t)
      (no not) → no λ { (lowerᵢ t) → not t }
  dec-Inferable (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
    case dec-Inferable A ×-dec dec-Checkable B of λ where
      (yes (A , B)) → yes (ΠΣᵢ A B)
      (no not)      → no λ { (ΠΣᵢ A B) → not (A , B) }
  dec-Inferable (lam _ _) =
    no λ ()
  dec-Inferable (t ∘⟨ _ ⟩ u) =
    case dec-Inferable t ×-dec dec-Checkable u of λ where
      (yes (t , u)) → yes (∘ᵢ t u)
      (no not)      → no λ { (∘ᵢ t u) → not (t , u) }
  dec-Inferable (prod! _ _) =
    no λ ()
  dec-Inferable (fst _ t) =
    case dec-Inferable t of λ where
      (yes t)  → yes (fstᵢ t)
      (no not) → no λ { (fstᵢ t) → not t }
  dec-Inferable (snd _ t) =
    case dec-Inferable t of λ where
      (yes t)  → yes (sndᵢ t)
      (no not) → no λ { (sndᵢ t) → not t }
  dec-Inferable (prodrec _ _ _ A t u) =
    case dec-Checkable-type A ×-dec dec-Inferable t ×-dec
         dec-Checkable u of λ where
    (yes (A , t , u)) → yes (prodrecᵢ A t u)
    (no not)          → no λ { (prodrecᵢ A t u) → not (A , t , u) }
  dec-Inferable ℕ =
    yes ℕᵢ
  dec-Inferable zero =
    yes zeroᵢ
  dec-Inferable (suc t) =
    case dec-Checkable t of λ where
      (yes t)  → yes (sucᵢ t)
      (no not) → no λ { (sucᵢ t) → not t }
  dec-Inferable (natrec _ _ _ A t u v) =
    case dec-Checkable-type A ×-dec dec-Checkable t ×-dec
         dec-Checkable u ×-dec dec-Checkable v of λ where
      (yes (A , t , u , v)) → yes (natrecᵢ A t u v)
      (no not)              →
        no λ { (natrecᵢ A t u v) → not (A , t , u , v) }
  dec-Inferable (Unit _) =
    yes Unitᵢ
  dec-Inferable (star _) =
    yes starᵢ
  dec-Inferable (unitrec _ _ A t u) =
    case dec-Checkable-type A ×-dec dec-Checkable t ×-dec
         dec-Checkable u of λ where
      (yes (A , t , u)) → yes (unitrecᵢ A t u)
      (no not)          → no λ { (unitrecᵢ A t u) → not (A , t , u) }
  dec-Inferable Empty =
    yes Emptyᵢ
  dec-Inferable (emptyrec p A t) =
    case dec-Checkable-type A ×-dec dec-Checkable t of λ where
      (yes (A , t)) → yes (emptyrecᵢ A t)
      (no not)      → no λ { (emptyrecᵢ A t) → not (A , t) }
  dec-Inferable (Id A t u) =
    case dec-Inferable A ×-dec dec-Checkable t ×-dec
         dec-Checkable u of λ where
      (yes (A , t , u)) → yes (Idᵢ A t u)
      (no not)          → no λ { (Idᵢ A t u) → not (A , t , u) }
  dec-Inferable rfl =
    no λ ()
  dec-Inferable (J _ _ A t B u v w) =
    case dec-Checkable-type A ×-dec dec-Checkable t ×-dec
         dec-Checkable-type B ×-dec dec-Checkable u ×-dec
         dec-Checkable v ×-dec dec-Checkable w of λ where
      (yes (A , t , B , u , v , w)) → yes (Jᵢ A t B u v w)
      (no not)                      →
        no λ { (Jᵢ A t B u v w) → not (A , t , B , u , v , w) }
  dec-Inferable (K _ A t B u v) =
    case dec-Checkable-type A ×-dec dec-Checkable t ×-dec
         dec-Checkable-type B ×-dec dec-Checkable u ×-dec
         dec-Checkable v of λ where
      (yes (A , t , B , u , v)) → yes (Kᵢ A t B u v)
      (no not)                  →
        no λ { (Kᵢ A t B u v) → not (A , t , B , u , v) }
  dec-Inferable ([]-cong s l A t u v) =
    case dec-Checkable-level l ×-dec dec-Checkable-type A ×-dec
         dec-Checkable t ×-dec dec-Checkable u ×-dec
         dec-Checkable v of λ where
      (yes (l , A , t , u , v)) → yes ([]-congᵢ l A t u v)
      (no not)                  →
        no λ { ([]-congᵢ l A t u v) → not (l , A , t , u , v) }

  -- Decidability of terms being checkable

  dec-Checkable : (t : Term n) → Dec (Checkable t)
  dec-Checkable t = helper t (dec-Inferable t)
    where
    helper : (t : Term n) → Dec (Inferable t) → Dec (Checkable t)
    helper (lift t) _ =
      case dec-Checkable t of λ where
        (yes t)  → yes (liftᶜ t)
        (no not) → no λ where
          (liftᶜ x) → not x
          (infᶜ ())
    helper (lam _ t) _ =
      case dec-Checkable t of λ where
        (yes t)  → yes (lamᶜ t)
        (no not) → no λ where
          (lamᶜ t)  → not t
          (infᶜ ())
    helper (prod! t u) _ =
      case dec-Checkable t ×-dec dec-Checkable u of λ where
        (yes (t , u)) → yes (prodᶜ t u)
        (no not)      → no λ where
          (prodᶜ t u) → not (t , u)
          (infᶜ ())
    helper rfl _ =
      yes rflᶜ
    helper (var _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper Level = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper zeroᵘ = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (sucᵘ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (_ supᵘ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (U _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (Lift _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (lower _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (_ ∘⟨ _ ⟩ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (fst _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (snd _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (prodrec _ _ _ _ _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper ℕ = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper zero = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (suc _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (natrec _ _ _ _ _ _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper Unit!  = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper star! = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (unitrec _ _ _ _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper Empty = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (emptyrec _ _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (Id _ t u) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (J _ _ _ _ _ _ _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper (K _ _ _ _ _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper ([]-cong _ _ _ _ _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }

  -- It is decidable whether Checkable-level l holds.

  dec-Checkable-level : (l : Term n) → Dec (Checkable-level l)
  dec-Checkable-level l =
    case Level-allowed? of λ where
      (yes ok) →
        Dec-map (sym⇔ $ Checkable-level⇔ ok) $
        dec-Checkable l
      (no not-ok) →
        yes (literal not-ok)

private opaque

  -- A variant of isΠΣ.

  isΠΣ-with-cont :
    {Γ : Con Term n}
    {P : BinderMode → M → M → Term n → Term (1+ n) → Set a} →
    Γ ⊢ A →
    (∀ {b p q B C} →
     Γ ⊢ B → Γ ∙ B ⊢ C → ΠΣ-allowed b p q →
     Γ ⊢ A ↘ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C → Dec (P b p q B C)) →
    Dec
      (∃ λ ((b , p , q , B , C , _) :
            ∃₅ λ b p q B C → Γ ⊢ A ↘ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C) →
       P b p q B C)
  isΠΣ-with-cont {P} ⊢A cont =
    Σ-dec
      (Dec.map
         (λ (_ , _ , _ , _ , _ , A⇒*ΠΣ) →
            _ , _ , _ , _ , _ , A⇒*ΠΣ , ΠΣₙ)
         (λ (_ , _ , _ , _ , _ , A⇒*ΠΣ , _) →
            _ , _ , _ , _ , _ , A⇒*ΠΣ) $
       isΠΣ ⊢A)
      (λ (_ , _ , _ , _ , _ , A↘ΠΣ₁) (_ , _ , _ , _ , _ , A↘ΠΣ₂) →
         case whrDet* A↘ΠΣ₁ A↘ΠΣ₂ of λ { PE.refl → idᶠ })
      (λ (_ , _ , _ , _ , _ , A↘ΠΣ) →
         let ⊢B , ⊢C , ok =
               inversion-ΠΣ (syntacticRed (A↘ΠΣ .proj₁) .proj₂)
         in
         cont ⊢B ⊢C ok A↘ΠΣ)

private opaque

  -- A variant of ⇒*U?.

  ↘U? : Γ ⊢ A → Dec (∃ λ l → Γ ⊢ A ↘ U l)
  ↘U? = Dec.map (Σ.map idᶠ (_, Uₙ)) (Σ.map idᶠ proj₁) ∘→ ⇒*U?

mutual

  private

    -- Some lemmas used below.

    dec⇉-with-cont :
      {Γ : Con Term n} {P : Term n → Set a} →
      ⊢ Γ → Inferable t → (∀ {A} → Γ ⊢ A → Γ ⊢ t ∷ A → Dec (P A)) →
      Dec (Σ (∃ λ A → Γ ⊢ t ⇉ A) (P ∘→ proj₁))
    dec⇉-with-cont ⊢Γ t cont =
      Σ-dec (dec⇉ ⊢Γ t)
        (λ (_ , t₁) (_ , t₂) →
           case deterministic⇉ t₁ t₂ of λ { PE.refl → idᶠ })
        (uncurry cont ∘→ soundness⇉ ⊢Γ ∘→ proj₂)

    dec⇇-with-cont :
      Checkable t → Γ ⊢ A → (Γ ⊢ t ∷ A → Dec P) → Dec (Γ ⊢ t ⇇ A × P)
    dec⇇-with-cont t ⊢A cont =
      dec⇇ t ⊢A ×-dec′ cont ∘→ soundness⇇

    dec⇇Level-with-cont :
      Checkable-level l → ⊢ Γ → (Γ ⊢ l ∷Level → Dec P) →
      Dec (Γ ⊢ l ⇇Level × P)
    dec⇇Level-with-cont l ⊢Γ cont =
      dec⇇Level l ⊢Γ ×-dec′ cont ∘→ soundness⇇Level ⊢Γ

    dec⇇Type-with-cont :
      ⊢ Γ → Checkable-type A → (Γ ⊢ A → Dec P) → Dec (Γ ⊢ A ⇇Type × P)
    dec⇇Type-with-cont ⊢Γ A cont =
      dec⇇Type ⊢Γ A ×-dec′ cont ∘→ soundness⇇Type ⊢Γ

    dec⇉Type-with-cont :
      ⊢ Γ → Inferable A → (Γ ⊢ A → Dec P) → Dec (Γ ⊢ A ⇇Type × P)
    dec⇉Type-with-cont ⊢Γ A cont =
      dec⇉Type ⊢Γ A ×-dec′ cont ∘→ soundness⇇Type ⊢Γ

    dec⇉-lower : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ lower t ⇉ A)
    dec⇉-lower ⊢Γ t =
      case (dec⇉-with-cont ⊢Γ t λ ⊢A _ → isLift ⊢A) of λ where
        (yes ((_ , t) , (_ , _ , A))) → yes (_ , lowerᵢ t (A , Liftₙ))
        (no not) → no λ { (_ , lowerᵢ t (A , _)) → not ((_ , t) , (_ , _ , A)) }

    dec⇉-app :
      ⊢ Γ → Inferable t → Checkable u →
      Dec (∃ λ A → Γ ⊢ t ∘⟨ p ⟩ u ⇉ A)
    dec⇉-app {p} ⊢Γ t u =
      case
        (dec⇉-with-cont ⊢Γ t λ ⊢A _ →
         isΠΣ-with-cont ⊢A λ {b = b} {p = p′} ⊢B _ _ _ →
         decBinderMode b BMΠ ×-dec p ≟ p′ ×-dec dec⇇ u ⊢B)
        of λ where
        (yes
           ((_ , t) , (_ , _ , _ , _ , _ , A) ,
            PE.refl , PE.refl , u)) →
          yes (_ , appᵢ t A u)
        (no not) →
          no λ { (_ , appᵢ t A u) →
          not
            ( (_ , t)
            , (_ , _ , _ , _ , _ , A)
            , PE.refl , PE.refl , u
            ) }

    dec⇉-fst : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ fst p t ⇉ A)
    dec⇉-fst {p} ⊢Γ t =
      case
        (dec⇉-with-cont ⊢Γ t λ ⊢A _ →
         isΠΣ-with-cont ⊢A λ {b = b} {p = p′} ⊢B _ _ _ →
         decBinderMode b (BMΣ 𝕤) ×-dec p ≟ p′)
        of λ where
        (yes
           ((_ , t) , (_ , _ , _ , _ , _ , A) ,
            PE.refl , PE.refl)) →
          yes (_ , fstᵢ t A)
        (no not) →
          no λ { (_ , fstᵢ t A) →
          not
            ( (_ , t)
            , (_ , _ , _ , _ , _ , A)
            , PE.refl , PE.refl
            ) }

    dec⇉-snd : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ snd p t ⇉ A)
    dec⇉-snd {p} ⊢Γ t =
      case
        (dec⇉-with-cont ⊢Γ t λ ⊢A _ →
         isΠΣ-with-cont ⊢A λ {b = b} {p = p′} ⊢B _ _ _ →
         decBinderMode b (BMΣ 𝕤) ×-dec p ≟ p′)
        of λ where
        (yes ((_ , t) , (_ , _ , _ , _ , _ , A) , PE.refl , PE.refl)) →
          yes (_ , sndᵢ t A)
        (no not) →
          no λ { (_ , sndᵢ t A) →
          not
            ( (_ , t)
            , (_ , _ , _ , _ , _ , A)
            , PE.refl , PE.refl
            ) }

    dec⇉-natrec :
      ⊢ Γ → Checkable-type A → Checkable t → Checkable u → Checkable v →
      Dec (∃ λ B → Γ ⊢ natrec p q r A t u v ⇉ B)
    dec⇉-natrec ⊢Γ A t u v =
      case
        (dec⇇Type-with-cont (⊢Γ ∙[ ⊢ℕ ]) A λ ⊢A →
         dec⇇ t (substType ⊢A (zeroⱼ ⊢Γ)) ×-dec
         dec⇇ u (subst↑²Type ⊢A (sucⱼ (var₁ ⊢A))) ×-dec
         dec⇇ v (⊢ℕ ⊢Γ))
        of λ where
        (yes (A , t , u , v)) → yes (_ , natrecᵢ A t u v)
        (no not)              →
          no λ { (_ , natrecᵢ A t u v) → not (A , t , u , v) }

    dec⇉-prodrec :
      ⊢ Γ → Checkable-type A → Inferable t → Checkable u →
      Dec (∃ λ B → Γ ⊢ prodrec r p q A t u ⇉ B)
    dec⇉-prodrec {p} ⊢Γ A t u =
      case
        (dec⇉-with-cont ⊢Γ t λ ⊢B _ →
         isΠΣ-with-cont ⊢B λ {b = b} {p = p′} _ ⊢D ok _ →
         decBinderMode b (BMΣ 𝕨) ×-dec′ λ b≡ →
         p ≟ p′ ×-dec
         dec⇇Type-with-cont (∙ ΠΣⱼ ⊢D ok) A λ ⊢A →
         dec⇇ u
           (subst↑²Type-prod
              (PE.subst (λ b → _ ∙ ΠΣ⟨ b ⟩ _ , _ ▷ _ ▹ _ ⊢ _) b≡ ⊢A)))
        of λ where
        (yes
           ((_ , t) , (_ , _ , _ , _ , _ , A↘) ,
            PE.refl , PE.refl , A , u)) →
          yes (_ , prodrecᵢ A t A↘ u)
        (no not) →
          no λ { (_ , prodrecᵢ A t A↘ u) →
          not
            ( (_ , t)
            , (_ , _ , _ , _ , _ , A↘)
            , PE.refl , PE.refl , A , u
            ) }

    dec⇉-emptyrec :
      ⊢ Γ → Checkable-type A → Checkable t →
      Dec (∃ λ B → Γ ⊢ emptyrec p A t ⇉ B)
    dec⇉-emptyrec ⊢Γ A t =
      case dec⇇Type ⊢Γ A ×-dec dec⇇ t (⊢Empty ⊢Γ) of λ where
        (yes (A , t)) → yes (_ , emptyrecᵢ A t)
        (no not)      → no λ { (_ , emptyrecᵢ A t) → not (A , t) }

    dec⇉-unitrec :
      ⊢ Γ → Checkable-type A → Checkable t → Checkable u →
      Dec (∃ λ B → Γ ⊢ unitrec p q A t u ⇉ B)
    dec⇉-unitrec ⊢Γ A t u =
      case
        (Unit-allowed? 𝕨 ×-dec′ λ ok →
         let ⊢Unit = ⊢Unit ⊢Γ ok in
         dec⇇Type-with-cont (∙ ⊢Unit) A λ ⊢A →
         dec⇇ t ⊢Unit ×-dec
         dec⇇ u (substType ⊢A (starⱼ ⊢Γ ok)))
        of λ where
        (yes (_ , A , t , u)) → yes (_ , unitrecᵢ A t u)
        (no not)              →
          no λ { (_ , unitrecᵢ A t u) →
          not (⊢∷Unit→Unit-allowed (soundness⇇ t) , A , t , u) }

    dec⇉-J :
      ⊢ Γ → Checkable-type A → Checkable t → Checkable-type B →
      Checkable u → Checkable v → Checkable w →
      Dec (∃ λ C → Γ ⊢ J p q A t B u v w ⇉ C)
    dec⇉-J ⊢Γ A t B u v w =
      case
        (dec⇇Type-with-cont ⊢Γ A λ ⊢A →
         dec⇇-with-cont t ⊢A λ ⊢t →
         dec⇇Type-with-cont (∙ Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A)) B λ ⊢B →
         dec⇇ u
           (substType₂ ⊢B ⊢t $
            PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ $
            rflⱼ ⊢t) ×-dec
         dec⇇-with-cont v ⊢A λ ⊢v →
         dec⇇ w (Idⱼ′ ⊢t ⊢v))
        of λ where
        (yes (A , t , B , u , v , w)) → yes (_ , Jᵢ A t B u v w)
        (no not)                      →
          no λ { (_ , Jᵢ A t B u v w) → not (A , t , B , u , v , w) }

    dec⇉-K :
      ⊢ Γ → Checkable-type A → Checkable t → Checkable-type B →
      Checkable u → Checkable v →
      Dec (∃ λ C → Γ ⊢ K p A t B u v ⇉ C)
    dec⇉-K ⊢Γ A t B u v =
      case
        (K-allowed? ×-dec′ λ ok →
         dec⇇Type-with-cont ⊢Γ A λ ⊢A →
         dec⇇-with-cont t ⊢A λ ⊢t →
         dec⇇Type-with-cont (∙ Idⱼ′ ⊢t ⊢t) B λ ⊢B →
         dec⇇ u (substType ⊢B (rflⱼ ⊢t)) ×-dec
         dec⇇ v (Idⱼ′ ⊢t ⊢t))
        of λ where
        (yes (ok , A , t , B , u , v)) → yes (_ , Kᵢ A t B u v ok)
        (no not)                       →
          no λ { (_ , Kᵢ A t B u v ok) → not (ok , A , t , B , u , v) }

  -- Decidability of checking that an inferable term is a type

  dec⇉Type : ⊢ Γ → Inferable A → Dec (Γ ⊢ A ⇇Type)
  dec⇉Type ⊢Γ Levelᵢ =
    case Level-allowed? of λ where
      (yes ok)    → yes (Levelᶜ ok)
      (no not-ok) → no λ where
        (Levelᶜ ok)           → not-ok ok
        (univᶜ (Levelᵢ ok) _) →
          not-ok (Level-allowed⇔⊎ .proj₂ (inj₁ ok))
  dec⇉Type ⊢Γ zeroᵘᵢ = no λ where
    (univᶜ (zeroᵘᵢ _) ↘U) →
      case whnfRed* (↘U .proj₁) Levelₙ of λ ()
  dec⇉Type ⊢Γ (sucᵘᵢ x) = no λ where
    (univᶜ (sucᵘᵢ _) ↘U) →
      case whnfRed* (↘U .proj₁) Levelₙ of λ ()
  dec⇉Type ⊢Γ (supᵘᵢ x y) = no λ where
    (univᶜ (supᵘᵢ _ _) ↘U) →
      case whnfRed* (↘U .proj₁) Levelₙ of λ ()
  dec⇉Type ⊢Γ (Uᵢ l) =
    case dec⇇Level l ⊢Γ of λ where
      (yes l)  → yes (Uᶜ l)
      (no not) → no λ where
        (Uᶜ l)           → not l
        (univᶜ (Uᵢ l) _) → not l
  dec⇉Type ⊢Γ (Liftᵢ l A) =
    case dec⇇Level l ⊢Γ ×-dec dec⇉Type ⊢Γ A of λ where
      (yes (l , A)) → yes (Liftᶜ l A)
      (no not) → no λ where
        (Liftᶜ l A)              → not (l , A)
        (univᶜ (Liftᵢ l A ↘U) _) → not (l , univᶜ A ↘U)
  dec⇉Type ⊢Γ (ΠΣᵢ {b} {p} {q} A B) =
    case
      (ΠΣ-allowed? b p q ×-dec
       dec⇉Type-with-cont ⊢Γ A λ ⊢A →
       dec⇇Type′ (∙ ⊢A) B)
      of λ where
      (yes (ok , A , B)) → yes (ΠΣᶜ A B ok)
      (no not)           → no λ where
        (ΠΣᶜ A B ok)               → not (ok , A , B)
        (univᶜ (ΠΣᵢ A ↘U₁ B ok) _) →
          not (ok , univᶜ A ↘U₁ , ⊢⇇U→⊢⇇Type B)
  dec⇉Type ⊢Γ (varᵢ {x}) =
    let B , x∷ = dec⇉-var x
        ⊢x     = var ⊢Γ x∷
    in
    case ↘U? (syntacticTerm ⊢x) of λ where
      (yes (_ , A↘)) → yes (univᶜ (varᵢ x∷) A↘)
      (no not)       →
        no λ { (univᶜ {B = C} {l} x ↘U) →
        not
          ( _
          , U-norm
              (B    ≡⟨ neTypeEq (var _) ⊢x (soundness⇉ ⊢Γ x .proj₂) ⟩⊢
               C    ≡⟨ subset* (↘U .proj₁) ⟩⊢∎
               U l  ∎)
              .proj₂
          , Uₙ
          ) }
  dec⇉Type ⊢Γ (lowerᵢ t) =
    case
      (Σ-dec (dec⇉-lower ⊢Γ t)
         (λ (_ , lower-t₁) (_ , lower-t₂) →
            case deterministic⇉ lower-t₁ lower-t₂ of λ { PE.refl → idᶠ })
         λ (_ , lower-t) →
       ↘U? (soundness⇉ ⊢Γ lower-t .proj₁))
      of λ where
      (yes ((_ , lower-t) , (_ , A))) → yes (univᶜ lower-t A)
      (no not)                        →
        no λ { (univᶜ lower-t A) → not ((_ , lower-t) , (_ , A)) }
  dec⇉Type ⊢Γ (∘ᵢ t u) =
    case
      (Σ-dec (dec⇉-app ⊢Γ t u)
         (λ (_ , t∘u₁) (_ , t∘u₂) →
            case deterministic⇉ t∘u₁ t∘u₂ of λ { PE.refl → idᶠ })
         λ (_ , t∘u) →
       ↘U? (soundness⇉ ⊢Γ t∘u .proj₁))
      of λ where
      (yes ((_ , t∘u) , (_ , A))) → yes (univᶜ t∘u A)
      (no not)                    →
        no λ { (univᶜ t∘u A) → not ((_ , t∘u) , (_ , A)) }
  dec⇉Type ⊢Γ (fstᵢ t) =
    case
      (Σ-dec (dec⇉-fst ⊢Γ t)
         (λ (_ , fst-t₁) (_ , fst-t₂) →
            case deterministic⇉ fst-t₁ fst-t₂ of λ { PE.refl → idᶠ })
         λ (_ , fst-t) →
       ↘U? (soundness⇉ ⊢Γ fst-t .proj₁))
      of λ where
      (yes ((_ , fst-t) , (_ , A))) → yes (univᶜ fst-t A)
      (no not)                      →
        no λ { (univᶜ fst-t A) → not ((_ , fst-t) , (_ , A)) }
  dec⇉Type ⊢Γ (sndᵢ t) =
    case
      (Σ-dec (dec⇉-snd ⊢Γ t)
         (λ (_ , snd-t₁) (_ , snd-t₂) →
            case deterministic⇉ snd-t₁ snd-t₂ of λ { PE.refl → idᶠ })
         λ (_ , snd-t) →
       ↘U? (soundness⇉ ⊢Γ snd-t .proj₁))
      of λ where
      (yes ((_ , snd-t) , (_ , A))) → yes (univᶜ snd-t A)
      (no not)                      →
        no λ { (univᶜ snd-t A) → not ((_ , snd-t) , (_ , A)) }
  dec⇉Type ⊢Γ (prodrecᵢ B t u) =
    case
      (Σ-dec (dec⇉-prodrec ⊢Γ B t u)
         (λ (_ , pr₁) (_ , pr₂) →
            case deterministic⇉ pr₁ pr₂ of λ { PE.refl → idᶠ })
         λ (_ , pr) →
       ↘U? (soundness⇉ ⊢Γ pr .proj₁))
      of λ where
      (yes ((_ , pr) , (_ , A))) → yes (univᶜ pr A)
      (no not)                   →
        no λ { (univᶜ pr A) → not ((_ , pr) , (_ , A)) }
  dec⇉Type ⊢Γ ℕᵢ = yes ℕᶜ
  dec⇉Type ⊢Γ zeroᵢ = no λ where
    (univᶜ zeroᵢ ↘U) →
      case whnfRed* (↘U .proj₁) ℕₙ of λ ()
  dec⇉Type ⊢Γ (sucᵢ x) = no λ where
    (univᶜ (sucᵢ _) ↘U) →
      case whnfRed* (↘U .proj₁) ℕₙ of λ ()
  dec⇉Type ⊢Γ (natrecᵢ B t u v) =
    case
      (Σ-dec (dec⇉-natrec ⊢Γ B t u v)
         (λ (_ , nr₁) (_ , nr₂) →
            case deterministic⇉ nr₁ nr₂ of λ { PE.refl → idᶠ })
         λ (_ , nr) →
       ↘U? (soundness⇉ ⊢Γ nr .proj₁))
      of λ where
      (yes ((_ , nr) , (_ , A))) → yes (univᶜ nr A)
      (no not)                   →
        no λ { (univᶜ nr A) → not ((_ , nr) , (_ , A)) }
  dec⇉Type ⊢Γ (Unitᵢ {s = s}) =
    case Unit-allowed? s of λ where
      (yes ok)    → yes (Unitᶜ ok)
      (no not-ok) → no λ where
        (Unitᶜ ok)           → not-ok ok
        (univᶜ (Unitᵢ ok) _) → not-ok ok
  dec⇉Type ⊢Γ starᵢ = no λ where
    (univᶜ (starᵢ _) ↘U) →
      case whnfRed* (↘U .proj₁) Unitₙ of λ ()
  dec⇉Type ⊢Γ (unitrecᵢ B t u) =
    case
      (Σ-dec (dec⇉-unitrec ⊢Γ B t u)
         (λ (_ , ur₁) (_ , ur₂) →
            case deterministic⇉ ur₁ ur₂ of λ { PE.refl → idᶠ })
         λ (_ , ur) →
       ↘U? (soundness⇉ ⊢Γ ur .proj₁))
      of λ where
      (yes ((_ , ur) , (_ , A))) → yes (univᶜ ur A)
      (no not)                   →
        no λ { (univᶜ ur A) → not ((_ , ur) , (_ , A)) }
  dec⇉Type ⊢Γ Emptyᵢ = yes Emptyᶜ
  dec⇉Type ⊢Γ (emptyrecᵢ B t) =
    case
      (Σ-dec (dec⇉-emptyrec ⊢Γ B t)
         (λ (_ , er₁) (_ , er₂) →
            case deterministic⇉ er₁ er₂ of λ { PE.refl → idᶠ })
         λ (_ , er) →
       ↘U? (soundness⇉ ⊢Γ er .proj₁))
      of λ where
      (yes ((_ , er) , (_ , A))) → yes (univᶜ er A)
      (no not)                   →
        no λ { (univᶜ er A) → not ((_ , er) , (_ , A)) }
  dec⇉Type ⊢Γ (Idᵢ A t u) =
    case
      (dec⇉Type-with-cont ⊢Γ A λ ⊢A →
       dec⇇ t ⊢A ×-dec dec⇇ u ⊢A)
      of λ where
      (yes (A , t , u)) → yes (Idᶜ A t u)
      (no not)          → no λ where
        (Idᶜ A t u)              → not (A , t , u)
        (univᶜ (Idᵢ A ↘U t u) _) → not (univᶜ A ↘U , t , u)
  dec⇉Type ⊢Γ (Jᵢ A t B u v w) =
    case
      (Σ-dec (dec⇉-J ⊢Γ A t B u v w)
         (λ (_ , J₁) (_ , J₂) →
            case deterministic⇉ J₁ J₂ of λ { PE.refl → idᶠ })
         λ (_ , J′) →
       ↘U? (soundness⇉ ⊢Γ J′ .proj₁))
      of λ where
      (yes ((_ , J′) , (_ , A))) → yes (univᶜ J′ A)
      (no not)                   →
        no λ { (univᶜ J′ A) → not ((_ , J′) , (_ , A)) }
  dec⇉Type ⊢Γ (Kᵢ A t B u v) =
    case
      (Σ-dec (dec⇉-K ⊢Γ A t B u v)
         (λ (_ , K₁) (_ , K₂) →
            case deterministic⇉ K₁ K₂ of λ { PE.refl → idᶠ })
         λ (_ , K′) →
       ↘U? (soundness⇉ ⊢Γ K′ .proj₁))
      of λ where
      (yes ((_ , K′) , (_ , A))) → yes (univᶜ K′ A)
      (no not)                   →
        no λ { (univᶜ K′ A) → not ((_ , K′) , (_ , A)) }
  dec⇉Type _ ([]-congᵢ _ _ _ _ _) =
    no λ where
      (univᶜ ([]-congᵢ _ _ _ _ _ _) ↘U) →
        case whnfRed* (↘U .proj₁) Idₙ of λ ()

  -- It is decidable whether a checkable type is a type.

  dec⇇Type : ⊢ Γ → Checkable-type A → Dec (Γ ⊢ A ⇇Type)
  dec⇇Type ⊢Γ (Liftᶜ l A) =
    case dec⇇Level l ⊢Γ ×-dec dec⇇Type ⊢Γ A of λ where
      (yes (l , A)) → yes (Liftᶜ l A)
      (no not) → no λ where
        (Liftᶜ l A)              → not (l , A)
        (univᶜ (Liftᵢ l A ↘U) _) → not (l , univᶜ A ↘U)
  dec⇇Type ⊢Γ (ΠΣᶜ {b} {p} {q} A B) =
    case
      (ΠΣ-allowed? b p q ×-dec
       dec⇇Type-with-cont ⊢Γ A λ ⊢A →
       dec⇇Type (∙ ⊢A) B)
      of λ where
      (yes (ok , A , B)) → yes (ΠΣᶜ A B ok)
      (no not)           → no λ where
        (ΠΣᶜ A B ok)               → not (ok , A , B)
        (univᶜ (ΠΣᵢ A ↘U₁ B ok) _) →
          not (ok , univᶜ A ↘U₁ , ⊢⇇U→⊢⇇Type B)
  dec⇇Type ⊢Γ (Idᶜ A t u) =
    case
      (dec⇇Type-with-cont ⊢Γ A λ ⊢A →
       dec⇇ t ⊢A ×-dec dec⇇ u ⊢A)
      of λ where
      (yes (A , t , u)) → yes (Idᶜ A t u)
      (no not)          → no λ where
        (Idᶜ A t u)              → not (A , t , u)
        (univᶜ (Idᵢ A ↘U t u) _) → not (univᶜ A ↘U , t , u)
  dec⇇Type {Γ} {A} ⊢Γ (checkᶜ A-c) = dec⇇Type′ ⊢Γ A-c

  dec⇇Type′ : ⊢ Γ → Checkable A → Dec (Γ ⊢ A ⇇Type)
  dec⇇Type′ ⊢Γ (liftᶜ _)   = no λ { (univᶜ () _) }
  dec⇇Type′ ⊢Γ (lamᶜ _)    = no λ { (univᶜ () _) }
  dec⇇Type′ ⊢Γ (prodᶜ _ _) = no λ { (univᶜ () _) }
  dec⇇Type′ ⊢Γ rflᶜ        = no λ { (univᶜ () _) }
  dec⇇Type′ ⊢Γ (infᶜ A)    = dec⇉Type ⊢Γ A

  -- Decidability of bi-directional type inference

  dec⇉ : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ⇉ A)
  dec⇉ ⊢Γ Levelᵢ = case Level-is-small? of λ where
    (yes ok) → yes (U zeroᵘ , Levelᵢ ok)
    (no ¬ok) → no λ where
      (_ , Levelᵢ ok) → ¬ok ok
  dec⇉ ⊢Γ zeroᵘᵢ =
    case Level-allowed? of λ where
      (yes ok)    → yes (Level , zeroᵘᵢ ok)
      (no not-ok) → no λ where
        (_ , zeroᵘᵢ ok) → not-ok ok
  dec⇉ ⊢Γ (sucᵘᵢ t) =
    case (Level-allowed? ×-dec′ λ ok →
          dec⇇ t (Levelⱼ′ ok ⊢Γ)) of λ where
      (yes (_ , t⇇Level)) → yes (_ , sucᵘᵢ t⇇Level)
      (no not)            → no λ where
        (_ , sucᵘᵢ t) →
          let ok = inversion-Level-⊢ (wf-⊢∷ (soundness⇇ t)) in
          not (ok , t)
  dec⇉ ⊢Γ (supᵘᵢ t u) =
    case (Level-allowed? ×-dec′ λ ok →
          dec⇇ t (Levelⱼ′ ok ⊢Γ) ×-dec
          dec⇇ u (Levelⱼ′ ok ⊢Γ)) of λ where
      (yes (_ , t⇇Level , u⇇Level)) → yes (_ , supᵘᵢ t⇇Level u⇇Level)
      (no not)                      → no λ where
        (_ , supᵘᵢ t u) →
          let ok = inversion-Level-⊢ (wf-⊢∷ (soundness⇇ t)) in
          not (ok , t , u)
  dec⇉ ⊢Γ (Uᵢ l) =
    case dec⇇Level l ⊢Γ of λ where
      (yes l) → yes (_ , Uᵢ l)
      (no not) → no λ { (_ , Uᵢ l) → not l }
  dec⇉ ⊢Γ (Liftᵢ l A) =
    case (dec⇇Level l ⊢Γ ×-dec
          dec⇉-with-cont ⊢Γ A λ ⊢A _ → ↘U? ⊢A) of λ where
      (yes (l , (_ , A) , (_ , ↘U))) → yes (_ , Liftᵢ l A ↘U)
      (no not) → no λ { (_ , Liftᵢ l A ↘U) → not (l , (_ , A) , (_ , ↘U)) }
  dec⇉ ⊢Γ (ΠΣᵢ {b} {p} {q} A B) =
    case
      (ΠΣ-allowed? b p q ×-dec
       dec⇉-with-cont ⊢Γ A λ ⊢C₁ ⊢A →
      Σ-dec (↘U? ⊢C₁)
        (λ (l , C₁⇒*U , _) (l′ , C₁⇒*U′ , _) →
          case whrDet* (C₁⇒*U , Uₙ) (C₁⇒*U′ , Uₙ) of λ {
            PE.refl → idᶠ })
        λ (l , C₁⇒*U , _) →
      let ⊢A′ = univ (conv ⊢A (subset* C₁⇒*U)) in
      dec⇇ B (wk₁ ⊢A′ (syntacticRed C₁⇒*U .proj₂)))
      of λ where
      (yes (ok , (_ , A) , (_ , ↘U₁) , B)) →
        yes (_ , ΠΣᵢ A ↘U₁ B ok)
      (no not) →
        no λ { (_ , ΠΣᵢ A ↘U₁ B ok) →
        not (ok , (_ , A) , (_ , ↘U₁) , B) }
  dec⇉ ⊢Γ varᵢ = yes (_ , varᵢ (dec⇉-var _ .proj₂))
  dec⇉ ⊢Γ (lowerᵢ t) = dec⇉-lower ⊢Γ t
  dec⇉ ⊢Γ (∘ᵢ t u) = dec⇉-app ⊢Γ t u
  dec⇉ ⊢Γ (fstᵢ t) = dec⇉-fst ⊢Γ t
  dec⇉ ⊢Γ (sndᵢ t) = dec⇉-snd ⊢Γ t
  dec⇉ ⊢Γ (prodrecᵢ A t u) = dec⇉-prodrec ⊢Γ A t u
  dec⇉ ⊢Γ ℕᵢ = yes (U zeroᵘ , ℕᵢ)
  dec⇉ ⊢Γ zeroᵢ = yes (ℕ , zeroᵢ)
  dec⇉ ⊢Γ (sucᵢ t) = case dec⇇ t (⊢ℕ ⊢Γ) of λ where
    (yes t⇇ℕ) → yes (_ , sucᵢ t⇇ℕ)
    (no ¬t⇇ℕ) → no λ where
      (_ , sucᵢ x) → ¬t⇇ℕ x
  dec⇉ ⊢Γ (natrecᵢ A z s n) = dec⇉-natrec ⊢Γ A z s n
  dec⇉ ⊢Γ (Unitᵢ {s}) =
    case Unit-allowed? s of λ where
      (yes ok)    → yes (_ , Unitᵢ ok)
      (no not-ok) → no λ where
        (_ , Unitᵢ ok) → not-ok ok
  dec⇉ ⊢Γ (starᵢ {s = s}) =
    case Unit-allowed? s of λ where
      (yes ok)    → yes (_ , starᵢ ok)
      (no not-ok) → no λ where
        (_ , starᵢ ok) → not-ok ok
  dec⇉ ⊢Γ (unitrecᵢ A t u) = dec⇉-unitrec ⊢Γ A t u
  dec⇉ ⊢Γ Emptyᵢ = yes (U zeroᵘ , Emptyᵢ)
  dec⇉ ⊢Γ (emptyrecᵢ A t) = dec⇉-emptyrec ⊢Γ A t
  dec⇉ ⊢Γ (Idᵢ A t u) =
    case
      (dec⇉-with-cont ⊢Γ A λ ⊢B ⊢A →
       ↘U? ⊢B ×-dec′ λ (_ , B⇒*U , _) →
       let ⊢A = univ (conv ⊢A (subset* B⇒*U)) in
       dec⇇ t ⊢A ×-dec dec⇇ u ⊢A)
      of λ where
      (yes ((_ , A) , (_ , ↘U) , t , u)) → yes (_ , Idᵢ A ↘U t u)
      (no not)                           →
        no λ { (_ , Idᵢ A ↘U t u) → not ((_ , A) , (_ , ↘U) , t , u) }
  dec⇉ ⊢Γ (Jᵢ A t B u v w) =
    dec⇉-J ⊢Γ A t B u v w
  dec⇉ ⊢Γ (Kᵢ A t B u v) =
    dec⇉-K ⊢Γ A t B u v
  dec⇉ ⊢Γ ([]-congᵢ {s} l A t u v) =
    case
      ([]-cong-allowed? s ×-dec
       dec⇇Level-with-cont l ⊢Γ λ ⊢l →
       dec⇇Type-with-cont ⊢Γ A λ ⊢A →
       dec⇇-with-cont t ⊢A λ ⊢t →
       dec⇇-with-cont u ⊢A λ ⊢u →
       dec⇇ v (Idⱼ′ ⊢t ⊢u))
      of λ where
      (yes (ok , l , A , t , u , v)) → yes (_ , []-congᵢ l A t u v ok)
      (no not)                       → no λ where
        (_ , []-congᵢ l A t u v ok) → not (ok , l , A , t , u , v)

  -- Decidability of bi-directional type checking

  dec⇇ : Checkable t → Γ ⊢ A → Dec (Γ ⊢ t ⇇ A)
  dec⇇ (liftᶜ t) ⊢A =
    case
      (Σ-dec (isLift ⊢A)
        (λ (_ , _ , A⇒) (_ , _ , A⇒′) →
          case whrDet* (A⇒ , Liftₙ) (A⇒′ , Liftₙ) of λ {
            PE.refl →
          idᶠ })
        λ (_ , _ , A⇒Lift) →
        let ⊢l , ⊢B = inversion-Lift (syntacticRed A⇒Lift .proj₂) in
        dec⇇ t ⊢B) of λ where
      (yes ((_ , _ , A⇒Lift) , t)) → yes (liftᶜ (A⇒Lift , Liftₙ) t)
      (no not) → no λ where
        (liftᶜ x x₁) → not ((_ , _ , x .proj₁) , x₁)
        (infᶜ () x₁)
  dec⇇ (lamᶜ {p} t) ⊢A =
    case
      (isΠΣ-with-cont ⊢A λ {b = b} {p = p′} _ ⊢C _ _ →
       decBinderMode b BMΠ ×-dec p ≟ p′ ×-dec dec⇇ t ⊢C)
      of λ where
      (yes ((_ , _ , _ , _ , _ , A) , PE.refl , PE.refl , t)) →
        yes (lamᶜ A t)
      (no not) → no λ where
        (lamᶜ A t) →
          not ((_ , _ , _ , _ , _ , A) , PE.refl , PE.refl , t)
        (infᶜ () _)
  dec⇇ (prodᶜ {p} {m = s} t u) ⊢A =
    case
      (Σ-dec (isΣ ⊢A)
         (λ (_ , _ , _ , _ , _ , A⇒*Σ₁) (_ , _ , _ , _ , _ , A⇒*Σ₂) →
            case whrDet* (A⇒*Σ₁ , ΠΣₙ) (A⇒*Σ₂ , ΠΣₙ) of λ {
              PE.refl →
            idᶠ })
         λ (s′ , p′ , _ , _ , _ , A⇒*Σ) →
       let ⊢B , ⊢C , _ = inversion-ΠΣ (syntacticRed A⇒*Σ .proj₂) in
       decStrength s s′ ×-dec p ≟ p′ ×-dec
       dec⇇-with-cont t ⊢B λ ⊢t →
       dec⇇ u (substType ⊢C ⊢t))
      of λ where
      (yes ((_ , _ , _ , _ , _ , A) , PE.refl , PE.refl , t , u)) →
        yes (prodᶜ (A , ΠΣₙ) t u)
      (no not) → no λ where
        (prodᶜ A t u) →
          not ((_ , _ , _ , _ , _ , A .proj₁) , PE.refl , PE.refl , t , u)
        (infᶜ () _)
  dec⇇ rflᶜ ⊢A =
    case
      (Σ-dec (is-Id ⊢A)
         (λ (_ , _ , _ , A⇒*Id₁) (_ , _ , _ , A⇒*Id₂) →
            case whrDet* (A⇒*Id₁ , Idₙ) (A⇒*Id₂ , Idₙ) of λ {
              PE.refl →
            idᶠ })
         λ (_ , _ , _ , A⇒*Id) →
       let _ , ⊢t , ⊢u = inversion-Id (syntacticRed A⇒*Id .proj₂) in
       decEqTerm ⊢t ⊢u)
      of λ where
      (yes ((_ , _ , _ , A) , t≡u)) →
        yes (rflᶜ (A , Idₙ) t≡u)
      (no not) → no λ where
        (rflᶜ A t≡u) → not ((_ , _ , _ , A .proj₁) , t≡u)
        (infᶜ () _)
  dec⇇ (infᶜ t) ⊢A =
    case
      (dec⇉-with-cont (wf ⊢A) t λ ⊢B _ →
       decEq ⊢B ⊢A)
      of λ where
      (yes ((_ , t) , B≡A)) → yes (infᶜ t B≡A)
      (no not) → no λ where
        (infᶜ t B≡A)  → not ((_ , t) , B≡A)
        (liftᶜ _ _)   → case t of λ ()
        (lamᶜ _ _)    → case t of λ ()
        (prodᶜ _ _ _) → case t of λ ()
        (rflᶜ _ _)    → case t of λ ()

  -- Decidability of bi-directional type-checking for levels.

  dec⇇Level : Checkable-level l → ⊢ Γ → Dec (Γ ⊢ l ⇇Level)
  dec⇇Level (term ok l) ⊢Γ =
    Dec-map (sym⇔ $ ⊢⇇Level⇔ ok) (dec⇇ l (Levelⱼ′ ok ⊢Γ))
  dec⇇Level {l} (literal not-ok) _ =
    case Level-literal? l of λ where
      (yes l-lit) →
        yes (literal not-ok l-lit)
      (no not-lit) →
        no λ where
          (term ok _)       → not-ok ok
          (literal _ l-lit) → not-lit l-lit
