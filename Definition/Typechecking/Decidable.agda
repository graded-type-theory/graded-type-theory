------------------------------------------------------------------------
-- Decidability of bi-derectional typechecking.
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
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as W
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Decidable.Equality R _≟_
open import Definition.Typed.Decidable.Reduction R _≟_
open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Neutral M type-variant as U

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n : Nat
    Γ : Con Term n
    t u v w A B : Term n
    p q r : M

dec⇉-var : (x : Fin n) → ∃ λ A → x ∷ A ∈ Γ
dec⇉-var {Γ = Γ ∙ A} x0 = _ , here
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

  -- Decidability of terms being inferable

  dec-Inferable : (t : Term n) → Dec (Inferable t)
  dec-Inferable (var x) = yes varᵢ
  dec-Inferable U = yes Uᵢ
  dec-Inferable (ΠΣ⟨ b ⟩ p , q ▷ F ▹ G) =
    case dec-Checkable F of λ where
      (yes F′) → case dec-Checkable G of λ where
        (yes G′) → yes (ΠΣᵢ F′ G′)
        (no ¬G′) → no λ where
          (ΠΣᵢ x x₁) → ¬G′ x₁
      (no ¬F′) → no λ where
        (ΠΣᵢ x x₁) → ¬F′ x
  dec-Inferable (lam p t) = no λ ()
  dec-Inferable (t ∘⟨ p ⟩ u) = case dec-Inferable t of λ where
    (yes t′) → case dec-Checkable u of λ where
      (yes u′) → yes (∘ᵢ t′ u′)
      (no ¬u′) → no λ where
        (∘ᵢ x x₁) → ¬u′ x₁
    (no ¬t′) → no λ where
      (∘ᵢ x x₁) → ¬t′ x
  dec-Inferable (prod! t u) = no λ ()
  dec-Inferable (fst p t) = case dec-Inferable t of λ where
    (yes t′) → yes (fstᵢ t′)
    (no ¬t′) → no λ where
      (fstᵢ x) → ¬t′ x
  dec-Inferable (snd p t) = case dec-Inferable t of λ where
    (yes t′) → yes (sndᵢ t′)
    (no ¬t′) → no λ where
      (sndᵢ x) → ¬t′ x
  dec-Inferable (prodrec r p q A t u) = case dec-Checkable A of λ where
    (yes A′) → case dec-Inferable t of λ where
      (yes t′) → case dec-Checkable u of λ where
        (yes u′) → yes (prodrecᵢ A′ t′ u′)
        (no ¬u′) → no λ where
          (prodrecᵢ x x₁ x₂) → ¬u′ x₂
      (no ¬t′) → no λ where
        (prodrecᵢ x x₁ x₂) → ¬t′ x₁
    (no ¬A′) → no λ where
      (prodrecᵢ x x₁ x₂) → ¬A′ x
  dec-Inferable ℕ = yes ℕᵢ
  dec-Inferable zero = yes zeroᵢ
  dec-Inferable (suc t) = case dec-Checkable t of λ where
    (yes t′) → yes (sucᵢ t′)
    (no ¬t′) → no λ where
      (sucᵢ x) → ¬t′ x
  dec-Inferable (natrec p q r A z s n) = case dec-Checkable A of λ where
    (yes A′) → case dec-Checkable z of λ where
      (yes z′) → case dec-Checkable s of λ where
        (yes s′) → case dec-Checkable n of λ where
          (yes n′) → yes (natrecᵢ A′ z′ s′ n′)
          (no ¬n′) →  no λ where
            (natrecᵢ x x₁ x₂ x₃) → ¬n′ x₃
        (no ¬s′) →  no λ where
          (natrecᵢ x x₁ x₂ x₃) → ¬s′ x₂
      (no ¬z′) →  no λ where
        (natrecᵢ x x₁ x₂ x₃) → ¬z′ x₁
    (no ¬A′) → no λ where
      (natrecᵢ x x₁ x₂ x₃) → ¬A′ x
  dec-Inferable Unit! = yes Unitᵢ
  dec-Inferable star! = yes starᵢ
  dec-Inferable (unitrec p q A t u) = case dec-Checkable A of λ where
    (yes A′) → case dec-Checkable t of λ where
      (yes t′) → case dec-Checkable u of λ where
        (yes u′) → yes (unitrecᵢ A′ t′ u′)
        (no ¬u′) → no λ where
          (unitrecᵢ x x₁ x₂) → ¬u′ x₂
      (no ¬t′) → no λ where
        (unitrecᵢ x x₁ x₂) → ¬t′ x₁
    (no ¬A′) → no λ where
      (unitrecᵢ x x₁ x₂) → ¬A′ x
  dec-Inferable Empty = yes Emptyᵢ
  dec-Inferable (emptyrec p A t) = case dec-Checkable A of λ where
    (yes A′) → case dec-Checkable t of λ where
      (yes t′) → yes (emptyrecᵢ A′ t′)
      (no ¬t′) →  no λ where
        (emptyrecᵢ x x₁) → ¬t′ x₁
    (no ¬A′) → no λ where
      (emptyrecᵢ x x₁) → ¬A′ x
  dec-Inferable (Id A t u) = case dec-Checkable A of λ where
    (no ¬A) → no λ where
      (Idᵢ A _ _) → ¬A A
    (yes A) → case dec-Checkable t of λ where
      (no ¬t) → no λ where
        (Idᵢ _ t _) → ¬t t
      (yes t) → case dec-Checkable u of λ where
        (no ¬u) → no λ where
          (Idᵢ _ _ u) → ¬u u
        (yes u) → yes (Idᵢ A t u)
  dec-Inferable rfl =
    no λ ()
  dec-Inferable (J _ _ A t B u v w) =
    case dec-Checkable A of λ where
      (no ¬A) → no λ { (Jᵢ A _ _ _ _ _) → ¬A A }
      (yes A) → case dec-Checkable t of λ where
        (no ¬t) → no λ { (Jᵢ _ t _ _ _ _) → ¬t t }
        (yes t) → case dec-Checkable B of λ where
          (no ¬B) → no λ { (Jᵢ _ _ B _ _ _) → ¬B B }
          (yes B) → case dec-Checkable u of λ where
            (no ¬u) → no λ { (Jᵢ _ _ _ u _ _) → ¬u u }
            (yes u) → case dec-Checkable v of λ where
              (no ¬v) → no λ { (Jᵢ _ _ _ _ v _) → ¬v v }
              (yes v) → case dec-Checkable w of λ where
                (no ¬w) → no λ { (Jᵢ _ _ _ _ _ w) → ¬w w }
                (yes w) → yes (Jᵢ A t B u v w)
  dec-Inferable (K _ A t B u v) =
    case dec-Checkable A of λ where
      (no ¬A) → no λ { (Kᵢ A _ _ _ _) → ¬A A }
      (yes A) → case dec-Checkable t of λ where
        (no ¬t) → no λ { (Kᵢ _ t _ _ _) → ¬t t }
        (yes t) → case dec-Checkable B of λ where
          (no ¬B) → no λ { (Kᵢ _ _ B _ _) → ¬B B }
          (yes B) → case dec-Checkable u of λ where
            (no ¬u) → no λ { (Kᵢ _ _ _ u _) → ¬u u }
            (yes u) → case dec-Checkable v of λ where
              (no ¬v) → no λ { (Kᵢ _ _ _ _ v) → ¬v v }
              (yes v) → yes (Kᵢ A t B u v)
  dec-Inferable ([]-cong s A t u v) =
    case dec-Checkable A of λ where
      (no ¬A) → no λ { ([]-congᵢ A _ _ _) → ¬A A }
      (yes A) → case dec-Checkable t of λ where
        (no ¬t) → no λ { ([]-congᵢ _ t _ _) → ¬t t }
        (yes t) → case dec-Checkable u of λ where
          (no ¬u) → no λ { ([]-congᵢ _ _ u _) → ¬u u }
          (yes u) → case dec-Checkable v of λ where
            (no ¬v) → no λ { ([]-congᵢ _ _ _ v) → ¬v v }
            (yes v) → yes ([]-congᵢ A t u v)

  -- Decidability of terms being checkable

  dec-Checkable : (t : Term n) → Dec (Checkable t)
  dec-Checkable t = helper t (dec-Inferable t)
    where
    helper : (t : Term n) → Dec (Inferable t) → Dec (Checkable t)
    helper (lam _ t) _ =
      case dec-Checkable t of λ where
        (no ¬t) → no λ { (lamᶜ t) → ¬t t }
        (yes t) → yes (lamᶜ t)
    helper (prod! t u) _ =
      case dec-Checkable t of λ where
        (no ¬t) → no λ { (prodᶜ t _) → ¬t t }
        (yes t) → case dec-Checkable u of λ where
          (no ¬u) → no λ { (prodᶜ _ u) → ¬u u }
          (yes u) → yes (prodᶜ t u)
    helper rfl _ =
      yes rflᶜ
    helper (var _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }
    helper U = λ where
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
    helper ([]-cong _ _ _ _ _) = λ where
      (yes t) → yes (infᶜ t)
      (no ¬t) → no λ { (infᶜ t) → ¬t t }

mutual

  dec⇉-app : ⊢ Γ → Inferable t → Checkable u → Dec (∃ λ A → Γ ⊢ t ∘⟨ p ⟩ u ⇉ A)
  dec⇉-app {p = p′} ⊢Γ t u = case dec⇉ ⊢Γ t of λ where
    (yes (A , t⇉A)) → case isΠ (proj₁ (soundness⇉ ⊢Γ t⇉A)) of λ where
      (yes (F , G , p , q , ⊢F , ⊢G , A⇒Π)) → case dec⇇ ⊢Γ u ⊢F of λ where
        (yes u⇇F) → case p ≟ p′ of λ where
          (yes PE.refl) → yes (_ , appᵢ t⇉A (A⇒Π , ΠΣₙ) u⇇F)
          (no p≢p′) → no λ where
            (_ , appᵢ x x₁ x₂) → case deterministic⇉ x t⇉A of λ where
              PE.refl → case whrDet* (A⇒Π , ΠΣₙ) x₁ of λ where
                PE.refl → p≢p′ PE.refl
        (no ¬u⇇F) → no λ where
          (_ , appᵢ x x₁ x₂) → case deterministic⇉ x t⇉A of λ where
             PE.refl → case whrDet* (A⇒Π , ΠΣₙ) x₁ of λ where
               PE.refl → ¬u⇇F x₂
      (no ¬isΠ) → no λ where
        (_ , appᵢ x x₁ x₂) → case deterministic⇉ x t⇉A of λ where
             PE.refl →
               let _ , ⊢Π = syntacticRed (proj₁ x₁)
                   ⊢F , ⊢G = syntacticΠ ⊢Π
               in  ¬isΠ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x₁)
    (no ¬t⇉A) → no λ where
      (_ , appᵢ x x₁ x₂) → ¬t⇉A (_ , x)

  dec⇉-fst : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ fst p t ⇉ A)
  dec⇉-fst {p = p′} ⊢Γ t = case dec⇉ ⊢Γ t of λ where
    (yes (A , t⇉A)) → case isΣˢ (proj₁ (soundness⇉ ⊢Γ t⇉A)) of λ where
      (yes (F , G , p , q , ⊢F , ⊢G , A⇒Σ)) → case p ≟ p′ of λ where
        (yes PE.refl) → yes (_ , fstᵢ t⇉A (A⇒Σ , U.ΠΣₙ))
        (no p≢p′) → no λ where
          (_ , fstᵢ x x₁) → case deterministic⇉ x t⇉A of λ where
             PE.refl → case whrDet* (A⇒Σ , ΠΣₙ) x₁ of λ where
               PE.refl → p≢p′ PE.refl
      (no ¬isΣ) → no λ where
        (_ , fstᵢ x x₁) → case deterministic⇉ x t⇉A of λ where
          PE.refl →
            let _ , ⊢Σ = syntacticRed (proj₁ x₁)
                ⊢F , ⊢G = syntacticΣ ⊢Σ
            in  ¬isΣ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x₁)
    (no ¬t⇉A) → no λ where
      (_ , fstᵢ x x₁) → ¬t⇉A (_ , x)

  dec⇉-snd : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ snd p t ⇉ A)
  dec⇉-snd {p = p′} ⊢Γ t = case dec⇉ ⊢Γ t of λ where
    (yes (A , t⇉A)) → case isΣˢ (proj₁ (soundness⇉ ⊢Γ t⇉A)) of λ where
      (yes (F , G , p , q , ⊢F , ⊢G , A⇒Σ)) → case p ≟ p′ of λ where
        (yes PE.refl) → yes (_ , sndᵢ t⇉A (A⇒Σ , U.ΠΣₙ))
        (no p≢p′) → no λ where
          (_ , sndᵢ x x₁) → case deterministic⇉ x t⇉A of λ where
             PE.refl → case whrDet* (A⇒Σ , ΠΣₙ) x₁ of λ where
               PE.refl → p≢p′ PE.refl
      (no ¬isΣ) → no λ where
        (_ , sndᵢ x x₁) → case deterministic⇉ x t⇉A of λ where
          PE.refl →
            let _ , ⊢Σ = syntacticRed (proj₁ x₁)
                ⊢F , ⊢G = syntacticΣ ⊢Σ
            in  ¬isΣ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x₁)
    (no ¬t⇉A) → no λ where
      (_ , sndᵢ x x₁) → ¬t⇉A (_ , x)

  dec⇉-natrec : ∀ {A z s n} → ⊢ Γ → Checkable A → Checkable z → Checkable s → Checkable n
              → Dec (∃ λ B → Γ ⊢ natrec p q r A z s n ⇉ B)
  dec⇉-natrec ⊢Γ A z s n = case dec⇇ ⊢Γ n (ℕⱼ ⊢Γ) of λ where
    (yes n⇇ℕ) → case dec⇇Type (⊢Γ ∙ ℕⱼ ⊢Γ) A of λ where
      (yes A⇇Type) →
        let ⊢A = soundness⇇Type (⊢Γ ∙ ℕⱼ ⊢Γ) A⇇Type
            ⊢A₀ = substType ⊢A (zeroⱼ ⊢Γ)
        in  case dec⇇ ⊢Γ z ⊢A₀ of λ where
          (yes z⇇A₀) →
            let ⊢Γ₊ = ⊢Γ ∙ ℕⱼ ⊢Γ ∙ ⊢A
                ⊢A₊ =  subst↑²Type (ℕⱼ ⊢Γ) ⊢A ⊢A (sucⱼ (var₁ ⊢A))
            in  case dec⇇ ⊢Γ₊ s ⊢A₊ of λ where
              (yes s⇇A₊) → yes (_ , natrecᵢ A⇇Type z⇇A₀ s⇇A₊ n⇇ℕ)
              (no ¬s⇇A₊) → no λ where
                (_ , natrecᵢ x x₁ x₂ x₃) → ¬s⇇A₊ x₂ --¬s⇇A₊ x₂
          (no ¬z⇇A₀) → no λ where
            (_ , natrecᵢ x x₁ x₂ x₃) → ¬z⇇A₀ x₁
      (no ¬A⇇Type) → no λ where
        (_ , natrecᵢ x x₁ x₂ x₃) → ¬A⇇Type x
    (no ¬n⇇ℕ) → no λ where
      (_ , natrecᵢ x x₁ x₂ x₃) → ¬n⇇ℕ x₃

  dec⇉-prodrec : ⊢ Γ → Checkable A → Inferable t → Checkable u
               → Dec (∃ λ B → Γ ⊢ prodrec r p q A t u ⇉ B)
  dec⇉-prodrec {r = r} {p = p′} {q = q} ⊢Γ A t u =
    case dec⇉ ⊢Γ t of λ where
      (yes (B , t⇉B)) → case isΣʷ (proj₁ (soundness⇉ ⊢Γ t⇉B)) of λ where
        (yes (F , G , p , _ , ⊢F , ⊢G , B⇒Σ)) →
          case inversion-ΠΣ (syntacticRed B⇒Σ .proj₂) of λ {
            (_ , _ , ok) →
          case dec⇇Type (⊢Γ ∙ ΠΣⱼ ⊢F ⊢G ok) A of λ where
            (yes A⇇Type) →
              let ⊢ΓΣ = ⊢Γ ∙ ΠΣⱼ {p = p} ⊢F ⊢G ok
                  ⊢A = soundness⇇Type ⊢ΓΣ A⇇Type
                  ⊢A₊ = subst↑²Type-prod ⊢A ok
              in  case dec⇇ (⊢Γ ∙ ⊢F ∙ ⊢G) u ⊢A₊ of λ where
                (yes u⇇A₊) → case p ≟ p′ of λ where
                  (yes PE.refl) →
                    yes (_ , prodrecᵢ A⇇Type t⇉B (B⇒Σ , ΠΣₙ) u⇇A₊)
                  (no p≢p′) → no λ where
                    (_ , prodrecᵢ _ x₁ x₂ _) →
                      case deterministic⇉ t⇉B x₁ of λ where
                        PE.refl → case whrDet* (B⇒Σ , ΠΣₙ) x₂ of λ where
                          PE.refl → p≢p′ PE.refl
                (no ¬u⇇A₊) → no λ where
                  (_ , prodrecᵢ _ x₁ x₂ x₃) →
                    case deterministic⇉ t⇉B x₁ of λ where
                       PE.refl → case whrDet* (B⇒Σ , ΠΣₙ) x₂ of λ where
                         PE.refl → ¬u⇇A₊ x₃
            (no ¬A⇇Type) → no λ where
              (_ , prodrecᵢ x x₁ x₂ _) →
                case deterministic⇉ t⇉B x₁ of λ where
                  PE.refl → case whrDet* (B⇒Σ , ΠΣₙ) x₂ of λ where
                    PE.refl → ¬A⇇Type x }
        (no ¬isΣ) → no λ where
          (_ , prodrecᵢ _ x₁ x₂ _) →
            case deterministic⇉ t⇉B x₁ of λ where
              PE.refl →
                let _ , ⊢Σ = syntacticRed (proj₁ x₂)
                    ⊢F , ⊢G = syntacticΣ ⊢Σ
                in  ¬isΣ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x₂)
      (no ¬t⇉B) → no λ where
        (_ , prodrecᵢ x x₁ x₂ x₃) → ¬t⇉B (_ , x₁)

  dec⇉-emptyrec : ⊢ Γ → Checkable A → Checkable t → Dec (∃ λ B → Γ ⊢ emptyrec p A t ⇉ B)
  dec⇉-emptyrec ⊢Γ A t = case dec⇇Type ⊢Γ A of λ where
    (yes A⇇Type) → case dec⇇ ⊢Γ t (Emptyⱼ ⊢Γ) of λ where
      (yes t⇇Empty) → yes (_ , emptyrecᵢ A⇇Type t⇇Empty)
      (no ¬t⇇Empty) → no λ where
        (_ , emptyrecᵢ x x₁) → ¬t⇇Empty x₁
    (no ¬A⇇Type) → no λ where
      (_ , emptyrecᵢ x x₁) → ¬A⇇Type x

  dec⇉-unitrec : ⊢ Γ → Checkable A → Checkable t
              → Checkable u → Dec (∃ λ B → Γ ⊢ unitrec p q A t u ⇉ B)
  dec⇉-unitrec ⊢Γ A t u = case Unit-allowed? 𝕨 of λ where
    (yes ok) → case Unitⱼ ⊢Γ ok of λ
      ⊢Unit → case dec⇇Type (⊢Γ ∙ ⊢Unit) A of λ where
        (yes A⇇Type) → case dec⇇ ⊢Γ t ⊢Unit of λ where
          (yes t⇇Unit) → case dec⇇ ⊢Γ u (substType (soundness⇇Type (⊢Γ ∙ ⊢Unit) A⇇Type)
                                                   (starⱼ ⊢Γ ok)) of λ where
            (yes u⇇A₊) → yes (_ , unitrecᵢ A⇇Type t⇇Unit u⇇A₊)
            (no ¬u⇇A₊) → no λ where
              (_ , unitrecᵢ x x₁ x₂) → ¬u⇇A₊ x₂
          (no ¬t⇇Unit) → no λ where
            (_ , unitrecᵢ x x₁ x₂) → ¬t⇇Unit x₁
        (no ¬A⇇Type) → no λ where
          (_ , unitrecᵢ x x₁ x₂) → ¬A⇇Type x
    (no not-ok) → no λ where
      (_ , unitrecᵢ x x₁ x₂) →
        let ⊢t = soundness⇇ ⊢Γ x₁
            ⊢Unit = syntacticTerm ⊢t
        in  not-ok (inversion-Unit ⊢Unit)

  private

    -- Some lemmas used below.

    dec⇉-J :
      ⊢ Γ → Checkable A → Checkable t → Checkable B → Checkable u →
      Checkable v → Checkable w →
      Dec (∃ λ C → Γ ⊢ J p q A t B u v w ⇉ C)
    dec⇉-J ⊢Γ A t B u v w =
      case dec⇇Type ⊢Γ A of λ where
        (no ¬A) → no λ { (_ , Jᵢ A _ _ _ _ _) → ¬A A }
        (yes A) →
          case soundness⇇Type ⊢Γ A of λ {
            ⊢A →
          case dec⇇ ⊢Γ t ⊢A of λ where
            (no ¬t) → no λ { (_ , Jᵢ _ t _ _ _ _) → ¬t t }
            (yes t) →
              case soundness⇇ ⊢Γ t of λ {
                ⊢t →
              case ⊢Γ ∙ ⊢A ∙ Idⱼ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A) of λ {
                ⊢Γ∙A∙Id-t-0 →
              case dec⇇Type ⊢Γ∙A∙Id-t-0 B of λ where
                (no ¬B) → no λ { (_ , Jᵢ _ _ B _ _ _) → ¬B B }
                (yes B) →
                  case dec⇇ ⊢Γ u
                         (substType₂ (soundness⇇Type ⊢Γ∙A∙Id-t-0 B) ⊢t $
                          PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ $
                          rflⱼ ⊢t) of λ where
                    (no ¬u) → no λ { (_ , Jᵢ _ _ _ u _ _) → ¬u u }
                    (yes u) → case dec⇇ ⊢Γ v ⊢A of λ where
                      (no ¬v) → no λ { (_ , Jᵢ _ _ _ _ v _) → ¬v v }
                      (yes v) →
                        case dec⇇ ⊢Γ w
                               (Idⱼ ⊢t (soundness⇇ ⊢Γ v)) of λ where
                          (no ¬w) → no λ { (_ , Jᵢ _ _ _ _ _ w) → ¬w w }
                          (yes w) → yes (_ , Jᵢ A t B u v w) }}}

    dec⇉-K :
      ⊢ Γ → Checkable A → Checkable t → Checkable B → Checkable u →
      Checkable v → Dec (∃ λ C → Γ ⊢ K p A t B u v ⇉ C)
    dec⇉-K ⊢Γ A t B u v =
      case K-allowed? of λ where
        (no not-ok) → no λ { (_ , Kᵢ _ _ _ _ _ ok) → not-ok ok }
        (yes ok)    → case dec⇇Type ⊢Γ A of λ where
          (no ¬A) → no λ { (_ , Kᵢ A _ _ _ _ _) → ¬A A }
          (yes A) →
            case soundness⇇Type ⊢Γ A of λ {
              ⊢A →
            case dec⇇ ⊢Γ t ⊢A of λ where
              (no ¬t) → no λ { (_ , Kᵢ _ t _ _ _ _) → ¬t t }
              (yes t) →
                case soundness⇇ ⊢Γ t of λ {
                  ⊢t →
                case ⊢Γ ∙ Idⱼ ⊢t ⊢t of λ {
                  ⊢Γ∙Id-t-t →
                case dec⇇Type ⊢Γ∙Id-t-t B of λ where
                  (no ¬B) → no λ { (_ , Kᵢ _ _ B _ _ _) → ¬B B }
                  (yes B) →
                    case dec⇇ ⊢Γ u
                           (substType (soundness⇇Type ⊢Γ∙Id-t-t B)
                              (rflⱼ ⊢t)) of λ where
                      (no ¬u) → no λ { (_ , Kᵢ _ _ _ u _ _) → ¬u u }
                      (yes u) → case dec⇇ ⊢Γ v (Idⱼ ⊢t ⊢t) of λ where
                        (no ¬v) → no λ { (_ , Kᵢ _ _ _ _ v _) → ¬v v }
                        (yes v) → yes (_ , Kᵢ A t B u v ok) }}}

  -- Decidability of checking that an inferable term is a type

  dec⇉Type : ⊢ Γ → Inferable A → Dec (Γ ⊢ A ⇇Type)
  dec⇉Type ⊢Γ Uᵢ = yes Uᶜ
  dec⇉Type ⊢Γ (ΠΣᵢ {b = b} {p = p} {q = q} F G) =
    case dec⇇Type ⊢Γ F of λ where
      (yes F⇇Type) →
        case dec⇇Type (⊢Γ ∙ soundness⇇Type ⊢Γ F⇇Type) G of λ where
          (yes G⇇Type) → case ΠΣ-allowed? b p q of λ where
            (yes ok)    → yes (ΠΣᶜ F⇇Type G⇇Type ok)
            (no not-ok) → no λ where
              (ΠΣᶜ _ _ ok)                  → not-ok ok
              (univᶜ (infᶜ (ΠΣᵢ _ _ ok) _)) → not-ok ok
          (no ¬G⇇Type) → no λ where
            (ΠΣᶜ _ x _)                  → ¬G⇇Type x
            (univᶜ (infᶜ (ΠΣᵢ _ x _) _)) → ¬G⇇Type (univᶜ x)
      (no ¬F⇇Type) → no λ where
        (ΠΣᶜ x _ _)                  → ¬F⇇Type x
        (univᶜ (infᶜ (ΠΣᵢ x _ _) _)) → ¬F⇇Type (univᶜ x)
  dec⇉Type ⊢Γ (varᵢ {x = x}) = case dec⇇-var x (Uⱼ ⊢Γ) of λ where
    (yes x⇇U) → yes (univᶜ x⇇U)
    (no ¬x⇇U) → no λ where
      (univᶜ x) → ¬x⇇U x
  dec⇉Type ⊢Γ (∘ᵢ t u) = case dec⇉-app ⊢Γ t u of λ where
    (yes (A , tu⇉A)) → case decEq (proj₁ (soundness⇉ ⊢Γ tu⇉A)) (Uⱼ ⊢Γ) of λ where
      (yes A≡U) → yes (univᶜ (infᶜ tu⇉A A≡U))
      (no A≢U) → no λ where
        (univᶜ (infᶜ x x₁)) → case deterministic⇉ tu⇉A x of λ where
          PE.refl → A≢U x₁
    (no ¬t′) → no λ where
      (univᶜ (infᶜ x x₁)) → ¬t′ (_ , x)
  dec⇉Type ⊢Γ (fstᵢ t) = case dec⇉-fst ⊢Γ t of λ where
    (yes (A , t₁⇉A)) → case decEq (proj₁ (soundness⇉ ⊢Γ t₁⇉A)) (Uⱼ ⊢Γ) of λ where
      (yes A≡U) → yes (univᶜ (infᶜ t₁⇉A A≡U))
      (no A≢U) → no λ where
        (univᶜ (infᶜ x x₁)) → case deterministic⇉ t₁⇉A x of λ where
          PE.refl → A≢U x₁
    (no ¬t₁⇉A) → no λ where
      (univᶜ (infᶜ x x₁)) → ¬t₁⇉A (_ , x)
  dec⇉Type ⊢Γ (sndᵢ t) = case dec⇉-snd ⊢Γ t of λ where
    (yes (A , t₂⇉A)) → case decEq (proj₁ (soundness⇉ ⊢Γ t₂⇉A)) (Uⱼ ⊢Γ) of λ where
      (yes A≡U) → yes (univᶜ (infᶜ t₂⇉A A≡U))
      (no A≢U) → no λ where
        (univᶜ (infᶜ x x₁)) → case deterministic⇉ t₂⇉A x of λ where
          PE.refl → A≢U x₁
    (no ¬t₂⇉A) → no λ where
      (univᶜ (infᶜ x x₁)) → ¬t₂⇉A (_ , x)
  dec⇉Type ⊢Γ (prodrecᵢ B t u) = case dec⇉-prodrec ⊢Γ B t u of λ where
    (yes (A , pr⇉A)) → case decEq (proj₁ (soundness⇉ ⊢Γ pr⇉A)) (Uⱼ ⊢Γ) of λ where
      (yes A≡U) → yes (univᶜ (infᶜ pr⇉A A≡U))
      (no A≢U) → no λ where
        (univᶜ (infᶜ x x₁)) → case deterministic⇉ pr⇉A x of λ where
          PE.refl → A≢U x₁
    (no ¬pr⇉A) → no λ where
      (univᶜ (infᶜ x x₁)) → ¬pr⇉A (_ , x)
  dec⇉Type ⊢Γ ℕᵢ = yes ℕᶜ
  dec⇉Type ⊢Γ zeroᵢ = no λ where
    (univᶜ (infᶜ zeroᵢ x₁)) → U≢ℕ (sym x₁)
  dec⇉Type ⊢Γ (sucᵢ x) = no λ where
    (univᶜ (infᶜ (sucᵢ x) x₁)) → U≢ℕ (sym x₁)
  dec⇉Type ⊢Γ (natrecᵢ B z s n) = case dec⇉-natrec ⊢Γ B z s n of λ where
    (yes (A , pr⇉A)) → case decEq (proj₁ (soundness⇉ ⊢Γ pr⇉A)) (Uⱼ ⊢Γ) of λ where
      (yes A≡U) → yes (univᶜ (infᶜ pr⇉A A≡U))
      (no A≢U) → no λ where
        (univᶜ (infᶜ x x₁)) → case deterministic⇉ pr⇉A x of λ where
          PE.refl → A≢U x₁
    (no ¬pr⇉A) → no λ where
      (univᶜ (infᶜ x x₁)) → ¬pr⇉A (_ , x)
  dec⇉Type ⊢Γ (Unitᵢ {s = s}) = case Unit-allowed? s of λ where
    (yes ok)    → yes (Unitᶜ ok)
    (no not-ok) → no λ where
      (Unitᶜ ok)                  → not-ok ok
      (univᶜ (infᶜ (Unitᵢ ok) _)) → not-ok ok
  dec⇉Type ⊢Γ starᵢ = no λ where
    (univᶜ (infᶜ (starᵢ _) x)) → U≢Unitⱼ (sym x)
  dec⇉Type ⊢Γ (unitrecᵢ A t u) = case dec⇉-unitrec ⊢Γ A t u of λ where
    (yes (_ , ur⇉A)) → case decEq (proj₁ (soundness⇉ ⊢Γ ur⇉A)) (Uⱼ ⊢Γ) of λ where
      (yes A≡U) → yes (univᶜ (infᶜ ur⇉A A≡U))
      (no A≢U) → no λ where
        (univᶜ (infᶜ x x₁)) → case deterministic⇉ ur⇉A x of λ where
          PE.refl → A≢U x₁
    (no ¬ur⇉A) → no λ where
      (univᶜ (infᶜ x x₁)) → ¬ur⇉A (_ , x)
  dec⇉Type ⊢Γ Emptyᵢ = yes Emptyᶜ
  dec⇉Type ⊢Γ (emptyrecᵢ B t) = case dec⇉-emptyrec ⊢Γ B t of λ where
    (yes (A , pr⇉A)) → case decEq (proj₁ (soundness⇉ ⊢Γ pr⇉A)) (Uⱼ ⊢Γ) of λ where
      (yes A≡U) → yes (univᶜ (infᶜ pr⇉A A≡U))
      (no A≢U) → no λ where
        (univᶜ (infᶜ x x₁)) → case deterministic⇉ pr⇉A x of λ where
          PE.refl → A≢U x₁
    (no ¬pr⇉A) → no λ where
      (univᶜ (infᶜ x x₁)) → ¬pr⇉A (_ , x)
  dec⇉Type ⊢Γ (Idᵢ A t u) =
    case dec⇇Type ⊢Γ A of λ where
      (no ¬A) → no λ where
        (Idᶜ A _ _)                  → ¬A A
        (univᶜ (infᶜ (Idᵢ A _ _) _)) → ¬A (univᶜ A)
      (yes A) →
        case soundness⇇Type ⊢Γ A of λ {
          ⊢A →
        case dec⇇ ⊢Γ t ⊢A of λ where
          (no ¬t) → no λ where
            (Idᶜ _ t _)                  → ¬t t
            (univᶜ (infᶜ (Idᵢ _ t _) _)) → ¬t t
          (yes t) →
            case dec⇇ ⊢Γ u ⊢A of λ where
              (no ¬u) → no λ where
                (Idᶜ _ _ u)                  → ¬u u
                (univᶜ (infᶜ (Idᵢ _ _ u) _)) → ¬u u
              (yes u) → yes (Idᶜ A t u) }
  dec⇉Type ⊢Γ (Jᵢ A t B u v w) =
    case dec⇉-J ⊢Γ A t B u v w of λ where
      (no ¬⊢J)       → no λ { (univᶜ (infᶜ ⊢J _)) → ¬⊢J (_ , ⊢J) }
      (yes (_ , ⊢J)) →
        case decEq (soundness⇉ ⊢Γ ⊢J .proj₁) (Uⱼ ⊢Γ) of λ where
          (no C≢U) → no λ { (univᶜ (infᶜ ⊢J′ C′≡U)) →
            case deterministic⇉ ⊢J ⊢J′ of λ {
              PE.refl →
            C≢U C′≡U }}
          (yes C≡U) → yes (univᶜ (infᶜ ⊢J C≡U))
  dec⇉Type ⊢Γ (Kᵢ A t B u v) =
    case dec⇉-K ⊢Γ A t B u v of λ where
      (no ¬⊢K)       → no λ { (univᶜ (infᶜ ⊢K _)) → ¬⊢K (_ , ⊢K) }
      (yes (_ , ⊢K)) →
        case decEq (soundness⇉ ⊢Γ ⊢K .proj₁) (Uⱼ ⊢Γ) of λ where
          (no C≢U) → no λ { (univᶜ (infᶜ ⊢K′ C′≡U)) →
            case deterministic⇉ ⊢K ⊢K′ of λ {
              PE.refl →
            C≢U C′≡U }}
          (yes C≡U) → yes (univᶜ (infᶜ ⊢K C≡U))
  dec⇉Type _ ([]-congᵢ _ _ _ _) =
    no λ { (univᶜ (infᶜ ([]-congᵢ _ _ _ _ _) Id≡U)) → Id≢U Id≡U }

  -- Decidability of checking that a checkable term is a type

  dec⇇Type : ⊢ Γ → Checkable A → Dec (Γ ⊢ A ⇇Type)
  dec⇇Type ⊢Γ (lamᶜ t) = no λ where
    (univᶜ (lamᶜ x x₁)) → U.U≢B BΠ! (whnfRed* (proj₁ x) Uₙ)
  dec⇇Type ⊢Γ (prodᶜ t u) = no λ where
    (univᶜ (prodᶜ x x₁ x₂)) → U.U≢B BΣ! (whnfRed* (proj₁ x) Uₙ)
  dec⇇Type ⊢Γ rflᶜ = no λ where
    (univᶜ (rflᶜ (U⇒*Id , _) _)) → case whnfRed* U⇒*Id Uₙ of λ ()
    (univᶜ (infᶜ () _))
  dec⇇Type ⊢Γ (infᶜ x) = dec⇉Type ⊢Γ x

  -- Decidability of bi-directional type inference

  dec⇉ : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ⇉ A)
  dec⇉ ⊢Γ Uᵢ = no λ where (A , ())
  dec⇉ ⊢Γ (ΠΣᵢ {b = b} {p = p} {q = q} F G) =
    case dec⇇ ⊢Γ F (Uⱼ ⊢Γ) of λ where
      (yes F⇇U) →
        let ⊢F = soundness⇇ ⊢Γ F⇇U
        in  case dec⇇ (⊢Γ ∙ univ ⊢F) G (Uⱼ (⊢Γ ∙ univ ⊢F)) of λ where
          (yes G⇇U) → case ΠΣ-allowed? b p q of λ where
            (yes ok)    → yes (_ , ΠΣᵢ F⇇U G⇇U ok)
            (no not-ok) → no λ where
              (_ , ΠΣᵢ _ _ ok) → not-ok ok
          (no ¬G⇇U) → no λ where
            (_ , ΠΣᵢ _ x _) → ¬G⇇U x
      (no ¬F⇇U) → no λ where
        (_ , ΠΣᵢ x _ _) → ¬F⇇U x
  dec⇉ ⊢Γ varᵢ = yes (_ , varᵢ (proj₂ (dec⇉-var _)))
  dec⇉ ⊢Γ (∘ᵢ t u) = dec⇉-app ⊢Γ t u
  dec⇉ ⊢Γ (fstᵢ t) = dec⇉-fst ⊢Γ t
  dec⇉ ⊢Γ (sndᵢ t) = dec⇉-snd ⊢Γ t
  dec⇉ ⊢Γ (prodrecᵢ A t u) = dec⇉-prodrec ⊢Γ A t u
  dec⇉ ⊢Γ ℕᵢ = yes (U , ℕᵢ)
  dec⇉ ⊢Γ zeroᵢ = yes (ℕ , zeroᵢ)
  dec⇉ ⊢Γ (sucᵢ t) = case dec⇇ ⊢Γ t (ℕⱼ ⊢Γ) of λ where
    (yes t⇇ℕ) → yes (_ , sucᵢ t⇇ℕ)
    (no ¬t⇇ℕ) → no λ where
      (_ , sucᵢ x) → ¬t⇇ℕ x
  dec⇉ ⊢Γ (natrecᵢ A z s n) = dec⇉-natrec ⊢Γ A z s n
  dec⇉ ⊢Γ (Unitᵢ {s = s}) = case Unit-allowed? s of λ where
    (yes ok)    → yes (U , Unitᵢ ok)
    (no not-ok) → no λ where
      (_ , Unitᵢ ok) → not-ok ok
  dec⇉ ⊢Γ (starᵢ {s = s}) = case Unit-allowed? s of λ where
    (yes ok)    → yes (Unit! , starᵢ ok)
    (no not-ok) → no λ where
      (_ , starᵢ ok) → not-ok ok
  dec⇉ ⊢Γ (unitrecᵢ A t u) = dec⇉-unitrec ⊢Γ A t u
  dec⇉ ⊢Γ Emptyᵢ = yes (U , Emptyᵢ)
  dec⇉ ⊢Γ (emptyrecᵢ A t) = dec⇉-emptyrec ⊢Γ A t
  dec⇉ ⊢Γ (Idᵢ A t u) =
    case dec⇇ ⊢Γ A (Uⱼ ⊢Γ) of λ where
      (no ¬A) → no λ { (_ , Idᵢ A _ _) → ¬A A }
      (yes A) →
        case univ (soundness⇇ ⊢Γ A) of λ {
          ⊢A →
        case dec⇇ ⊢Γ t ⊢A of λ where
          (no ¬t) → no λ { (_ , Idᵢ _ t _) → ¬t t }
          (yes t) →
            case dec⇇ ⊢Γ u ⊢A of λ where
              (no ¬u) → no λ { (_ , Idᵢ _ _ u) → ¬u u }
              (yes u) → yes (_ , Idᵢ A t u) }
  dec⇉ ⊢Γ (Jᵢ A t B u v w) =
    dec⇉-J ⊢Γ A t B u v w
  dec⇉ ⊢Γ (Kᵢ A t B u v) =
    dec⇉-K ⊢Γ A t B u v
  dec⇉ ⊢Γ ([]-congᵢ {s = s} A t u v) =
    case []-cong-allowed? s of λ where
      (no not-ok) → no λ { (_ , []-congᵢ _ _ _ _ ok) → not-ok ok }
      (yes ok)    → case dec⇇Type ⊢Γ A of λ where
        (no ¬A) → no λ { (_ , []-congᵢ A _ _ _ _) → ¬A A }
        (yes A) →
          case soundness⇇Type ⊢Γ A of λ {
            ⊢A →
          case dec⇇ ⊢Γ t ⊢A of λ where
            (no ¬t) → no λ { (_ , []-congᵢ _ t _ _ _) → ¬t t }
            (yes t) →
              case dec⇇ ⊢Γ u ⊢A of λ where
                (no ¬u) → no λ { (_ , []-congᵢ _ _ u _ _) → ¬u u }
                (yes u) →
                  case dec⇇ ⊢Γ v
                         (Idⱼ (soundness⇇ ⊢Γ t)
                            (soundness⇇ ⊢Γ u)) of λ where
                    (no ¬v) → no λ { (_ , []-congᵢ _ _ _ v _) → ¬v v }
                    (yes v) → yes (_ , []-congᵢ A t u v ok) }

  -- Decidability of bi-directional type checking

  dec⇇ : ⊢ Γ → Checkable t → Γ ⊢ A → Dec (Γ ⊢ t ⇇ A)
  dec⇇ ⊢Γ (lamᶜ {p = p′} t) ⊢A = case isΠ ⊢A of λ where
    (yes (F , G , p , q , ⊢F , ⊢G , A⇒Π)) → case dec⇇ (⊢Γ ∙ ⊢F) t ⊢G of λ where
      (yes t⇇G) → case p ≟ p′ of λ where
        (yes PE.refl) → yes (lamᶜ (A⇒Π , ΠΣₙ) t⇇G)
        (no p≢p′) → no λ where
          (lamᶜ x x₁) → case whrDet* (A⇒Π , ΠΣₙ) x of λ where
            PE.refl → p≢p′ PE.refl
      (no ¬t⇇G) → no λ where
        (lamᶜ x x₁) → case whrDet* (A⇒Π , ΠΣₙ) x of λ where
          PE.refl → ¬t⇇G x₁
    (no ¬isΠ) → no λ where
      (lamᶜ x x₁) →
        let _ , ⊢Π = syntacticRed (proj₁ x)
            ⊢F , ⊢G = syntacticΠ ⊢Π
        in  ¬isΠ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x)
  dec⇇ ⊢Γ (prodᶜ {p = p′} {m = m′} t u) ⊢A = case isΣ ⊢A of λ where
    (yes (F , G , m , p , q , ⊢F , ⊢G , A⇒Σ)) → case dec⇇ ⊢Γ t ⊢F of λ where
      (yes t⇇F) → case dec⇇ ⊢Γ u (substType ⊢G (soundness⇇ ⊢Γ t⇇F)) of λ where
        (yes u⇇Gₜ) → case p ≟ p′ of λ where
          (yes PE.refl) → case decStrength m m′ of λ where
            (yes PE.refl) → yes (prodᶜ (A⇒Σ , ΠΣₙ) t⇇F u⇇Gₜ)
            (no m≢m′) → no λ where
              (prodᶜ x x₁ x₂) →
                let Σ≡Σ′ = whrDet* (A⇒Σ , ΠΣₙ) x
                    _ , _ , W≡W′ = B-PE-injectivity BΣ! BΣ! Σ≡Σ′
                    _ , _ , m≡m′ = BΣ-PE-injectivity W≡W′
                in  m≢m′ m≡m′
          (no p≢p′) → no λ where
            (prodᶜ x x₁ x₂) → case whrDet* (A⇒Σ , ΠΣₙ) x of λ where
              PE.refl → p≢p′ PE.refl
        (no ¬u⇇Gₜ) → no λ where
          (prodᶜ x x₁ x₂) → case whrDet* (A⇒Σ , ΠΣₙ) x of λ where
            PE.refl → ¬u⇇Gₜ x₂
      (no ¬t⇇F) → no λ where
        (prodᶜ x x₁ x₂) → case whrDet* (A⇒Σ , ΠΣₙ) x of λ where
          PE.refl → ¬t⇇F x₁
    (no ¬isΣ) → no λ where
      (prodᶜ x x₁ x₂) →
        let _ , ⊢Σ = syntacticRed (proj₁ x)
            ⊢F , ⊢G = syntacticΣ ⊢Σ
        in  ¬isΣ (_ , _ , _ , _ , _ , ⊢F , ⊢G , proj₁ x)
  dec⇇ ⊢Γ rflᶜ ⊢A =
    case is-Id ⊢A of λ where
      (no is-not-Id) → no λ where
        (rflᶜ (A⇒*Id-t-u , _) t≡u) →
          case syntacticEqTerm t≡u of λ {
            (⊢B , ⊢t , ⊢u) →
          is-not-Id (_ , _ , _ , ⊢B , ⊢t , ⊢u , A⇒*Id-t-u) }
        (infᶜ () _)
      (yes (_ , _ , _ , ⊢B , ⊢t , ⊢u , A⇒*Id-t-u)) →
        case decEqTerm ⊢t ⊢u of λ where
          (no t≢u) → no λ where
            (rflᶜ A↘Id-t′-u′ t′≡u′) →
              case whrDet* (A⇒*Id-t-u , Idₙ) A↘Id-t′-u′ of λ {
                PE.refl →
              t≢u t′≡u′ }
            (infᶜ () _)
          (yes t≡u) → yes (rflᶜ (A⇒*Id-t-u , Idₙ) t≡u)
  dec⇇ ⊢Γ (infᶜ t) ⊢A = case dec⇉ ⊢Γ t of λ where
    (yes (B , t⇉B)) → case decEq (proj₁ (soundness⇉ ⊢Γ t⇉B)) ⊢A of λ where
      (yes B≡A) → yes (infᶜ t⇉B B≡A)
      (no B≢A) → no λ where
        (infᶜ x x₁) → case deterministic⇉ t⇉B x of λ where
          PE.refl → B≢A x₁
        (rflᶜ _ _) → case t of λ ()
    (no ¬t⇉B) → no λ where
      (infᶜ x x₁) → ¬t⇉B (_ , x)
      (rflᶜ _ _) → case t of λ ()
