------------------------------------------------------------------------
-- Decidability of bi-derectional typechecking.
------------------------------------------------------------------------

{-# OPTIONS --no-infer-absurd-clauses #-}

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
open import Definition.Typed.Consequences.DerivedRules R
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
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    P : Set a
    n : Nat
    Γ : Con Term n
    t u v w A B : Term n
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

  -- Decidability of terms being inferable

  dec-Inferable : (t : Term n) → Dec (Inferable t)
  dec-Inferable (var _) =
    yes varᵢ
  dec-Inferable U =
    yes Uᵢ
  dec-Inferable (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
    case dec-Checkable A ×-dec dec-Checkable B of λ where
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
    case dec-Checkable A ×-dec dec-Inferable t ×-dec
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
    case dec-Checkable A ×-dec dec-Checkable t ×-dec
         dec-Checkable u ×-dec dec-Checkable v of λ where
      (yes (A , t , u , v)) → yes (natrecᵢ A t u v)
      (no not)              →
        no λ { (natrecᵢ A t u v) → not (A , t , u , v) }
  dec-Inferable Unit! =
    yes Unitᵢ
  dec-Inferable star! =
    yes starᵢ
  dec-Inferable (unitrec _ _ A t u) =
    case dec-Checkable A ×-dec dec-Checkable t ×-dec
         dec-Checkable u of λ where
      (yes (A , t , u)) → yes (unitrecᵢ A t u)
      (no not)          → no λ { (unitrecᵢ A t u) → not (A , t , u) }
  dec-Inferable Empty =
    yes Emptyᵢ
  dec-Inferable (emptyrec p A t) =
    case dec-Checkable A ×-dec dec-Checkable t of λ where
      (yes (A , t)) → yes (emptyrecᵢ A t)
      (no not)      → no λ { (emptyrecᵢ A t) → not (A , t) }
  dec-Inferable (Id A t u) =
    case dec-Checkable A ×-dec dec-Checkable t ×-dec
         dec-Checkable u of λ where
      (yes (A , t , u)) → yes (Idᵢ A t u)
      (no not)          → no λ { (Idᵢ A t u) → not (A , t , u) }
  dec-Inferable rfl =
    no λ ()
  dec-Inferable (J _ _ A t B u v w) =
    case dec-Checkable A ×-dec dec-Checkable t ×-dec
         dec-Checkable B ×-dec dec-Checkable u ×-dec
         dec-Checkable v ×-dec dec-Checkable w of λ where
      (yes (A , t , B , u , v , w)) → yes (Jᵢ A t B u v w)
      (no not)                      →
        no λ { (Jᵢ A t B u v w) → not (A , t , B , u , v , w) }
  dec-Inferable (K _ A t B u v) =
    case dec-Checkable A ×-dec dec-Checkable t ×-dec
         dec-Checkable B ×-dec dec-Checkable u ×-dec
         dec-Checkable v of λ where
      (yes (A , t , B , u , v)) → yes (Kᵢ A t B u v)
      (no not)                  →
        no λ { (Kᵢ A t B u v) → not (A , t , B , u , v) }
  dec-Inferable ([]-cong s A t u v) =
    case dec-Checkable A ×-dec dec-Checkable t ×-dec
         dec-Checkable u ×-dec dec-Checkable v of λ where
      (yes (A , t , u , v)) → yes ([]-congᵢ A t u v)
      (no not)              →
        no λ { ([]-congᵢ A t u v) → not (A , t , u , v) }

  -- Decidability of terms being checkable

  dec-Checkable : (t : Term n) → Dec (Checkable t)
  dec-Checkable t = helper t (dec-Inferable t)
    where
    helper : (t : Term n) → Dec (Inferable t) → Dec (Checkable t)
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

private opaque

  -- A variant of isΠΣ.

  isΠΣ-with-cont :
    {Γ : Con Term n}
    {P : BinderMode → M → M → Term n → Term (1+ n) → Set a} →
    Γ ⊢ A →
    (∀ {b p q B C} →
     Γ ⊢ B → Γ ∙ B ⊢ C → ΠΣ-allowed b p q →
     Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B ▹ C → Dec (P b p q B C)) →
    Dec
      (∃ λ ((b , p , q , B , C , _) :
            ∃₅ λ b p q B C → Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B ▹ C) →
       P b p q B C)
  isΠΣ-with-cont {P} ⊢A cont =
    Σ-dec (isΠΣ ⊢A)
      (λ (_ , _ , _ , _ , _ , A⇒*ΠΣ₁) (_ , _ , _ , _ , _ , A⇒*ΠΣ₂) →
         case whrDet* (A⇒*ΠΣ₁ , ΠΣₙ) (A⇒*ΠΣ₂ , ΠΣₙ) of λ {
           PE.refl →
         idᶠ })
      (λ (_ , _ , _ , _ , _ , A⇒*ΠΣ) →
         let ⊢B , ⊢C , ok = inversion-ΠΣ (syntacticRed A⇒*ΠΣ .proj₂) in
         cont ⊢B ⊢C ok A⇒*ΠΣ)

mutual

  private

    -- Some lemmas used below.

    dec⇉-with-cont :
      {Γ : Con Term n} {P : Term n → Set a} →
      ⊢ Γ → Inferable t → (∀ {A} → Γ ⊢ A → Dec (P A)) →
      Dec (Σ (∃ λ A → Γ ⊢ t ⇉ A) (P ∘→ proj₁))
    dec⇉-with-cont ⊢Γ t cont =
      Σ-dec (dec⇉ ⊢Γ t)
        (λ (_ , t₁) (_ , t₂) →
           case deterministic⇉ t₁ t₂ of λ { PE.refl → idᶠ })
        (cont ∘→ proj₁ ∘→ soundness⇉ ⊢Γ ∘→ proj₂)

    dec⇇-with-cont :
      Checkable t → Γ ⊢ A → (Γ ⊢ t ∷ A → Dec P) → Dec (Γ ⊢ t ⇇ A × P)
    dec⇇-with-cont t ⊢A cont =
      dec⇇ t ⊢A ×-dec′ cont ∘→ soundness⇇

    dec⇇Type-with-cont :
      ⊢ Γ → Checkable A → (Γ ⊢ A → Dec P) → Dec (Γ ⊢ A ⇇Type × P)
    dec⇇Type-with-cont ⊢Γ A cont =
      dec⇇Type ⊢Γ A ×-dec′ cont ∘→ soundness⇇Type ⊢Γ

    dec⇉-app :
      ⊢ Γ → Inferable t → Checkable u →
      Dec (∃ λ A → Γ ⊢ t ∘⟨ p ⟩ u ⇉ A)
    dec⇉-app {p} ⊢Γ t u =
      case
        (dec⇉-with-cont ⊢Γ t λ ⊢A →
         isΠΣ-with-cont ⊢A λ {b = b} {p = p′} ⊢B _ _ _ →
         decBinderMode b BMΠ ×-dec p ≟ p′ ×-dec dec⇇ u ⊢B)
        of λ where
        (yes
           ((_ , t) , (_ , _ , _ , _ , _ , A) ,
            PE.refl , PE.refl , u)) →
          yes (_ , appᵢ t (A , ΠΣₙ) u)
        (no not) →
          no λ { (_ , appᵢ t (A , _) u) →
          not
            ( (_ , t)
            , (_ , _ , _ , _ , _ , A)
            , PE.refl , PE.refl , u
            ) }

    dec⇉-fst : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ fst p t ⇉ A)
    dec⇉-fst {p} ⊢Γ t =
      case
        (dec⇉-with-cont ⊢Γ t λ ⊢A →
         isΠΣ-with-cont ⊢A λ {b = b} {p = p′} ⊢B _ _ _ →
         decBinderMode b (BMΣ 𝕤) ×-dec p ≟ p′)
        of λ where
        (yes
           ((_ , t) , (_ , _ , _ , _ , _ , A) ,
            PE.refl , PE.refl)) →
          yes (_ , fstᵢ t (A , U.ΠΣₙ))
        (no not) →
          no λ { (_ , fstᵢ t (A , _)) →
          not
            ( (_ , t)
            , (_ , _ , _ , _ , _ , A)
            , PE.refl , PE.refl
            ) }

    dec⇉-snd : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ snd p t ⇉ A)
    dec⇉-snd {p} ⊢Γ t =
      case
        (dec⇉-with-cont ⊢Γ t λ ⊢A →
         isΠΣ-with-cont ⊢A λ {b = b} {p = p′} ⊢B _ _ _ →
         decBinderMode b (BMΣ 𝕤) ×-dec p ≟ p′)
        of λ where
        (yes ((_ , t) , (_ , _ , _ , _ , _ , A) , PE.refl , PE.refl)) →
          yes (_ , sndᵢ t (A , U.ΠΣₙ))
        (no not) →
          no λ { (_ , sndᵢ t (A , _)) →
          not
            ( (_ , t)
            , (_ , _ , _ , _ , _ , A)
            , PE.refl , PE.refl
            ) }

    dec⇉-natrec :
      ⊢ Γ → Checkable A → Checkable t → Checkable u → Checkable v →
      Dec (∃ λ B → Γ ⊢ natrec p q r A t u v ⇉ B)
    dec⇉-natrec ⊢Γ A t u v =
      case
        (dec⇇Type-with-cont (⊢Γ ∙[ ℕⱼ ]) A λ ⊢A →
         dec⇇ t (substType ⊢A (zeroⱼ ⊢Γ)) ×-dec
         dec⇇ u (subst↑²Type ⊢A (sucⱼ (var₁ ⊢A))) ×-dec
         dec⇇ v (ℕⱼ ⊢Γ))
        of λ where
        (yes (A , t , u , v)) → yes (_ , natrecᵢ A t u v)
        (no not)              →
          no λ { (_ , natrecᵢ A t u v) → not (A , t , u , v) }

    dec⇉-prodrec :
      ⊢ Γ → Checkable A → Inferable t → Checkable u →
      Dec (∃ λ B → Γ ⊢ prodrec r p q A t u ⇉ B)
    dec⇉-prodrec {p} ⊢Γ A t u =
      case
        (dec⇉-with-cont ⊢Γ t λ ⊢B →
         isΠΣ-with-cont ⊢B λ {b = b} {p = p′} _ ⊢D ok _ →
         decBinderMode b (BMΣ 𝕨) ×-dec′ λ b≡ →
         p ≟ p′ ×-dec
         dec⇇Type-with-cont (⊢→⊢∙ (ΠΣⱼ′ ⊢D ok)) A λ ⊢A →
         dec⇇ u
           (subst↑²Type-prod
              (PE.subst (λ b → _ ∙ ΠΣ⟨ b ⟩ _ , _ ▷ _ ▹ _ ⊢ _) b≡ ⊢A)
              (PE.subst (λ b → ΠΣ-allowed b _ _) b≡ ok)))
        of λ where
        (yes
           ((_ , t) , (_ , _ , _ , _ , _ , A⇒*) ,
            PE.refl , PE.refl , A , u)) →
          yes (_ , prodrecᵢ A t (A⇒* , ΠΣₙ) u)
        (no not) →
          no λ { (_ , prodrecᵢ A t (A⇒* , _) u) →
          not
            ( (_ , t)
            , (_ , _ , _ , _ , _ , A⇒*)
            , PE.refl , PE.refl , A , u
            ) }

    dec⇉-emptyrec :
      ⊢ Γ → Checkable A → Checkable t →
      Dec (∃ λ B → Γ ⊢ emptyrec p A t ⇉ B)
    dec⇉-emptyrec ⊢Γ A t =
      case dec⇇Type ⊢Γ A ×-dec dec⇇ t (Emptyⱼ ⊢Γ) of λ where
        (yes (A , t)) → yes (_ , emptyrecᵢ A t)
        (no not)      → no λ { (_ , emptyrecᵢ A t) → not (A , t) }

    dec⇉-unitrec :
      ⊢ Γ → Checkable A → Checkable t → Checkable u →
      Dec (∃ λ B → Γ ⊢ unitrec p q A t u ⇉ B)
    dec⇉-unitrec ⊢Γ A t u =
      case
        (Unit-allowed? 𝕨 ×-dec′ λ ok →
         let ⊢Unit = Unitⱼ ⊢Γ ok in
         dec⇇Type-with-cont (⊢→⊢∙ ⊢Unit) A λ ⊢A →
         dec⇇ t ⊢Unit ×-dec
         dec⇇ u (substType ⊢A (starⱼ ⊢Γ ok)))
        of λ where
        (yes (_ , A , t , u)) → yes (_ , unitrecᵢ A t u)
        (no not)              →
          no λ { (_ , unitrecᵢ A t u) →
          not (⊢∷Unit→Unit-allowed (soundness⇇ t) , A , t , u) }

    dec⇉-J :
      ⊢ Γ → Checkable A → Checkable t → Checkable B → Checkable u →
      Checkable v → Checkable w →
      Dec (∃ λ C → Γ ⊢ J p q A t B u v w ⇉ C)
    dec⇉-J ⊢Γ A t B u v w =
      case
        (dec⇇Type-with-cont ⊢Γ A λ ⊢A →
         dec⇇-with-cont t ⊢A λ ⊢t →
         dec⇇Type-with-cont
           (⊢→⊢∙ (Idⱼ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A))) B λ ⊢B →
         dec⇇ u
           (substType₂ ⊢B ⊢t $
            PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ $
            rflⱼ ⊢t) ×-dec
         dec⇇-with-cont v ⊢A λ ⊢v →
         dec⇇ w (Idⱼ ⊢t ⊢v))
        of λ where
        (yes (A , t , B , u , v , w)) → yes (_ , Jᵢ A t B u v w)
        (no not)                      →
          no λ { (_ , Jᵢ A t B u v w) → not (A , t , B , u , v , w) }

    dec⇉-K :
      ⊢ Γ → Checkable A → Checkable t → Checkable B → Checkable u →
      Checkable v →
      Dec (∃ λ C → Γ ⊢ K p A t B u v ⇉ C)
    dec⇉-K ⊢Γ A t B u v =
      case
        (K-allowed? ×-dec′ λ ok →
         dec⇇Type-with-cont ⊢Γ A λ ⊢A →
         dec⇇-with-cont t ⊢A λ ⊢t →
         dec⇇Type-with-cont (⊢→⊢∙ (Idⱼ ⊢t ⊢t)) B λ ⊢B →
         dec⇇ u (substType ⊢B (rflⱼ ⊢t)) ×-dec
         dec⇇ v (Idⱼ ⊢t ⊢t))
        of λ where
        (yes (ok , A , t , B , u , v)) → yes (_ , Kᵢ A t B u v ok)
        (no not)                       →
          no λ { (_ , Kᵢ A t B u v ok) → not (ok , A , t , B , u , v) }

  -- Decidability of checking that an inferable term is a type

  dec⇉Type : ⊢ Γ → Inferable A → Dec (Γ ⊢ A ⇇Type)
  dec⇉Type _ Uᵢ = yes Uᶜ
  dec⇉Type ⊢Γ (ΠΣᵢ {b} {p} {q} A B) =
    case
      (ΠΣ-allowed? b p q ×-dec
       dec⇇Type-with-cont ⊢Γ A λ ⊢A →
       dec⇇Type (⊢→⊢∙ ⊢A) B)
      of λ where
      (yes (ok , A , B)) → yes (ΠΣᶜ A B ok)
      (no not)           → no λ where
        (ΠΣᶜ A B ok)                  → not (ok , A , B)
        (univᶜ (infᶜ (ΠΣᵢ A B ok) _)) → not (ok , univᶜ A , univᶜ B)
  dec⇉Type ⊢Γ (varᵢ {x = x}) = case dec⇇-var x (Uⱼ ⊢Γ) of λ where
    (yes x⇇U) → yes (univᶜ x⇇U)
    (no ¬x⇇U) → no λ where
      (univᶜ x) → ¬x⇇U x
  dec⇉Type ⊢Γ (∘ᵢ t u) =
    case
      (Σ-dec (dec⇉-app ⊢Γ t u)
         (λ (_ , t∘u₁) (_ , t∘u₂) →
            case deterministic⇉ t∘u₁ t∘u₂ of λ { PE.refl → idᶠ })
         λ (_ , t∘u) →
       decEq (soundness⇉ ⊢Γ t∘u .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , t∘u) , A≡U)) → yes (univᶜ (infᶜ t∘u A≡U))
      (no not)                →
        no λ { (univᶜ (infᶜ t∘u A≡U)) → not ((_ , t∘u) , A≡U) }
  dec⇉Type ⊢Γ (fstᵢ t) =
    case
      (Σ-dec (dec⇉-fst ⊢Γ t)
         (λ (_ , fst-t₁) (_ , fst-t₂) →
            case deterministic⇉ fst-t₁ fst-t₂ of λ { PE.refl → idᶠ })
         λ (_ , fst-t) →
       decEq (soundness⇉ ⊢Γ fst-t .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , fst-t) , A≡U)) → yes (univᶜ (infᶜ fst-t A≡U))
      (no not)                  →
        no λ { (univᶜ (infᶜ fst-t A≡U)) → not ((_ , fst-t) , A≡U) }
  dec⇉Type ⊢Γ (sndᵢ t) =
    case
      (Σ-dec (dec⇉-snd ⊢Γ t)
         (λ (_ , snd-t₁) (_ , snd-t₂) →
            case deterministic⇉ snd-t₁ snd-t₂ of λ { PE.refl → idᶠ })
         λ (_ , snd-t) →
       decEq (soundness⇉ ⊢Γ snd-t .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , snd-t) , A≡U)) → yes (univᶜ (infᶜ snd-t A≡U))
      (no not)                  →
        no λ { (univᶜ (infᶜ snd-t A≡U)) → not ((_ , snd-t) , A≡U) }
  dec⇉Type ⊢Γ (prodrecᵢ B t u) =
    case
      (Σ-dec (dec⇉-prodrec ⊢Γ B t u)
         (λ (_ , pr₁) (_ , pr₂) →
            case deterministic⇉ pr₁ pr₂ of λ { PE.refl → idᶠ })
         λ (_ , pr) →
       decEq (soundness⇉ ⊢Γ pr .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , pr) , A≡U)) → yes (univᶜ (infᶜ pr A≡U))
      (no not)               →
        no λ { (univᶜ (infᶜ pr A≡U)) → not ((_ , pr) , A≡U) }
  dec⇉Type ⊢Γ ℕᵢ = yes ℕᶜ
  dec⇉Type ⊢Γ zeroᵢ = no λ where
    (univᶜ (infᶜ zeroᵢ x₁)) → U≢ℕ (sym x₁)
  dec⇉Type ⊢Γ (sucᵢ x) = no λ where
    (univᶜ (infᶜ (sucᵢ x) x₁)) → U≢ℕ (sym x₁)
  dec⇉Type ⊢Γ (natrecᵢ B t u v) =
    case
      (Σ-dec (dec⇉-natrec ⊢Γ B t u v)
         (λ (_ , nr₁) (_ , nr₂) →
            case deterministic⇉ nr₁ nr₂ of λ { PE.refl → idᶠ })
         λ (_ , nr) →
       decEq (soundness⇉ ⊢Γ nr .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , nr) , A≡U)) → yes (univᶜ (infᶜ nr A≡U))
      (no not)               →
        no λ { (univᶜ (infᶜ nr A≡U)) → not ((_ , nr) , A≡U) }
  dec⇉Type ⊢Γ (Unitᵢ {s = s}) = case Unit-allowed? s of λ where
    (yes ok)    → yes (Unitᶜ ok)
    (no not-ok) → no λ where
      (Unitᶜ ok)                  → not-ok ok
      (univᶜ (infᶜ (Unitᵢ ok) _)) → not-ok ok
  dec⇉Type ⊢Γ starᵢ = no λ where
    (univᶜ (infᶜ (starᵢ _) x)) → U≢Unitⱼ (sym x)
  dec⇉Type ⊢Γ (unitrecᵢ B t u) =
    case
      (Σ-dec (dec⇉-unitrec ⊢Γ B t u)
         (λ (_ , ur₁) (_ , ur₂) →
            case deterministic⇉ ur₁ ur₂ of λ { PE.refl → idᶠ })
         λ (_ , ur) →
       decEq (soundness⇉ ⊢Γ ur .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , ur) , A≡U)) → yes (univᶜ (infᶜ ur A≡U))
      (no not)               →
        no λ { (univᶜ (infᶜ ur A≡U)) → not ((_ , ur) , A≡U) }
  dec⇉Type ⊢Γ Emptyᵢ = yes Emptyᶜ
  dec⇉Type ⊢Γ (emptyrecᵢ B t) =
    case
      (Σ-dec (dec⇉-emptyrec ⊢Γ B t)
         (λ (_ , er₁) (_ , er₂) →
            case deterministic⇉ er₁ er₂ of λ { PE.refl → idᶠ })
         λ (_ , er) →
       decEq (soundness⇉ ⊢Γ er .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , er) , A≡U)) → yes (univᶜ (infᶜ er A≡U))
      (no not)               →
        no λ { (univᶜ (infᶜ er A≡U)) → not ((_ , er) , A≡U) }
  dec⇉Type ⊢Γ (Idᵢ A t u) =
    case
      (dec⇇Type-with-cont ⊢Γ A λ ⊢A →
       dec⇇ t ⊢A ×-dec dec⇇ u ⊢A)
      of λ where
      (yes (A , t , u)) → yes (Idᶜ A t u)
      (no not)          → no λ where
        (Idᶜ A t u)                  → not (A , t , u)
        (univᶜ (infᶜ (Idᵢ A t u) _)) → not (univᶜ A , t , u)
  dec⇉Type ⊢Γ (Jᵢ A t B u v w) =
    case
      (Σ-dec (dec⇉-J ⊢Γ A t B u v w)
         (λ (_ , J₁) (_ , J₂) →
            case deterministic⇉ J₁ J₂ of λ { PE.refl → idᶠ })
         λ (_ , J′) →
       decEq (soundness⇉ ⊢Γ J′ .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , J′) , A≡U)) → yes (univᶜ (infᶜ J′ A≡U))
      (no not)               →
        no λ { (univᶜ (infᶜ J′ A≡U)) → not ((_ , J′) , A≡U) }
  dec⇉Type ⊢Γ (Kᵢ A t B u v) =
    case
      (Σ-dec (dec⇉-K ⊢Γ A t B u v)
         (λ (_ , K₁) (_ , K₂) →
            case deterministic⇉ K₁ K₂ of λ { PE.refl → idᶠ })
         λ (_ , K′) →
       decEq (soundness⇉ ⊢Γ K′ .proj₁) (Uⱼ ⊢Γ))
      of λ where
      (yes ((_ , K′) , A≡U)) → yes (univᶜ (infᶜ K′ A≡U))
      (no not)               →
        no λ { (univᶜ (infᶜ K′ A≡U)) → not ((_ , K′) , A≡U) }
  dec⇉Type _ ([]-congᵢ _ _ _ _) =
    no λ { (univᶜ (infᶜ ([]-congᵢ _ _ _ _ _) Id≡U)) → Id≢U Id≡U }

  -- Decidability of checking that a checkable term is a type

  dec⇇Type : ⊢ Γ → Checkable A → Dec (Γ ⊢ A ⇇Type)
  dec⇇Type ⊢Γ (lamᶜ t) = no λ where
    (univᶜ (lamᶜ x x₁)) → U.U≢B BΠ! (whnfRed* (proj₁ x) Uₙ)
    (univᶜ (infᶜ () _))
  dec⇇Type ⊢Γ (prodᶜ t u) = no λ where
    (univᶜ (prodᶜ x x₁ x₂)) → U.U≢B BΣ! (whnfRed* (proj₁ x) Uₙ)
    (univᶜ (infᶜ () _))
  dec⇇Type ⊢Γ rflᶜ = no λ where
    (univᶜ (rflᶜ (U⇒*Id , _) _)) → case whnfRed* U⇒*Id Uₙ of λ ()
    (univᶜ (infᶜ () _))
  dec⇇Type ⊢Γ (infᶜ x) = dec⇉Type ⊢Γ x

  -- Decidability of bi-directional type inference

  dec⇉ : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ⇉ A)
  dec⇉ _ Uᵢ = no λ { (_ , ()) }
  dec⇉ ⊢Γ (ΠΣᵢ {b} {p} {q} A B) =
    case
      (ΠΣ-allowed? b p q ×-dec
       dec⇇-with-cont A (Uⱼ ⊢Γ) λ ⊢A →
       dec⇇ B (Uⱼ (⊢→⊢∙ (univ ⊢A))))
      of λ where
      (yes (ok , A , B)) → yes (_ , ΠΣᵢ A B ok)
      (no not)           → no λ { (_ , ΠΣᵢ A B ok) → not (ok , A , B) }
  dec⇉ ⊢Γ varᵢ = yes (_ , varᵢ (dec⇉-var _ .proj₂))
  dec⇉ ⊢Γ (∘ᵢ t u) = dec⇉-app ⊢Γ t u
  dec⇉ ⊢Γ (fstᵢ t) = dec⇉-fst ⊢Γ t
  dec⇉ ⊢Γ (sndᵢ t) = dec⇉-snd ⊢Γ t
  dec⇉ ⊢Γ (prodrecᵢ A t u) = dec⇉-prodrec ⊢Γ A t u
  dec⇉ ⊢Γ ℕᵢ = yes (U , ℕᵢ)
  dec⇉ ⊢Γ zeroᵢ = yes (ℕ , zeroᵢ)
  dec⇉ ⊢Γ (sucᵢ t) = case dec⇇ t (ℕⱼ ⊢Γ) of λ where
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
    case
      (dec⇇-with-cont A (Uⱼ ⊢Γ) λ ⊢A →
       let ⊢A = univ ⊢A in
       dec⇇ t ⊢A ×-dec dec⇇ u ⊢A)
      of λ where
      (yes (A , t , u)) → yes (_ , Idᵢ A t u)
      (no not)          → no λ { (_ , Idᵢ A t u) → not (A , t , u) }
  dec⇉ ⊢Γ (Jᵢ A t B u v w) =
    dec⇉-J ⊢Γ A t B u v w
  dec⇉ ⊢Γ (Kᵢ A t B u v) =
    dec⇉-K ⊢Γ A t B u v
  dec⇉ ⊢Γ ([]-congᵢ {s} A t u v) =
    case
      ([]-cong-allowed? s ×-dec
       dec⇇Type-with-cont ⊢Γ A λ ⊢A →
       dec⇇-with-cont t ⊢A λ ⊢t →
       dec⇇-with-cont u ⊢A λ ⊢u →
       dec⇇ v (Idⱼ ⊢t ⊢u))
      of λ where
      (yes (ok , A , t , u , v)) → yes (_ , []-congᵢ A t u v ok)
      (no not)                   →
        no λ { (_ , []-congᵢ A t u v ok) → not (ok , A , t , u , v) }

  -- Decidability of bi-directional type checking

  dec⇇ : Checkable t → Γ ⊢ A → Dec (Γ ⊢ t ⇇ A)
  dec⇇ (lamᶜ {p} t) ⊢A =
    case
      (isΠΣ-with-cont ⊢A λ {b = b} {p = p′} _ ⊢C _ _ →
       decBinderMode b BMΠ ×-dec p ≟ p′ ×-dec dec⇇ t ⊢C)
      of λ where
      (yes ((_ , _ , _ , _ , _ , A) , PE.refl , PE.refl , t)) →
        yes (lamᶜ (A , ΠΣₙ) t)
      (no not) → no λ where
        (lamᶜ (A , _) t) →
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
        (prodᶜ (A , _) t u) →
          not ((_ , _ , _ , _ , _ , A) , PE.refl , PE.refl , t , u)
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
        (rflᶜ (A , _) t≡u) → not ((_ , _ , _ , A) , t≡u)
        (infᶜ () _)
  dec⇇ (infᶜ t) ⊢A =
    case
      (dec⇉-with-cont (wf ⊢A) t λ ⊢B →
       decEq ⊢B ⊢A)
      of λ where
      (yes ((_ , t) , B≡A)) → yes (infᶜ t B≡A)
      (no not) → no λ where
        (infᶜ t B≡A)  → not ((_ , t) , B≡A)
        (lamᶜ _ _)    → case t of λ ()
        (prodᶜ _ _ _) → case t of λ ()
        (rflᶜ _ _)    → case t of λ ()
