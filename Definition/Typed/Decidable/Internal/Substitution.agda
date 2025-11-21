------------------------------------------------------------------------
-- Substitution operations used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Substitution
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Decidable.Internal.Term R
import Definition.Typed.Decidable.Internal.Substitution.Primitive
open import Definition.Typed.Inversion R
open import Definition.Typed.Well-formed R

import Definition.Untyped M as U
open import Definition.Untyped.Properties M
import Definition.Untyped.Sup R as S

open import Tools.Empty
open import Tools.Function
open import Tools.Maybe
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open Definition.Typed.Decidable.Internal.Substitution.Primitive R public

private variable
  n n₁ n₂ : Nat
  c       : Constants
  γ       : Contexts _
  Γ       : U.Cons _ _
  A       : U.Term _
  t       : Term _ _
  σ       : Subst _ _ _

------------------------------------------------------------------------
-- Applying substitutions to terms

-- Substitution (lazy): This operation applies the substitution by
-- pushing it just below the term's top-level constructor (unless the
-- term is a variable).

infix 25 _[_]

_[_] : Term c n₁ → Subst c n₂ n₁ → Term c n₂
meta-var x σ′         [ σ ] = meta-var x (σ ₛ•ₛ σ′)
weaken ρ t            [ σ ] = subst t (σ ₛ• ρ)
subst t σ′            [ σ ] = subst t (σ ₛ•ₛ σ′)
var x                 [ σ ] = x [ σ ]ᵛ
defn α                [ σ ] = defn α
Level                 [ _ ] = Level
zeroᵘ                 [ _ ] = zeroᵘ
sucᵘ l                [ σ ] = sucᵘ (subst l σ)
l₁ supᵘₗ l₂           [ σ ] = subst l₁ σ supᵘₗ subst l₂ σ
U l                   [ σ ] = U (subst l σ)
Lift l A              [ σ ] = Lift (subst l σ) (subst A σ)
lift l t              [ σ ] = lift (flip subst σ <$> l) (subst t σ)
lower t               [ σ ] = lower (subst t σ)
Empty                 [ σ ] = Empty
emptyrec p A t        [ σ ] = emptyrec p (subst A σ) (subst t σ)
Unit s                [ σ ] = Unit s
star s                [ σ ] = star s
unitrec p q A t u     [ σ ] = unitrec p q (subst A (σ ⇑)) (subst t σ)
                                (subst u σ)
ΠΣ⟨ b ⟩ p , q ▷ A ▹ B [ σ ] = ΠΣ⟨ b ⟩ p , q ▷ subst A σ ▹ subst B (σ ⇑)
lam p qA t            [ σ ] = lam p (Σ.map idᶠ (flip subst σ) <$> qA)
                                (subst t (σ ⇑))
t ∘⟨ p ⟩ u            [ σ ] = subst t σ ∘⟨ p ⟩ subst u σ
prod s p qB t u       [ σ ] = prod s p
                                (Σ.map idᶠ (flip subst (σ ⇑)) <$> qB)
                                (subst t σ) (subst u σ)
fst p t               [ σ ] = fst p (subst t σ)
snd p t               [ σ ] = snd p (subst t σ)
prodrec r p q A t u   [ σ ] = prodrec r p q (subst A (σ ⇑)) (subst t σ)
                                (subst u (σ ⇑[ 2 ]))
ℕ                     [ σ ] = ℕ
zero                  [ σ ] = zero
suc t                 [ σ ] = suc (subst t σ)
natrec p q r A t u v  [ σ ] = natrec p q r (subst A (σ ⇑)) (subst t σ)
                                (subst u (σ ⇑[ 2 ])) (subst v σ)
Id A t u              [ σ ] = Id (subst A σ) (subst t σ) (subst u σ)
rfl t                 [ σ ] = rfl (flip subst σ <$> t)
J p q A t B u v w     [ σ ] = J p q (subst A σ) (subst t σ)
                                (subst B (σ ⇑[ 2 ])) (subst u σ)
                                (subst v σ) (subst w σ)
K p A t B u v         [ σ ] = K p (subst A σ) (subst t σ)
                                (subst B (σ ⇑)) (subst u σ) (subst v σ)
[]-cong s l A t u v   [ σ ] = []-cong s (subst l σ) (subst A σ)
                                (subst t σ) (subst u σ) (subst v σ)

------------------------------------------------------------------------
-- Not-supᵘₗ

-- The term is not an application of _supᵘₗ_.

Not-supᵘₗ : Term c n → Set a
Not-supᵘₗ t = ¬ (∃₂ λ l₁ l₂ → t PE.≡ l₁ supᵘₗ l₂)

opaque

  -- If t [ σ ] is not an application of _supᵘₗ_, then the same
  -- applies to t.

  Not-supᵘₗ-[]→ : Not-supᵘₗ (t [ σ ]) → Not-supᵘₗ t
  Not-supᵘₗ-[]→ {t = _ supᵘₗ _} hyp _ =
    hyp (_ , _ , PE.refl)
  Not-supᵘₗ-[]→ {t = meta-var _ _}          _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = weaken _ _}            _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = subst _ _}             _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = var _}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = defn _}                _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = Level}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = zeroᵘ}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = sucᵘ _}                _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = U _}                   _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = Lift _ _}              _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = lift _ _}              _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = lower _}               _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = Empty}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = emptyrec _ _ _}        _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = Unit _}                _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = star _}                _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = unitrec _ _ _ _ _}     _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = lam _ _ _}             _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = _ ∘⟨ _ ⟩ _}            _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = prod _ _ _ _ _}        _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = fst _ _}               _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = snd _ _}               _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = prodrec _ _ _ _ _ _}   _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = ℕ}                     _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = zero}                  _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = suc _}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = natrec _ _ _ _ _ _ _}  _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = Id _ _ _}              _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = rfl _}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = J _ _ _ _ _ _ _ _}     _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = K _ _ _ _ _ _}         _ (_ , _ , ())
  Not-supᵘₗ-[]→ {t = []-cong _ _ _ _ _ _}   _ (_ , _ , ())

------------------------------------------------------------------------
-- ⌜[]⌝

-- A type used to state ⌜[]⌝.

data ⌜[]⌝-assumption
       (t : Term c n₁) (σ : Subst c n₂ n₁) (γ : Contexts c) :
       Set a where
  level-allowed : Level-allowed → ⌜[]⌝-assumption t σ γ

  not-supᵘₗ : Not-supᵘₗ t → ⌜[]⌝-assumption t σ γ

  type₁ : Γ ⊢ ⌜ t [ σ ] ⌝ γ                 → ⌜[]⌝-assumption t σ γ
  type₂ : Γ ⊢ ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]        → ⌜[]⌝-assumption t σ γ
  level : Γ ⊢ ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ] ∷Level → ⌜[]⌝-assumption t σ γ
  term₁ : Γ ⊢ ⌜ t [ σ ] ⌝ γ          ∷ A    → ⌜[]⌝-assumption t σ γ
  term₂ : Γ ⊢ ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ] ∷ A    → ⌜[]⌝-assumption t σ γ

opaque

  -- The function ⌜_⌝ commutes with substitution, given a certain
  -- assumption.

  ⌜[]⌝ :
    (t : Term c n) →
    ⌜[]⌝-assumption t σ γ →
    ⌜ t [ σ ] ⌝ γ PE.≡ ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜[]⌝ {σ} {γ} (meta-var x σ′) _ =
    ⌜ meta-var x (σ ₛ•ₛ σ′) ⌝ γ              ≡⟨ ⌜meta-var⌝ (σ ₛ•ₛ _) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ≡⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ x ⌝ᵐ γ) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substCompEq (⌜ x ⌝ᵐ γ) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ≡˘⟨ PE.cong U._[ _ ] (⌜meta-var⌝ σ′) ⟩
    ⌜ meta-var x σ′ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]       ∎
  ⌜[]⌝ {σ} {γ} (weaken ρ t) _ =
    ⌜ t ⌝ γ U.[ ⌜ σ ₛ• ρ ⌝ˢ γ ]      ≡⟨ substVar-to-subst (⌜ₛ•⌝ˢ σ) (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ• ρ ]    ≡˘⟨ subst-wk (⌜ t ⌝ _) ⟩
    U.wk ρ (⌜ t ⌝ γ) U.[ ⌜ σ ⌝ˢ γ ]  ∎
  ⌜[]⌝ {σ} {γ} (subst t σ′) _ =
    ⌜ t ⌝ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ≡⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substCompEq (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ∎
  ⌜[]⌝ {σ} (var _) _ =
    ⌜[]ᵛ⌝ σ _
  ⌜[]⌝ (defn _) _ =
    PE.refl
  ⌜[]⌝ Level _ =
    PE.refl
  ⌜[]⌝ zeroᵘ _ =
    PE.refl
  ⌜[]⌝ (sucᵘ _) _ =
    PE.refl
  ⌜[]⌝ {σ} {γ} (l₁ supᵘₗ l₂) hyp =
    case hyp of λ where
      (level-allowed okᴸ) →
        lemma′ okᴸ
      (not-supᵘₗ not-sup) →
        ⊥-elim (not-sup (_ , _ , PE.refl))
      (type₁ ⊢⊔) →
        let _ , _ , _ , ≡Level = inversion-supᵘₗ-⊢ ⊢⊔ in
        lemma ≡Level
      (type₂ ⊢⊔) →
        case S.supᵘₗ≡ (⌜ l₁ ⌝ γ) (⌜ l₂ ⌝ γ) of λ where
          (inj₁ (n , eq)) →
            let _ , ≡Level =
                  inversion-↓ᵘ-⊢ {n = n} $
                  PE.subst (_⊢_ _)
                    (PE.trans (PE.cong U._[ _ ] eq) ↓ᵘ-[]) ⊢⊔
            in
            lemma ≡Level
          (inj₂ eq) →
            let _ , _ , _ , ≡Level =
                  inversion-supᵘ-⊢ $
                  PE.subst (_⊢_ _) (PE.cong U._[ _ ] eq) ⊢⊔
            in
            lemma ≡Level
      (level (term okᴸ _)) →
        lemma′ okᴸ
      (level (literal not-ok _ ⊔-lit)) →
        case U.Level-literal? (⌜ l₁ ⌝ γ) ×-dec
             U.Level-literal? (⌜ l₂ ⌝ γ) of λ where
          (yes both-lit) →
            PE.sym (S.supᵘₗ-[]′ (λ _ → both-lit))
          (no not-both) →
            case
              PE.subst (λ l → U.Level-literal (l U.[ _ ]))
                (⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ   ≡⟨ S.supᵘₗ≡supᵘₗ′ not-ok ⟩
                 ⌜ l₁ ⌝ γ U.supᵘₗ′ ⌜ l₂ ⌝ γ  ≡⟨ supᵘₗ′≡supᵘ not-both ⟩
                 ⌜ l₁ ⌝ γ U.supᵘ ⌜ l₂ ⌝ γ    ∎)
                ⊔-lit
            of λ ()
      (term₁ ⊢⊔) →
        let _ , _ , ≡Level = inversion-supᵘₗ-⊢∷ ⊢⊔ in
        lemma ≡Level
      (term₂ ⊢⊔) →
        case S.supᵘₗ≡ (⌜ l₁ ⌝ γ) (⌜ l₂ ⌝ γ) of λ where
          (inj₁ (n , eq)) →
            let ≡Level =
                  inversion-↓ᵘ {n = n} $
                  PE.subst (flip (_⊢_∷_ _) _)
                    (PE.trans (PE.cong U._[ _ ] eq) ↓ᵘ-[]) ⊢⊔
            in
            lemma ≡Level
          (inj₂ eq) →
            let _ , _ , ≡Level =
                  inversion-supᵘ $
                  PE.subst (flip (_⊢_∷_ _) _) (PE.cong U._[ _ ] eq) ⊢⊔
            in
            lemma ≡Level
    where
    lemma′ :
      Level-allowed →
      (⌜ l₁ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]) S.supᵘₗ (⌜ l₂ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]) PE.≡
      ⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
    lemma′ okᴸ = PE.sym (S.supᵘₗ-[]′ (⊥-elim ∘→ (_$ okᴸ)))

    lemma :
      Γ ⊢ A ≡ U.Level →
      (⌜ l₁ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]) S.supᵘₗ (⌜ l₂ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]) PE.≡
      ⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
    lemma ≡Level = lemma′ (inversion-Level-⊢ (wf-⊢≡ ≡Level .proj₂))
  ⌜[]⌝ (U _) _ =
    PE.refl
  ⌜[]⌝ (Lift _ _) _ =
    PE.refl
  ⌜[]⌝ (lift _ _) _ =
    PE.refl
  ⌜[]⌝ (lower _) _ =
    PE.refl
  ⌜[]⌝ Empty _ =
    PE.refl
  ⌜[]⌝ (emptyrec _ _ _) _ =
    PE.refl
  ⌜[]⌝ (Unit _) _ =
    PE.refl
  ⌜[]⌝ (star _) _ =
    PE.refl
  ⌜[]⌝ (unitrec _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) _ =
    PE.refl
  ⌜[]⌝ (lam _ _ _) _ =
    PE.refl
  ⌜[]⌝ (_ ∘⟨ _ ⟩ _) _ =
    PE.refl
  ⌜[]⌝ (prod _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ (fst _ _) _ =
    PE.refl
  ⌜[]⌝ (snd _ _) _ =
    PE.refl
  ⌜[]⌝ (prodrec _ _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ ℕ _ =
    PE.refl
  ⌜[]⌝ zero _ =
    PE.refl
  ⌜[]⌝ (suc _) _ =
    PE.refl
  ⌜[]⌝ (natrec _ _ _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ (Id _ _ _) _ =
    PE.refl
  ⌜[]⌝ (rfl _) _ =
    PE.refl
  ⌜[]⌝ (J _ _ _ _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ (K _ _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ ([]-cong _ _ _ _ _ _) _ =
    PE.refl
