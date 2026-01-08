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
import Definition.Typed.Decidable.Internal.Substitution.Primitive
open import Definition.Typed.Decidable.Internal.Term R
open import Definition.Typed.Decidable.Internal.Weakening R
open import Definition.Typed.Inversion R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M as U using (Level-literal)
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Properties M
import Definition.Untyped.Sup R as S

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
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
  b         : Bool
  n n₁ n₂   : Nat
  x         : Fin _
  c         : Constants
  γ         : Contexts _
  Γ         : U.Cons _ _
  A         : U.Term _
  t t₁ t₂ u : Term _ _
  σ         : Subst _ _ _

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
-- Cons-free

-- Cons-free σ means that σ does not contain the constructor cons,
-- with the exception of applications of the form cons _ (var _).

infix 35 _⇑

data Cons-free {c} : Subst c n₂ n₁ → Set a where
  id   : Cons-free (id {n = n})
  wk1  : Cons-free σ → Cons-free (wk1 σ)
  _⇑   : Cons-free σ → Cons-free (σ ⇑)
  cons : Cons-free σ → Cons-free (cons σ (var x))

-- Is the substitution cons-free?

cons-free? : (σ : Subst c n₂ n₁) → Maybe (Cons-free σ)
cons-free? id               = just id
cons-free? (wk1 σ)          = wk1 <$> cons-free? σ
cons-free? (σ ⇑)            = _⇑ <$> cons-free? σ
cons-free? (cons σ (var _)) = cons <$> cons-free? σ
cons-free? (cons _ _)       = nothing

opaque

  -- If σ is cons-free, then U.var x U.[ ⌜ σ ⌝ˢ γ ] is a variable.

  Cons-free→var-[] :
    Cons-free σ → ∃ λ y → U.var x U.[ ⌜ σ ⌝ˢ γ ] PE.≡ U.var y
  Cons-free→var-[] {x} id =
    x , PE.refl
  Cons-free→var-[] {x} {γ} (wk1 {σ} σ-cf) =
    Σ.map _+1
      (λ {x = y} hyp →
         U.wk1 (U.var x U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ PE.cong U.wk1 hyp ⟩
         U.wk1 (U.var y)                 ≡⟨⟩
         U.var (y +1)                    ∎)
      (Cons-free→var-[] σ-cf)
  Cons-free→var-[] {x = x0} (_ ⇑) =
    x0 , PE.refl
  Cons-free→var-[] {x = x +1} {γ} (_⇑ {σ} σ-cf) =
    Σ.map _+1
      (λ {x = y} hyp →
         U.wk1 (U.var x U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ PE.cong U.wk1 hyp ⟩
         U.wk1 (U.var y)                 ≡⟨⟩
         U.var (y +1)                    ∎)
      (Cons-free→var-[] σ-cf)
  Cons-free→var-[] {x = x0} (cons {x} _) =
    x , PE.refl
  Cons-free→var-[] {x = _ +1} (cons σ-cf) =
    Cons-free→var-[] σ-cf

opaque

  -- If σ is cons-free, then t is a level literal if and only if
  -- t U.[ ⌜ σ ⌝ˢ γ ] is a level literal.

  Cons-free→Level-literal-[] :
    ∀ {t} →
    Cons-free σ →
    Level-literal t ⇔ Level-literal (t U.[ ⌜ σ ⌝ˢ γ ])
  Cons-free→Level-literal-[] σ-cf =
    Level-literal-[] , flip (lemma σ-cf) PE.refl
    where
    lemma :
      ∀ {t u} →
      Cons-free σ → Level-literal u → t U.[ ⌜ σ ⌝ˢ γ ] PE.≡ u →
      Level-literal t
    lemma {t} σ-cf U.zeroᵘ eq =
      case subst-zeroᵘ {t = t} eq of λ where
        (inj₁ (_ , PE.refl)) →
          case PE.trans (PE.sym eq) (Cons-free→var-[] σ-cf .proj₂)
          of λ ()
        (inj₂ PE.refl) →
          U.zeroᵘ
    lemma {t} σ-cf (U.sucᵘ u-lit) eq =
      case subst-sucᵘ {t = t} eq of λ where
        (inj₁ (_ , PE.refl)) →
          case PE.trans (PE.sym eq) (Cons-free→var-[] σ-cf .proj₂)
          of λ ()
        (inj₂ (_ , PE.refl , eq)) →
          U.sucᵘ (lemma σ-cf u-lit eq)

opaque
  unfolding S._supᵘₗ_

  -- If σ is cons-free, then U_.[ ⌜ σ ⌝ˢ γ ] commutes with S._supᵘₗ_.

  Cons-free→supᵘₗ[⌜⌝ˢ] :
    ∀ {t u} →
    Cons-free σ →
    t S.supᵘₗ u U.[ ⌜ σ ⌝ˢ γ ] PE.≡
    (t U.[ ⌜ σ ⌝ˢ γ ]) S.supᵘₗ (u U.[ ⌜ σ ⌝ˢ γ ])
  Cons-free→supᵘₗ[⌜⌝ˢ] {σ} {γ} {t} {u} σ-cf
    with level-support
  … | U.level-type _  = PE.refl
  … | U.only-literals
    with U.Level-literal? t ×-dec U.Level-literal? u
       | U.Level-literal? (t U.[ ⌜ σ ⌝ˢ γ ]) ×-dec
         U.Level-literal? (u U.[ ⌜ σ ⌝ˢ γ ])
  …   | yes (tₗ , uₗ) | _ =
        supᵘₗ′-[] tₗ uₗ
  …   | no not-both₁ | no not-both₂ =
        t U.supᵘₗ′ u U.[ ⌜ σ ⌝ˢ γ ]                     ≡⟨ PE.cong U._[ _ ] (supᵘₗ′≡supᵘ not-both₁) ⟩
        t U.supᵘ u U.[ ⌜ σ ⌝ˢ γ ]                       ≡⟨⟩
        (t U.[ ⌜ σ ⌝ˢ γ ]) U.supᵘ (u U.[ ⌜ σ ⌝ˢ γ ])    ≡˘⟨ supᵘₗ′≡supᵘ not-both₂ ⟩
        (t U.[ ⌜ σ ⌝ˢ γ ]) U.supᵘₗ′ (u U.[ ⌜ σ ⌝ˢ γ ])  ∎
  …   | no not-both | yes both =
        ⊥-elim $ not-both $
        Σ.map (Cons-free→Level-literal-[] σ-cf .proj₂)
          (Cons-free→Level-literal-[] σ-cf .proj₂) both

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
  cons-free : Cons-free σ → ⌜[]⌝-assumption t σ γ

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
      (cons-free σ-cf) →
        PE.sym (Cons-free→supᵘₗ[⌜⌝ˢ] σ-cf)
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
      (level (literal _ _ ⊔-lit)) →
        PE.sym $ S.supᵘₗ-[]′ λ not-okᴸ _ →
          (                                                     $⟨ ⊔-lit ⟩
           Level-literal (⌜ subst (l₁ supᵘₗ l₂) σ ⌝ γ)          →⟨ S.Level-literal-supᵘₗ-[] ⟩
           Level-literal (⌜ l₁ supᵘₗ l₂ ⌝ γ)                    ⇔⟨ S.Level-literal-supᵘₗ⇔ not-okᴸ ⟩→
           Level-literal (⌜ l₁ ⌝ γ) × Level-literal (⌜ l₂ ⌝ γ)  □)
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

------------------------------------------------------------------------
-- Removing weaken and subst

-- Removes top-level weaken and subst constructors.

remove-weaken-subst′ :
  (t : Term c n) →
  ∃₃ λ n′ (σ : Subst c n n′) (u : Term c n′) →
    ∀ {γ} → ⌜ t ⌝ γ PE.≡ ⌜ subst u σ ⌝ γ
remove-weaken-subst′ (weaken ρ t) with remove-weaken-subst′ t
… | _ , σ , u , hyp = _ , ρ •ₛ σ , u , lemma
  where
  opaque
    lemma : U.wk ρ (⌜ t ⌝ γ) PE.≡ ⌜ u ⌝ γ U.[ ⌜ ρ •ₛ σ ⌝ˢ γ ]
    lemma {γ} =
      U.wk ρ (⌜ t ⌝ γ)                 ≡⟨ PE.cong (U.wk _) hyp ⟩
      U.wk ρ (⌜ u ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ wk-subst (⌜ u ⌝ _) ⟩
      ⌜ u ⌝ γ U.[ ρ U.•ₛ ⌜ σ ⌝ˢ γ ]    ≡˘⟨ substVar-to-subst ⌜•ₛ⌝ˢ (⌜ u ⌝ _) ⟩
      ⌜ u ⌝ γ U.[ ⌜ ρ •ₛ σ ⌝ˢ γ ]      ∎
remove-weaken-subst′ (subst t σ) with remove-weaken-subst′ t
… | _ , σ′ , u , hyp = _ , σ ₛ•ₛ σ′ , u , lemma
  where
  opaque
    lemma : ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ] PE.≡ ⌜ u ⌝ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]
    lemma {γ} =
      ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]                  ≡⟨ PE.cong U._[ _ ] hyp ⟩
      ⌜ u ⌝ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ≡⟨ substCompEq (⌜ u ⌝ _) ⟩
      ⌜ u ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ u ⌝ _) ⟩
      ⌜ u ⌝ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ∎
remove-weaken-subst′ t = _ , id , t , lemma
  where
  opaque
    lemma : ⌜ t ⌝ γ PE.≡ ⌜ subst t id ⌝ γ
    lemma {γ} =
      ⌜ t ⌝ γ                  ≡˘⟨ subst-id _ ⟩
      ⌜ t ⌝ γ U.[ U.idSubst ]  ∎

-- A type used to state remove-weaken-subst.

data Remove-weaken-subst-assumption
       (t u : Term c n) (b : Bool) (γ : Contexts c) : Set a where
  cons-free : b PE.≡ true → Remove-weaken-subst-assumption t u b γ

  level-allowed : Level-allowed → Remove-weaken-subst-assumption t u b γ

  not-supᵘₗ : Not-supᵘₗ u → Remove-weaken-subst-assumption t u b γ

  type₁ : Γ ⊢ ⌜ t ⌝ γ        → Remove-weaken-subst-assumption t u b γ
  type₂ : Γ ⊢ ⌜ u ⌝ γ        → Remove-weaken-subst-assumption t u b γ
  level : Γ ⊢ ⌜ t ⌝ γ ∷Level → Remove-weaken-subst-assumption t u b γ
  term₁ : Γ ⊢ ⌜ t ⌝ γ ∷ A    → Remove-weaken-subst-assumption t u b γ
  term₂ : Γ ⊢ ⌜ u ⌝ γ ∷ A    → Remove-weaken-subst-assumption t u b γ

opaque

  -- A cast lemma for Remove-weaken-subst-assumption.

  cast-Remove-weaken-subst-assumption :
    ⌜ t₁ ⌝ γ PE.≡ ⌜ t₂ ⌝ γ →
    Remove-weaken-subst-assumption t₁ u b γ →
    Remove-weaken-subst-assumption t₂ u b γ
  cast-Remove-weaken-subst-assumption eq = λ where
    (cons-free cf)     → cons-free cf
    (level-allowed ok) → level-allowed ok
    (not-supᵘₗ ns)     → not-supᵘₗ ns
    (type₁ ⊢t)         → type₁ (PE.subst (_⊢_ _) eq ⊢t)
    (type₂ ⊢u)         → type₂ ⊢u
    (level ⊢t)         → level (PE.subst (_⊢_∷Level _) eq ⊢t)
    (term₁ ⊢t)         → term₁ (PE.subst (flip (_⊢_∷_ _) _) eq ⊢t)
    (term₂ ⊢u)         → term₂ ⊢u

-- Removes top-level weaken and subst constructors.
--
-- Note that the result might have top-level weaken or subst
-- constructors (for instance if the term is
-- subst (var x0) (cons id (subst ℕ id))).

remove-weaken-subst :
  (t : Term c n) →
  ∃₂ λ (u : Term c n) (b : Bool) →
    ∀ {γ} → Remove-weaken-subst-assumption t u b γ →
    ⌜ t ⌝ γ PE.≡ ⌜ u ⌝ γ
remove-weaken-subst t with remove-weaken-subst′ t
… | _ , σ , u , hyp = u [ σ ] , cf , lemma
  where
  cf : Bool
  cf with cons-free? σ
  … | just _  = true
  … | nothing = false

  opaque

    ≡true→Cons-free : cf PE.≡ true → Cons-free σ
    ≡true→Cons-free _  with cons-free? σ
    ≡true→Cons-free _  | just cf = cf
    ≡true→Cons-free () | nothing

    lemma :
      Remove-weaken-subst-assumption t (u [ σ ]) cf γ →
      ⌜ t ⌝ γ PE.≡ ⌜ u [ σ ] ⌝ γ
    lemma {γ} ass =
      ⌜ t ⌝ γ                 ≡⟨ hyp ⟩
      ⌜ subst u σ ⌝ γ         ≡⟨⟩
      ⌜ u ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]  ≡˘⟨ ⌜[]⌝ _ ass′ ⟩
      ⌜ u [ σ ] ⌝ γ           ∎
      where
      ass′ : ⌜[]⌝-assumption u σ γ
      ass′ = case ass of λ where
        (cons-free ok)     → cons-free (≡true→Cons-free ok)
        (level-allowed ok) → level-allowed ok
        (not-supᵘₗ ns)     → not-supᵘₗ (Not-supᵘₗ-[]→ ns)
        (type₁ ⊢t)         → type₂ (PE.subst (_⊢_ _) hyp ⊢t)
        (type₂ ⊢u[σ])      → type₁ ⊢u[σ]
        (level ⊢t)         → level (PE.subst (_⊢_∷Level _) hyp ⊢t)
        (term₁ ⊢t)         → term₂ (PE.subst (flip (_⊢_∷_ _) _) hyp ⊢t)
        (term₂ ⊢u[σ])      → term₁ ⊢u[σ]

-- The result of remove-weaken-subst can have top-level weaken or
-- subst constructors.

_ :
  remove-weaken-subst {c = c} {n = n}
    (subst (var x0) (cons id (subst ℕ id))) .proj₁ PE.≡
  subst ℕ id
_ = PE.refl
