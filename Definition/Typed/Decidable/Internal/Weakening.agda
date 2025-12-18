------------------------------------------------------------------------
-- Weakening operations used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Weakening
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open import Definition.Typed.Decidable.Internal.Term TR

open import Definition.Untyped M as U using (Wk)
open import Definition.Untyped.Properties M

open Wk

open import Tools.Fin
open import Tools.Function
open import Tools.Maybe
open import Tools.Nat as N
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  n n₁ n₂ n₃ : Nat
  c          : Constants
  γ          : Contexts _
  ρ          : Wk _ _
  σ          : Subst _ _ _

------------------------------------------------------------------------
-- Composition

mutual

  -- Composition of weakenings and substitutions.

  infixl 30 _•ₛ_

  _•ₛ_ : Wk n₃ n₂ → Subst c n₂ n₁ → Subst c n₃ n₁
  id     •ₛ σ        = σ
  step ρ •ₛ σ        = wk1 (ρ •ₛ σ)
  lift ρ •ₛ id       = toSubst ρ ⇑
  lift ρ •ₛ σ ⇑      = (ρ •ₛ σ) ⇑
  lift ρ •ₛ wk1 σ    = wk1 (ρ •ₛ σ)
  ρ      •ₛ cons σ t = cons (ρ •ₛ σ) (weaken ρ t)

  -- Turns weakenings into substitutions.

  toSubst : Wk n₂ n₁ → Subst c n₂ n₁
  toSubst ρ = ρ •ₛ id

opaque mutual

  -- The function ⌜_⌝ˢ commutes with _•ₛ_/U._•ₛ_.

  ⌜•ₛ⌝ˢ : ∀ x → ⌜ ρ •ₛ σ ⌝ˢ γ x PE.≡ (ρ U.•ₛ ⌜ σ ⌝ˢ γ) x
  ⌜•ₛ⌝ˢ {ρ = id} {σ} {γ} x =
    ⌜ σ ⌝ˢ γ x              ≡˘⟨ wk-id _ ⟩
    U.wk U.id (⌜ σ ⌝ˢ γ x)  ∎
  ⌜•ₛ⌝ˢ {ρ = step ρ} {σ} {γ} x =
    U.wk1 (⌜ ρ •ₛ σ ⌝ˢ γ x)      ≡⟨ PE.cong U.wk1 (⌜•ₛ⌝ˢ _) ⟩
    U.wk1 ((ρ U.•ₛ ⌜ σ ⌝ˢ γ) x)  ≡⟨⟩
    U.wk1 (U.wk ρ (⌜ σ ⌝ˢ γ x))  ≡⟨ wk1-wk _ _ ⟩
    U.wk (step ρ) (⌜ σ ⌝ˢ γ x)   ∎
  ⌜•ₛ⌝ˢ {ρ = lift _} {σ = id} x0 =
    PE.refl
  ⌜•ₛ⌝ˢ {ρ = lift ρ} {σ = id} {γ} (x +1) =
    U.wk1 (⌜ toSubst ρ ⌝ˢ γ x)  ≡⟨ PE.cong U.wk1 (⌜toSubst⌝ˢ x) ⟩
    U.wk1 (U.toSubst ρ x)       ∎
  ⌜•ₛ⌝ˢ {ρ = lift ρ} {σ = wk1 σ} {γ} x =
    U.wk1 (⌜ ρ •ₛ σ ⌝ˢ γ x)             ≡⟨ PE.cong U.wk1 (⌜•ₛ⌝ˢ _) ⟩
    U.wk1 (U.wk ρ (⌜ σ ⌝ˢ γ x))         ≡⟨ wk1-wk≡lift-wk1 _ _ ⟩
    U.wk (lift ρ) (U.wk1 (⌜ σ ⌝ˢ γ x))  ∎
  ⌜•ₛ⌝ˢ {ρ = lift _} {σ = _ ⇑} x0 =
    PE.refl
  ⌜•ₛ⌝ˢ {ρ = lift ρ} {σ = σ ⇑} {γ} (x +1) =
    U.wk1 (⌜ ρ •ₛ σ ⌝ˢ γ x)               ≡⟨ PE.cong U.wk1 (⌜•ₛ⌝ˢ _) ⟩
    U.wk1 (U.wk ρ (⌜ σ ⌝ˢ γ x))           ≡⟨ wk1-wk≡lift-wk1 _ _ ⟩
    U.wk (U.lift ρ) (U.wk1 (⌜ σ ⌝ˢ γ x))  ∎
  ⌜•ₛ⌝ˢ {ρ = lift _} {σ = cons _ _} x0 =
    PE.refl
  ⌜•ₛ⌝ˢ {ρ = ρ@(lift _)} {σ = cons σ _} {γ} (x +1) =
    ⌜ ρ •ₛ σ ⌝ˢ γ x      ≡⟨ ⌜•ₛ⌝ˢ {σ = σ} x ⟩
    U.wk ρ (⌜ σ ⌝ˢ γ x)  ∎

  -- The function ⌜_⌝ˢ commutes with toSubst/U.toSubst.

  ⌜toSubst⌝ˢ : ∀ x → ⌜ toSubst ρ ⌝ˢ γ x PE.≡ U.toSubst ρ x
  ⌜toSubst⌝ˢ = ⌜•ₛ⌝ˢ {σ = id}

------------------------------------------------------------------------
-- Weakening of terms

-- Weakening (lazy): This operation applies the weakening by pushing
-- it just below the term's top-level constructor.

wk : Wk n₂ n₁ → Term c n₁ → Term c n₂
wk ρ (meta-var x σ)          = meta-var x (ρ •ₛ σ)
wk ρ (weaken ρ′ t)           = weaken (ρ U.• ρ′) t
wk ρ (subst t σ)             = subst t (ρ •ₛ σ)
wk ρ (var x)                 = var (U.wkVar ρ x)
wk ρ (defn α)                = defn α
wk ρ Empty                   = Empty
wk ρ (emptyrec p A t)        = emptyrec p (weaken ρ A) (weaken ρ t)
wk ρ (U l)                   = U l
wk ρ (Unit s l)              = Unit s l
wk ρ (star s l)              = star s l
wk ρ (unitrec l p q A t u)   = unitrec l p q (weaken (lift ρ) A)
                                 (weaken ρ t) (weaken ρ u)
wk ρ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) = ΠΣ⟨ b ⟩ p , q ▷ weaken ρ A ▹
                               weaken (lift ρ) B
wk ρ (lam p qA t)            = lam p (Σ.map idᶠ (weaken ρ) <$> qA)
                                 (weaken (lift ρ) t)
wk ρ (t ∘⟨ p ⟩ u)            = weaken ρ t ∘⟨ p ⟩ weaken ρ u
wk ρ (prod s p qB t u)       = prod s p
                                 (Σ.map idᶠ (weaken (lift ρ)) <$> qB)
                                 (weaken ρ t) (weaken ρ u)
wk ρ (fst p t)               = fst p (weaken ρ t)
wk ρ (snd p t)               = snd p (weaken ρ t)
wk ρ (prodrec r p q A t u)   = prodrec r p q (weaken (lift ρ) A)
                                 (weaken ρ t) (weaken (U.liftn ρ 2) u)
wk ρ ℕ                       = ℕ
wk ρ zero                    = zero
wk ρ (suc t)                 = suc (weaken ρ t)
wk ρ (natrec p q r A t u v)  = natrec p q r (weaken (lift ρ) A)
                                 (weaken ρ t) (weaken (U.liftn ρ 2) u)
                                 (weaken ρ v)
wk ρ (Id A t u)              = Id (weaken ρ A) (weaken ρ t) (weaken ρ u)
wk ρ (rfl t)                 = rfl (weaken ρ <$> t)
wk ρ (J p q A t B u v w)     = J p q (weaken ρ A) (weaken ρ t)
                                 (weaken (U.liftn ρ 2) B) (weaken ρ u)
                                 (weaken ρ v) (weaken ρ w)
wk ρ (K p A t B u v)         = K p (weaken ρ A) (weaken ρ t)
                                 (weaken (lift ρ) B) (weaken ρ u)
                                 (weaken ρ v)
wk ρ ([]-cong s A t u v)     = []-cong s (weaken ρ A) (weaken ρ t)
                                 (weaken ρ u) (weaken ρ v)

opaque

  -- The function ⌜_⌝ commutes with weakening.

  ⌜wk⌝ : (t : Term c n) → ⌜ wk ρ t ⌝ γ PE.≡ U.wk ρ (⌜ t ⌝ γ)
  ⌜wk⌝ {ρ} {γ} (meta-var x σ) =
    ⌜ meta-var x (ρ •ₛ σ) ⌝ γ         ≡⟨ ⌜meta-var⌝ (ρ •ₛ _) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ ρ •ₛ σ ⌝ˢ γ ]      ≡⟨ substVar-to-subst ⌜•ₛ⌝ˢ (⌜ x ⌝ᵐ γ) ⟩
    ⌜ x ⌝ᵐ γ U.[ ρ U.•ₛ ⌜ σ ⌝ˢ γ ]    ≡˘⟨ wk-subst (⌜ x ⌝ᵐ γ) ⟩
    U.wk ρ (⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ ])  ≡˘⟨ PE.cong (U.wk _) (⌜meta-var⌝ σ) ⟩
    U.wk ρ (⌜ meta-var x σ ⌝ γ)       ∎
  ⌜wk⌝ {ρ} {γ} (weaken ρ′ t) =
    ⌜ weaken (ρ U.• ρ′) t ⌝ γ   ≡⟨⟩
    U.wk (ρ U.• ρ′) (⌜ t ⌝ γ)   ≡˘⟨ wk-comp _ _ _ ⟩
    U.wk ρ (U.wk ρ′ (⌜ t ⌝ γ))  ∎
  ⌜wk⌝ {ρ} {γ} (subst t σ) =
    ⌜ t ⌝ γ U.[ ⌜ ρ •ₛ σ ⌝ˢ γ ]      ≡⟨ substVar-to-subst ⌜•ₛ⌝ˢ (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ρ U.•ₛ ⌜ σ ⌝ˢ γ ]    ≡˘⟨ wk-subst (⌜ t ⌝ _) ⟩
    U.wk ρ (⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])  ∎
  ⌜wk⌝ (var _) =
    PE.refl
  ⌜wk⌝ (defn _) =
    PE.refl
  ⌜wk⌝ (U _) =
    PE.refl
  ⌜wk⌝ Empty =
    PE.refl
  ⌜wk⌝ (emptyrec _ _ _) =
    PE.refl
  ⌜wk⌝ (Unit _ _) =
    PE.refl
  ⌜wk⌝ (star _ _) =
    PE.refl
  ⌜wk⌝ (unitrec _ _ _ _ _ _) =
    PE.refl
  ⌜wk⌝ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) =
    PE.refl
  ⌜wk⌝ (lam _ _ _) =
    PE.refl
  ⌜wk⌝ (_ ∘⟨ _ ⟩ _) =
    PE.refl
  ⌜wk⌝ (prod _ _ _ _ _) =
    PE.refl
  ⌜wk⌝ (fst _ _) =
    PE.refl
  ⌜wk⌝ (snd _ _) =
    PE.refl
  ⌜wk⌝ (prodrec _ _ _ _ _ _) =
    PE.refl
  ⌜wk⌝ ℕ =
    PE.refl
  ⌜wk⌝ zero =
    PE.refl
  ⌜wk⌝ (suc _) =
    PE.refl
  ⌜wk⌝ (natrec _ _ _ _ _ _ _) =
    PE.refl
  ⌜wk⌝ (Id _ _ _) =
    PE.refl
  ⌜wk⌝ (rfl _) =
    PE.refl
  ⌜wk⌝ (J _ _ _ _ _ _ _ _) =
    PE.refl
  ⌜wk⌝ (K _ _ _ _ _ _) =
    PE.refl
  ⌜wk⌝ ([]-cong _ _ _ _ _) =
    PE.refl

------------------------------------------------------------------------
-- A derived term former

-- Weakens a term the given number of steps.

wk[_] : ∀ k → Term c n → Term c (k N.+ n)
wk[ k ] t = weaken (U.stepn id k) t
