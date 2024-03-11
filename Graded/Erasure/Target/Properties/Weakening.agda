------------------------------------------------------------------------
-- Laws for weakenings in the target language.
------------------------------------------------------------------------

module Graded.Erasure.Target.Properties.Weakening where

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

open import Graded.Erasure.Target renaming (refl to ⇒*-refl; trans to ⇒*-trans)

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality hiding (subst)

private
  variable
    ℓ m n : Nat
    ρ ρ′ : Wk m n
    t : Term n
    s : Strictness

-- Weakening properties

-- Extensionally equal weakenings, if applied to a term,
-- yield the same weakened term.  Or:
-- If two weakenings are equal under wkVar, then they are equal under wk.

mutual
  wkVar-to-wk : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
              → ∀ (t : Term n) → wk ρ t ≡ wk ρ′ t
  wkVar-to-wk eq (var x) = cong var (eq x)
  wkVar-to-wk eq (lam t) = cong lam (wkVar-to-wk (wkVar-lift eq) t)
  wkVar-to-wk eq (t ∘⟨ _ ⟩ u) =
    cong₂ _∘⟨ _ ⟩_ (wkVar-to-wk eq t) (wkVar-to-wk eq u)
  wkVar-to-wk eq zero = refl
  wkVar-to-wk eq (suc t) = cong suc (wkVar-to-wk eq t)
  wkVar-to-wk eq (natrec z s n) = cong₃ natrec (wkVar-to-wk eq z) (wkVar-to-wk (wkVar-lift (wkVar-lift eq)) s) (wkVar-to-wk eq n)
  wkVar-to-wk eq (prod t u) = cong₂ prod (wkVar-to-wk eq t) (wkVar-to-wk eq u)
  wkVar-to-wk eq (fst t) = cong fst (wkVar-to-wk eq t)
  wkVar-to-wk eq (snd t) = cong snd (wkVar-to-wk eq t)
  wkVar-to-wk eq (prodrec t u) = cong₂ prodrec (wkVar-to-wk eq t) (wkVar-to-wk (wkVar-lift (wkVar-lift eq)) u)
  wkVar-to-wk eq star = refl
  wkVar-to-wk eq (unitrec t u) = cong₂ unitrec (wkVar-to-wk eq t) (wkVar-to-wk eq u)
  wkVar-to-wk eq ↯ = refl

-- id is the identity renaming.

mutual
  wk-id : (t : Term n) → wk id t ≡ t
  wk-id (var x) = refl
  wk-id (lam t) = cong lam (trans (wkVar-to-wk wkVar-lift-id t) (wk-id t))
  wk-id (t ∘⟨ _ ⟩ u) = cong₂ _∘⟨ _ ⟩_ (wk-id t) (wk-id u)
  wk-id zero = refl
  wk-id (suc t) = cong suc (wk-id t)
  wk-id (natrec z s n) = cong₃ natrec (wk-id z) (trans (wkVar-to-wk (wkVar-lifts-id 2) s) (wk-id s)) (wk-id n)
  wk-id (prod t u) = cong₂ prod (wk-id t) (wk-id u)
  wk-id (fst t) = cong fst (wk-id t)
  wk-id (snd t) = cong snd (wk-id t)
  wk-id (prodrec t u) = cong₂ prodrec (wk-id t) (trans (wkVar-to-wk (wkVar-lifts-id 2) u) (wk-id u))
  wk-id star = refl
  wk-id (unitrec t u) = cong₂ unitrec (wk-id t) (wk-id u)
  wk-id ↯ = refl

-- lift id  is also the identity renaming.

wk-lift-id : (t : Term (1+ n)) → wk (lift id) t ≡ t
wk-lift-id t = trans (wkVar-to-wk wkVar-lift-id t) (wk-id t)

-- The function wk commutes with composition.

mutual
  wk-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (t : Term n) → wk ρ (wk ρ′ t) ≡ wk (ρ • ρ′) t
  wk-comp ρ ρ′ (var x) = cong var (wkVar-comp ρ ρ′ x)
  wk-comp ρ ρ′ (lam t) = cong lam (wk-comp (lift ρ) (lift ρ′) t)
  wk-comp ρ ρ′ (t ∘⟨ _ ⟩ u) =
    cong₂ _∘⟨ _ ⟩_ (wk-comp ρ ρ′ t) (wk-comp ρ ρ′ u)
  wk-comp ρ ρ′ zero = refl
  wk-comp ρ ρ′ (suc t) = cong suc (wk-comp ρ ρ′ t)
  wk-comp ρ ρ′ (natrec z s n) = cong₃ natrec (wk-comp ρ ρ′ z) (wk-comp (lift (lift ρ)) (lift (lift ρ′)) s) (wk-comp ρ ρ′ n)
  wk-comp ρ ρ′ (prod t u) = cong₂ prod (wk-comp ρ ρ′ t) (wk-comp ρ ρ′ u)
  wk-comp ρ ρ′ (fst t) = cong fst (wk-comp ρ ρ′ t)
  wk-comp ρ ρ′ (snd t) = cong snd (wk-comp ρ ρ′ t)
  wk-comp ρ ρ′ (prodrec t u) = cong₂ prodrec (wk-comp ρ ρ′ t) (wk-comp (lift (lift ρ)) (lift (lift ρ′)) u)
  wk-comp ρ ρ′ star = refl
  wk-comp ρ ρ′ (unitrec t u) = cong₂ unitrec (wk-comp ρ ρ′ t) (wk-comp ρ ρ′ u)
  wk-comp ρ ρ′ ↯ = refl



-- The following lemmata are variations on the equality
--
--   wk1 ∘ ρ = lift ρ ∘ wk1.
--
-- Typing:  Γ∙A ≤ Γ ≤ Δ  <==>  Γ∙A ≤ Δ∙A ≤ Δ.

wk1-wk : (ρ : Wk m n) (t : Term n) → wk1 (wk ρ t) ≡ wk (step ρ) t
wk1-wk ρ t = wk-comp (step id) ρ t

lift-wk1 : (ρ : Wk m n) (t : Term n) → wk (lift ρ) (wk1 t) ≡ wk (step ρ) t
lift-wk1 pr A = trans (wk-comp (lift pr) (step id) A)
                      (sym (cong (λ x → wk x A) (lift-step-comp pr)))

wk1-wk≡lift-wk1 : (ρ : Wk m n) (t : Term n) → wk1 (wk ρ t) ≡ wk (lift ρ) (wk1 t)
wk1-wk≡lift-wk1 ρ t = trans (wk1-wk ρ t) (sym (lift-wk1 ρ t))

opaque

  -- A weakening lemma for suc⟨_⟩.

  wk-suc⟨⟩ : wk ρ (suc⟨ s ⟩ t) ≡ suc⟨ s ⟩ (wk ρ t)
  wk-suc⟨⟩ {s = strict}     = refl
  wk-suc⟨⟩ {s = non-strict} = refl
