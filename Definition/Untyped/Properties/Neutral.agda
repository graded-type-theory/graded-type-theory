------------------------------------------------------------------------
-- Properties of neutral terms and WHNFs
------------------------------------------------------------------------

open import Definition.Typed.Variant
open import Tools.Nat

module Definition.Untyped.Properties.Neutral
  {a} (M : Set a)
  (type-variant : Type-variant)
  where

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant

private variable
  P : Set _
  A B t u : Term _
  ρ : Wk _ _
  σ : Subst _ _
  b : BinderMode
  s : Strength
  l : Universe-level
  p q : M
  n : Nat
  x : Fin _

opaque

  -- Constructor applications are not neutral.

  ¬-Neutral-U : ¬ Neutral {n = n} (U l)
  ¬-Neutral-U ()

  ¬-Neutral-ΠΣ : ¬ Neutral (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ¬-Neutral-ΠΣ ()

  ¬-Neutral-lam : ¬ Neutral (lam p t)
  ¬-Neutral-lam ()

  ¬-Neutral-prod : ¬ Neutral (prod s p t u)
  ¬-Neutral-prod ()

  ¬-Neutral-Empty : ¬ Neutral {n = n} Empty
  ¬-Neutral-Empty ()

  ¬-Neutral-Unit : ¬ Neutral {n = n} (Unit s l)
  ¬-Neutral-Unit ()

  ¬-Neutral-star : ¬ Neutral {n = n} (star s l)
  ¬-Neutral-star ()

  ¬-Neutral-ℕ : ¬ Neutral {n = n} ℕ
  ¬-Neutral-ℕ ()

  ¬-Neutral-zero : ¬ Neutral {n = n} zero
  ¬-Neutral-zero ()

  ¬-Neutral-suc : ¬ Neutral (suc t)
  ¬-Neutral-suc ()

  ¬-Neutral-Id : ¬ Neutral (Id A t u)
  ¬-Neutral-Id ()

  ¬-Neutral-rfl : ¬ Neutral {n = n} rfl
  ¬-Neutral-rfl ()

opaque

  -- Being a numeral is preserved under weakening

  wk-numeral : Numeral t → Numeral (wk ρ t)
  wk-numeral zeroₙ = zeroₙ
  wk-numeral (sucₙ n) = sucₙ (wk-numeral n)

opaque

  -- Terms that are neutral after applying a substitution are neutral
  -- before applying the substitution.

  neutral-subst : Neutral (t [ σ ]) → Neutral t
  neutral-subst n = lemma n refl
    where
    open import Tools.Product
    lemma : Neutral u → t [ σ ] ≡ u → Neutral t
    lemma {t} (var x) ≡u =
      case subst-var {t = t} ≡u of λ {
        (x , refl , ≡t′) →
      var x }
    lemma {t} (∘ₙ n) ≡u =
      case subst-∘ {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , refl , ≡t′ , _)) →
      ∘ₙ (lemma n ≡t′)}
    lemma {t} (fstₙ n) ≡u =
      case subst-fst {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , refl , ≡t′)) →
      fstₙ (lemma n ≡t′) }
    lemma {t} (sndₙ n) ≡u =
      case subst-snd {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , refl , ≡t′)) →
      sndₙ (lemma n ≡t′) }
    lemma {t} (natrecₙ n) ≡u =
      case subst-natrec {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , _ , refl , _ , _ , _ , ≡t′)) →
      natrecₙ (lemma n ≡t′) }
    lemma {t} (prodrecₙ n) ≡u =
      case subst-prodrec {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , refl , _ , ≡t′ , _)) →
      prodrecₙ (lemma n ≡t′) }
    lemma {t} (emptyrecₙ n) ≡u =
      case subst-emptyrec {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , refl , _ , ≡t′)) →
      emptyrecₙ (lemma n ≡t′) }
    lemma {t} (unitrecₙ no-η n) ≡u =
      case subst-unitrec {t = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , refl , _ , ≡t′ , _)) →
      unitrecₙ no-η (lemma n ≡t′) }
    lemma {t} (Jₙ n) ≡u =
      case subst-J {w = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , _ , _ , _ , refl , _ , _ , _ , _ , _ , ≡t′)) →
      Jₙ (lemma n ≡t′) }
    lemma {t} (Kₙ n) ≡u =
      case subst-K {w = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , _ , _ , refl , _ , _ , _ , _ , ≡t′)) →
      Kₙ (lemma n ≡t′) }
    lemma {t} ([]-congₙ n) ≡u =
      case subst-[]-cong {w = t} ≡u of λ {
        (inj₁ (_ , refl)) → var _ ;
        (inj₂ (_ , _ , _ , _ , refl , _ , _ , _ , ≡t′)) →
      []-congₙ (lemma n ≡t′) }


opaque

  -- Terms in whnf after applying a substitution are in whnf before
  -- applying the substitution.

  whnf-subst : Whnf (t [ σ ]) → Whnf t
  whnf-subst {t} = lemma refl
    where
    lemma : t [ σ ] ≡ u → Whnf u → Whnf t
    lemma ≡u Uₙ =
      case subst-U {t = t} ≡u of λ where
        (inj₁ (x , refl)) → ne (var x)
        (inj₂ refl) → Uₙ
    lemma ≡u ΠΣₙ =
      case subst-ΠΣ {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ (_ , _ , refl , _)) → ΠΣₙ
    lemma ≡u ℕₙ =
      case subst-ℕ {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ refl) → ℕₙ
    lemma ≡u Unitₙ =
      case subst-Unit {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ refl) → Unitₙ
    lemma ≡u Emptyₙ =
      case subst-Empty {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ refl) → Emptyₙ
    lemma ≡u Idₙ =
      case subst-Id {v = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ (_ , _ , _ , refl , _)) → Idₙ
    lemma ≡u lamₙ =
      case subst-lam {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ (_ , refl , _)) → lamₙ
    lemma ≡u zeroₙ =
      case subst-zero {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ refl) → zeroₙ
    lemma ≡u sucₙ =
      case subst-suc {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ (_ , refl , _)) → sucₙ
    lemma ≡u starₙ =
      case subst-star {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ refl) → starₙ
    lemma ≡u prodₙ =
      case subst-prod {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ (_ , _ , refl , _)) → prodₙ
    lemma ≡u rflₙ =
      case subst-rfl {t = t} ≡u of λ where
        (inj₁ (_ , refl)) → ne (var _)
        (inj₂ refl) → rflₙ
    lemma ≡u (ne n) =
      ne (neutral-subst (subst Neutral (sym ≡u) n))

opaque

  -- Terms that are "NeutralAt x" are neutral

  NeutralAt→Neutral : NeutralAt x t → Neutral t
  NeutralAt→Neutral var = var _
  NeutralAt→Neutral (∘ₙ n) = ∘ₙ (NeutralAt→Neutral n)
  NeutralAt→Neutral (fstₙ n) = fstₙ (NeutralAt→Neutral n)
  NeutralAt→Neutral (sndₙ n) = sndₙ (NeutralAt→Neutral n)
  NeutralAt→Neutral (natrecₙ n) = natrecₙ (NeutralAt→Neutral n)
  NeutralAt→Neutral (prodrecₙ n) = prodrecₙ (NeutralAt→Neutral n)
  NeutralAt→Neutral (emptyrecₙ n) = emptyrecₙ (NeutralAt→Neutral n)
  NeutralAt→Neutral (unitrecₙ x n) = unitrecₙ x (NeutralAt→Neutral n)
  NeutralAt→Neutral (Jₙ n) = Jₙ (NeutralAt→Neutral n)
  NeutralAt→Neutral (Kₙ n) = Kₙ (NeutralAt→Neutral n)
  NeutralAt→Neutral ([]-congₙ n) = []-congₙ (NeutralAt→Neutral n)


opaque

  -- Neutral terms are "NeutralAt x" for some x

  Neutral→NeutralAt : Neutral t → ∃ λ x → NeutralAt x t
  Neutral→NeutralAt (var x) = x , var
  Neutral→NeutralAt (∘ₙ n) = _ , ∘ₙ (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt (fstₙ n) = _ , fstₙ (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt (sndₙ n) = _ , sndₙ (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt (natrecₙ n) = _ , natrecₙ (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt (prodrecₙ n) = _ , prodrecₙ (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt (emptyrecₙ n) = _ , emptyrecₙ (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt (unitrecₙ x n) = _ , unitrecₙ x (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt (Jₙ n) = _ , Jₙ (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt (Kₙ n) = _ , Kₙ (Neutral→NeutralAt n .proj₂)
  Neutral→NeutralAt ([]-congₙ n) = _ , []-congₙ (Neutral→NeutralAt n .proj₂)

opaque

  -- If Γ and t are both indexed by n, t is neutral, and P or-empty Γ
  -- holds, then P holds.

  or-empty-Neutral→ :
    {Γ : Con Term n} {t : Term n}
    ⦃ ok : P or-empty Γ ⦄ →
    Neutral t → P
  or-empty-Neutral→ ⦃ ok = possibly-nonempty ⦃ ok ⦄ ⦄ _    = ok
  or-empty-Neutral→ ⦃ ok = ε ⦄                        t-ne =
    ⊥-elim (noClosedNe t-ne)
