------------------------------------------------------------------------
-- Inversion lemmas for weakening and substitution
------------------------------------------------------------------------

module Definition.Untyped.Inversion {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

private variable
  l              : Nat
  x              : Fin _
  ρ              : Wk _ _
  A B t t′ u v w : Term _
  p q r          : M
  s              : Strength
  b              : BinderMode
  σ              : Subst _ _

-- Inversion for var.

wk-var :
  wk ρ t ≡ var x →
  ∃ λ x′ → t ≡ var x′ × wkVar ρ x′ ≡ x
wk-var {t = var _} refl = _ , refl , refl

subst-var :
  t [ σ ] ≡ var x →
  ∃ λ x′ → t ≡ var x′ ×  σ x′ ≡ var x
subst-var {t = var _} eq = _ , refl , eq

-- Inversion for U.

wk-U : wk ρ t ≡ U l → t ≡ U l
wk-U {t = U l} refl = refl

subst-U : t [ σ ] ≡ U l → (∃ λ x → t ≡ var x) ⊎ t ≡ U l
subst-U {t = var _} _ = inj₁ (_ , refl)
subst-U {t = U _} refl = inj₂ refl

-- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

wk-ΠΣ :
  wk ρ t ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  ∃₂ λ A′ B′ →
     t ≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     wk ρ A′ ≡ A × wk (lift ρ) B′ ≡ B
wk-ΠΣ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} refl =
  _ , _ , refl , refl , refl

subst-ΠΣ :
  t [ σ ] ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  (∃ λ x → t ≡ var x) ⊎
  ∃₂ λ A′ B′ →
    t ≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
    A′ [ σ ] ≡ A × B′ [ liftSubst σ ] ≡ B
subst-ΠΣ {t = var _} _ =
  inj₁ (_ , refl)
subst-ΠΣ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} refl =
  inj₂ (_ , _ , refl , refl , refl)

-- Inversion for lam.

wk-lam :
  wk ρ t ≡ lam p u →
  ∃ λ u′ → t ≡ lam p u′ × wk (lift ρ) u′ ≡ u
wk-lam {t = lam _ _} refl = _ , refl , refl

subst-lam :
  t [ σ ] ≡ lam p u →
  (∃ λ x → t ≡ var x) ⊎
  ∃ λ u′ → t ≡ lam p u′ × u′ [ liftSubst σ ] ≡ u
subst-lam {t = var x} _ = inj₁ (_ , refl)
subst-lam {t = lam _ _} refl = inj₂ (_ , refl , refl)

-- Inversion for _∘⟨_⟩_.

wk-∘ :
  wk ρ t ≡ u ∘⟨ p ⟩ v →
  ∃₂ λ u′ v′ → t ≡ u′ ∘⟨ p ⟩ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-∘ {t = _ ∘⟨ _ ⟩ _} refl = _ , _ , refl , refl , refl

subst-∘ :
  t [ σ ] ≡ u ∘⟨ p ⟩ v →
  (∃ λ x → t ≡ var x) ⊎
  ∃₂ λ u′ v′ → t ≡ u′ ∘⟨ p ⟩ v′ × u′ [ σ ] ≡ u × v′ [ σ ] ≡ v
subst-∘ {t = var x} _ = inj₁ (_ , refl)
subst-∘ {t = _ ∘ _} refl = inj₂ (_ , _ , refl , refl , refl)


-- Inversion for prod.

wk-prod :
  wk ρ t ≡ prod s p u v →
  ∃₂ λ u′ v′ → t ≡ prod s p u′ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-prod {t = prod _ _ _ _} refl = _ , _ , refl , refl , refl

subst-prod :
  t [ σ ] ≡ prod s p u v →
  (∃ λ x → t ≡ var x) ⊎
  ∃₂ λ u′ v′ → t ≡ prod s p u′ v′ × u′ [ σ ] ≡ u × v′ [ σ ] ≡ v
subst-prod {t = var _} _ =
  inj₁ (_ , refl)
subst-prod {t = prod _ _ _ _} refl =
  inj₂ (_ , _ , refl , refl , refl)

-- Inversion for fst.

wk-fst :
  wk ρ t ≡ fst p u →
  ∃ λ u′ → t ≡ fst p u′ × wk ρ u′ ≡ u
wk-fst {t = fst _ _} refl = _ , refl , refl

subst-fst :
  t [ σ ] ≡ fst p u →
  (∃ λ x → t ≡ var x) ⊎
  ∃ λ u′ → t ≡ fst p u′ × u′ [ σ ] ≡ u
subst-fst {t = var _} _ = inj₁ (_ , refl)
subst-fst {t = fst _ _} refl = inj₂ (_ , refl , refl)

-- Inversion for snd.

wk-snd :
  wk ρ t ≡ snd p u →
  ∃ λ u′ → t ≡ snd p u′ × wk ρ u′ ≡ u
wk-snd {t = snd _ _} refl = _ , refl , refl

subst-snd :
  t [ σ ] ≡ snd p u →
  (∃ λ x → t ≡ var x) ⊎
  ∃ λ u′ → t ≡ snd p u′ × u′ [ σ ] ≡ u
subst-snd {t = var _} _ = inj₁ (_ , refl)
subst-snd {t = snd _ _} refl = inj₂ (_ , refl , refl)

-- Inversion for prodrec.

wk-prodrec :
  wk ρ t ≡ prodrec r p q A u v →
  ∃₃ λ A′ u′ v′ →
     t ≡ prodrec r p q A′ u′ v′ ×
     wk (lift ρ) A′ ≡ A × wk ρ u′ ≡ u × wk (lift (lift ρ)) v′ ≡ v
wk-prodrec {t = prodrec _ _ _ _ _ _} refl =
  _ , _ , _ , refl , refl , refl , refl

subst-prodrec :
  t [ σ ] ≡ prodrec r p q A u v →
  (∃ λ x → t ≡ var x) ⊎
  ∃₃ λ A′ u′ v′ →
     t ≡ prodrec r p q A′ u′ v′ ×
     A′ [ liftSubst σ ] ≡ A × u′ [ σ ] ≡ u × v′ [ liftSubstn σ 2 ] ≡ v
subst-prodrec {t = var _} _ =
  inj₁ (_ , refl)
subst-prodrec {t = prodrec _ _ _ _ _ _} refl =
  inj₂ (_ , _ , _ , refl , refl , refl , refl)

-- Inversion for Unit.

wk-Unit : wk ρ t ≡ Unit s → t ≡ Unit s
wk-Unit {t = Unit!} refl = refl

subst-Unit : t [ σ ] ≡ Unit s →
             (∃ λ x → t ≡ var x) ⊎ t ≡ Unit s
subst-Unit {t = var _} _ = inj₁ (_ , refl)
subst-Unit {t = Unit!} refl = inj₂ refl

-- Inversion for star.

wk-star : wk ρ t ≡ star s → t ≡ star s
wk-star {t = star!} refl = refl

subst-star : t [ σ ] ≡ star s →
            (∃ λ x → t ≡ var x) ⊎ t ≡ star s
subst-star {t = var _} _ = inj₁ (_ , refl)
subst-star {t = star!} refl = inj₂ refl

-- Inversion for unitrec.

wk-unitrec :
  wk ρ t ≡ unitrec p q A u v →
  ∃₃ λ A′ u′ v′ →
     t ≡ unitrec p q A′ u′ v′ ×
     wk (lift ρ) A′ ≡ A × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-unitrec {t = unitrec _ _ _ _ _} refl =
  _ , _ , _ , refl , refl , refl , refl

subst-unitrec :
  t [ σ ] ≡ unitrec p q A u v →
  (∃ λ x → t ≡ var x) ⊎
  ∃₃ λ A′ u′ v′ →
     t ≡ unitrec p q A′ u′ v′ ×
     A′ [ liftSubst σ ] ≡ A × u′ [ σ ] ≡ u × v′ [ σ ] ≡ v
subst-unitrec {t = var _} _ =
  inj₁ (_ , refl)
subst-unitrec {t = unitrec _ _ _ _ _} refl =
  inj₂ (_ , _ , _ , refl , refl , refl , refl)

-- Inversion for Empty.

wk-Empty : wk ρ t ≡ Empty → t ≡ Empty
wk-Empty {t = Empty} refl = refl

subst-Empty : t [ σ ] ≡ Empty →
              (∃ λ x → t ≡ var x) ⊎ t ≡ Empty
subst-Empty {t = var _} _ = inj₁ (_ , refl)
subst-Empty {t = Empty} refl = inj₂ refl

-- Inversion for emptyrec.

wk-emptyrec :
  wk ρ t ≡ emptyrec p A u →
  ∃₂ λ A′ u′ → t ≡ emptyrec p A′ u′ × wk ρ A′ ≡ A × wk ρ u′ ≡ u
wk-emptyrec {t = emptyrec _ _ _} refl =
  _ , _ , refl , refl , refl

subst-emptyrec :
  t [ σ ] ≡ emptyrec p A u →
  (∃ λ x → t ≡ var x) ⊎
  ∃₂ λ A′ u′ → t ≡ emptyrec p A′ u′ × A′ [ σ ] ≡ A × u′ [ σ ] ≡ u
subst-emptyrec {t = var _} _ =
  inj₁ (_ , refl)
subst-emptyrec {t = emptyrec _ _ _} refl =
  inj₂ (_ , _ , refl , refl , refl)

-- Inversion for ℕ.

wk-ℕ : wk ρ t ≡ ℕ → t ≡ ℕ
wk-ℕ {t = ℕ} refl = refl

subst-ℕ : t [ σ ] ≡ ℕ → (∃ λ x → t ≡ var x) ⊎ t ≡ ℕ
subst-ℕ {t = var _} _ = inj₁ (_ , refl)
subst-ℕ {t = ℕ} refl = inj₂ refl

-- Inversion for zero.

wk-zero : wk ρ t ≡ zero → t ≡ zero
wk-zero {t = zero} refl = refl

subst-zero : t [ σ ] ≡ zero → (∃ λ x → t ≡ var x) ⊎ t ≡ zero
subst-zero {t = var _} _ = inj₁ (_ , refl)
subst-zero {t = zero} refl = inj₂ refl

-- Inversion for suc.

wk-suc :
  wk ρ t ≡ suc u →
  ∃ λ u′ → t ≡ suc u′ × wk ρ u′ ≡ u
wk-suc {t = suc _} refl = _ , refl , refl

subst-suc :
  t [ σ ] ≡ suc u →
  (∃ λ x → t ≡ var x) ⊎ ∃ λ u′ → t ≡ suc u′ × u′ [ σ ] ≡ u
subst-suc {t = var _} _ = inj₁ (_ , refl)
subst-suc {t = suc _} refl = inj₂ (_ , refl , refl)

-- Inversion for natrec.

wk-natrec :
  wk ρ t ≡ natrec p q r A u v w →
  ∃₄ λ A′ u′ v′ w′ →
     t ≡ natrec p q r A′ u′ v′ w′ ×
     wk (lift ρ) A′ ≡ A ×
     wk ρ u′ ≡ u × wk (lift (lift ρ)) v′ ≡ v × wk ρ w′ ≡ w
wk-natrec {t = natrec _ _ _ _ _ _ _} refl =
  _ , _ , _ , _ , refl , refl , refl , refl , refl

subst-natrec :
  t [ σ ] ≡ natrec p q r A u v w →
  (∃ λ x → t ≡ var x) ⊎
  ∃₄ λ A′ u′ v′ w′ →
     t ≡ natrec p q r A′ u′ v′ w′ ×
     A′ [ liftSubst σ ] ≡ A ×
     u′ [ σ ] ≡ u × v′ [ liftSubstn σ 2 ] ≡ v × w′ [ σ ] ≡ w
subst-natrec {t = var _} _ =
  inj₁ (_ , refl)
subst-natrec {t = natrec _ _ _ _ _ _ _} refl =
  inj₂ (_ , _ , _ , _ , refl , refl , refl , refl , refl)

-- Inversion for Id.

wk-Id :
  wk ρ v ≡ Id A t u →
  ∃₃ λ A′ t′ u′ →
     v ≡ Id A′ t′ u′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk ρ u′ ≡ u
wk-Id {v = Id _ _ _} refl = _ , _ , _ , refl , refl , refl , refl

subst-Id :
  v [ σ ] ≡ Id A t u →
  (∃ λ x → v ≡ var x) ⊎
  ∃₃ λ A′ t′ u′ →
     v ≡ Id A′ t′ u′ ×
     A′ [ σ ] ≡ A × t′ [ σ ] ≡ t × u′ [ σ ] ≡ u
subst-Id {v = var _} _ =
  inj₁ (_ , refl)
subst-Id {v = Id _ _ _} refl =
  inj₂ (_ , _ , _ , refl , refl , refl , refl)

-- Inversion for rfl.

wk-rfl : wk ρ t ≡ rfl → t ≡ rfl
wk-rfl {t = rfl} refl = refl

subst-rfl : t [ σ ] ≡ rfl → (∃ λ x → t ≡ var x) ⊎ t ≡ rfl
subst-rfl {t = var x} _ = inj₁ (_ , refl)
subst-rfl {t = rfl} refl = inj₂ refl

-- Inversion for J.

wk-J :
  wk ρ w ≡ J p q A t B u t′ v →
  ∃₆ λ A′ t″ B′ u′ t‴ v′ →
     w ≡ J p q A′ t″ B′ u′ t‴ v′ ×
     wk ρ A′ ≡ A × wk ρ t″ ≡ t × wk (lift (lift ρ)) B′ ≡ B ×
     wk ρ u′ ≡ u × wk ρ t‴ ≡ t′ × wk ρ v′ ≡ v
wk-J {w = J _ _ _ _ _ _ _ _} refl =
  _ , _ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl , refl

subst-J :
  w [ σ ] ≡ J p q A t B u t′ v →
  (∃ λ x → w ≡ var x) ⊎
  ∃₃ λ A′ t″ B′ → ∃₃ λ u′ t‴ v′ →
     w ≡ J p q A′ t″ B′ u′ t‴ v′ ×
     A′ [ σ ] ≡ A × t″ [ σ ] ≡ t × B′ [ liftSubstn σ 2 ] ≡ B ×
     u′ [ σ ] ≡ u × t‴ [ σ ] ≡ t′ × v′ [ σ ] ≡ v
subst-J {w = var _} _ =
  inj₁ (_ , refl)
subst-J {w = J _ _ _ _ _ _ _ _} refl =
  inj₂ (_ , _ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl , refl)


-- Inversion for K.

wk-K :
  wk ρ w ≡ K p A t B u v →
  ∃₅ λ A′ t′ B′ u′ v′ →
     w ≡ K p A′ t′ B′ u′ v′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk (lift ρ) B′ ≡ B ×
     wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-K {w = K _ _ _ _ _ _} refl =
  _ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl

subst-K :
  w [ σ ] ≡ K p A t B u v →
  (∃ λ x → w ≡ var x) ⊎
  ∃₃ λ A′ t′ B′ → ∃₂ λ u′ v′ →
     w ≡ K p A′ t′ B′ u′ v′ ×
     A′ [ σ ] ≡ A × t′ [ σ ] ≡ t × B′ [ liftSubst σ ] ≡ B ×
     u′ [ σ ] ≡ u × v′ [ σ ] ≡ v
subst-K {w = var _} _ =
  inj₁ (_ , refl)
subst-K {w = K _ _ _ _ _ _} refl =
  inj₂ (_ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl)

-- Inversion for []-cong.

wk-[]-cong :
  wk ρ w ≡ []-cong s A t u v →
  ∃₄ λ A′ t′ u′ v′ →
     w ≡ []-cong s A′ t′ u′ v′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-[]-cong {w = []-cong _ _ _ _ _} refl =
  _ , _ , _ , _ , refl , refl , refl , refl , refl

subst-[]-cong :
  w [ σ ] ≡ []-cong s A t u v →
  (∃ λ x → w ≡ var x) ⊎
  ∃₄ λ A′ t′ u′ v′ →
     w ≡ []-cong s A′ t′ u′ v′ ×
     A′ [ σ ] ≡ A × t′ [ σ ] ≡ t × u′ [ σ ] ≡ u × v′ [ σ ] ≡ v
subst-[]-cong {w = var _} _ =
  inj₁ (_ , refl)
subst-[]-cong {w = []-cong _ _ _ _ _} refl =
  inj₂ (_ , _ , _ , _ , refl , refl , refl , refl , refl)
