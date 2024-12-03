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
wk-var {t = var _}                 refl = _ , refl , refl
wk-var {t = U _}                   ()
wk-var {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-var {t = lam _ _}               ()
wk-var {t = _ ∘⟨ _ ⟩ _}            ()
wk-var {t = prod _ _ _ _}          ()
wk-var {t = fst _ _}               ()
wk-var {t = snd _ _}               ()
wk-var {t = prodrec _ _ _ _ _ _}   ()
wk-var {t = Empty}                 ()
wk-var {t = emptyrec _ _ _}        ()
wk-var {t = Unit _ _}              ()
wk-var {t = star _ _}              ()
wk-var {t = unitrec _ _ _ _ _ _}   ()
wk-var {t = ℕ}                     ()
wk-var {t = zero}                  ()
wk-var {t = suc _}                 ()
wk-var {t = natrec _ _ _ _ _ _ _}  ()
wk-var {t = Id _ _ _}              ()
wk-var {t = rfl}                   ()
wk-var {t = J _ _ _ _ _ _ _ _}     ()
wk-var {t = K _ _ _ _ _ _}         ()
wk-var {t = []-cong _ _ _ _ _}     ()

subst-var :
  t [ σ ] ≡ var x →
  ∃ λ x′ → t ≡ var x′ ×  σ x′ ≡ var x
subst-var {t = var _}                 eq = _ , refl , eq
subst-var {t = U _}                   ()
subst-var {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-var {t = lam _ _}               ()
subst-var {t = _ ∘⟨ _ ⟩ _}            ()
subst-var {t = prod _ _ _ _}          ()
subst-var {t = fst _ _}               ()
subst-var {t = snd _ _}               ()
subst-var {t = prodrec _ _ _ _ _ _}   ()
subst-var {t = Empty}                 ()
subst-var {t = emptyrec _ _ _}        ()
subst-var {t = Unit _ _}              ()
subst-var {t = star _ _}              ()
subst-var {t = unitrec _ _ _ _ _ _}   ()
subst-var {t = ℕ}                     ()
subst-var {t = zero}                  ()
subst-var {t = suc _}                 ()
subst-var {t = natrec _ _ _ _ _ _ _}  ()
subst-var {t = Id _ _ _}              ()
subst-var {t = rfl}                   ()
subst-var {t = J _ _ _ _ _ _ _ _}     ()
subst-var {t = K _ _ _ _ _ _}         ()
subst-var {t = []-cong _ _ _ _ _}     ()

-- Inversion for U.

wk-U : wk ρ t ≡ U l → t ≡ U l
wk-U {t = U l}                   refl = refl
wk-U {t = var _}                 ()
wk-U {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-U {t = lam _ _}               ()
wk-U {t = _ ∘⟨ _ ⟩ _}            ()
wk-U {t = prod _ _ _ _}          ()
wk-U {t = fst _ _}               ()
wk-U {t = snd _ _}               ()
wk-U {t = prodrec _ _ _ _ _ _}   ()
wk-U {t = Empty}                 ()
wk-U {t = emptyrec _ _ _}        ()
wk-U {t = Unit _ _}              ()
wk-U {t = star _ _}              ()
wk-U {t = unitrec _ _ _ _ _ _}   ()
wk-U {t = ℕ}                     ()
wk-U {t = zero}                  ()
wk-U {t = suc _}                 ()
wk-U {t = natrec _ _ _ _ _ _ _}  ()
wk-U {t = Id _ _ _}              ()
wk-U {t = rfl}                   ()
wk-U {t = J _ _ _ _ _ _ _ _}     ()
wk-U {t = K _ _ _ _ _ _}         ()
wk-U {t = []-cong _ _ _ _ _}     ()

subst-U : t [ σ ] ≡ U l → (∃ λ x → t ≡ var x) ⊎ t ≡ U l
subst-U {t = var _}                 _    = inj₁ (_ , refl)
subst-U {t = U _}                   refl = inj₂ refl
subst-U {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-U {t = lam _ _}               ()
subst-U {t = _ ∘⟨ _ ⟩ _}            ()
subst-U {t = prod _ _ _ _}          ()
subst-U {t = fst _ _}               ()
subst-U {t = snd _ _}               ()
subst-U {t = prodrec _ _ _ _ _ _}   ()
subst-U {t = Empty}                 ()
subst-U {t = emptyrec _ _ _}        ()
subst-U {t = Unit _ _}              ()
subst-U {t = star _ _}              ()
subst-U {t = unitrec _ _ _ _ _ _}   ()
subst-U {t = ℕ}                     ()
subst-U {t = zero}                  ()
subst-U {t = suc _}                 ()
subst-U {t = natrec _ _ _ _ _ _ _}  ()
subst-U {t = Id _ _ _}              ()
subst-U {t = rfl}                   ()
subst-U {t = J _ _ _ _ _ _ _ _}     ()
subst-U {t = K _ _ _ _ _ _}         ()
subst-U {t = []-cong _ _ _ _ _}     ()

-- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

wk-ΠΣ :
  wk ρ t ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  ∃₂ λ A′ B′ →
     t ≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     wk ρ A′ ≡ A × wk (lift ρ) B′ ≡ B
wk-ΠΣ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} refl =
  _ , _ , refl , refl , refl
wk-ΠΣ {t = var _}                ()
wk-ΠΣ {t = U _}                  ()
wk-ΠΣ {t = lam _ _}              ()
wk-ΠΣ {t = _ ∘⟨ _ ⟩ _}           ()
wk-ΠΣ {t = prod _ _ _ _}         ()
wk-ΠΣ {t = fst _ _}              ()
wk-ΠΣ {t = snd _ _}              ()
wk-ΠΣ {t = prodrec _ _ _ _ _ _}  ()
wk-ΠΣ {t = Empty}                ()
wk-ΠΣ {t = emptyrec _ _ _}       ()
wk-ΠΣ {t = Unit _ _}             ()
wk-ΠΣ {t = star _ _}             ()
wk-ΠΣ {t = unitrec _ _ _ _ _ _}  ()
wk-ΠΣ {t = ℕ}                    ()
wk-ΠΣ {t = zero}                 ()
wk-ΠΣ {t = suc _}                ()
wk-ΠΣ {t = natrec _ _ _ _ _ _ _} ()
wk-ΠΣ {t = Id _ _ _}             ()
wk-ΠΣ {t = rfl}                  ()
wk-ΠΣ {t = J _ _ _ _ _ _ _ _}    ()
wk-ΠΣ {t = K _ _ _ _ _ _}        ()
wk-ΠΣ {t = []-cong _ _ _ _ _}    ()

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
subst-ΠΣ {t = U _}                  ()
subst-ΠΣ {t = lam _ _}              ()
subst-ΠΣ {t = _ ∘⟨ _ ⟩ _}           ()
subst-ΠΣ {t = prod _ _ _ _}         ()
subst-ΠΣ {t = fst _ _}              ()
subst-ΠΣ {t = snd _ _}              ()
subst-ΠΣ {t = prodrec _ _ _ _ _ _}  ()
subst-ΠΣ {t = Empty}                ()
subst-ΠΣ {t = emptyrec _ _ _}       ()
subst-ΠΣ {t = Unit _ _}             ()
subst-ΠΣ {t = star _ _}             ()
subst-ΠΣ {t = unitrec _ _ _ _ _ _}  ()
subst-ΠΣ {t = ℕ}                    ()
subst-ΠΣ {t = zero}                 ()
subst-ΠΣ {t = suc _}                ()
subst-ΠΣ {t = natrec _ _ _ _ _ _ _} ()
subst-ΠΣ {t = Id _ _ _}             ()
subst-ΠΣ {t = rfl}                  ()
subst-ΠΣ {t = J _ _ _ _ _ _ _ _}    ()
subst-ΠΣ {t = K _ _ _ _ _ _}        ()
subst-ΠΣ {t = []-cong _ _ _ _ _}    ()

-- Inversion for lam.

wk-lam :
  wk ρ t ≡ lam p u →
  ∃ λ u′ → t ≡ lam p u′ × wk (lift ρ) u′ ≡ u
wk-lam {t = lam _ _}               refl = _ , refl , refl
wk-lam {t = var _}                 ()
wk-lam {t = U _}                   ()
wk-lam {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-lam {t = _ ∘⟨ _ ⟩ _}            ()
wk-lam {t = prod _ _ _ _}          ()
wk-lam {t = fst _ _}               ()
wk-lam {t = snd _ _}               ()
wk-lam {t = prodrec _ _ _ _ _ _}   ()
wk-lam {t = Empty}                 ()
wk-lam {t = emptyrec _ _ _}        ()
wk-lam {t = Unit _ _}              ()
wk-lam {t = star _ _}              ()
wk-lam {t = unitrec _ _ _ _ _ _}   ()
wk-lam {t = ℕ}                     ()
wk-lam {t = zero}                  ()
wk-lam {t = suc _}                 ()
wk-lam {t = natrec _ _ _ _ _ _ _}  ()
wk-lam {t = Id _ _ _}              ()
wk-lam {t = rfl}                   ()
wk-lam {t = J _ _ _ _ _ _ _ _}     ()
wk-lam {t = K _ _ _ _ _ _}         ()
wk-lam {t = []-cong _ _ _ _ _}     ()

subst-lam :
  t [ σ ] ≡ lam p u →
  (∃ λ x → t ≡ var x) ⊎
  ∃ λ u′ → t ≡ lam p u′ × u′ [ liftSubst σ ] ≡ u
subst-lam {t = var x}                 _    = inj₁ (_ , refl)
subst-lam {t = lam _ _}               refl = inj₂ (_ , refl , refl)
subst-lam {t = U _}                   ()
subst-lam {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-lam {t = _ ∘⟨ _ ⟩ _}            ()
subst-lam {t = prod _ _ _ _}          ()
subst-lam {t = fst _ _}               ()
subst-lam {t = snd _ _}               ()
subst-lam {t = prodrec _ _ _ _ _ _}   ()
subst-lam {t = Empty}                 ()
subst-lam {t = emptyrec _ _ _}        ()
subst-lam {t = Unit _ _}              ()
subst-lam {t = star _ _}              ()
subst-lam {t = unitrec _ _ _ _ _ _}   ()
subst-lam {t = ℕ}                     ()
subst-lam {t = zero}                  ()
subst-lam {t = suc _}                 ()
subst-lam {t = natrec _ _ _ _ _ _ _}  ()
subst-lam {t = Id _ _ _}              ()
subst-lam {t = rfl}                   ()
subst-lam {t = J _ _ _ _ _ _ _ _}     ()
subst-lam {t = K _ _ _ _ _ _}         ()
subst-lam {t = []-cong _ _ _ _ _}     ()

-- Inversion for _∘⟨_⟩_.

wk-∘ :
  wk ρ t ≡ u ∘⟨ p ⟩ v →
  ∃₂ λ u′ v′ → t ≡ u′ ∘⟨ p ⟩ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-∘ {t = _ ∘⟨ _ ⟩ _}            refl = _ , _ , refl , refl , refl
wk-∘ {t = var _}                 ()
wk-∘ {t = U _}                   ()
wk-∘ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-∘ {t = lam _ _}               ()
wk-∘ {t = prod _ _ _ _}          ()
wk-∘ {t = fst _ _}               ()
wk-∘ {t = snd _ _}               ()
wk-∘ {t = prodrec _ _ _ _ _ _}   ()
wk-∘ {t = Empty}                 ()
wk-∘ {t = emptyrec _ _ _}        ()
wk-∘ {t = Unit _ _}              ()
wk-∘ {t = star _ _}              ()
wk-∘ {t = unitrec _ _ _ _ _ _}   ()
wk-∘ {t = ℕ}                     ()
wk-∘ {t = zero}                  ()
wk-∘ {t = suc _}                 ()
wk-∘ {t = natrec _ _ _ _ _ _ _}  ()
wk-∘ {t = Id _ _ _}              ()
wk-∘ {t = rfl}                   ()
wk-∘ {t = J _ _ _ _ _ _ _ _}     ()
wk-∘ {t = K _ _ _ _ _ _}         ()
wk-∘ {t = []-cong _ _ _ _ _}     ()

subst-∘ :
  t [ σ ] ≡ u ∘⟨ p ⟩ v →
  (∃ λ x → t ≡ var x) ⊎
  ∃₂ λ u′ v′ → t ≡ u′ ∘⟨ p ⟩ v′ × u′ [ σ ] ≡ u × v′ [ σ ] ≡ v
subst-∘ {t = var x} _    = inj₁ (_ , refl)
subst-∘ {t = _ ∘ _} refl =
  inj₂ (_ , _ , refl , refl , refl)
subst-∘ {t = U _}                   ()
subst-∘ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-∘ {t = lam _ _}               ()
subst-∘ {t = prod _ _ _ _}          ()
subst-∘ {t = fst _ _}               ()
subst-∘ {t = snd _ _}               ()
subst-∘ {t = prodrec _ _ _ _ _ _}   ()
subst-∘ {t = Empty}                 ()
subst-∘ {t = emptyrec _ _ _}        ()
subst-∘ {t = Unit _ _}              ()
subst-∘ {t = star _ _}              ()
subst-∘ {t = unitrec _ _ _ _ _ _}   ()
subst-∘ {t = ℕ}                     ()
subst-∘ {t = zero}                  ()
subst-∘ {t = suc _}                 ()
subst-∘ {t = natrec _ _ _ _ _ _ _}  ()
subst-∘ {t = Id _ _ _}              ()
subst-∘ {t = rfl}                   ()
subst-∘ {t = J _ _ _ _ _ _ _ _}     ()
subst-∘ {t = K _ _ _ _ _ _}         ()
subst-∘ {t = []-cong _ _ _ _ _}     ()

-- Inversion for prod.

wk-prod :
  wk ρ t ≡ prod s p u v →
  ∃₂ λ u′ v′ → t ≡ prod s p u′ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-prod {t = prod _ _ _ _}          refl = _ , _ , refl , refl , refl
wk-prod {t = var _}                 ()
wk-prod {t = U _}                   ()
wk-prod {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-prod {t = lam _ _}               ()
wk-prod {t = _ ∘⟨ _ ⟩ _}            ()
wk-prod {t = fst _ _}               ()
wk-prod {t = snd _ _}               ()
wk-prod {t = prodrec _ _ _ _ _ _}   ()
wk-prod {t = Empty}                 ()
wk-prod {t = emptyrec _ _ _}        ()
wk-prod {t = Unit _ _}              ()
wk-prod {t = star _ _}              ()
wk-prod {t = unitrec _ _ _ _ _ _}   ()
wk-prod {t = ℕ}                     ()
wk-prod {t = zero}                  ()
wk-prod {t = suc _}                 ()
wk-prod {t = natrec _ _ _ _ _ _ _}  ()
wk-prod {t = Id _ _ _}              ()
wk-prod {t = rfl}                   ()
wk-prod {t = J _ _ _ _ _ _ _ _}     ()
wk-prod {t = K _ _ _ _ _ _}         ()
wk-prod {t = []-cong _ _ _ _ _}     ()

subst-prod :
  t [ σ ] ≡ prod s p u v →
  (∃ λ x → t ≡ var x) ⊎
  ∃₂ λ u′ v′ → t ≡ prod s p u′ v′ × u′ [ σ ] ≡ u × v′ [ σ ] ≡ v
subst-prod {t = var _} _ =
  inj₁ (_ , refl)
subst-prod {t = prod _ _ _ _} refl =
  inj₂ (_ , _ , refl , refl , refl)
subst-prod {t = U _}                   ()
subst-prod {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-prod {t = lam _ _}               ()
subst-prod {t = _ ∘⟨ _ ⟩ _}            ()
subst-prod {t = fst _ _}               ()
subst-prod {t = snd _ _}               ()
subst-prod {t = prodrec _ _ _ _ _ _}   ()
subst-prod {t = Empty}                 ()
subst-prod {t = emptyrec _ _ _}        ()
subst-prod {t = Unit _ _}              ()
subst-prod {t = star _ _}              ()
subst-prod {t = unitrec _ _ _ _ _ _}   ()
subst-prod {t = ℕ}                     ()
subst-prod {t = zero}                  ()
subst-prod {t = suc _}                 ()
subst-prod {t = natrec _ _ _ _ _ _ _}  ()
subst-prod {t = Id _ _ _}              ()
subst-prod {t = rfl}                   ()
subst-prod {t = J _ _ _ _ _ _ _ _}     ()
subst-prod {t = K _ _ _ _ _ _}         ()
subst-prod {t = []-cong _ _ _ _ _}     ()

-- Inversion for fst.

wk-fst :
  wk ρ t ≡ fst p u →
  ∃ λ u′ → t ≡ fst p u′ × wk ρ u′ ≡ u
wk-fst {t = fst _ _}               refl = _ , refl , refl
wk-fst {t = var _}                 ()
wk-fst {t = U _}                   ()
wk-fst {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-fst {t = lam _ _}               ()
wk-fst {t = _ ∘⟨ _ ⟩ _}            ()
wk-fst {t = prod _ _ _ _}          ()
wk-fst {t = snd _ _}               ()
wk-fst {t = prodrec _ _ _ _ _ _}   ()
wk-fst {t = Empty}                 ()
wk-fst {t = emptyrec _ _ _}        ()
wk-fst {t = Unit _ _}              ()
wk-fst {t = star _ _}              ()
wk-fst {t = unitrec _ _ _ _ _ _}   ()
wk-fst {t = ℕ}                     ()
wk-fst {t = zero}                  ()
wk-fst {t = suc _}                 ()
wk-fst {t = natrec _ _ _ _ _ _ _}  ()
wk-fst {t = Id _ _ _}              ()
wk-fst {t = rfl}                   ()
wk-fst {t = J _ _ _ _ _ _ _ _}     ()
wk-fst {t = K _ _ _ _ _ _}         ()
wk-fst {t = []-cong _ _ _ _ _}     ()

subst-fst :
  t [ σ ] ≡ fst p u →
  (∃ λ x → t ≡ var x) ⊎
  ∃ λ u′ → t ≡ fst p u′ × u′ [ σ ] ≡ u
subst-fst {t = var _}                 _    = inj₁ (_ , refl)
subst-fst {t = fst _ _}               refl = inj₂ (_ , refl , refl)
subst-fst {t = U _}                   ()
subst-fst {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-fst {t = lam _ _}               ()
subst-fst {t = _ ∘⟨ _ ⟩ _}            ()
subst-fst {t = prod _ _ _ _}          ()
subst-fst {t = snd _ _}               ()
subst-fst {t = prodrec _ _ _ _ _ _}   ()
subst-fst {t = Empty}                 ()
subst-fst {t = emptyrec _ _ _}        ()
subst-fst {t = Unit _ _}              ()
subst-fst {t = star _ _}              ()
subst-fst {t = unitrec _ _ _ _ _ _}   ()
subst-fst {t = ℕ}                     ()
subst-fst {t = zero}                  ()
subst-fst {t = suc _}                 ()
subst-fst {t = natrec _ _ _ _ _ _ _}  ()
subst-fst {t = Id _ _ _}              ()
subst-fst {t = rfl}                   ()
subst-fst {t = J _ _ _ _ _ _ _ _}     ()
subst-fst {t = K _ _ _ _ _ _}         ()
subst-fst {t = []-cong _ _ _ _ _}     ()

-- Inversion for snd.

wk-snd :
  wk ρ t ≡ snd p u →
  ∃ λ u′ → t ≡ snd p u′ × wk ρ u′ ≡ u
wk-snd {t = snd _ _}               refl = _ , refl , refl
wk-snd {t = var _}                 ()
wk-snd {t = U _}                   ()
wk-snd {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-snd {t = lam _ _}               ()
wk-snd {t = _ ∘⟨ _ ⟩ _}            ()
wk-snd {t = prod _ _ _ _}          ()
wk-snd {t = fst _ _}               ()
wk-snd {t = prodrec _ _ _ _ _ _}   ()
wk-snd {t = Empty}                 ()
wk-snd {t = emptyrec _ _ _}        ()
wk-snd {t = Unit _ _}              ()
wk-snd {t = star _ _}              ()
wk-snd {t = unitrec _ _ _ _ _ _}   ()
wk-snd {t = ℕ}                     ()
wk-snd {t = zero}                  ()
wk-snd {t = suc _}                 ()
wk-snd {t = natrec _ _ _ _ _ _ _}  ()
wk-snd {t = Id _ _ _}              ()
wk-snd {t = rfl}                   ()
wk-snd {t = J _ _ _ _ _ _ _ _}     ()
wk-snd {t = K _ _ _ _ _ _}         ()
wk-snd {t = []-cong _ _ _ _ _}     ()

subst-snd :
  t [ σ ] ≡ snd p u →
  (∃ λ x → t ≡ var x) ⊎
  ∃ λ u′ → t ≡ snd p u′ × u′ [ σ ] ≡ u
subst-snd {t = var _}                 _    = inj₁ (_ , refl)
subst-snd {t = snd _ _}               refl = inj₂ (_ , refl , refl)
subst-snd {t = U _}                   ()
subst-snd {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-snd {t = lam _ _}               ()
subst-snd {t = _ ∘⟨ _ ⟩ _}            ()
subst-snd {t = prod _ _ _ _}          ()
subst-snd {t = fst _ _}               ()
subst-snd {t = prodrec _ _ _ _ _ _}   ()
subst-snd {t = Empty}                 ()
subst-snd {t = emptyrec _ _ _}        ()
subst-snd {t = Unit _ _}              ()
subst-snd {t = star _ _}              ()
subst-snd {t = unitrec _ _ _ _ _ _}   ()
subst-snd {t = ℕ}                     ()
subst-snd {t = zero}                  ()
subst-snd {t = suc _}                 ()
subst-snd {t = natrec _ _ _ _ _ _ _}  ()
subst-snd {t = Id _ _ _}              ()
subst-snd {t = rfl}                   ()
subst-snd {t = J _ _ _ _ _ _ _ _}     ()
subst-snd {t = K _ _ _ _ _ _}         ()
subst-snd {t = []-cong _ _ _ _ _}     ()

-- Inversion for prodrec.

wk-prodrec :
  wk ρ t ≡ prodrec r p q A u v →
  ∃₃ λ A′ u′ v′ →
     t ≡ prodrec r p q A′ u′ v′ ×
     wk (lift ρ) A′ ≡ A × wk ρ u′ ≡ u × wk (lift (lift ρ)) v′ ≡ v
wk-prodrec {t = prodrec _ _ _ _ _ _} refl =
  _ , _ , _ , refl , refl , refl , refl
wk-prodrec {t = var _}                 ()
wk-prodrec {t = U _}                   ()
wk-prodrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-prodrec {t = lam _ _}               ()
wk-prodrec {t = _ ∘⟨ _ ⟩ _}            ()
wk-prodrec {t = prod _ _ _ _}          ()
wk-prodrec {t = fst _ _}               ()
wk-prodrec {t = snd _ _}               ()
wk-prodrec {t = Empty}                 ()
wk-prodrec {t = emptyrec _ _ _}        ()
wk-prodrec {t = Unit _ _}              ()
wk-prodrec {t = star _ _}              ()
wk-prodrec {t = unitrec _ _ _ _ _ _}   ()
wk-prodrec {t = ℕ}                     ()
wk-prodrec {t = zero}                  ()
wk-prodrec {t = suc _}                 ()
wk-prodrec {t = natrec _ _ _ _ _ _ _}  ()
wk-prodrec {t = Id _ _ _}              ()
wk-prodrec {t = rfl}                   ()
wk-prodrec {t = J _ _ _ _ _ _ _ _}     ()
wk-prodrec {t = K _ _ _ _ _ _}         ()
wk-prodrec {t = []-cong _ _ _ _ _}     ()

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
subst-prodrec {t = U _}                   ()
subst-prodrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-prodrec {t = lam _ _}               ()
subst-prodrec {t = _ ∘⟨ _ ⟩ _}            ()
subst-prodrec {t = prod _ _ _ _}          ()
subst-prodrec {t = fst _ _}               ()
subst-prodrec {t = snd _ _}               ()
subst-prodrec {t = Empty}                 ()
subst-prodrec {t = emptyrec _ _ _}        ()
subst-prodrec {t = Unit _ _}              ()
subst-prodrec {t = star _ _}              ()
subst-prodrec {t = unitrec _ _ _ _ _ _}   ()
subst-prodrec {t = ℕ}                     ()
subst-prodrec {t = zero}                  ()
subst-prodrec {t = suc _}                 ()
subst-prodrec {t = natrec _ _ _ _ _ _ _}  ()
subst-prodrec {t = Id _ _ _}              ()
subst-prodrec {t = rfl}                   ()
subst-prodrec {t = J _ _ _ _ _ _ _ _}     ()
subst-prodrec {t = K _ _ _ _ _ _}         ()
subst-prodrec {t = []-cong _ _ _ _ _}     ()

-- Inversion for Unit.

wk-Unit : wk ρ t ≡ Unit s l → t ≡ Unit s l
wk-Unit {t = Unit!}                 refl = refl
wk-Unit {t = var _}                 ()
wk-Unit {t = U _}                   ()
wk-Unit {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-Unit {t = lam _ _}               ()
wk-Unit {t = _ ∘⟨ _ ⟩ _}            ()
wk-Unit {t = prod _ _ _ _}          ()
wk-Unit {t = fst _ _}               ()
wk-Unit {t = snd _ _}               ()
wk-Unit {t = prodrec _ _ _ _ _ _}   ()
wk-Unit {t = Empty}                 ()
wk-Unit {t = emptyrec _ _ _}        ()
wk-Unit {t = star _ _}              ()
wk-Unit {t = unitrec _ _ _ _ _ _}   ()
wk-Unit {t = ℕ}                     ()
wk-Unit {t = zero}                  ()
wk-Unit {t = suc _}                 ()
wk-Unit {t = natrec _ _ _ _ _ _ _}  ()
wk-Unit {t = Id _ _ _}              ()
wk-Unit {t = rfl}                   ()
wk-Unit {t = J _ _ _ _ _ _ _ _}     ()
wk-Unit {t = K _ _ _ _ _ _}         ()
wk-Unit {t = []-cong _ _ _ _ _}     ()

subst-Unit : t [ σ ] ≡ Unit s l →
             (∃ λ x → t ≡ var x) ⊎ t ≡ Unit s l
subst-Unit {t = var _}                 _    = inj₁ (_ , refl)
subst-Unit {t = Unit!}                 refl = inj₂ refl
subst-Unit {t = U _}                   ()
subst-Unit {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-Unit {t = lam _ _}               ()
subst-Unit {t = _ ∘⟨ _ ⟩ _}            ()
subst-Unit {t = prod _ _ _ _}          ()
subst-Unit {t = fst _ _}               ()
subst-Unit {t = snd _ _}               ()
subst-Unit {t = prodrec _ _ _ _ _ _}   ()
subst-Unit {t = Empty}                 ()
subst-Unit {t = emptyrec _ _ _}        ()
subst-Unit {t = star _ _}              ()
subst-Unit {t = unitrec _ _ _ _ _ _}   ()
subst-Unit {t = ℕ}                     ()
subst-Unit {t = zero}                  ()
subst-Unit {t = suc _}                 ()
subst-Unit {t = natrec _ _ _ _ _ _ _}  ()
subst-Unit {t = Id _ _ _}              ()
subst-Unit {t = rfl}                   ()
subst-Unit {t = J _ _ _ _ _ _ _ _}     ()
subst-Unit {t = K _ _ _ _ _ _}         ()
subst-Unit {t = []-cong _ _ _ _ _}     ()

-- Inversion for star.

wk-star : wk ρ t ≡ star s l → t ≡ star s l
wk-star {t = star!}                 refl = refl
wk-star {t = var _}                 ()
wk-star {t = U _}                   ()
wk-star {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-star {t = lam _ _}               ()
wk-star {t = _ ∘⟨ _ ⟩ _}            ()
wk-star {t = prod _ _ _ _}          ()
wk-star {t = fst _ _}               ()
wk-star {t = snd _ _}               ()
wk-star {t = prodrec _ _ _ _ _ _}   ()
wk-star {t = Empty}                 ()
wk-star {t = emptyrec _ _ _}        ()
wk-star {t = Unit _ _}              ()
wk-star {t = unitrec _ _ _ _ _ _}   ()
wk-star {t = ℕ}                     ()
wk-star {t = zero}                  ()
wk-star {t = suc _}                 ()
wk-star {t = natrec _ _ _ _ _ _ _}  ()
wk-star {t = Id _ _ _}              ()
wk-star {t = rfl}                   ()
wk-star {t = J _ _ _ _ _ _ _ _}     ()
wk-star {t = K _ _ _ _ _ _}         ()
wk-star {t = []-cong _ _ _ _ _}     ()

subst-star : t [ σ ] ≡ star s l →
            (∃ λ x → t ≡ var x) ⊎ t ≡ star s l
subst-star {t = var _}                 _    = inj₁ (_ , refl)
subst-star {t = star!}                 refl = inj₂ refl
subst-star {t = U _}                   ()
subst-star {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-star {t = lam _ _}               ()
subst-star {t = _ ∘⟨ _ ⟩ _}            ()
subst-star {t = prod _ _ _ _}          ()
subst-star {t = fst _ _}               ()
subst-star {t = snd _ _}               ()
subst-star {t = prodrec _ _ _ _ _ _}   ()
subst-star {t = Empty}                 ()
subst-star {t = emptyrec _ _ _}        ()
subst-star {t = Unit _ _}              ()
subst-star {t = unitrec _ _ _ _ _ _}   ()
subst-star {t = ℕ}                     ()
subst-star {t = zero}                  ()
subst-star {t = suc _}                 ()
subst-star {t = natrec _ _ _ _ _ _ _}  ()
subst-star {t = Id _ _ _}              ()
subst-star {t = rfl}                   ()
subst-star {t = J _ _ _ _ _ _ _ _}     ()
subst-star {t = K _ _ _ _ _ _}         ()
subst-star {t = []-cong _ _ _ _ _}     ()

-- Inversion for unitrec.

wk-unitrec :
  wk ρ t ≡ unitrec l p q A u v →
  ∃₃ λ A′ u′ v′ →
     t ≡ unitrec l p q A′ u′ v′ ×
     wk (lift ρ) A′ ≡ A × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-unitrec {t = unitrec _ _ _ _ _ _} refl =
  _ , _ , _ , refl , refl , refl , refl
wk-unitrec {t = var _}                 ()
wk-unitrec {t = U _}                   ()
wk-unitrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-unitrec {t = lam _ _}               ()
wk-unitrec {t = _ ∘⟨ _ ⟩ _}            ()
wk-unitrec {t = prod _ _ _ _}          ()
wk-unitrec {t = fst _ _}               ()
wk-unitrec {t = snd _ _}               ()
wk-unitrec {t = prodrec _ _ _ _ _ _}   ()
wk-unitrec {t = Empty}                 ()
wk-unitrec {t = emptyrec _ _ _}        ()
wk-unitrec {t = Unit _ _}              ()
wk-unitrec {t = star _ _}              ()
wk-unitrec {t = ℕ}                     ()
wk-unitrec {t = zero}                  ()
wk-unitrec {t = suc _}                 ()
wk-unitrec {t = natrec _ _ _ _ _ _ _}  ()
wk-unitrec {t = Id _ _ _}              ()
wk-unitrec {t = rfl}                   ()
wk-unitrec {t = J _ _ _ _ _ _ _ _}     ()
wk-unitrec {t = K _ _ _ _ _ _}         ()
wk-unitrec {t = []-cong _ _ _ _ _}     ()

subst-unitrec :
  t [ σ ] ≡ unitrec l p q A u v →
  (∃ λ x → t ≡ var x) ⊎
  ∃₃ λ A′ u′ v′ →
     t ≡ unitrec l p q A′ u′ v′ ×
     A′ [ liftSubst σ ] ≡ A × u′ [ σ ] ≡ u × v′ [ σ ] ≡ v
subst-unitrec {t = var _} _ =
  inj₁ (_ , refl)
subst-unitrec {t = unitrec _ _ _ _ _ _} refl =
  inj₂ (_ , _ , _ , refl , refl , refl , refl)
subst-unitrec {t = U _}                   ()
subst-unitrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-unitrec {t = lam _ _}               ()
subst-unitrec {t = _ ∘⟨ _ ⟩ _}            ()
subst-unitrec {t = prod _ _ _ _}          ()
subst-unitrec {t = fst _ _}               ()
subst-unitrec {t = snd _ _}               ()
subst-unitrec {t = prodrec _ _ _ _ _ _}   ()
subst-unitrec {t = Empty}                 ()
subst-unitrec {t = emptyrec _ _ _}        ()
subst-unitrec {t = Unit _ _}              ()
subst-unitrec {t = star _ _}              ()
subst-unitrec {t = ℕ}                     ()
subst-unitrec {t = zero}                  ()
subst-unitrec {t = suc _}                 ()
subst-unitrec {t = natrec _ _ _ _ _ _ _}  ()
subst-unitrec {t = Id _ _ _}              ()
subst-unitrec {t = rfl}                   ()
subst-unitrec {t = J _ _ _ _ _ _ _ _}     ()
subst-unitrec {t = K _ _ _ _ _ _}         ()
subst-unitrec {t = []-cong _ _ _ _ _}     ()

-- Inversion for Empty.

wk-Empty : wk ρ t ≡ Empty → t ≡ Empty
wk-Empty {t = Empty}                 refl = refl
wk-Empty {t = var _}                 ()
wk-Empty {t = U _}                   ()
wk-Empty {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-Empty {t = lam _ _}               ()
wk-Empty {t = _ ∘⟨ _ ⟩ _}            ()
wk-Empty {t = prod _ _ _ _}          ()
wk-Empty {t = fst _ _}               ()
wk-Empty {t = snd _ _}               ()
wk-Empty {t = prodrec _ _ _ _ _ _}   ()
wk-Empty {t = emptyrec _ _ _}        ()
wk-Empty {t = Unit _ _}              ()
wk-Empty {t = star _ _}              ()
wk-Empty {t = unitrec _ _ _ _ _ _}   ()
wk-Empty {t = ℕ}                     ()
wk-Empty {t = zero}                  ()
wk-Empty {t = suc _}                 ()
wk-Empty {t = natrec _ _ _ _ _ _ _}  ()
wk-Empty {t = Id _ _ _}              ()
wk-Empty {t = rfl}                   ()
wk-Empty {t = J _ _ _ _ _ _ _ _}     ()
wk-Empty {t = K _ _ _ _ _ _}         ()
wk-Empty {t = []-cong _ _ _ _ _}     ()

subst-Empty : t [ σ ] ≡ Empty →
              (∃ λ x → t ≡ var x) ⊎ t ≡ Empty
subst-Empty {t = var _}                 _    = inj₁ (_ , refl)
subst-Empty {t = Empty}                 refl = inj₂ refl
subst-Empty {t = U _}                   ()
subst-Empty {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-Empty {t = lam _ _}               ()
subst-Empty {t = _ ∘⟨ _ ⟩ _}            ()
subst-Empty {t = prod _ _ _ _}          ()
subst-Empty {t = fst _ _}               ()
subst-Empty {t = snd _ _}               ()
subst-Empty {t = prodrec _ _ _ _ _ _}   ()
subst-Empty {t = emptyrec _ _ _}        ()
subst-Empty {t = Unit _ _}              ()
subst-Empty {t = star _ _}              ()
subst-Empty {t = unitrec _ _ _ _ _ _}   ()
subst-Empty {t = ℕ}                     ()
subst-Empty {t = zero}                  ()
subst-Empty {t = suc _}                 ()
subst-Empty {t = natrec _ _ _ _ _ _ _}  ()
subst-Empty {t = Id _ _ _}              ()
subst-Empty {t = rfl}                   ()
subst-Empty {t = J _ _ _ _ _ _ _ _}     ()
subst-Empty {t = K _ _ _ _ _ _}         ()
subst-Empty {t = []-cong _ _ _ _ _}     ()

-- Inversion for emptyrec.

wk-emptyrec :
  wk ρ t ≡ emptyrec p A u →
  ∃₂ λ A′ u′ → t ≡ emptyrec p A′ u′ × wk ρ A′ ≡ A × wk ρ u′ ≡ u
wk-emptyrec {t = emptyrec _ _ _} refl =
  _ , _ , refl , refl , refl
wk-emptyrec {t = var _}                 ()
wk-emptyrec {t = U _}                   ()
wk-emptyrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-emptyrec {t = lam _ _}               ()
wk-emptyrec {t = _ ∘⟨ _ ⟩ _}            ()
wk-emptyrec {t = prod _ _ _ _}          ()
wk-emptyrec {t = fst _ _}               ()
wk-emptyrec {t = snd _ _}               ()
wk-emptyrec {t = prodrec _ _ _ _ _ _}   ()
wk-emptyrec {t = Empty}                 ()
wk-emptyrec {t = Unit _ _}              ()
wk-emptyrec {t = star _ _}              ()
wk-emptyrec {t = unitrec _ _ _ _ _ _}   ()
wk-emptyrec {t = ℕ}                     ()
wk-emptyrec {t = zero}                  ()
wk-emptyrec {t = suc _}                 ()
wk-emptyrec {t = natrec _ _ _ _ _ _ _}  ()
wk-emptyrec {t = Id _ _ _}              ()
wk-emptyrec {t = rfl}                   ()
wk-emptyrec {t = J _ _ _ _ _ _ _ _}     ()
wk-emptyrec {t = K _ _ _ _ _ _}         ()
wk-emptyrec {t = []-cong _ _ _ _ _}     ()

subst-emptyrec :
  t [ σ ] ≡ emptyrec p A u →
  (∃ λ x → t ≡ var x) ⊎
  ∃₂ λ A′ u′ → t ≡ emptyrec p A′ u′ × A′ [ σ ] ≡ A × u′ [ σ ] ≡ u
subst-emptyrec {t = var _} _ =
  inj₁ (_ , refl)
subst-emptyrec {t = emptyrec _ _ _} refl =
  inj₂ (_ , _ , refl , refl , refl)
subst-emptyrec {t = U _}                   ()
subst-emptyrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-emptyrec {t = lam _ _}               ()
subst-emptyrec {t = _ ∘⟨ _ ⟩ _}            ()
subst-emptyrec {t = prod _ _ _ _}          ()
subst-emptyrec {t = fst _ _}               ()
subst-emptyrec {t = snd _ _}               ()
subst-emptyrec {t = prodrec _ _ _ _ _ _}   ()
subst-emptyrec {t = Empty}                 ()
subst-emptyrec {t = Unit _ _}              ()
subst-emptyrec {t = star _ _}              ()
subst-emptyrec {t = unitrec _ _ _ _ _ _}   ()
subst-emptyrec {t = ℕ}                     ()
subst-emptyrec {t = zero}                  ()
subst-emptyrec {t = suc _}                 ()
subst-emptyrec {t = natrec _ _ _ _ _ _ _}  ()
subst-emptyrec {t = Id _ _ _}              ()
subst-emptyrec {t = rfl}                   ()
subst-emptyrec {t = J _ _ _ _ _ _ _ _}     ()
subst-emptyrec {t = K _ _ _ _ _ _}         ()
subst-emptyrec {t = []-cong _ _ _ _ _}     ()

-- Inversion for ℕ.

wk-ℕ : wk ρ t ≡ ℕ → t ≡ ℕ
wk-ℕ {t = ℕ}                     refl = refl
wk-ℕ {t = var _}                 ()
wk-ℕ {t = U _}                   ()
wk-ℕ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-ℕ {t = lam _ _}               ()
wk-ℕ {t = _ ∘⟨ _ ⟩ _}            ()
wk-ℕ {t = prod _ _ _ _}          ()
wk-ℕ {t = fst _ _}               ()
wk-ℕ {t = snd _ _}               ()
wk-ℕ {t = prodrec _ _ _ _ _ _}   ()
wk-ℕ {t = Empty}                 ()
wk-ℕ {t = emptyrec _ _ _}        ()
wk-ℕ {t = Unit _ _}              ()
wk-ℕ {t = star _ _}              ()
wk-ℕ {t = unitrec _ _ _ _ _ _}   ()
wk-ℕ {t = zero}                  ()
wk-ℕ {t = suc _}                 ()
wk-ℕ {t = natrec _ _ _ _ _ _ _}  ()
wk-ℕ {t = Id _ _ _}              ()
wk-ℕ {t = rfl}                   ()
wk-ℕ {t = J _ _ _ _ _ _ _ _}     ()
wk-ℕ {t = K _ _ _ _ _ _}         ()
wk-ℕ {t = []-cong _ _ _ _ _}     ()

subst-ℕ : t [ σ ] ≡ ℕ → (∃ λ x → t ≡ var x) ⊎ t ≡ ℕ
subst-ℕ {t = var _}                 _    = inj₁ (_ , refl)
subst-ℕ {t = ℕ}                     refl = inj₂ refl
subst-ℕ {t = U _}                   ()
subst-ℕ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-ℕ {t = lam _ _}               ()
subst-ℕ {t = _ ∘⟨ _ ⟩ _}            ()
subst-ℕ {t = prod _ _ _ _}          ()
subst-ℕ {t = fst _ _}               ()
subst-ℕ {t = snd _ _}               ()
subst-ℕ {t = prodrec _ _ _ _ _ _}   ()
subst-ℕ {t = Empty}                 ()
subst-ℕ {t = emptyrec _ _ _}        ()
subst-ℕ {t = Unit _ _}              ()
subst-ℕ {t = star _ _}              ()
subst-ℕ {t = unitrec _ _ _ _ _ _}   ()
subst-ℕ {t = zero}                  ()
subst-ℕ {t = suc _}                 ()
subst-ℕ {t = natrec _ _ _ _ _ _ _}  ()
subst-ℕ {t = Id _ _ _}              ()
subst-ℕ {t = rfl}                   ()
subst-ℕ {t = J _ _ _ _ _ _ _ _}     ()
subst-ℕ {t = K _ _ _ _ _ _}         ()
subst-ℕ {t = []-cong _ _ _ _ _}     ()

-- Inversion for zero.

wk-zero : wk ρ t ≡ zero → t ≡ zero
wk-zero {t = zero}                  refl = refl
wk-zero {t = var _}                 ()
wk-zero {t = U _}                   ()
wk-zero {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-zero {t = lam _ _}               ()
wk-zero {t = _ ∘⟨ _ ⟩ _}            ()
wk-zero {t = prod _ _ _ _}          ()
wk-zero {t = fst _ _}               ()
wk-zero {t = snd _ _}               ()
wk-zero {t = prodrec _ _ _ _ _ _}   ()
wk-zero {t = Empty}                 ()
wk-zero {t = emptyrec _ _ _}        ()
wk-zero {t = Unit _ _}              ()
wk-zero {t = star _ _}              ()
wk-zero {t = unitrec _ _ _ _ _ _}   ()
wk-zero {t = ℕ}                     ()
wk-zero {t = suc _}                 ()
wk-zero {t = natrec _ _ _ _ _ _ _}  ()
wk-zero {t = Id _ _ _}              ()
wk-zero {t = rfl}                   ()
wk-zero {t = J _ _ _ _ _ _ _ _}     ()
wk-zero {t = K _ _ _ _ _ _}         ()
wk-zero {t = []-cong _ _ _ _ _}     ()

subst-zero : t [ σ ] ≡ zero → (∃ λ x → t ≡ var x) ⊎ t ≡ zero
subst-zero {t = var _}                 _    = inj₁ (_ , refl)
subst-zero {t = zero}                  refl = inj₂ refl
subst-zero {t = U _}                   ()
subst-zero {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-zero {t = lam _ _}               ()
subst-zero {t = _ ∘⟨ _ ⟩ _}            ()
subst-zero {t = prod _ _ _ _}          ()
subst-zero {t = fst _ _}               ()
subst-zero {t = snd _ _}               ()
subst-zero {t = prodrec _ _ _ _ _ _}   ()
subst-zero {t = Empty}                 ()
subst-zero {t = emptyrec _ _ _}        ()
subst-zero {t = Unit _ _}              ()
subst-zero {t = star _ _}              ()
subst-zero {t = unitrec _ _ _ _ _ _}   ()
subst-zero {t = ℕ}                     ()
subst-zero {t = suc _}                 ()
subst-zero {t = natrec _ _ _ _ _ _ _}  ()
subst-zero {t = Id _ _ _}              ()
subst-zero {t = rfl}                   ()
subst-zero {t = J _ _ _ _ _ _ _ _}     ()
subst-zero {t = K _ _ _ _ _ _}         ()
subst-zero {t = []-cong _ _ _ _ _}     ()

-- Inversion for suc.

wk-suc :
  wk ρ t ≡ suc u →
  ∃ λ u′ → t ≡ suc u′ × wk ρ u′ ≡ u
wk-suc {t = suc _}                 refl = _ , refl , refl
wk-suc {t = var _}                 ()
wk-suc {t = U _}                   ()
wk-suc {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-suc {t = lam _ _}               ()
wk-suc {t = _ ∘⟨ _ ⟩ _}            ()
wk-suc {t = prod _ _ _ _}          ()
wk-suc {t = fst _ _}               ()
wk-suc {t = snd _ _}               ()
wk-suc {t = prodrec _ _ _ _ _ _}   ()
wk-suc {t = Empty}                 ()
wk-suc {t = emptyrec _ _ _}        ()
wk-suc {t = Unit _ _}              ()
wk-suc {t = star _ _}              ()
wk-suc {t = unitrec _ _ _ _ _ _}   ()
wk-suc {t = ℕ}                     ()
wk-suc {t = zero}                  ()
wk-suc {t = natrec _ _ _ _ _ _ _}  ()
wk-suc {t = Id _ _ _}              ()
wk-suc {t = rfl}                   ()
wk-suc {t = J _ _ _ _ _ _ _ _}     ()
wk-suc {t = K _ _ _ _ _ _}         ()
wk-suc {t = []-cong _ _ _ _ _}     ()

subst-suc :
  t [ σ ] ≡ suc u →
  (∃ λ x → t ≡ var x) ⊎ ∃ λ u′ → t ≡ suc u′ × u′ [ σ ] ≡ u
subst-suc {t = var _}                 _    = inj₁ (_ , refl)
subst-suc {t = suc _}                 refl = inj₂ (_ , refl , refl)
subst-suc {t = U _}                   ()
subst-suc {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-suc {t = lam _ _}               ()
subst-suc {t = _ ∘⟨ _ ⟩ _}            ()
subst-suc {t = prod _ _ _ _}          ()
subst-suc {t = fst _ _}               ()
subst-suc {t = snd _ _}               ()
subst-suc {t = prodrec _ _ _ _ _ _}   ()
subst-suc {t = Empty}                 ()
subst-suc {t = emptyrec _ _ _}        ()
subst-suc {t = Unit _ _}              ()
subst-suc {t = star _ _}              ()
subst-suc {t = unitrec _ _ _ _ _ _}   ()
subst-suc {t = ℕ}                     ()
subst-suc {t = zero}                  ()
subst-suc {t = natrec _ _ _ _ _ _ _}  ()
subst-suc {t = Id _ _ _}              ()
subst-suc {t = rfl}                   ()
subst-suc {t = J _ _ _ _ _ _ _ _}     ()
subst-suc {t = K _ _ _ _ _ _}         ()
subst-suc {t = []-cong _ _ _ _ _}     ()

-- Inversion for natrec.

wk-natrec :
  wk ρ t ≡ natrec p q r A u v w →
  ∃₄ λ A′ u′ v′ w′ →
     t ≡ natrec p q r A′ u′ v′ w′ ×
     wk (lift ρ) A′ ≡ A ×
     wk ρ u′ ≡ u × wk (lift (lift ρ)) v′ ≡ v × wk ρ w′ ≡ w
wk-natrec {t = natrec _ _ _ _ _ _ _} refl =
  _ , _ , _ , _ , refl , refl , refl , refl , refl
wk-natrec {t = var _}                 ()
wk-natrec {t = U _}                   ()
wk-natrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-natrec {t = lam _ _}               ()
wk-natrec {t = _ ∘⟨ _ ⟩ _}            ()
wk-natrec {t = prod _ _ _ _}          ()
wk-natrec {t = fst _ _}               ()
wk-natrec {t = snd _ _}               ()
wk-natrec {t = prodrec _ _ _ _ _ _}   ()
wk-natrec {t = Empty}                 ()
wk-natrec {t = emptyrec _ _ _}        ()
wk-natrec {t = Unit _ _}              ()
wk-natrec {t = star _ _}              ()
wk-natrec {t = unitrec _ _ _ _ _ _}   ()
wk-natrec {t = ℕ}                     ()
wk-natrec {t = zero}                  ()
wk-natrec {t = suc _}                 ()
wk-natrec {t = Id _ _ _}              ()
wk-natrec {t = rfl}                   ()
wk-natrec {t = J _ _ _ _ _ _ _ _}     ()
wk-natrec {t = K _ _ _ _ _ _}         ()
wk-natrec {t = []-cong _ _ _ _ _}     ()

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
subst-natrec {t = U _}                   ()
subst-natrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-natrec {t = lam _ _}               ()
subst-natrec {t = _ ∘⟨ _ ⟩ _}            ()
subst-natrec {t = prod _ _ _ _}          ()
subst-natrec {t = fst _ _}               ()
subst-natrec {t = snd _ _}               ()
subst-natrec {t = prodrec _ _ _ _ _ _}   ()
subst-natrec {t = Empty}                 ()
subst-natrec {t = emptyrec _ _ _}        ()
subst-natrec {t = Unit _ _}              ()
subst-natrec {t = star _ _}              ()
subst-natrec {t = unitrec _ _ _ _ _ _}   ()
subst-natrec {t = ℕ}                     ()
subst-natrec {t = zero}                  ()
subst-natrec {t = suc _}                 ()
subst-natrec {t = Id _ _ _}              ()
subst-natrec {t = rfl}                   ()
subst-natrec {t = J _ _ _ _ _ _ _ _}     ()
subst-natrec {t = K _ _ _ _ _ _}         ()
subst-natrec {t = []-cong _ _ _ _ _}     ()

-- Inversion for Id.

wk-Id :
  wk ρ v ≡ Id A t u →
  ∃₃ λ A′ t′ u′ →
     v ≡ Id A′ t′ u′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk ρ u′ ≡ u
wk-Id {v = Id _ _ _} refl =
  _ , _ , _ , refl , refl , refl , refl
wk-Id {v = var _}                 ()
wk-Id {v = U _}                   ()
wk-Id {v = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-Id {v = lam _ _}               ()
wk-Id {v = _ ∘⟨ _ ⟩ _}            ()
wk-Id {v = prod _ _ _ _}          ()
wk-Id {v = fst _ _}               ()
wk-Id {v = snd _ _}               ()
wk-Id {v = prodrec _ _ _ _ _ _}   ()
wk-Id {v = Empty}                 ()
wk-Id {v = emptyrec _ _ _}        ()
wk-Id {v = Unit _ _}              ()
wk-Id {v = star _ _}              ()
wk-Id {v = unitrec _ _ _ _ _ _}   ()
wk-Id {v = ℕ}                     ()
wk-Id {v = zero}                  ()
wk-Id {v = suc _}                 ()
wk-Id {v = natrec _ _ _ _ _ _ _}  ()
wk-Id {v = rfl}                   ()
wk-Id {v = J _ _ _ _ _ _ _ _}     ()
wk-Id {v = K _ _ _ _ _ _}         ()
wk-Id {v = []-cong _ _ _ _ _}     ()

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
subst-Id {v = U _}                   ()
subst-Id {v = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-Id {v = lam _ _}               ()
subst-Id {v = _ ∘⟨ _ ⟩ _}            ()
subst-Id {v = prod _ _ _ _}          ()
subst-Id {v = fst _ _}               ()
subst-Id {v = snd _ _}               ()
subst-Id {v = prodrec _ _ _ _ _ _}   ()
subst-Id {v = Empty}                 ()
subst-Id {v = emptyrec _ _ _}        ()
subst-Id {v = Unit _ _}              ()
subst-Id {v = star _ _}              ()
subst-Id {v = unitrec _ _ _ _ _ _}   ()
subst-Id {v = ℕ}                     ()
subst-Id {v = zero}                  ()
subst-Id {v = suc _}                 ()
subst-Id {v = natrec _ _ _ _ _ _ _}  ()
subst-Id {v = rfl}                   ()
subst-Id {v = J _ _ _ _ _ _ _ _}     ()
subst-Id {v = K _ _ _ _ _ _}         ()
subst-Id {v = []-cong _ _ _ _ _}     ()

-- Inversion for rfl.

wk-rfl : wk ρ t ≡ rfl → t ≡ rfl
wk-rfl {t = rfl}                   refl = refl
wk-rfl {t = var _}                 ()
wk-rfl {t = U _}                   ()
wk-rfl {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-rfl {t = lam _ _}               ()
wk-rfl {t = _ ∘⟨ _ ⟩ _}            ()
wk-rfl {t = prod _ _ _ _}          ()
wk-rfl {t = fst _ _}               ()
wk-rfl {t = snd _ _}               ()
wk-rfl {t = prodrec _ _ _ _ _ _}   ()
wk-rfl {t = Empty}                 ()
wk-rfl {t = emptyrec _ _ _}        ()
wk-rfl {t = Unit _ _}              ()
wk-rfl {t = star _ _}              ()
wk-rfl {t = unitrec _ _ _ _ _ _}   ()
wk-rfl {t = ℕ}                     ()
wk-rfl {t = zero}                  ()
wk-rfl {t = suc _}                 ()
wk-rfl {t = natrec _ _ _ _ _ _ _}  ()
wk-rfl {t = Id _ _ _}              ()
wk-rfl {t = J _ _ _ _ _ _ _ _}     ()
wk-rfl {t = K _ _ _ _ _ _}         ()
wk-rfl {t = []-cong _ _ _ _ _}     ()

subst-rfl : t [ σ ] ≡ rfl → (∃ λ x → t ≡ var x) ⊎ t ≡ rfl
subst-rfl {t = var x}                 _    = inj₁ (_ , refl)
subst-rfl {t = rfl}                   refl = inj₂ refl
subst-rfl {t = U _}                   ()
subst-rfl {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-rfl {t = lam _ _}               ()
subst-rfl {t = _ ∘⟨ _ ⟩ _}            ()
subst-rfl {t = prod _ _ _ _}          ()
subst-rfl {t = fst _ _}               ()
subst-rfl {t = snd _ _}               ()
subst-rfl {t = prodrec _ _ _ _ _ _}   ()
subst-rfl {t = Empty}                 ()
subst-rfl {t = emptyrec _ _ _}        ()
subst-rfl {t = Unit _ _}              ()
subst-rfl {t = star _ _}              ()
subst-rfl {t = unitrec _ _ _ _ _ _}   ()
subst-rfl {t = ℕ}                     ()
subst-rfl {t = zero}                  ()
subst-rfl {t = suc _}                 ()
subst-rfl {t = natrec _ _ _ _ _ _ _}  ()
subst-rfl {t = Id _ _ _}              ()
subst-rfl {t = J _ _ _ _ _ _ _ _}     ()
subst-rfl {t = K _ _ _ _ _ _}         ()
subst-rfl {t = []-cong _ _ _ _ _}     ()

-- Inversion for J.

wk-J :
  wk ρ w ≡ J p q A t B u t′ v →
  ∃₆ λ A′ t″ B′ u′ t‴ v′ →
     w ≡ J p q A′ t″ B′ u′ t‴ v′ ×
     wk ρ A′ ≡ A × wk ρ t″ ≡ t × wk (lift (lift ρ)) B′ ≡ B ×
     wk ρ u′ ≡ u × wk ρ t‴ ≡ t′ × wk ρ v′ ≡ v
wk-J {w = J _ _ _ _ _ _ _ _} refl =
  _ , _ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl , refl
wk-J {w = var _}                 ()
wk-J {w = U _}                   ()
wk-J {w = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-J {w = lam _ _}               ()
wk-J {w = _ ∘⟨ _ ⟩ _}            ()
wk-J {w = prod _ _ _ _}          ()
wk-J {w = fst _ _}               ()
wk-J {w = snd _ _}               ()
wk-J {w = prodrec _ _ _ _ _ _}   ()
wk-J {w = Empty}                 ()
wk-J {w = emptyrec _ _ _}        ()
wk-J {w = Unit _ _}              ()
wk-J {w = star _ _}              ()
wk-J {w = unitrec _ _ _ _ _ _}   ()
wk-J {w = ℕ}                     ()
wk-J {w = zero}                  ()
wk-J {w = suc _}                 ()
wk-J {w = natrec _ _ _ _ _ _ _}  ()
wk-J {w = Id _ _ _}              ()
wk-J {w = rfl}                   ()
wk-J {w = K _ _ _ _ _ _}         ()
wk-J {w = []-cong _ _ _ _ _}     ()

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
subst-J {w = U _}                   ()
subst-J {w = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-J {w = lam _ _}               ()
subst-J {w = _ ∘⟨ _ ⟩ _}            ()
subst-J {w = prod _ _ _ _}          ()
subst-J {w = fst _ _}               ()
subst-J {w = snd _ _}               ()
subst-J {w = prodrec _ _ _ _ _ _}   ()
subst-J {w = Empty}                 ()
subst-J {w = emptyrec _ _ _}        ()
subst-J {w = Unit _ _}              ()
subst-J {w = star _ _}              ()
subst-J {w = unitrec _ _ _ _ _ _}   ()
subst-J {w = ℕ}                     ()
subst-J {w = zero}                  ()
subst-J {w = suc _}                 ()
subst-J {w = natrec _ _ _ _ _ _ _}  ()
subst-J {w = Id _ _ _}              ()
subst-J {w = rfl}                   ()
subst-J {w = K _ _ _ _ _ _}         ()
subst-J {w = []-cong _ _ _ _ _}     ()

-- Inversion for K.

wk-K :
  wk ρ w ≡ K p A t B u v →
  ∃₅ λ A′ t′ B′ u′ v′ →
     w ≡ K p A′ t′ B′ u′ v′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk (lift ρ) B′ ≡ B ×
     wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-K {w = K _ _ _ _ _ _} refl =
  _ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl
wk-K {w = var _}                 ()
wk-K {w = U _}                   ()
wk-K {w = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-K {w = lam _ _}               ()
wk-K {w = _ ∘⟨ _ ⟩ _}            ()
wk-K {w = prod _ _ _ _}          ()
wk-K {w = fst _ _}               ()
wk-K {w = snd _ _}               ()
wk-K {w = prodrec _ _ _ _ _ _}   ()
wk-K {w = Empty}                 ()
wk-K {w = emptyrec _ _ _}        ()
wk-K {w = Unit _ _}              ()
wk-K {w = star _ _}              ()
wk-K {w = unitrec _ _ _ _ _ _}   ()
wk-K {w = ℕ}                     ()
wk-K {w = zero}                  ()
wk-K {w = suc _}                 ()
wk-K {w = natrec _ _ _ _ _ _ _}  ()
wk-K {w = Id _ _ _}              ()
wk-K {w = rfl}                   ()
wk-K {w = J _ _ _ _ _ _ _ _}     ()
wk-K {w = []-cong _ _ _ _ _}     ()

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
subst-K {w = U _}                   ()
subst-K {w = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-K {w = lam _ _}               ()
subst-K {w = _ ∘⟨ _ ⟩ _}            ()
subst-K {w = prod _ _ _ _}          ()
subst-K {w = fst _ _}               ()
subst-K {w = snd _ _}               ()
subst-K {w = prodrec _ _ _ _ _ _}   ()
subst-K {w = Empty}                 ()
subst-K {w = emptyrec _ _ _}        ()
subst-K {w = Unit _ _}              ()
subst-K {w = star _ _}              ()
subst-K {w = unitrec _ _ _ _ _ _}   ()
subst-K {w = ℕ}                     ()
subst-K {w = zero}                  ()
subst-K {w = suc _}                 ()
subst-K {w = natrec _ _ _ _ _ _ _}  ()
subst-K {w = Id _ _ _}              ()
subst-K {w = rfl}                   ()
subst-K {w = J _ _ _ _ _ _ _ _}     ()
subst-K {w = []-cong _ _ _ _ _}     ()

-- Inversion for []-cong.

wk-[]-cong :
  wk ρ w ≡ []-cong s A t u v →
  ∃₄ λ A′ t′ u′ v′ →
     w ≡ []-cong s A′ t′ u′ v′ ×
     wk ρ A′ ≡ A × wk ρ t′ ≡ t × wk ρ u′ ≡ u × wk ρ v′ ≡ v
wk-[]-cong {w = []-cong _ _ _ _ _} refl =
  _ , _ , _ , _ , refl , refl , refl , refl , refl
wk-[]-cong {w = var _}                 ()
wk-[]-cong {w = U _}                   ()
wk-[]-cong {w = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
wk-[]-cong {w = lam _ _}               ()
wk-[]-cong {w = _ ∘⟨ _ ⟩ _}            ()
wk-[]-cong {w = prod _ _ _ _}          ()
wk-[]-cong {w = fst _ _}               ()
wk-[]-cong {w = snd _ _}               ()
wk-[]-cong {w = prodrec _ _ _ _ _ _}   ()
wk-[]-cong {w = Empty}                 ()
wk-[]-cong {w = emptyrec _ _ _}        ()
wk-[]-cong {w = Unit _ _}              ()
wk-[]-cong {w = star _ _}              ()
wk-[]-cong {w = unitrec _ _ _ _ _ _}   ()
wk-[]-cong {w = ℕ}                     ()
wk-[]-cong {w = zero}                  ()
wk-[]-cong {w = suc _}                 ()
wk-[]-cong {w = natrec _ _ _ _ _ _ _}  ()
wk-[]-cong {w = Id _ _ _}              ()
wk-[]-cong {w = rfl}                   ()
wk-[]-cong {w = J _ _ _ _ _ _ _ _}     ()
wk-[]-cong {w = K _ _ _ _ _ _}         ()

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
subst-[]-cong {w = U _}                   ()
subst-[]-cong {w = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
subst-[]-cong {w = lam _ _}               ()
subst-[]-cong {w = _ ∘⟨ _ ⟩ _}            ()
subst-[]-cong {w = prod _ _ _ _}          ()
subst-[]-cong {w = fst _ _}               ()
subst-[]-cong {w = snd _ _}               ()
subst-[]-cong {w = prodrec _ _ _ _ _ _}   ()
subst-[]-cong {w = Empty}                 ()
subst-[]-cong {w = emptyrec _ _ _}        ()
subst-[]-cong {w = Unit _ _}              ()
subst-[]-cong {w = star _ _}              ()
subst-[]-cong {w = unitrec _ _ _ _ _ _}   ()
subst-[]-cong {w = ℕ}                     ()
subst-[]-cong {w = zero}                  ()
subst-[]-cong {w = suc _}                 ()
subst-[]-cong {w = natrec _ _ _ _ _ _ _}  ()
subst-[]-cong {w = Id _ _ _}              ()
subst-[]-cong {w = rfl}                   ()
subst-[]-cong {w = J _ _ _ _ _ _ _ _}     ()
subst-[]-cong {w = K _ _ _ _ _ _}         ()
