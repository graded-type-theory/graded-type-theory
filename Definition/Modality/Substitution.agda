module Definition.Modality.Substitution where

open import Definition.Untyped as U hiding (_∷_)
open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Usage

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE

infix 30 _*>_

private
  variable
    M : Set
    ℓ m n : Nat
    p q : M
    𝕄 : Modality M
    t u A : Term M n
    γ δ : ConM 𝕄 n
    σ : Subst {M} m n

data Substₘ (𝕄 : Modality M) : (m n : Nat) → Set where
  ε : Substₘ 𝕄 m 0
  _∙_ : Substₘ 𝕄 m n →  ConM 𝕄 m → Substₘ 𝕄 m (1+ n)

private
  variable
    Ψ Φ : Substₘ 𝕄 m n

_*_ : {𝕄 : Modality M} (γ δ : ConM 𝕄 n) → M
_*_ {𝕄 = 𝕄} ε ε = Modality.𝟘 𝕄
_*_ {𝕄 = 𝕄} (γ ∙ p) (δ ∙ q) = Modality._+_ 𝕄 (γ * δ) (Modality._·_ 𝕄 p q)

_*>_ : (Ψ : Substₘ 𝕄 m n) → (γ : ConM 𝕄 n) → ConM 𝕄 m
ε *> ε = 𝟘ᶜ
(Ψ ∙ δ) *> (γ ∙ p) = p ·ᶜ δ +ᶜ (Ψ *> γ)

substₘ = _*>_

_<*_ : (γ : ConM 𝕄 m) → (Ψ : Substₘ 𝕄 m n) → ConM 𝕄 n
γ <* ε = ε
γ <* (Ψ ∙ δ) = (γ <* Ψ) ∙ (γ * δ)

_<*>_ : (Ψ : Substₘ 𝕄 m ℓ) (Φ : Substₘ 𝕄 ℓ n) → Substₘ 𝕄 m n
Ψ <*> ε = ε
Ψ <*> (Φ ∙ δ) = (Ψ <*> Φ) ∙ (Ψ *> δ)

*>-distr-+ᶜ : Ψ *> (γ +ᶜ δ) ≡ Ψ *> γ +ᶜ Ψ *> δ
*>-distr-+ᶜ {Ψ = ε} {ε} {ε} = PE.sym rightUnit
*>-distr-+ᶜ {Ψ = Ψ ∙ η} {γ ∙ p} {δ ∙ q} = subst₂ _≡_ (cong₂ _+ᶜ_ refl (PE.sym *>-distr-+ᶜ)) {!+ᶜ-associative!} (cong₂ _+ᶜ_ (rightDistr+ p q η) {!!})

*>-distr-·ᶜ : Ψ *> (p ·ᶜ γ) ≡ p ·ᶜ (Ψ *> γ)
*>-distr-·ᶜ {Ψ = ε} {γ = ε} = PE.sym rightZero
*>-distr-·ᶜ {Ψ = Ψ ∙ x} = *>-distr-·ᶜ

*>-linear : Ψ *> (p ·ᶜ γ +ᶜ q ·ᶜ δ) ≡ p ·ᶜ Ψ *> γ +ᶜ q ·ᶜ Ψ *> δ
*>-linear = {!!}


stepSubstₘ : Substₘ 𝕄 m n → Substₘ 𝕄 (1+ m) n
stepSubstₘ ε = ε
stepSubstₘ {𝕄 = 𝕄} (Ψ ∙ δ) = (stepSubstₘ Ψ) ∙ (δ ∙ Modality.𝟘 𝕄)

liftSubstₘ : Substₘ 𝕄 m n → Substₘ 𝕄 (1+ m) (1+ n)
liftSubstₘ {𝕄 = 𝕄} Ψ = (stepSubstₘ Ψ) ∙ (𝟘ᶜ , x0 ≔ Modality.𝟙 𝕄)

idSubstₘ : Substₘ 𝕄 n n
idSubstₘ {n = Nat.zero} = ε
idSubstₘ {𝕄 = 𝕄} {n = 1+ n} = liftSubstₘ idSubstₘ

sgSubstₘ : {𝕄 : Modality M} (γ : ConM 𝕄 n) → Substₘ 𝕄 n (1+ n)
sgSubstₘ γ = idSubstₘ ∙ γ

wk1Substₘ : {𝕄 : Modality M} {γ : ConM 𝕄 n} → stepSubstₘ idSubstₘ *> γ ≡ γ ∙ (Modality.𝟘 𝕄)
wk1Substₘ {γ = ε} = refl
wk1Substₘ {γ = γ ∙ p} = subst₂ _≡_ {!!} {!!} wk1Substₘ

_▶_ : (Ψ : Substₘ 𝕄 m n) → (σ : Subst m n) → Set₁
_▶_ {𝕄 = 𝕄} {n = n} Ψ σ = ∀ (x : Fin n) → (Ψ *> (𝟘ᶜ , x ≔ (Modality.𝟙 𝕄))) ▸ (σ x)

idSubstₘ-leftUnit : {𝕄 : Modality M} {γ : ConM 𝕄 n} → idSubstₘ *> γ ≡ γ
idSubstₘ-leftUnit {γ = ε} = refl
idSubstₘ-leftUnit {𝕄 = 𝕄} {γ = γ ∙ p} = subst₂ _≡_ (cong₂ _+ᶜ_ (cong₂ _∙_ (PE.sym rightZero) (PE.sym (proj₂ (Modality.·-Identity 𝕄) p))) (PE.sym wk1Substₘ)) (cong₂ _∙_ leftUnit (proj₂ (Modality.+-Identity 𝕄) p)) refl

substₘ-rightZero : {Ψ : Substₘ 𝕄 m n} → substₘ Ψ 𝟘ᶜ ≡ 𝟘ᶜ
substₘ-rightZero {Ψ = ε} = refl
substₘ-rightZero {Ψ = Ψ ∙ γ} = PE.subst (_≡ 𝟘ᶜ) (cong₂ _+ᶜ_ (PE.sym leftZero) (PE.sym (substₘ-rightZero {Ψ = Ψ}))) leftUnit
  
wu-sgSubst : γ ▸ u → sgSubstₘ γ ▶ sgSubst u
wu-sgSubst {γ = γ} {u} γ▸u x0 = subst₂ _▸_ (PE.subst (γ ≡_) (cong₂ _+ᶜ_ (PE.sym identity) (PE.sym idSubstₘ-leftUnit)) (PE.sym rightUnit)) refl γ▸u
wu-sgSubst γ▸u (x +1) = PE.subst (_▸ var x) (subst₂ _≡_ leftUnit (cong₂ _+ᶜ_ (PE.sym leftZero) (PE.sym idSubstₘ-leftUnit)) refl) var

wu-stepSubst : Ψ ▶ σ → stepSubstₘ Ψ ▶ wk1Subst σ
wu-stepSubst Ψ▶σ x0 = {!!}
wu-stepSubst Ψ▶σ (_+1 x) = {!!}

wu-liftSubst : Ψ ▶ σ → liftSubstₘ Ψ ▶ liftSubst σ
wu-liftSubst Ψ▶σ x0 = PE.subst (_▸ var x0) {!!} {!!}
wu-liftSubst Ψ▶σ (_+1 x) = {!!}


substₘ-lemma : {Ψ : Substₘ 𝕄 m n} {σ : Subst m n} → Ψ ▶ σ → γ ▸ t → substₘ Ψ γ ▸ U.subst σ t
substₘ-lemma Ψ▶σ Uₘ = PE.subst (_▸ gen Ukind []) (PE.sym substₘ-rightZero) Uₘ
substₘ-lemma Ψ▶σ ℕₘ = PE.subst (_▸ gen Natkind []) (PE.sym substₘ-rightZero) ℕₘ
substₘ-lemma Ψ▶σ Emptyₘ =  PE.subst (_▸ gen Emptykind []) (PE.sym substₘ-rightZero) Emptyₘ
substₘ-lemma Ψ▶σ Unitₘ =  PE.subst (_▸ gen Unitkind []) (PE.sym substₘ-rightZero) Unitₘ
substₘ-lemma Ψ▶σ (Πₘ γ▸F δ▸G) = subst₂ _▸_ (PE.sym *>-distr-+ᶜ) refl
             (Πₘ (substₘ-lemma Ψ▶σ γ▸F) (substₘ-lemma (wu-liftSubst Ψ▶σ) δ▸G))
substₘ-lemma Ψ▶σ (Σₘ γ▸F δ▸G) = subst₂ _▸_ (PE.sym *>-distr-+ᶜ) refl
             (Σₘ (substₘ-lemma Ψ▶σ γ▸F) (substₘ-lemma (wu-liftSubst Ψ▶σ) δ▸G))
substₘ-lemma Ψ▶σ (var {x}) = Ψ▶σ x
substₘ-lemma Ψ▶σ (lamₘ γ▸t) = lamₘ (substₘ-lemma (wu-liftSubst Ψ▶σ) γ▸t)
substₘ-lemma Ψ▶σ (γ▸t ∘ₘ δ▸u) = subst₂ _▸_ (subst₂ _≡_ *>-distr-·ᶜ (PE.sym *>-distr-+ᶜ) refl) refl (substₘ-lemma Ψ▶σ γ▸t ∘ₘ substₘ-lemma Ψ▶σ δ▸u)
substₘ-lemma Ψ▶σ (prodₘ γ▸t δ▸u) = subst₂ _▸_ (PE.sym *>-distr-+ᶜ) refl (prodₘ (substₘ-lemma Ψ▶σ γ▸t) (substₘ-lemma Ψ▶σ δ▸u))
substₘ-lemma Ψ▶σ (fstₘ γ▸t) = subst₂ _▸_ (PE.sym substₘ-rightZero) refl (fstₘ (substₘ-lemma Ψ▶σ γ▸t))
substₘ-lemma Ψ▶σ (sndₘ γ▸t) =  subst₂ _▸_ (PE.sym substₘ-rightZero) refl (sndₘ (substₘ-lemma Ψ▶σ γ▸t))
substₘ-lemma Ψ▶σ (prodrecₘ γ▸t δ▸u) = subst₂ _▸_ (PE.sym *>-distr-+ᶜ) refl (prodrecₘ (substₘ-lemma Ψ▶σ γ▸t) (substₘ-lemma (wu-liftSubst (wu-liftSubst Ψ▶σ)) δ▸u))
substₘ-lemma Ψ▶σ zeroₘ =  PE.subst (_▸ gen Zerokind []) (PE.sym substₘ-rightZero) zeroₘ
substₘ-lemma Ψ▶σ (sucₘ γ▸t) = sucₘ (substₘ-lemma Ψ▶σ γ▸t)
substₘ-lemma Ψ▶σ (natrecₘ γ▸z γ▸s δ▸n x) = subst₂ _▸_ (PE.sym *>-distr-·ᶜ) refl (natrecₘ (substₘ-lemma Ψ▶σ γ▸z) (substₘ-lemma Ψ▶σ γ▸s) (substₘ-lemma Ψ▶σ δ▸n) x)
substₘ-lemma Ψ▶σ (Emptyrecₘ γ▸t) = Emptyrecₘ (substₘ-lemma Ψ▶σ γ▸t)
substₘ-lemma Ψ▶σ starₘ =  PE.subst (_▸ gen Starkind []) (PE.sym substₘ-rightZero) starₘ
substₘ-lemma Ψ▶σ (sub γ▸t x) = substₘ-lemma Ψ▶σ γ▸t
