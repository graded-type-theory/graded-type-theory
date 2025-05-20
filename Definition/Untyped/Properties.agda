------------------------------------------------------------------------
-- Properties of the untyped syntax
-- Laws for weakenings and substitutions.
------------------------------------------------------------------------

module Definition.Untyped.Properties {a} (M : Set a) where

open import Definition.Untyped M
open import Definition.Untyped.Properties.NotParametrised public

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Relation
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private
  variable
    j k k₁ k₂ ℓ m n o : Nat
    x x₁ x₂ : Fin _
    eq eq₁ eq₂ : _ ≡ _
    A A₁ A₂ B₁ B₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
    ρ ρ′ : Wk m n
    η : Wk n ℓ
    σ σ₁ σ₂ σ′ : Subst m n
    p p₁ p₂ q q₁ q₂ r r₁ r₂ : M
    s s₁ s₂ : Strength
    b₁ b₂ : BinderMode
    l₁ l₂ : Universe-level

------------------------------------------------------------------------
-- Properties of toTerm and fromTerm.

opaque

  -- Converting to the alternative term representation and back is
  -- identity.

  toTerm∘fromTerm : (t : Term n) → toTerm (fromTerm t) ≡ t
  toTerm∘fromTerm (var x) = refl
  toTerm∘fromTerm (U l) = refl
  toTerm∘fromTerm (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
    cong₂ (ΠΣ⟨ b ⟩ p , q ▷_▹_) (toTerm∘fromTerm A) (toTerm∘fromTerm B)
  toTerm∘fromTerm (lam p t) =
    cong (lam p) (toTerm∘fromTerm t)
  toTerm∘fromTerm (t ∘⟨ p ⟩ u) =
    cong₂ (_∘⟨ p ⟩_) (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm (prod s p t u) =
    cong₂ (prod s p) (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm (fst p t) =
    cong (fst p) (toTerm∘fromTerm t)
  toTerm∘fromTerm (snd p t) =
    cong (snd p) (toTerm∘fromTerm t)
  toTerm∘fromTerm (prodrec r p q A t u) =
    cong₃ (prodrec r p q) (toTerm∘fromTerm A)
      (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm ℕ = refl
  toTerm∘fromTerm zero = refl
  toTerm∘fromTerm (suc t) =
    cong suc (toTerm∘fromTerm t)
  toTerm∘fromTerm (natrec p q r A z s n) =
    cong₄ (natrec p q r) (toTerm∘fromTerm A) (toTerm∘fromTerm z)
      (toTerm∘fromTerm s) (toTerm∘fromTerm n)
  toTerm∘fromTerm (Unit s l) = refl
  toTerm∘fromTerm (star s l) = refl
  toTerm∘fromTerm (unitrec l p q A t u) =
    cong₃ (unitrec l p q) (toTerm∘fromTerm A)
      (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm Empty = refl
  toTerm∘fromTerm (emptyrec p A t) =
    cong₂ (emptyrec p) (toTerm∘fromTerm A) (toTerm∘fromTerm t)
  toTerm∘fromTerm (Id A t u) =
    cong₃ Id (toTerm∘fromTerm A) (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm rfl = refl
  toTerm∘fromTerm (J p q A t B u v w) =
    cong₆ (J p q) (toTerm∘fromTerm A) (toTerm∘fromTerm t)
      (toTerm∘fromTerm B) (toTerm∘fromTerm u)
      (toTerm∘fromTerm v) (toTerm∘fromTerm w)
  toTerm∘fromTerm (K p A t B u v) =
    cong₅ (K p) (toTerm∘fromTerm A) (toTerm∘fromTerm t)
      (toTerm∘fromTerm B) (toTerm∘fromTerm u) (toTerm∘fromTerm v)
  toTerm∘fromTerm ([]-cong s A t u v) =
    cong₄ ([]-cong s) (toTerm∘fromTerm A) (toTerm∘fromTerm t)
      (toTerm∘fromTerm u) (toTerm∘fromTerm v)

opaque

  -- Converting from the alternative term representation and back is
  -- identity.

  fromTerm∘toTerm : (t : Term′ n) → fromTerm (toTerm t) ≡ t
  fromTerm∘toTerm (var x) = refl
  fromTerm∘toTerm (gen (Ukind l) []) = refl
  fromTerm∘toTerm (gen (Binderkind b p q) (A ∷ₜ B ∷ₜ [])) =
    cong₂ (λ A B → gen (Binderkind b p q) (A ∷ₜ B ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm B)
  fromTerm∘toTerm (gen (Lamkind p) (t ∷ₜ [])) =
    cong (λ t → gen (Lamkind p) (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (gen (Appkind p) (t ∷ₜ u ∷ₜ [])) =
    cong₂ (λ t u → gen (Appkind p) (t ∷ₜ u ∷ₜ []))
      (fromTerm∘toTerm t) (fromTerm∘toTerm u)
  fromTerm∘toTerm (gen (Prodkind s p) (t ∷ₜ u ∷ₜ [])) =
    cong₂ (λ t u → gen (Prodkind s p) (t ∷ₜ u ∷ₜ []))
      (fromTerm∘toTerm t) (fromTerm∘toTerm u)
  fromTerm∘toTerm (gen (Fstkind p) (t ∷ₜ [])) =
    cong (λ t → gen (Fstkind p) (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (gen (Sndkind p) (t ∷ₜ [])) =
    cong (λ t → gen (Sndkind p) (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (gen (Prodreckind r p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
    cong₃ (λ A t u → gen (Prodreckind r p q) (A ∷ₜ t ∷ₜ u ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm u)
  fromTerm∘toTerm (gen Natkind []) = refl
  fromTerm∘toTerm (gen Zerokind []) = refl
  fromTerm∘toTerm (gen Suckind (t ∷ₜ [])) =
    cong (λ t → gen Suckind (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (gen (Natreckind p q r) (A ∷ₜ z ∷ₜ s ∷ₜ n ∷ₜ [])) =
    cong₄ (λ A z s n → gen (Natreckind p q r) (A ∷ₜ z ∷ₜ s ∷ₜ n ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm z)
      (fromTerm∘toTerm s) (fromTerm∘toTerm n)
  fromTerm∘toTerm (gen (Unitkind s l) []) = refl
  fromTerm∘toTerm (gen (Starkind s l) []) = refl
  fromTerm∘toTerm (gen (Unitreckind l p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
    cong₃ (λ A t u → gen (Unitreckind l p q) (A ∷ₜ t ∷ₜ u ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm u)
  fromTerm∘toTerm (gen Emptykind []) = refl
  fromTerm∘toTerm (gen (Emptyreckind p) (A ∷ₜ t ∷ₜ [])) =
    cong₂ (λ A t → gen (Emptyreckind p) (A ∷ₜ t ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t)
  fromTerm∘toTerm (gen Idkind (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
    cong₃ (λ A t u → gen Idkind (A ∷ₜ t ∷ₜ u ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm u)
  fromTerm∘toTerm (gen Reflkind []) = refl
  fromTerm∘toTerm (gen (Jkind p q) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ w ∷ₜ [])) =
    cong₆ (λ A t B u v w →
            gen (Jkind p q) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ w ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm B)
      (fromTerm∘toTerm u) (fromTerm∘toTerm v) (fromTerm∘toTerm w)
  fromTerm∘toTerm (gen (Kkind p) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ [])) =
    cong₅ (λ A t B u v → gen (Kkind p) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm B)
      (fromTerm∘toTerm u) (fromTerm∘toTerm v)
  fromTerm∘toTerm (gen (Boxcongkind s) (A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ [])) =
    cong₄ (λ A t u v → gen (Boxcongkind s) (A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t)
      (fromTerm∘toTerm u) (fromTerm∘toTerm v)

------------------------------------------------------------------------
-- Weakening properties

opaque

  -- Relating weakening of terms with weakening of the alternative
  -- term representation.

  wk≡wk′ : ∀ t → wk ρ t ≡ toTerm (wk′ ρ (fromTerm t))
  wk≡wk′ (var x) = refl
  wk≡wk′ (U x) = refl
  wk≡wk′ (ΠΣ⟨ b ⟩ p , q ▷ t ▹ t₁) =
    cong₂ (ΠΣ⟨ b ⟩ p , q ▷_▹_) (wk≡wk′ t) (wk≡wk′ t₁)
  wk≡wk′ (lam p t) = cong (lam p) (wk≡wk′ t)
  wk≡wk′ (t ∘⟨ p ⟩ t₁) = cong₂ _∘_ (wk≡wk′ t) (wk≡wk′ t₁)
  wk≡wk′ (prod x p t t₁) = cong₂ prod! (wk≡wk′ t) (wk≡wk′ t₁)
  wk≡wk′ (fst p t) = cong (fst p) (wk≡wk′ t)
  wk≡wk′ (snd p t) = cong (snd p) (wk≡wk′ t)
  wk≡wk′ (prodrec r p q t t₁ t₂) =
    cong₃ (prodrec r p q) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
  wk≡wk′ ℕ = refl
  wk≡wk′ zero = refl
  wk≡wk′ (suc t) = cong suc (wk≡wk′ t)
  wk≡wk′ (natrec p q r t t₁ t₂ t₃) =
    cong₄ (natrec p q r) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂) (wk≡wk′ t₃)
  wk≡wk′ (Unit x x₁) = refl
  wk≡wk′ (star x x₁) = refl
  wk≡wk′ (unitrec x p q t t₁ t₂) =
    cong₃ (unitrec x p q) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
  wk≡wk′ Empty = refl
  wk≡wk′ (emptyrec p t t₁) =
    cong₂ (emptyrec p) (wk≡wk′ t) (wk≡wk′ t₁)
  wk≡wk′ (Id t t₁ t₂) =
    cong₃ Id (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
  wk≡wk′ rfl = refl
  wk≡wk′ (J p q t t₁ t₂ t₃ t₄ t₅) =
    cong₆ (J p q) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
      (wk≡wk′ t₃) (wk≡wk′ t₄) (wk≡wk′ t₅)
  wk≡wk′ (K p t t₁ t₂ t₃ t₄) =
    cong₅ (K p) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
      (wk≡wk′ t₃) (wk≡wk′ t₄)
  wk≡wk′ ([]-cong x t t₁ t₂ t₃) =
    cong₄ []-cong! (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂) (wk≡wk′ t₃)

opaque mutual

  -- If two weakenings are equal under wkVar, then they are equal under
  -- wk′.

  wkVar-to-wk′ :
    (∀ x → wkVar ρ x ≡ wkVar ρ′ x) →
    ∀ (t : Term′ n) → wk′ ρ t ≡ wk′ ρ′ t
  wkVar-to-wk′ eq (var x)    = cong var (eq x)
  wkVar-to-wk′ eq (gen k ts) = cong (gen k) (wkVar-to-wkGen eq ts)

  wkVar-to-wkGen :
    (∀ x → wkVar ρ x ≡ wkVar ρ′ x) →
    ∀ {bs} ts → wkGen {bs = bs} ρ ts ≡ wkGen {bs = bs} ρ′ ts
  wkVar-to-wkGen eq []              = refl
  wkVar-to-wkGen eq (_∷ₜ_ {b} t ts) =
    cong₂ _∷ₜ_ (wkVar-to-wk′ (wkVar-lifts eq b) t)
      (wkVar-to-wkGen eq ts)

opaque

  -- Extensionally equal weakenings, if applied to a term,
  -- yield the same weakened term.  Or:
  -- If two weakenings are equal under wkVar, then they are equal under
  -- wk.

  wkVar-to-wk : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
              → (t : Term n) → wk ρ t ≡ wk ρ′ t
  wkVar-to-wk {ρ} {ρ′} eq t = begin
    wk ρ t                       ≡⟨ wk≡wk′ t ⟩
    toTerm (wk′ ρ (fromTerm t))  ≡⟨ cong toTerm (wkVar-to-wk′ eq _) ⟩
    toTerm (wk′ ρ′ (fromTerm t)) ≡˘⟨ wk≡wk′ t ⟩
    wk ρ′ t                      ∎

opaque mutual

  -- id is the identity renaming for the alternative term representation

  wk′-id : (t : Term′ n) → wk′ id t ≡ t
  wk′-id (var x)   = refl
  wk′-id (gen k ts) = cong (gen k) (wkGen-id ts)

  wkGen-id : ∀ {bs} ts → wkGen {m = n} {n} {bs} id ts ≡ ts
  wkGen-id []              = refl
  wkGen-id (_∷ₜ_ {b} t ts) =
    cong₂ _∷ₜ_ (trans (wkVar-to-wk′ (wkVar-lifts-id b) t) (wk′-id t))
      (wkGen-id ts)

opaque

  -- id is the identity renaming.

  wk-id : (t : Term n) → wk id t ≡ t
  wk-id t = begin
    wk id t                      ≡⟨ wk≡wk′ t ⟩
    toTerm (wk′ id (fromTerm t)) ≡⟨ cong toTerm (wk′-id _) ⟩
    toTerm (fromTerm t)          ≡⟨ toTerm∘fromTerm t ⟩
    t                            ∎

-- lift id  is also the identity renaming.

wk-lift-id : (t : Term (1+ n)) → wk (lift id) t ≡ t
wk-lift-id t = trans (wkVar-to-wk wkVar-lift-id t) (wk-id t)

opaque mutual

  -- The function wk′ commutes with composition.

  wk′-comp :
    (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (t : Term′ n) →
    wk′ ρ (wk′ ρ′ t) ≡ wk′ (ρ • ρ′) t
  wk′-comp ρ ρ′ (var x) = cong var (wkVar-comp ρ ρ′ x)
  wk′-comp ρ ρ′ (gen k ts) = cong (gen k) (wkGen-comp ρ ρ′ ts)

  wkGen-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) → ∀ {bs} g
             → wkGen ρ (wkGen ρ′ g) ≡ wkGen {bs = bs} (ρ • ρ′) g
  wkGen-comp ρ ρ′ []              = refl
  wkGen-comp ρ ρ′ (_∷ₜ_ {b} t ts) =
    cong₂ _∷ₜ_
      (trans (wk′-comp (liftn ρ b) (liftn ρ′ b) t)
        (wkVar-to-wk′ (wkVar-comps b ρ ρ′) t))
      (wkGen-comp ρ ρ′ ts)

opaque

  -- The function wk commutes with composition.

  wk-comp :
    (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (t : Term n) →
    wk ρ (wk ρ′ t) ≡ wk (ρ • ρ′) t
  wk-comp ρ ρ′ t = begin
    wk ρ (wk ρ′ t)                                           ≡⟨ cong (wk ρ) (wk≡wk′ t) ⟩
    wk ρ (toTerm (wk′ ρ′ (fromTerm t)))                      ≡⟨ wk≡wk′ _ ⟩
    toTerm (wk′ ρ (fromTerm (toTerm (wk′ ρ′ (fromTerm t))))) ≡⟨ cong (λ x → toTerm (wk′ ρ x)) (fromTerm∘toTerm _) ⟩
    toTerm (wk′ ρ (wk′ ρ′ (fromTerm t)))                     ≡⟨ cong toTerm (wk′-comp ρ ρ′ _) ⟩
    toTerm (wk′ (ρ • ρ′) (fromTerm t))                       ≡˘⟨ wk≡wk′ t ⟩
    wk (ρ • ρ′) t                                            ∎

opaque

  -- id is the right identity of weakening composition

  •-idʳ : (ρ : Wk m n) → ρ • id ≡ ρ
  •-idʳ id = refl
  •-idʳ (step ρ) = cong step (•-idʳ ρ)
  •-idʳ (lift ρ) = refl


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

------------------------------------------------------------------------
-- Substitution properties.

opaque

  -- Relating substitution of terms with susbtitution of the alternative
  -- term representation.

  subst≡subst′ : ∀ t → t [ σ ] ≡ toTerm (fromTerm t [ σ ]′)
  subst≡subst′ (var x) = sym (toTerm∘fromTerm _)
  subst≡subst′ (U x) = refl
  subst≡subst′ (ΠΣ⟨ b ⟩ p , q ▷ t ▹ t₁) =
    cong₂ (ΠΣ⟨ b ⟩ p , q ▷_▹_) (subst≡subst′ t) (subst≡subst′ t₁)
  subst≡subst′ (lam p t) = cong (lam p) (subst≡subst′ t)
  subst≡subst′ (t ∘⟨ p ⟩ t₁) =
    cong₂ _∘_ (subst≡subst′ t) (subst≡subst′ t₁)
  subst≡subst′ (prod x p t t₁) =
    cong₂ prod! (subst≡subst′ t) (subst≡subst′ t₁)
  subst≡subst′ (fst p t) = cong (fst p) (subst≡subst′ t)
  subst≡subst′ (snd p t) = cong (snd p) (subst≡subst′ t)
  subst≡subst′ (prodrec r p q t t₁ t₂) =
    cong₃ (prodrec r p q) (subst≡subst′ t)
      (subst≡subst′ t₁) (subst≡subst′ t₂)
  subst≡subst′ ℕ = refl
  subst≡subst′ zero = refl
  subst≡subst′ (suc t) = cong suc (subst≡subst′ t)
  subst≡subst′ (natrec p q r t t₁ t₂ t₃) =
    cong₄ (natrec p q r) (subst≡subst′ t)
      (subst≡subst′ t₁) (subst≡subst′ t₂) (subst≡subst′ t₃)
  subst≡subst′ (Unit x x₁) = refl
  subst≡subst′ (star x x₁) = refl
  subst≡subst′ (unitrec x p q t t₁ t₂) =
    cong₃ (unitrec x p q) (subst≡subst′ t)
      (subst≡subst′ t₁) (subst≡subst′ t₂)
  subst≡subst′ Empty = refl
  subst≡subst′ (emptyrec p t t₁) =
    cong₂ (emptyrec p) (subst≡subst′ t) (subst≡subst′ t₁)
  subst≡subst′ (Id t t₁ t₂) =
    cong₃ Id (subst≡subst′ t) (subst≡subst′ t₁) (subst≡subst′ t₂)
  subst≡subst′ rfl = refl
  subst≡subst′ (J p q t t₁ t₂ t₃ t₄ t₅) =
    cong₆ (J p q) (subst≡subst′ t) (subst≡subst′ t₁) (subst≡subst′ t₂)
      (subst≡subst′ t₃) (subst≡subst′ t₄) (subst≡subst′ t₅)
  subst≡subst′ (K p t t₁ t₂ t₃ t₄) =
    cong₅ (K p) (subst≡subst′ t) (subst≡subst′ t₁) (subst≡subst′ t₂)
      (subst≡subst′ t₃) (subst≡subst′ t₄)
  subst≡subst′ ([]-cong x t t₁ t₂ t₃) =
    cong₄ []-cong! (subst≡subst′ t) (subst≡subst′ t₁)
      (subst≡subst′ t₂) (subst≡subst′ t₃)

-- Two substitutions σ and σ′ are equal if they are pointwise equal,
-- i.e., agree on all variables.
--
--   ∀ x →  σ x ≡ σ′ x

-- If  σ = σ′  then  lift σ = lift σ′.

substVar-lift : (∀ x → σ x ≡ σ′ x) → ∀ x → liftSubst σ x ≡ liftSubst σ′ x

substVar-lift eq x0     = refl
substVar-lift eq (x +1) = cong wk1 (eq x)

substVar-lifts : (∀ x → σ x ≡ σ′ x) → ∀ n x → liftSubstn σ n x ≡ liftSubstn σ′ n x

substVar-lifts eq 0 x           = eq x
substVar-lifts eq (1+ n) x0     = refl
substVar-lifts eq (1+ n) (x +1) = cong wk1 (substVar-lifts eq n x)

-- If σ = σ′ then consSubst σ t = consSubst σ′ t.

consSubst-cong :
  ∀ {t} →
  (∀ x → σ x ≡ σ′ x) →
  ∀ x → consSubst σ t x ≡ consSubst σ′ t x
consSubst-cong eq x0     = refl
consSubst-cong eq (x +1) = eq x

opaque

  -- An η-law for consSubst.

  consSubst-η : ∀ x → consSubst (tail σ) (head σ) x ≡ σ x
  consSubst-η x0     = refl
  consSubst-η (_ +1) = refl

-- If σ = σ′ then wk1Subst σ = wk1Subst σ′.

wk1Subst-cong :
  (∀ x → σ x ≡ σ′ x) →
  ∀ x → wk1Subst σ x ≡ wk1Subst σ′ x
wk1Subst-cong eq x = cong wk1 (eq x)

opaque mutual

  -- If  σ = σ′  then  t [ σ ]′ = t [ σ′ ]′.

  substVar-to-subst′ : ((x : Fin n) → σ x ≡ σ′ x)
                     → (t : Term′ n) → t [ σ ]′ ≡ t [ σ′ ]′
  substVar-to-subst′ eq (var x)    = cong fromTerm (eq x)
  substVar-to-subst′ eq (gen k ts) = cong (gen k) (substVar-to-substGen eq ts)

  substVar-to-substGen : ∀ {bs} → ((x : Fin n) → σ x ≡ σ′ x)
                       → ∀ ts → substGen {bs = bs} σ ts ≡ substGen {bs = bs} σ′ ts
  substVar-to-substGen eq []              = refl
  substVar-to-substGen eq (_∷ₜ_ {b} t ts) =
    cong₂ _∷ₜ_ (substVar-to-subst′ (substVar-lifts eq b) t)
      (substVar-to-substGen eq ts)

opaque

  -- If  σ = σ′  then  t [ σ ] = t [ σ′ ].

  substVar-to-subst : ((x : Fin n) → σ x ≡ σ′ x)
                    → (t : Term n) → t [ σ ] ≡ t [ σ′ ]
  substVar-to-subst {σ} {σ′} eq t = begin
    t [ σ ]                     ≡⟨ subst≡subst′ t ⟩
    toTerm (fromTerm t [ σ ]′)  ≡⟨ cong toTerm (substVar-to-subst′ eq (fromTerm t)) ⟩
    toTerm (fromTerm t [ σ′ ]′) ≡˘⟨ subst≡subst′ t ⟩
    t [ σ′ ]                    ∎

-- lift id = id  (as substitutions)

subst-lift-id : (x : Fin (1+ n)) → (liftSubst idSubst) x ≡ idSubst x
subst-lift-id x0     = refl
subst-lift-id (x +1) = refl

subst-lifts-id : (n : Nat) → (x : Fin (n + m)) → (liftSubstn idSubst n) x ≡ idSubst x
subst-lifts-id 0 x = refl
subst-lifts-id (1+ n) x0 = refl
subst-lifts-id (1+ n) (x +1) = cong wk1 (subst-lifts-id n x)

opaque mutual

  -- idSubst is the identity substitution for the alternative term
  -- representation.

  subst′-id : (t : Term′ n) → t [ idSubst ]′ ≡ t
  subst′-id (var x) = refl
  subst′-id (gen k ts) = cong (gen k) (substGen-id ts)

  substGen-id : ∀ {bs} ts → substGen {m = n} {n} {bs} idSubst ts ≡ ts
  substGen-id []              = refl
  substGen-id (_∷ₜ_ {b} t ts) =
    cong₂ _∷ₜ_
      (trans (substVar-to-subst′ (subst-lifts-id b) t)
         (subst′-id t))
      (substGen-id ts)

opaque

  -- idSubst is the identity substitution.

  subst-id : (t : Term n) → t [ idSubst ] ≡ t
  subst-id t = begin
    t [ idSubst ]                    ≡⟨ subst≡subst′ t ⟩
    toTerm (fromTerm t [ idSubst ]′) ≡⟨ cong toTerm (subst′-id (fromTerm t)) ⟩
    toTerm (fromTerm t)              ≡⟨ toTerm∘fromTerm t ⟩
    t                                ∎

opaque

  -- The identity substitution is a left identity for _ₛ•ₛ_ (in a
  -- certain sense).

  idSubst-ₛ•ₛˡ : (x : Fin n) → (idSubst ₛ•ₛ σ) x ≡ σ x
  idSubst-ₛ•ₛˡ _ = subst-id _

opaque

  -- The identity substitution is a right identity for _ₛ•ₛ_ (in a
  -- certain sense).

  idSubst-ₛ•ₛʳ : (x : Fin n) → (σ ₛ•ₛ idSubst) x ≡ σ x
  idSubst-ₛ•ₛʳ _ = refl

opaque

  -- The substitution liftSubstn idSubst m does not have any effect.

  [idSubst⇑ⁿ]≡ :
    ∀ m {t : Term (m + n)} → t [ liftSubstn idSubst m ] ≡ t
  [idSubst⇑ⁿ]≡ m {t} =
    t [ liftSubstn idSubst m ]  ≡⟨ substVar-to-subst (subst-lifts-id m) t ⟩
    t [ idSubst ]               ≡⟨ subst-id _ ⟩
    t                           ∎

-- Correctness of composition of weakening and substitution.

-- Composition of liftings is lifting of the composition.
-- lift ρ •ₛ lift σ = lift (ρ •ₛ σ)

subst-lift-•ₛ : ∀ t
              → t [ lift ρ •ₛ liftSubst σ ]
              ≡ t [ liftSubst (ρ •ₛ σ) ]
subst-lift-•ₛ =
  substVar-to-subst (λ { x0 → refl ; (x +1) → sym (wk1-wk≡lift-wk1 _ _)})

helper1 : (n : Nat) (x : Fin (1+ n + m)) →
      (lift (liftn ρ n) •ₛ liftSubst (liftSubstn σ n)) x ≡
      liftSubst (liftSubstn (ρ •ₛ σ) n) x
helper1 0      x0     = refl
helper1 0      (x +1) = sym (wk1-wk≡lift-wk1 _ _)
helper1 (1+ n) x0     = refl
helper1 (1+ n) (x +1) = trans (sym (wk1-wk≡lift-wk1 _ _)) (cong wk1 (helper1 n x))

subst-lifts-•ₛ : ∀ n t
              → t [ liftn ρ n •ₛ liftSubstn σ n ]
              ≡ t [ liftSubstn (ρ •ₛ σ) n ]
subst-lifts-•ₛ 0 t = refl
subst-lifts-•ₛ (1+ n) t = substVar-to-subst (helper1 n) t

subst′-lifts-•ₛ : ∀ n t
              → t [ liftn ρ n •ₛ liftSubstn σ n ]′
              ≡ t [ liftSubstn (ρ •ₛ σ) n ]′
subst′-lifts-•ₛ 0 t = refl
subst′-lifts-•ₛ (1+ n) t = substVar-to-subst′ (helper1 n) t


-- lift σ ₛ• lift ρ = lift (σ ₛ• ρ)

subst-lift-ₛ• : ∀ t
              → t [ liftSubst σ ₛ• lift ρ ]
              ≡ t [ liftSubst (σ ₛ• ρ) ]
subst-lift-ₛ• = substVar-to-subst (λ { x0 → refl ; (x +1) → refl})

helper2 : (n : Nat) → (x : Fin (1+ n + m))
        → liftSubst (liftSubstn σ n) (wkVar (lift (liftn ρ n)) x) ≡
          liftSubst (liftSubstn (λ x₁ → σ (wkVar ρ x₁)) n) x
helper2 0 x0          = refl
helper2 0 (x +1)      = refl
helper2 (1+ n) x0     = refl
helper2 (1+ n) (x +1) = cong wk1 (helper2 n x)

subst-lifts-ₛ• : ∀ n t
              → t [ liftSubstn σ n ₛ• liftn ρ n ]
              ≡ t [ liftSubstn (σ ₛ• ρ) n ]
subst-lifts-ₛ• 0 t = refl
subst-lifts-ₛ• (1+ n) t = substVar-to-subst (helper2 n) t

opaque

  -- A variant of the above property for the alternative term
  -- representation.

  subst′-lifts-ₛ• : ∀ n t
                → t [ liftSubstn σ n ₛ• liftn ρ n ]′
                ≡ t [ liftSubstn (σ ₛ• ρ) n ]′
  subst′-lifts-ₛ• 0 t = refl
  subst′-lifts-ₛ• (1+ n) t = substVar-to-subst′ (helper2 n) t



opaque mutual

  -- Soundness of weakening-substitution composition for the alternative
  -- term representation.

  wk′-subst′ : ∀ t → wk′ ρ (t [ σ ]′) ≡ t [ ρ •ₛ σ ]′
  wk′-subst′ {ρ} {σ} (var x) = begin
    wk′ ρ (var x [ σ ]′)                       ≡⟨⟩
    wk′ ρ (fromTerm (σ x))                     ≡˘⟨ fromTerm∘toTerm _ ⟩
    fromTerm (toTerm (wk′ ρ (fromTerm (σ x)))) ≡˘⟨ cong fromTerm (wk≡wk′ (σ x)) ⟩
    fromTerm (wk ρ (σ x))                      ≡⟨⟩
    (var x [ ρ •ₛ σ ]′)                        ∎
  wk′-subst′ (gen k ts) = cong (gen k) (wkGen-substGen ts)

  wkGen-substGen : ∀ {bs} ts → wkGen ρ (substGen σ ts) ≡ substGen {bs = bs} (ρ •ₛ σ) ts
  wkGen-substGen []              = refl
  wkGen-substGen {ρ} {σ} (_∷ₜ_ {b} t ts) =
    cong₂ _∷ₜ_ (trans (wk′-subst′ t) (subst′-lifts-•ₛ b t)) (wkGen-substGen ts)

opaque

  -- Soundness of weakening-substitution composition.

  wk-subst : ∀ t → wk ρ (t [ σ ]) ≡ t [ ρ •ₛ σ ]
  wk-subst {ρ} {σ} t = begin
    wk ρ (t [ σ ])                                         ≡⟨ cong (wk ρ) (subst≡subst′ t) ⟩
    wk ρ (toTerm (fromTerm t [ σ ]′))                      ≡⟨ wk≡wk′ _ ⟩
    toTerm (wk′ ρ (fromTerm (toTerm (fromTerm t [ σ ]′)))) ≡⟨ cong (λ x → toTerm (wk′ ρ x)) (fromTerm∘toTerm _ ) ⟩
    toTerm (wk′ ρ (fromTerm t [ σ ]′))                     ≡⟨ cong toTerm (wk′-subst′ (fromTerm t)) ⟩
    toTerm (fromTerm t [ ρ •ₛ σ ]′)                        ≡˘⟨ subst≡subst′ t ⟩
    t [ ρ •ₛ σ ]                                           ∎

-- _[ σ ] ∘ wk ρ = _[ σ •ₛ ρ ]

mutual

  -- Soundness of substitution-weakening composition for the alternative
  -- term representation.

  subst′-wk′ : ∀ t → wk′ ρ t [ σ ]′ ≡ t [ σ ₛ• ρ ]′
  subst′-wk′ (var x) = refl
  subst′-wk′ (gen k ts) = cong (gen k) (substGen-wkGen ts)

  substGen-wkGen : ∀ {bs} ts → substGen σ (wkGen ρ ts) ≡ substGen {bs = bs} (σ ₛ• ρ) ts
  substGen-wkGen []              = refl
  substGen-wkGen (_∷ₜ_ {b} t ts) =
    cong₂ _∷ₜ_ (trans (subst′-wk′ t) (subst′-lifts-ₛ• b t))
      (substGen-wkGen ts)

opaque

  -- Soundness of substitution-weakening composition.

  subst-wk : ∀ t → wk ρ t [ σ ] ≡ t [ σ ₛ• ρ ]
  subst-wk {ρ} {σ} t = begin
    wk ρ t [ σ ]                                           ≡⟨ cong (_[ σ ]) (wk≡wk′ t) ⟩
    toTerm (wk′ ρ (fromTerm t)) [ σ ]                      ≡⟨ subst≡subst′ (toTerm (wk′ ρ (fromTerm t))) ⟩
    toTerm (fromTerm (toTerm (wk′ ρ (fromTerm t))) [ σ ]′) ≡⟨ cong (λ x → toTerm (x [ σ ]′)) (fromTerm∘toTerm (wk′ ρ (fromTerm t))) ⟩
    toTerm (wk′ ρ (fromTerm t) [ σ ]′)                     ≡⟨ cong toTerm (subst′-wk′ (fromTerm t)) ⟩
    toTerm (fromTerm t [ σ ₛ• ρ ]′)                        ≡˘⟨ subst≡subst′ t ⟩
    t [ σ ₛ• ρ ]                                           ∎

opaque

  -- Applying wk1Subst σ is the same thing as applying σ and then
  -- weakening one step.

  wk1Subst-wk1 : ∀ t → t [ wk1Subst σ ] ≡ wk1 (t [ σ ])
  wk1Subst-wk1 {σ} t =
    t [ wk1Subst σ ]    ≡⟨⟩
    t [ step id •ₛ σ ]  ≡˘⟨ wk-subst t ⟩
    wk1 (t [ σ ])       ∎

opaque

  -- Applying liftSubst σ to wk1 t amounts to the same thing as first
  -- applying σ and then weakening the result one step.

  wk1-liftSubst : ∀ t → wk1 t [ liftSubst σ ] ≡ wk1 (t [ σ ])
  wk1-liftSubst {σ} t =
    wk1 t [ liftSubst σ ]         ≡⟨ subst-wk t ⟩
    t [ liftSubst σ ₛ• step id ]  ≡⟨⟩
    t [ wk1Subst σ ]              ≡⟨ wk1Subst-wk1 t ⟩
    wk1 (t [ σ ])                 ∎

-- Composition of liftings is lifting of the composition.

wk-subst-lift : (G : Term (1+ n))
              → wk (lift ρ) (G [ liftSubst σ ])
              ≡ G [ liftSubst (ρ •ₛ σ) ]
wk-subst-lift G = trans (wk-subst G) (subst-lift-•ₛ G)

-- Renaming with ρ is the same as substituting with ρ turned into a substitution.

wk≡subst : (ρ : Wk m n) (t : Term n) → wk ρ t ≡ t [ toSubst ρ ]
wk≡subst ρ t = trans (cong (wk ρ) (sym (subst-id t))) (wk-subst t)

opaque

  -- The function toSubst commutes, in a certain sense, with lifting.

  toSubst-liftn : ∀ k x → toSubst (liftn ρ k) x ≡ (toSubst ρ ⇑[ k ]) x
  toSubst-liftn 0      _      = refl
  toSubst-liftn (1+ _) x0     = refl
  toSubst-liftn (1+ k) (x +1) =
    cong wk1 $ toSubst-liftn k x

opaque

  -- The application of a lifted weakening can be expressed as the
  -- application of a lifted substitution.

  wk-liftn : ∀ k {t} → wk (liftn ρ k) t ≡ t [ toSubst ρ ⇑[ k ] ]
  wk-liftn {ρ} k {t} =
    wk (liftn ρ k) t           ≡⟨ wk≡subst _ _ ⟩
    t [ toSubst (liftn ρ k) ]  ≡⟨ substVar-to-subst (toSubst-liftn k) t ⟩
    t [ toSubst ρ ⇑[ k ] ]     ∎

-- Composition of substitutions.

-- Composition of liftings is lifting of the composition.

substCompLift : ∀ x
              → (liftSubst σ ₛ•ₛ liftSubst σ′) x
              ≡ (liftSubst (σ ₛ•ₛ σ′)) x
substCompLift                    x0    = refl
substCompLift {σ = σ} {σ′ = σ′} (x +1) = trans (subst-wk (σ′ x)) (sym (wk-subst (σ′ x)))

substCompLifts : ∀ n x
              → (liftSubstn σ n ₛ•ₛ liftSubstn σ′ n) x
              ≡ (liftSubstn (σ ₛ•ₛ σ′) n) x
substCompLifts                   0       x     = refl
substCompLifts                   (1+ n)  x0    = refl
substCompLifts {σ = σ} {σ′ = σ′} (1+ n) (x +1) =
  trans (substCompLift {σ = liftSubstn σ n} {σ′ = liftSubstn σ′ n} (x +1))
        (cong wk1 (substCompLifts n x))


opaque mutual

  -- Soundness of the composition of substitutions for the alternative
  -- term representation.

  subst′CompEq : ∀ (t : Term′ n)
               → (t [ σ′ ]′) [ σ ]′ ≡ t [ σ ₛ•ₛ σ′ ]′
  subst′CompEq {σ′} {σ} (var x) = begin
    fromTerm (σ′ x) [ σ ]′                     ≡˘⟨ fromTerm∘toTerm _ ⟩
    fromTerm (toTerm (fromTerm (σ′ x) [ σ ]′)) ≡˘⟨ cong fromTerm (subst≡subst′ (σ′ x)) ⟩
    fromTerm (σ′ x [ σ ])                      ∎
  subst′CompEq (gen k ts) = cong (gen k) (substGenCompEq ts)

  substGenCompEq : ∀ {bs} ts
                 → substGen σ (substGen σ′ ts) ≡ substGen {bs = bs} (σ ₛ•ₛ σ′) ts
  substGenCompEq []              = refl
  substGenCompEq (_∷ₜ_ {b} t ts) =
    cong₂ _∷ₜ_
      (trans (subst′CompEq t) (substVar-to-subst′ (substCompLifts b) t))
      (substGenCompEq ts)

opaque

  -- Soundness of the composition of substitutions.

  substCompEq : ∀ (t : Term n)
              → (t [ σ′ ]) [ σ ] ≡ t [ σ ₛ•ₛ σ′ ]
  substCompEq {σ′} {σ} t = begin
    (t [ σ′ ]) [ σ ]                                       ≡⟨ subst≡subst′ (t [ σ′ ]) ⟩
    toTerm (fromTerm (t [ σ′ ]) [ σ ]′)                    ≡⟨ cong (λ x → toTerm (fromTerm x [ σ ]′)) (subst≡subst′ t) ⟩
    toTerm (fromTerm (toTerm (fromTerm t [ σ′ ]′)) [ σ ]′) ≡⟨ cong (λ x → toTerm (x [ σ ]′)) (fromTerm∘toTerm (fromTerm t [ σ′ ]′)) ⟩
    toTerm ((fromTerm t [ σ′ ]′) [ σ ]′)                   ≡⟨ cong toTerm (subst′CompEq (fromTerm t)) ⟩
    toTerm (fromTerm t [ σ ₛ•ₛ σ′ ]′)                      ≡˘⟨ subst≡subst′ t ⟩
    t [ σ ₛ•ₛ σ′ ]                                         ∎

-- Weakening single substitutions.

-- Pulling apart a weakening composition in specific context _[a].

wk-comp-subst : ∀ {a : Term m} (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) G
  → wk (lift (ρ • ρ′)) G [ a ]₀ ≡ wk (lift ρ) (wk (lift ρ′) G) [ a ]₀

wk-comp-subst {a = a} ρ ρ′ G =
  cong (λ x → x [ a ]₀) (sym (wk-comp (lift ρ) (lift ρ′) G))

-- Pushing a weakening into a single substitution.
-- ρ (t[a]) = ((lift ρ) t)[ρ a]

wk-β : ∀ {a : Term m} t → wk ρ (t [ a ]₀) ≡ wk (lift ρ) t [ wk ρ a ]₀
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t)
               (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))

-- Pushing a weakening into a single shifting substitution.
-- If  ρ′ = lift ρ  then  ρ′(t[a]↑) = ρ′(t) [ρ′(a)]↑

wk-β↑ : ∀ {a : Term (1+ n)} t {ρ : Wk m n} → wk (lift ρ) (t [ a ]↑) ≡ wk (lift ρ) t [ wk (lift ρ) a ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t)
                (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))

-- Pushing a weakening into a double shifting substitution.

wk-β↑² : ∀ {a} t → wk (lift (lift ρ)) (t [ a ]↑²) ≡ wk (lift ρ) t [ wk (lift (lift ρ)) a ]↑²
wk-β↑² t = trans (wk-subst t) (sym (trans (subst-wk t)
                 (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))


-- Composing a singleton substitution and a lifted substitution.
-- sg u ∘ lift σ = cons id u ∘ lift σ = cons σ u

substVarSingletonComp : ∀ {u} (x : Fin (1+ n))
  → (sgSubst u ₛ•ₛ liftSubst σ) x ≡ (consSubst σ u) x
substVarSingletonComp x0 = refl
substVarSingletonComp {σ = σ} (x +1) = trans (subst-wk (σ x)) (subst-id (σ x))

-- The same again, as action on a term t.

substSingletonComp : ∀ {a} t
  → t [ sgSubst a ₛ•ₛ liftSubst σ ] ≡ t [ consSubst σ a ]
substSingletonComp = substVar-to-subst substVarSingletonComp

-- A single substitution after a lifted substitution.
-- ((lift σ) G)[t] = (cons σ t)(G)

singleSubstComp : ∀ t (σ : Subst m n) G
                 → (G [ liftSubst σ ]) [ t ]₀
                 ≡ G [ consSubst σ t ]
singleSubstComp t σ G = trans (substCompEq G) (substSingletonComp G)

-- A single substitution after a lifted substitution (with weakening).
-- ((lift (ρ ∘ σ)) G)[t]₀ = (cons (ρ ∘ σ) t)(G)

singleSubstWkComp : ∀ t (σ : Subst m n) G
               → wk (lift ρ) (G [ liftSubst σ ]) [ t ]₀
               ≡ G [ consSubst (ρ •ₛ σ) t ]
singleSubstWkComp t σ G =
  trans (cong (_[ sgSubst t ])
              (trans (wk-subst G) (subst-lift-•ₛ G)))
        (trans (substCompEq G) (substSingletonComp G))

-- Pushing a substitution into a single substitution.

singleSubstLift : ∀ G t
                → G [ t ]₀ [ σ ]
                ≡ G [ liftSubst σ ] [ t [ σ ] ]₀
singleSubstLift G t =
  trans (substCompEq G)
        (trans (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G)
                      (sym (substSingletonComp G)))
               (sym (substCompEq G)))

-- More specific laws.

idWkLiftSubstLemma : ∀ (σ : Subst m n) G
  → wk (lift (step id)) (G [ liftSubst σ ]) [ var x0 ]₀
  ≡ G [ liftSubst σ ]
idWkLiftSubstLemma σ G =
  trans (singleSubstWkComp (var x0) σ G)
        (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G)

substVarComp↑ : ∀ {t} (σ : Subst m n) x
  → (consSubst (wk1Subst idSubst) (t [ liftSubst σ ]) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst σ ₛ•ₛ consSubst (wk1Subst idSubst) t) x
substVarComp↑ σ x0 = refl
substVarComp↑ σ (x +1) = trans (subst-wk (σ x)) (sym (wk≡subst (step id) (σ x)))

singleSubstLift↑ : ∀ (σ : Subst m n) G t
                 → G [ t ]↑ [ liftSubst σ ]
                 ≡ G [ liftSubst σ ] [ t [ liftSubst σ ] ]↑
singleSubstLift↑ σ G t =
  trans (substCompEq G)
        (sym (trans (substCompEq G) (substVar-to-subst (substVarComp↑ σ) G)))

substConsComp : ∀ {t G}
       → G [ consSubst (λ x → σ (x +1)) (t [ tail σ ]) ]
       ≡ G [ consSubst (λ x → var (x +1)) (wk1 t) ] [ σ ]
substConsComp {t = t} {G = G} =
  trans (substVar-to-subst (λ { x0 → sym (subst-wk t) ; (x +1) → refl }) G)
        (sym (substCompEq G))

wkSingleSubstId : (F : Term (1+ n)) → (wk (lift (step id)) F) [ var x0 ]₀ ≡ F
wkSingleSubstId F =
  trans (subst-wk F)
        (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) F)
               (subst-id F))

wkSingleSubstWk1 : (F : Term (1+ n))
                 → wk (lift (step (step id))) F [ var (x0 +1) ]₀ ≡ wk1 F
wkSingleSubstWk1 F =
  trans (subst-wk F)
        (trans (substVar-to-subst (λ {x0 → refl; (x +1) → refl}) F)
               (sym (wk≡subst (step id) F)))

cons-wk-subst : ∀ (ρ : Wk m n) (σ : Subst n ℓ) a t
       → t [ sgSubst a ₛ• lift ρ ₛ•ₛ liftSubst σ ]
       ≡ t [ consSubst (ρ •ₛ σ) a ]
cons-wk-subst ρ σ a = substVar-to-subst
  (λ { x0 → refl
     ; (x +1) → trans (subst-wk (σ x)) (sym (wk≡subst ρ (σ x))) })

-- A specific equation on weakenings used for the reduction of natrec.

wk-β-natrec : ∀ (ρ : Wk m n) (G : Term (1+ n))
            → wk (lift (lift ρ)) (G [ suc (var x1) ]↑²)
            ≡ wk (lift ρ) G [ suc (var x1) ]↑²
wk-β-natrec ρ G = wk-β↑² {ρ = ρ} G

-- A specific equation on eakenings used for the reduction of prodrec.

wk-β-prodrec :
  ∀ {s} (ρ : Wk m n) (A : Term (1+ n)) →
  wk (lift (lift ρ)) (A [ prod s p (var x1) (var x0) ]↑²) ≡
  wk (lift ρ) A [ prod s p (var x1) (var x0) ]↑²
wk-β-prodrec {p = p} ρ A = wk-β↑² {ρ = ρ} A

wk-β-doubleSubst : ∀ (ρ : Wk m n) (s : Term (2+ n)) (t u : Term n)
                 → wk ρ (s [ u , t ]₁₀)
                 ≡ wk (lift (lift ρ)) s [ wk ρ u , wk ρ t ]₁₀
wk-β-doubleSubst ρ s t u =
 begin
    wk ρ (s [ σₜ t u ])
       ≡⟨ wk-subst s ⟩
     s [ ρ •ₛ (σₜ t u) ]
       ≡⟨ substVar-to-subst eq′ s ⟩
     s [ (σₜ (wk ρ t) (wk ρ u)) ₛ• (lift (lift ρ)) ]
       ≡⟨ sym (subst-wk s) ⟩
     wk (lift (lift ρ)) s [ wk ρ u , wk ρ t ]₁₀ ∎
  where
    σₜ : (x y : Term ℓ) → Subst ℓ (2+ ℓ)
    σₜ x y = consSubst (consSubst idSubst y) x
    eq′ : ∀ x
       → substVar ((ρ •ₛ (σₜ t u))) x
       ≡ substVar (σₜ (wk ρ t) (wk ρ u)) (wkVar (lift (lift ρ)) x)
    eq′ x0      = refl
    eq′ (x0 +1) = refl
    eq′ (x +2)  = refl

natrecSucCaseLemma : (x : Fin (1+ n))
  → (liftSubstn σ 2 ₛ•ₛ consSubst (wkSubst 2 idSubst) (suc (var x1))) x
  ≡ (consSubst (wkSubst 2 idSubst) (suc (var x1)) ₛ•ₛ liftSubst σ) x
natrecSucCaseLemma x0 = refl
natrecSucCaseLemma {σ = σ} (_+1 x) = begin
  wk1 (wk1 (σ x))
    ≡⟨ wk-comp (step id) (step id) (σ x) ⟩
  wk (step id • step id) (σ x)
    ≡⟨ wk≡subst (step id • step id) (σ x) ⟩
  σ x [ wkSubst 2 idSubst ]
    ≡⟨⟩
  σ x [ consSubst (wkSubst 2 idSubst) (suc (var x1)) ₛ• step id ]
    ≡˘⟨ subst-wk (σ x) ⟩
  wk1 (σ x) [ consSubst (wkSubst 2 idSubst) (suc (var x1)) ] ∎

natrecSucCase : ∀ (σ : Subst m n) F
              → F [ suc (var x1) ]↑² [ liftSubstn σ 2 ]
              ≡ F [ liftSubst σ ] [ suc (var x1) ]↑²
natrecSucCase σ F = begin
  F [ suc (var x1) ]↑² [ liftSubstn σ 2 ]
    ≡⟨ substCompEq F ⟩
  F [ liftSubstn σ 2 ₛ•ₛ σₛ ]
    ≡⟨ substVar-to-subst natrecSucCaseLemma F ⟩
  F [ σₛ ₛ•ₛ liftSubst σ ]
    ≡˘⟨ substCompEq F ⟩
  F [ liftSubst σ ] [ suc (var x1) ]↑² ∎
  where
  σₛ : Subst (2+ ℓ) (1+ ℓ)
  σₛ = consSubst (wkSubst 2 idSubst) (suc (var x1))

natrecIrrelevantSubstLemma : ∀ p q r F z s m (σ : Subst ℓ n) (x : Fin (1+ n))
  → (sgSubst (natrec p q r
               (F [ liftSubst σ ])
               (z [ σ ])
               (s [ liftSubstn σ 2 ])
               m
             )
     ₛ•ₛ liftSubst (sgSubst m)
     ₛ•ₛ liftSubst (liftSubst σ)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst σ (suc m)) x
natrecIrrelevantSubstLemma p q r F z s m σ x0 =
  cong suc (trans (subst-wk m) (subst-id m))
natrecIrrelevantSubstLemma p q r F z s m σ (x +1) =
  trans (subst-wk (wk (step id) (σ x)))
           (trans (subst-wk (σ x))
                     (subst-id (σ x)))

natrecIrrelevantSubst : ∀ p q r F z s m (σ : Subst ℓ n)
  → F [ consSubst σ (suc m) ]
  ≡ wk1 (F [ suc (var x0) ]↑)
           [ liftSubstn σ 2 ]
           [ liftSubst (sgSubst m) ]
           [ natrec p q r (F [ liftSubst σ ]) (z [ σ ]) (s [ liftSubstn σ 2 ]) m ]₀
natrecIrrelevantSubst p q r F z s m σ =
  sym (trans (substCompEq (_[ liftSubstn σ 2 ]
        (wk (step id)
         (F [ consSubst (tail idSubst) (suc (var x0)) ]))))
         (trans (substCompEq (wk (step id)
        (F [ consSubst (tail idSubst) (suc (var x0)) ])))
        (trans
           (subst-wk (F [ consSubst (tail idSubst) (suc (var x0)) ]))
           (trans (substCompEq F)
                     (substVar-to-subst (natrecIrrelevantSubstLemma p q r F z s m σ) F)))))

natrecIrrelevantSubstLemma′ : ∀ (p q r : M) F z s n (x : Fin (1+ m))
  → (sgSubst (natrec p q r F z s n)
     ₛ•ₛ liftSubst (sgSubst n)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst var (suc n)) x
natrecIrrelevantSubstLemma′ p q r F z s n x0 =
  cong suc (trans (subst-wk n) (subst-id n))
natrecIrrelevantSubstLemma′ p q r F z s n (x +1) = refl

natrecIrrelevantSubst′ : ∀ p q r (F : Term (1+ m)) z s n
  → wk1 (F [ suc (var x0) ]↑) [ (liftSubst (sgSubst n)) ] [ natrec p q r F z s n ]₀
  ≡ F [ suc n ]₀
natrecIrrelevantSubst′ p q r F z s n =
  trans (substCompEq (wk (step id)
                         (F [ consSubst (tail idSubst) (suc (var x0)) ])))
        (trans (subst-wk (F [ consSubst (tail idSubst) (suc (var x0)) ]))
               (trans (substCompEq F)
                      (substVar-to-subst (natrecIrrelevantSubstLemma′ p q r F z s n) F)))

cons0wkLift1-id : ∀ (σ : Subst m n) G
    → (wk (lift (step id)) (G [ liftSubst σ ])) [ var x0 ]₀
    ≡ G [ liftSubst σ ]
cons0wkLift1-id σ G =
  trans (subst-wk (G [ liftSubst σ ]))
        (trans (substVar-to-subst (λ { x0 → refl ; (x +1) → refl })
                                  (G [ liftSubst σ ]))
               (subst-id (G [ liftSubst σ ])))

substConsId : ∀ {t} G
        → G [ consSubst σ (t [ σ ]) ]
        ≡ G [ t ]₀ [ σ ]
substConsId G =
  sym (trans (substCompEq G)
             (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) G))

substConsTailId : ∀ {G t}
                → G [ consSubst (tail σ) (t [ σ ]) ]
                ≡ G [ consSubst (tail idSubst) t ] [ σ ]
substConsTailId {G = G} =
  trans (substVar-to-subst (λ { x0 → refl
                            ; (x +1) → refl }) G)
        (sym (substCompEq G))

substConcatSingleton′ : ∀ {a} t
                      → t [ σ ₛ•ₛ sgSubst a ]
                      ≡ t [ consSubst σ (a [ σ ]) ]
substConcatSingleton′ t = substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t

step-consSubst : ∀ t → wk (step ρ) t [ consSubst σ u ] ≡ wk ρ t [ σ ]
step-consSubst {ρ} {σ} {u} t = begin
  wk (step ρ) t [ consSubst σ u ] ≡⟨ subst-wk t ⟩
  t [ consSubst σ u ₛ• step ρ ]   ≡⟨ substVar-to-subst (λ _ → refl) t ⟩
  t [ σ ₛ• ρ ]                    ≡˘⟨ subst-wk t ⟩
  wk ρ t [ σ ]                    ∎


wk1-tail : (t : Term n) → wk1 t [ σ ] ≡ t [ tail σ ]
wk1-tail {σ = σ} t = begin
  wk1 t [ σ ]          ≡⟨⟩
  wk (step id) t [ σ ] ≡⟨ subst-wk t ⟩
  t [ σ ₛ• step id ]   ≡⟨⟩
  t [ tail σ ]         ∎

wk1-tailId : (t : Term n) → wk1 t ≡ t [ tail idSubst ]
wk1-tailId t = trans (sym (subst-id (wk1 t))) (subst-wk t)

wk2-tail : (t : Term n) → wk2 t [ σ ] ≡ t [ tail (tail σ) ]
wk2-tail {σ = σ} t = begin
  wk2 t [ σ ]          ≡⟨ wk1-tail (wk1 t) ⟩
  wk1 t [ tail σ ]     ≡⟨ wk1-tail t ⟩
  t [ tail (tail σ) ]  ∎

wk2-tail-B′ : ∀ (W : BindingType) (F : Term n) (G : Term (1+ n))
           → ⟦ W ⟧ wk1 (wk1 F) [ σ ] ▹ (wk (lift (step (step id))) G [ liftSubst σ ])
           ≡ ⟦ W ⟧ F [ tail (tail σ) ] ▹ (G [ liftSubst (tail (tail σ)) ])
wk2-tail-B′ {n} {σ = σ} W F G = begin
  ⟦ W ⟧ wk1 (wk1 F) [ σ ] ▹ (wk (lift (step (step id))) G [ liftSubst σ ])
    ≡⟨ cong₂ (⟦ W ⟧_▹_) (wk1-tail (wk1 F)) (subst-wk G) ⟩
  ⟦ W ⟧ wk1 F [ tail σ ] ▹ (G [ liftSubst σ ₛ• lift (step (step id)) ])
    ≡⟨ cong₂ (⟦ W ⟧_▹_) (wk1-tail F) (substVar-to-subst eq′ G) ⟩
  ⟦ W ⟧ F [ tail (tail σ) ] ▹ (G [ liftSubst (tail (tail σ)) ]) ∎
  where
  eq′ :
    (x : Fin (1+ n)) →
    (liftSubst σ ₛ• lift (step (step id))) x ≡
    liftSubst (tail (tail σ)) x
  eq′ x0 = refl
  eq′ (x +1) = refl

wk2-tail-B : ∀ (W : BindingType) (F : Term n) (G : Term (1+ n))
           → ⟦ W ⟧ wk1 (wk1 F) [ σ ] ▹ (wk (lift (step (step id))) G [ liftSubst σ ])
           ≡ ⟦ W ⟧ F ▹ G [ tail (tail σ) ]
wk2-tail-B (BΠ p q)   F G = wk2-tail-B′ (BΠ p q)   F G
wk2-tail-B (BΣ m p q) F G = wk2-tail-B′ (BΣ m p q) F G

wk2-B : ∀ (W : BindingType) (F : Term n) (G : Term (1+ n))
      → ⟦ W ⟧ wk1 (wk1 F) ▹ wk (lift (step (step id))) G
      ≡ wk1 (wk1 (⟦ W ⟧ F ▹ G))
wk2-B (BΠ p q) F G = cong (Π p , q ▷ _ ▹_) (sym (wk-comp _ _ G))
wk2-B (BΣ s p q) F G = cong (Σ⟨ s ⟩ p , q ▷ _ ▹_) (sym (wk-comp _ _ G))

step-sgSubst : ∀ (t : Term n) t′ → wk (step ρ) t [ t′ ]₀ ≡ wk ρ t
step-sgSubst t t′ = trans (step-consSubst t) (subst-id _)

wk1-sgSubst : ∀ (t : Term n) t' → (wk1 t) [ t' ]₀ ≡ t
wk1-sgSubst t t' = trans (step-sgSubst t t') (wk-id t)

opaque

  -- Weakening twice and then substituting something for the two new
  -- variables amounts to the same thing as doing nothing.

  wk2-[,] : wk2 t [ u , v ]₁₀ ≡ t
  wk2-[,] {t} {u} {v} =
    wk2 t [ u , v ]₁₀  ≡⟨ wk2-tail t ⟩
    t [ idSubst ]      ≡⟨ subst-id _ ⟩
    t                  ∎

opaque

  -- A variant of wk2-[,] for wk₂.

  wk₂-[,] : wk₂ t [ u , v ]₁₀ ≡ t
  wk₂-[,] {t} {u} {v} =
    wk₂ t [ u , v ]₁₀  ≡⟨ subst-wk t ⟩
    t [ idSubst ]      ≡⟨ subst-id _ ⟩
    t                  ∎

-- Substituting variable one into t using _[_]↑² amounts to the same
-- thing as applying wk1 to t.

[1]↑² : t [ var x1 ]↑² ≡ wk1 t
[1]↑² {t = t} =
  t [ consSubst (λ x → var (x +2)) (var x1) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                     x0     → refl
                                                     (_ +1) → refl) ⟩
  t [ (λ x → var (x +1)) ]                     ≡˘⟨ wk≡subst _ _ ⟩
  wk1 t                                        ∎

-- Substituting wk1 u into t using _[_]↑² amounts to the same thing as
-- substituting u into t using _[_]↑ and then weakening one step.

[wk1]↑² : (t : Term (1 + n)) → t [ wk1 u ]↑² ≡ wk1 (t [ u ]↑)
[wk1]↑² {u = u} t =
  t [ consSubst (λ x → var (x +2)) (wk1 u) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                      x0     → refl
                                                      (_ +1) → refl) ⟩
  t [ wk1 ∘→ consSubst (λ x → var (x +1)) u ] ≡˘⟨ wk-subst t ⟩
  wk1 (t [ consSubst (λ x → var (x +1)) u ])  ∎

subst-β-prodrec :
  ∀ {s} (A : Term (1+ n)) (σ : Subst m n) →
  A [ prod s p (var x1) (var x0) ]↑² [ liftSubstn σ 2 ] ≡
  A [ liftSubst σ ] [ prod s p (var x1) (var x0) ]↑²
subst-β-prodrec {n = n} A σ = begin
   A [ t₁′ ]↑² [ liftSubstn σ 2 ]
     ≡⟨ substCompEq A ⟩
   A [ liftSubstn σ 2 ₛ•ₛ consSubst (wkSubst 2 idSubst) t₁′ ]
     ≡⟨ substVar-to-subst varEq A ⟩
   A [ consSubst (wkSubst 2 idSubst) t₂′ ₛ•ₛ liftSubst σ ]
     ≡˘⟨ substCompEq A ⟩
   A [ liftSubst σ ] [ t₂′ ]↑² ∎
   where
   t₁′ = prod! (var (x0 +1)) (var x0)
   t₂′ = prod! (var (x0 +1)) (var x0)
   varEq :
     (x : Fin (1+ n)) →
     (liftSubstn σ 2 ₛ•ₛ consSubst (wkSubst 2 idSubst) t₁′) x ≡
     (consSubst (wkSubst 2 idSubst) t₂′ ₛ•ₛ liftSubst σ) x
   varEq x0 = refl
   varEq (x +1) = begin
     wk1 (wk1 (σ x))
       ≡⟨ wk≡subst (step id) (wk1 (σ x)) ⟩
     wk1 (σ x) [ wk1Subst idSubst ]
       ≡⟨ subst-wk (σ x) ⟩
     σ x [ wk1Subst idSubst ₛ• step id ]
       ≡⟨ substVar-to-subst (λ x₁ → refl) (σ x) ⟩
     σ x [ (λ y → var (y +2)) ]
       ≡˘⟨ wk1-tail (σ x) ⟩
     wk1 (σ x) [ consSubst (λ y → var (y +2)) t₂′ ] ∎

substComp↑² :
  (A : Term (1+ n)) (t : Term (2 + n)) →
  A [ consSubst (tail (tail σ)) (t [ σ ]) ] ≡ A [ t ]↑² [ σ ]
substComp↑² {n = n} {σ = σ} A t = begin
  A [ consSubst (tail (tail σ)) (t [ σ ]) ]
    ≡⟨ substVar-to-subst varEq A ⟩
  A [ σ ₛ•ₛ consSubst (wkSubst 2 idSubst) t ]
    ≡˘⟨ substCompEq A ⟩
  A [ t ]↑² [ σ ] ∎
  where
  varEq : (x : Fin (1+ n)) →
          consSubst (tail (tail σ)) (t [ σ ]) x ≡
          (σ ₛ•ₛ consSubst (wkSubst 2 idSubst) t) x
  varEq x0 = refl
  varEq (x +1) = refl

substCompProdrec :
  ∀ {s} (A : Term (1+ n)) (t u : Term m) (σ : Subst m n) →
  A [ liftSubst σ ] [ prod s p t u ]₀ ≡
  A [ prod s p (var x1) (var x0) ]↑² [ consSubst (consSubst σ t) u ]
substCompProdrec {n = n} A t u σ = begin
   A [ liftSubst σ ] [ prod! t u ]₀
     ≡⟨ substCompEq A ⟩
   A [ sgSubst (prod! t u) ₛ•ₛ liftSubst σ ]
     ≡⟨ substVar-to-subst varEq A ⟩
   A [ consSubst (consSubst σ t) u ₛ•ₛ
       consSubst (wkSubst 2 idSubst) px ]
     ≡˘⟨ substCompEq A ⟩
   A [ px ]↑² [ consSubst (consSubst σ t) u ] ∎
   where
   px = prod! (var (x0 +1)) (var x0)
   varEq : (x : Fin (1+ n))
         → (sgSubst (prod! t u) ₛ•ₛ liftSubst σ) x
         ≡ (consSubst (consSubst σ t) u ₛ•ₛ
            consSubst (wkSubst 2 idSubst) px) x
   varEq x0 = refl
   varEq (x +1) = trans (wk1-tail (σ x)) (subst-id (σ x))

opaque

  -- A variant of the previous lemma.

  [1,0]↑²[,] :
    (t : Term (1+ n)) →
    t [ prod s p (var x1) (var x0) ]↑² [ u , v ]₁₀ ≡
    t [ prod s p u v ]₀
  [1,0]↑²[,] {s} {p} {u} {v} t =
    t [ prod s p (var x1) (var x0) ]↑² [ u , v ]₁₀  ≡˘⟨ substCompProdrec t _ _ _ ⟩

    t [ liftSubst idSubst ] [ prod s p u v ]₀       ≡⟨ cong _[ _ ] $
                                                       trans (substVar-to-subst subst-lift-id t) $
                                                       subst-id t ⟩
    t [ prod s p u v ]₀                             ∎

opaque

  -- A generalisation of doubleSubstComp (given below).

  doubleSubstComp′ :
    (t : Term (2+ n)) →
    t [ liftSubstn σ₁ 2 ] [ consSubst (consSubst σ₂ u) v ] ≡
    t [ consSubst (consSubst (σ₂ ₛ•ₛ σ₁) u) v ]
  doubleSubstComp′ {σ₁} {σ₂} {u} {v} t =
    t [ liftSubstn σ₁ 2 ] [ consSubst (consSubst σ₂ u) v ]  ≡⟨ substCompEq t ⟩
    t [ consSubst (consSubst σ₂ u) v ₛ•ₛ liftSubstn σ₁ 2 ]  ≡⟨ (flip substVar-to-subst t λ {
                                                                  x0          → refl;
                                                                  (x0 +1)     → refl;
                                                                  ((x +1) +1) →
      wk2 (σ₁ x) [ consSubst (consSubst σ₂ u) v ]                   ≡⟨ wk2-tail (σ₁ _) ⟩
      σ₁ x [ σ₂ ]                                                   ∎ }) ⟩

    t [ consSubst (consSubst (σ₂ ₛ•ₛ σ₁) u) v ]             ∎

doubleSubstComp : (A : Term (2+ n)) (t u : Term m) (σ : Subst m n)
                → A [ liftSubstn σ 2 ] [ t , u ]₁₀
                ≡ A [ consSubst (consSubst σ t) u ]
doubleSubstComp {n} A t u σ =
  A [ liftSubstn σ 2 ] [ t , u ]₁₀                 ≡⟨ doubleSubstComp′ A ⟩
  A [ consSubst (consSubst (idSubst ₛ•ₛ σ) t) u ]  ≡⟨ flip substVar-to-subst A $ consSubst-cong $ consSubst-cong $ idSubst-ₛ•ₛˡ ⟩
  A [ consSubst (consSubst σ t) u ]                ∎

head-tail-subst : ∀ t → t [ σ ] ≡ t [ consSubst (tail σ) (head σ) ]
head-tail-subst t =
  substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t

opaque

  -- Applying a weakening followed by a closing substitution to a closed term
  -- is the same as doing nothing.

  wk-subst-closed : {ρ : Wk n 0} {σ : Subst 0 n}
                  → (t : Term 0)
                  → wk ρ t [ σ ] ≡ t
  wk-subst-closed {0} {ρ = id} {σ} t = begin
    wk id t [ σ ] ≡⟨ cong (_[ σ ]) (wk-id t) ⟩
    t [ σ ]       ≡⟨ substVar-to-subst (λ ()) t ⟩
    t [ idSubst ] ≡⟨ subst-id t ⟩
    t             ∎
  wk-subst-closed {1+ n} {ρ = step ρ} {σ} t = begin
    wk (step ρ) t [ σ ]                           ≡⟨ head-tail-subst (wk (step ρ) t) ⟩
    wk (step ρ) t [ consSubst (tail σ) (head σ) ] ≡⟨ step-consSubst t ⟩
    wk ρ t [ tail σ ]                             ≡⟨ wk-subst-closed t ⟩
    t                                             ∎

opaque

  -- A special case of the property above

  wk₀-subst : ∀ t → wk wk₀ t [ σ ] ≡ t
  wk₀-subst t = wk-subst-closed t

opaque

  -- A version of the above property involving lifted weakenings and
  -- substitutions

  wk-subst-lift-closed : {ρ : Wk n 0} {σ : Subst 0 n}
                       → (t : Term 1)
                       → wk (lift ρ) t [ liftSubst σ ] ≡ t
  wk-subst-lift-closed {ρ} {σ} t = begin
    wk (lift ρ) t [ liftSubst σ ]  ≡⟨ subst-wk t ⟩
    t [ liftSubst σ ₛ• lift ρ ]    ≡⟨ subst-lift-ₛ• t ⟩
    t [ liftSubst (σ ₛ• ρ) ]       ≡⟨ substVar-to-subst (substVar-lift (λ ())) t ⟩
    t [ liftSubst idSubst ]        ≡⟨ substVar-to-subst subst-lift-id t ⟩
    t [ idSubst ]                  ≡⟨ subst-id t ⟩
    t                              ∎

opaque

  lifts-step-sgSubst : {ρ : Wk m n} (k : Nat) (t : Term (k + n))
                     → wk (liftn ρ k) t ≡ wk (liftn (step ρ) k) t [ liftSubstn (sgSubst u) k ]
  lifts-step-sgSubst {u} {ρ} k t = begin
    wk (liftn ρ k) t                                     ≡⟨ wk≡subst (liftn ρ k) t ⟩
    t [ toSubst (liftn ρ k) ]                            ≡⟨ substVar-to-subst (lemma k) t ⟩
    t [ liftSubstn (sgSubst u ₛ• step ρ) k ]             ≡˘⟨ subst-lifts-ₛ• k t ⟩
    t [ liftSubstn (sgSubst u) k ₛ• liftn (step ρ) k ]   ≡˘⟨ subst-wk t ⟩
    wk (liftn (step ρ) k) t [ liftSubstn (sgSubst u) k ] ∎
    where
    lemma : ∀ (k : Nat) x
          → toSubst (liftn ρ k) x ≡ liftSubstn (sgSubst u ₛ• step ρ) k x
    lemma 0 x = refl
    lemma (1+ k) x0 = refl
    lemma (1+ k) (_+1 x) = cong wk1 (lemma k x)

opaque

  lifts-step-[,] : {ρ : Wk m n} (k : Nat) (t : Term (k + n))
                 → wk (liftn ρ k) t ≡ wk (liftn (step (step ρ)) k) t [ liftSubstn (consSubst (sgSubst u) v) k ]
  lifts-step-[,] {u} {v} {ρ} k t = begin
    wk (liftn ρ k) t                                                          ≡⟨ wk≡subst (liftn ρ k) t ⟩
    t [ toSubst (liftn ρ k) ]                                                 ≡⟨ substVar-to-subst (lemma k) t ⟩
    t [ liftSubstn (consSubst (sgSubst u) v) k ₛ• liftn (step (step ρ)) k ]   ≡˘⟨ subst-wk t ⟩
    wk (liftn (step (step ρ)) k) t [ liftSubstn (consSubst (sgSubst u) v) k ] ∎
    where
    lemma : ∀ (k : Nat) x
          → toSubst (liftn ρ k) x ≡ (liftSubstn (consSubst (sgSubst u) v) k ₛ• liftn (step (step ρ)) k) x
    lemma 0 x = refl
    lemma (1+ k) x0 = refl
    lemma (1+ k) (x +1) = cong wk1 (lemma k x)

opaque

  -- One can express _[_,_]₁₀ using _[_]₀ and wk1.

  [,]≡[wk1]₀[]₀ :
    (t : Term (2+ n)) → t [ u , v ]₁₀ PE.≡ t [ wk1 v ]₀ [ u ]₀
  [,]≡[wk1]₀[]₀ {u} {v} t =
    t [ u , v ]₁₀             ≡˘⟨ PE.cong (t [ _ ,_]₁₀) $ wk1-sgSubst _ _ ⟩
    t [ u , wk1 v [ u ]₀ ]₁₀  ≡⟨ substConsId t ⟩
    t [ wk1 v ]₀ [ u ]₀       ∎

opaque

  -- One can fuse an application of _[_,_] and an application of _[_]
  -- into an application of _[_].

  [,]-[]-fusion :
    ∀ t →
    t [ u , v ]₁₀ [ σ ] ≡
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]
  [,]-[]-fusion {u} {v} {σ} t =
    t [ u , v ]₁₀ [ σ ]                                ≡⟨ substCompEq t ⟩
    t [ σ ₛ•ₛ consSubst (sgSubst u) v ]                ≡⟨ (flip substVar-to-subst t λ where
                                                             x0      → refl
                                                             (x0 +1) → refl
                                                             (_ +2)  → refl) ⟩
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]  ∎

opaque

  -- The function _[_,_]₁₀ kind of commutes with _[_].

  [,]-[]-commute :
    ∀ t →
    t [ u , v ]₁₀ [ σ ] ≡
    t [ liftSubstn σ 2 ] [ u [ σ ] , v [ σ ] ]₁₀
  [,]-[]-commute {u} {v} {σ} t =
    t [ u , v ]₁₀ [ σ ]                                ≡⟨ [,]-[]-fusion t ⟩
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]  ≡˘⟨ doubleSubstComp t _ _ _ ⟩
    t [ liftSubstn σ 2 ] [ u [ σ ] , v [ σ ] ]₁₀       ∎

opaque

  -- A lemma related to Id.

  ≡Id-wk1-wk1-0[]₀ :
    Id A t u ≡ Id (wk1 A) (wk1 t) (var x0) [ u ]₀
  ≡Id-wk1-wk1-0[]₀ {A} {t} {u} =
    Id A t u                            ≡˘⟨ cong₂ (λ A t → Id A t _) (wk1-sgSubst _ _) (wk1-sgSubst _ _) ⟩
    Id (wk1 A [ u ]₀) (wk1 t [ u ]₀) u  ≡⟨⟩
    Id (wk1 A) (wk1 t) (var x0) [ u ]₀  ∎

opaque

  -- A variant of the previous lemma.

  ≡Id-wk2-wk2-1[,] :
    Id A t u ≡ Id (wk2 A) (wk2 t) (var x1) [ u , v ]₁₀
  ≡Id-wk2-wk2-1[,] {A} {t} {u} {v} =
    Id A t u                                      ≡˘⟨ cong₂ (λ A t → Id A t _) wk2-[,] wk2-[,] ⟩
    Id (wk2 A [ u , v ]₁₀) (wk2 t [ u , v ]₁₀) u  ≡⟨⟩
    Id (wk2 A) (wk2 t) (var x1) [ u , v ]₁₀       ∎

opaque

  -- Another lemma related to Id.

  Id-wk1-wk1-0[⇑]≡ :
    ∀ A t →
    Id (wk1 A) (wk1 t) (var x0) [ liftSubst σ ] ≡
    Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0)
  Id-wk1-wk1-0[⇑]≡ {σ} A t =
    Id (wk1 A) (wk1 t) (var x0) [ liftSubst σ ]                  ≡⟨⟩
    Id (wk1 A [ liftSubst σ ]) (wk1 t [ liftSubst σ ]) (var x0)  ≡⟨ cong₂ (λ A t → Id A t _) (wk1-liftSubst A) (wk1-liftSubst t) ⟩
    Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0)                  ∎

opaque

  -- A _[t]₀ after _[u]↑ has the same effect as _[u[t]₀]₀.

  []↑-[]₀ :
    ∀ A →
    A [ u ]↑ [ t ]₀ ≡ A [ u [ t ]₀ ]₀
  []↑-[]₀ {u} {t} A = begin
    (A [ u ]↑) [ t ]₀                                   ≡⟨ substCompEq A ⟩
    A [ sgSubst t ₛ•ₛ consSubst (wk1Subst idSubst) u ]  ≡⟨ substVar-to-subst lemma A ⟩
    A [ u [ t ]₀ ]₀                                     ∎
    where
    lemma : ∀ x → (sgSubst t ₛ•ₛ consSubst (wk1Subst idSubst) u) x ≡ sgSubst (u [ t ]₀) x
    lemma x0 = refl
    lemma (_+1 x) = refl

opaque

  -- A lemma related to natrec

  lift-step-natrec : ∀ A z s n
                   → natrec p q r
                            (wk (lift ρ) A [ liftSubst σ ])
                            (wk ρ z [ σ ])
                            (wk (liftn ρ 2) s [ liftSubstn σ 2 ])
                            n
                   ≡ natrec p q r
                            (wk (liftn ρ 2) (wk (lift (step id)) A) [ liftSubst (consSubst σ u) ])
                            (wk (lift ρ) (wk1 z) [ consSubst σ u ])
                            (wk (liftn ρ 3) (wk (liftn (step id) 2) s) [ liftSubstn (consSubst σ u) 2 ])
                            n
  lift-step-natrec {ρ} {σ} {u} A z s n =
    case begin
           wk (lift ρ) A [ liftSubst σ ]
             ≡⟨ subst-wk A ⟩
           A [ liftSubst σ ₛ• lift ρ ]
             ≡⟨ substVar-to-subst (λ { x0 → refl ; (_+1 x) → refl}) A ⟩
           A [ liftSubst (consSubst σ u) ₛ• lift (step ρ) ]
             ≡˘⟨ cong (λ x → A [ liftSubst (consSubst σ u) ₛ• lift (step x) ]) (•-idʳ ρ) ⟩
           A [ liftSubst (consSubst σ u) ₛ• lift (step (ρ • id)) ]
             ≡˘⟨ subst-wk A ⟩
           wk (lift (step (ρ • id))) A [ liftSubst (consSubst σ u) ]
             ≡˘⟨ cong (_[ liftSubst (consSubst σ u) ]) (wk-comp (liftn ρ 2) (lift (step id)) A) ⟩
           wk (liftn ρ 2) (wk (lift (step id)) A) [ liftSubst (consSubst σ u) ] ∎ of λ
      A≡A′ →
    case begin
           wk ρ z [ σ ]                          ≡˘⟨ step-consSubst z ⟩
           wk (step ρ) z [ consSubst σ u ]       ≡˘⟨ cong (_[ consSubst σ u ]) (lift-wk1 ρ z) ⟩
           wk (lift ρ) (wk1 z) [ consSubst σ u ] ∎ of λ
      z≡z′ →
    case begin
           wk (liftn ρ 2) s [ liftSubstn σ 2 ]
             ≡⟨ subst-wk s ⟩
           s [ liftSubstn σ 2 ₛ• liftn ρ 2 ]
             ≡⟨ substVar-to-subst (λ { x0 → refl ; (x0 +1) → refl ; (x +2) → refl}) s ⟩
           s [ liftSubstn (consSubst σ u) 2 ₛ• liftn (step ρ) 2 ]
             ≡˘⟨ subst-wk s ⟩
           wk (liftn (step ρ) 2) s [ liftSubstn (consSubst σ u) 2 ]
             ≡˘⟨ cong (λ x → wk (liftn (step x) 2) s [ liftSubstn (consSubst σ u) 2 ]) (•-idʳ ρ) ⟩
           wk (liftn (step (ρ • id)) 2) s [ liftSubstn (consSubst σ u) 2 ]
             ≡˘⟨ cong (_[ liftSubstn (consSubst σ u) 2 ]) (wk-comp (liftn ρ 3) (liftn (step id) 2) s) ⟩
           wk (liftn ρ 3) (wk (liftn (step id) 2) s) [ liftSubstn (consSubst σ u) 2 ] ∎ of λ
      s≡s′ →
    cong₃ (λ A z s → natrec _ _ _ A z s n)
      A≡A′ z≡z′ s≡s′

opaque

  -- A lemma related to natrec, similar to the one above

  lift-step-natrec′ : ∀ A z s t
                    → let σ′ = consSubst (consSubst σ u) v in
                      natrec p q r
                             (wk (lift ρ) A [ liftSubst σ ])
                             (wk ρ z [ σ ])
                             (wk (liftn ρ 2) s [ liftSubstn σ 2 ])
                             (t [ σ ])
                    ≡ natrec p q r
                             (wk (lift (step (step id))) (wk (lift ρ) A) [ liftSubst σ′ ])
                             (wk (step (step id)) (wk ρ z) [ σ′ ])
                             (wk (liftn (step (step id)) 2) (wk (liftn ρ 2) s) [ liftSubstn σ′ 2 ])
                             (wk (step (step id)) t [ σ′ ] )
  lift-step-natrec′ {(m)} {(n)} {σ} {u} {v} {ρ} A z s t =
    case begin
           wk (lift ρ) A [ liftSubst σ ]                               ≡⟨ subst-wk A ⟩
           A [ liftSubst σ ₛ• lift ρ ]                                 ≡⟨ substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) A ⟩
           A [ liftSubst σ₊ ₛ• lift (step (step ρ)) ]                  ≡˘⟨ subst-wk A ⟩
           wk (lift (step (step ρ))) A [ liftSubst σ₊ ]                ≡˘⟨ cong (_[ liftSubst σ₊ ]) (wk-comp _ _ A) ⟩
           wk (lift (step (step id))) (wk (lift ρ) A) [ liftSubst σ₊ ] ∎ of λ
      A≡A′ →
    case begin
           wk ρ z [ σ ]                        ≡⟨ subst-wk z ⟩
           z [ σ ₛ• ρ ]                        ≡⟨ substVar-to-subst (λ _ → refl) z ⟩
           z [ σ₊ ₛ• step (step ρ) ]           ≡˘⟨ subst-wk z ⟩
           wk (step (step ρ)) z [ σ₊ ]         ≡˘⟨ cong (_[ σ₊ ]) (wk-comp _ _ z) ⟩
           wk (step (step id)) (wk ρ z) [ σ₊ ] ∎ of λ
      z≡z′ →
    case begin
           wk (liftn ρ 2) s [ liftSubstn σ 2 ]                                  ≡⟨ subst-wk s ⟩
           s [ liftSubstn σ 2 ₛ• liftn ρ 2 ]                                    ≡⟨ substVar-to-subst (λ { x0 → refl ; (x0 +1) → refl ; (x +2) → refl }) s ⟩
           s [ liftSubstn σ₊ 2 ₛ• liftn (step (step ρ)) 2 ]                     ≡˘⟨ subst-wk s ⟩
           wk (liftn (step (step ρ)) 2) s [ liftSubstn σ₊ 2 ]                   ≡˘⟨ cong (_[ liftSubstn σ₊ 2 ]) (wk-comp _ _ s) ⟩
           wk (liftn (step (step id)) 2) (wk (liftn ρ 2) s) [ liftSubstn σ₊ 2 ] ∎ of λ
      s≡s′ →
    cong₄ (natrec _ _ _) A≡A′ z≡z′ s≡s′
      (sym (trans (step-consSubst t) (wk1-tail t)))
    where
    σ₊ : Subst m (2+ n)
    σ₊ = consSubst (consSubst σ u) v

------------------------------------------------------------------------
-- Some lemmas related to wk[_], wk[_]′ and wkSubst

opaque

  -- The functions wk[_] and wk[_]′ are interchangeable.

  wk[]≡wk[]′ : wk[ k ] t ≡ wk[ k ]′ t
  wk[]≡wk[]′ {k = 0} {t} =
    t        ≡˘⟨ wk-id _ ⟩
    wk id t  ∎
  wk[]≡wk[]′ {k = 1+ k} {t} =
    wk1 (wk[ k ] t)   ≡⟨ cong wk1 wk[]≡wk[]′ ⟩
    wk1 (wk[ k ]′ t)  ≡⟨ wk-comp _ _ _ ⟩
    wk[ 1+ k ]′ t     ∎

opaque

  -- Applications of wk[_] can be expressed using a substitution.

  wk[]≡[] : ∀ k → wk[ k ] t ≡ t [ wkSubst k idSubst ]
  wk[]≡[] {t} 0 =
    t              ≡˘⟨ subst-id _ ⟩
    t [ idSubst ]  ∎
  wk[]≡[] {t} (1+ k) =
    wk1 (wk[ k ] t)                               ≡⟨ cong wk1 $ wk[]≡[] k ⟩
    wk1 (t [ wkSubst k idSubst ])                 ≡⟨ wk≡subst _ _ ⟩
    t [ wkSubst k idSubst ] [ wk1Subst idSubst ]  ≡⟨ substCompEq t ⟩
    t [ wk1Subst idSubst ₛ•ₛ wkSubst k idSubst ]  ≡⟨ substVar-to-subst lemma t ⟩
    t [ wkSubst (1+ k) idSubst ]                  ∎
    where
    lemma :
      (x : Fin n) →
      (wk1Subst idSubst ₛ•ₛ wkSubst k idSubst) x ≡
      wkSubst (1+ k) idSubst x
    lemma x =
      (wk1Subst idSubst ₛ•ₛ wkSubst k idSubst) x  ≡⟨⟩
      wkSubst k idSubst x [ wk1Subst idSubst ]    ≡⟨ wk1Subst-wk1 (wkSubst k _ _) ⟩
      wk1 (wkSubst k idSubst x [ idSubst ])       ≡⟨ cong wk1 $ subst-id _ ⟩
      wk1 (wkSubst k idSubst x)                   ≡⟨⟩
      wkSubst (1+ k) idSubst x                    ∎

opaque

  -- A lemma relating wk[_] and wkSubst.

  wk[]≡wkSubst : ∀ k x → wk[ k ] (σ x) ≡ wkSubst k σ x
  wk[]≡wkSubst 0      _ = refl
  wk[]≡wkSubst (1+ k) _ = cong wk1 (wk[]≡wkSubst k _)

opaque

  -- A composition lemma for wkSubst.

  wkSubst-idSubst-ₛ•ₛ :
    ∀ k x → (wkSubst k idSubst ₛ•ₛ σ) x ≡ wkSubst k σ x
  wkSubst-idSubst-ₛ•ₛ {σ} k x =
    σ x [ wkSubst k idSubst ]  ≡˘⟨ wk[]≡[] k ⟩
    wk[ k ] (σ x)              ≡⟨ wk[]≡wkSubst k _ ⟩
    wkSubst k σ x              ∎

opaque

  -- A composition lemma for wkSubst.

  wkSubst-comp :
    ∀ m x →
    subst Term (+-assoc m n o) (wkSubst (m + n) σ x) ≡
    wkSubst m (wkSubst n σ) x
  wkSubst-comp             0      _ = refl
  wkSubst-comp {n} {o} {σ} (1+ m) x =
    subst Term (cong 1+ (+-assoc m n o)) (wk1 (wkSubst (m + n) σ x))  ≡⟨ lemma {eq = +-assoc m _ _} ⟩
    wk1 (subst Term (+-assoc m n o) (wkSubst (m + n) σ x))            ≡⟨ cong wk1 $ wkSubst-comp m _ ⟩
    wk1 (wkSubst m (wkSubst n σ) x)                                   ∎
    where
    lemma :
      subst Term (cong 1+ eq) (wk1 t) ≡
      wk1 (subst Term eq t)
    lemma {eq = refl} = refl

opaque

  -- A composition lemma for wk[_].

  wk[]-comp :
    ∀ m →
    subst Term (+-assoc m n o) (wk[ m + n ] t) ≡
    wk[ m ] (wk[ n ] t)
  wk[]-comp {n} {o} {t} m =
    subst Term (+-assoc m n o) (wk[ m + n ] t)                   ≡⟨ cong (subst _ _) $ wk[]≡[] (m + _) ⟩
    subst Term (+-assoc m n o) (t [ wkSubst (m + n) idSubst ])   ≡⟨ lemma t ⟩
    t [ subst Term (+-assoc m n o) ∘→ wkSubst (m + n) idSubst ]  ≡⟨ flip substVar-to-subst t $ wkSubst-comp m ⟩
    t [ wkSubst m (wkSubst n idSubst) ]                          ≡˘⟨ flip substVar-to-subst t $ wkSubst-idSubst-ₛ•ₛ m ⟩
    t [ wkSubst m idSubst ₛ•ₛ wkSubst n idSubst ]                ≡˘⟨ substCompEq t ⟩
    t [ wkSubst n idSubst ] [ wkSubst m idSubst ]                ≡˘⟨ wk[]≡[] m ⟩
    wk[ m ] (t [ wkSubst n idSubst ])                            ≡˘⟨ cong wk[ m ] $ wk[]≡[] n ⟩
    wk[ m ] (wk[ n ] t)                                          ∎
    where
    lemma :
      ∀ t → subst Term eq (t [ σ ]) ≡ t [ subst Term eq ∘→ σ ]
    lemma {eq = refl} _ = refl

opaque

  -- A composition lemma for wk[_]′.

  wk[]′-comp :
    ∀ m →
    subst Term (+-assoc m n o) (wk[ m + n ]′ t) ≡
    wk[ m ]′ (wk[ n ]′ t)
  wk[]′-comp {n} {o} {t} m =
    subst Term (+-assoc m n o) (wk[ m + n ]′ t)  ≡˘⟨ cong (subst Term (+-assoc m _ _)) wk[]≡wk[]′ ⟩
    subst Term (+-assoc m n o) (wk[ m + n ] t)   ≡⟨ wk[]-comp m ⟩
    wk[ m ] (wk[ n ] t)                          ≡⟨ trans wk[]≡wk[]′ $
                                                    cong wk[ _ ]′ wk[]≡wk[]′ ⟩
    wk[ m ]′ (wk[ n ]′ t)                        ∎

opaque

  -- A composition lemma for wk[_] and wk[_]′.

  wk[]-wk[]′-comp :
    ∀ m →
    subst Term (+-assoc m n o) (wk[ m + n ]′ t) ≡
    wk[ m ] (wk[ n ]′ t)
  wk[]-wk[]′-comp {n} {o} {t} m =
    subst Term (+-assoc m n o) (wk[ m + n ]′ t)  ≡⟨ wk[]′-comp _ ⟩
    wk[ m ]′ (wk[ n ]′ t)                        ≡˘⟨ wk[]≡wk[]′ ⟩
    wk[ m ] (wk[ n ]′ t)                         ∎

opaque

  -- A lemma relating wk[_], _[_] and _⇑[_].

  wk[]-⇑[] : ∀ k → wk[ k ] t [ σ ⇑[ k ] ] ≡ wk[ k ] (t [ σ ])
  wk[]-⇑[]         0      = refl
  wk[]-⇑[] {t} {σ} (1+ k) =
    wk1 (wk[ k ] t) [ σ ⇑[ k ] ⇑ ]  ≡⟨ wk1-liftSubst (wk[ k ] _) ⟩
    wk1 (wk[ k ] t [ σ ⇑[ k ] ])    ≡⟨ cong wk1 $ wk[]-⇑[] k ⟩
    wk1 (wk[ k ] (t [ σ ]))         ∎

opaque

  -- A lemma relating wk[_]′, _[_] and _⇑[_].

  wk[]′-[⇑] : ∀ t → wk[ k ]′ t [ σ ⇑[ k ] ] ≡ wk[ k ]′ (t [ σ ])
  wk[]′-[⇑] {k} {σ} t =
    wk[ k ]′ t [ σ ⇑[ k ] ]  ≡˘⟨ cong _[ _ ] $ wk[]≡wk[]′ {t = t} ⟩
    wk[ k ] t [ σ ⇑[ k ] ]   ≡⟨ wk[]-⇑[] k ⟩
    wk[ k ] (t [ σ ])        ≡⟨ wk[]≡wk[]′ ⟩
    wk[ k ]′ (t [ σ ])       ∎

opaque

  -- Applying _[ u ]↑ to a term that has been weakened at least two
  -- steps amounts to the same thing as doing nothing.

  wk[]′-[]↑ : wk[ 2+ k ]′ t [ u ]↑ ≡ wk[ 2+ k ]′ t
  wk[]′-[]↑ {k} {t} {u} =
    wk[ 2+ k ]′ t [ u ]↑                                     ≡⟨⟩
    wk[ 2+ k ]′ t [ consSubst (wk1Subst idSubst) u ]         ≡⟨ subst-wk t ⟩
    t [ consSubst (wk1Subst idSubst) u ₛ• stepn id (2+ k) ]  ≡⟨⟩
    t [ toSubst (stepn id (2+ k)) ]                          ≡˘⟨ wk≡subst _ _ ⟩
    wk[ 2+ k ]′ t                                            ∎

opaque

  -- A variant of wk1-sgSubst.

  wk[1+]′-[]₀≡ : wk[ 1+ k ]′ t [ u ]₀ ≡ wk[ k ]′ t
  wk[1+]′-[]₀≡ {k} {t} {u} =
    wk[ 1+ k ]′ t [ u ]₀  ≡˘⟨ cong _[ _ ]₀ $ wk[]≡wk[]′ {k = 1+ k} ⟩
    wk[ 1+ k ] t [ u ]₀   ≡⟨ wk1-sgSubst _ _ ⟩
    wk[ k ] t             ≡⟨ wk[]≡wk[]′ ⟩
    wk[ k ]′ t            ∎

opaque

  -- A variant of wk1-sgSubst.

  wk[+1]′-[₀⇑]≡ :
    {t : Term n} →
    subst Term (+-assoc k _ _) (wk[ k + 1 ]′ t) [ sgSubst u ⇑[ k ] ] ≡
    wk[ k ]′ t
  wk[+1]′-[₀⇑]≡ {k} {u} {t} =
    subst Term (+-assoc k _ _) (wk[ k + 1 ]′ t) [ sgSubst u ⇑[ k ] ]  ≡⟨ cong _[ _ ] $ wk[]′-comp {t = t} _ ⟩
    wk[ k ]′ (wk1 t) [ sgSubst u ⇑[ k ] ]                             ≡⟨ wk[]′-[⇑] (wk1 t) ⟩
    wk[ k ]′ (wk1 t [ u ]₀)                                           ≡⟨ cong wk[ _ ]′ $ wk1-sgSubst _ _ ⟩
    wk[ k ]′ t                                                        ∎

opaque

  -- A variant of wk₂-[,].

  wk[2+]′-[,]≡ : wk[ 2+ k ]′ t [ u , v ]₁₀ ≡ wk[ k ]′ t
  wk[2+]′-[,]≡ {k} {t} {u} {v} =
    wk[ 2+ k ]′ t [ u , v ]₁₀  ≡˘⟨ cong _[ _ , _ ]₁₀ $ wk[]≡wk[]′ {k = 2+ k} ⟩
    wk[ 2+ k ] t [ u , v ]₁₀   ≡⟨ wk2-[,] ⟩
    wk[ k ] t                  ≡⟨ wk[]≡wk[]′ ⟩
    wk[ k ]′ t                 ∎

opaque

  -- A variant of wk₂-[,].

  wk[2+]′[,⇑]≡ :
    {t : Term n} →
    subst Term (+-assoc k _ _) (wk[ k + 2 ]′ t)
      [ consSubst (sgSubst u) v ⇑[ k ] ] ≡
    wk[ k ]′ t
  wk[2+]′[,⇑]≡ {k} {u} {v} {t} =
    subst Term (+-assoc k _ _) (wk[ k + 2 ]′ t)
      [ consSubst (sgSubst u) v ⇑[ k ] ]                      ≡⟨ cong _[ _ ] $ wk[]′-comp k ⟩
    wk[ k ]′ (wk[ 2 ]′ t) [ consSubst (sgSubst u) v ⇑[ k ] ]  ≡⟨ wk[]′-[⇑] (wk[ _ ]′ t) ⟩
    wk[ k ]′ (wk[ 2 ]′ t [ u , v ]₁₀)                         ≡⟨ cong wk[ _ ]′ wk₂-[,] ⟩
    wk[ k ]′ t                                                ∎

------------------------------------------------------------------------
-- Some lemmas related to _[_][_]↑

opaque

  -- One can express _[_][_]↑ using some other operations.

  [][]↑≡ :
    ∀ {k u} (t : Term (1+ n)) →
    t [ k ][ u ]↑ ≡ wk (lift (stepn id k)) t [ u ]₀
  [][]↑≡ {k} {u} t =
      t [ consSubst (wkSubst k idSubst) u ]  ≡⟨ (flip substVar-to-subst t λ where
                                                   x0     → refl
                                                   (x +1) →
                                                     trans (sym $ wk[]≡wkSubst k _) $
                                                     wk[]≡wk[]′ {t = var x}) ⟩
      t [ sgSubst u ₛ• lift (stepn id k) ]   ≡˘⟨ subst-wk t ⟩
      wk (lift (stepn id k)) t [ u ]₀        ∎

opaque

  -- The function _[_][_]↑ commutes (in a certain sense) with _[_].

  [][]↑-commutes :
    ∀ t →
    t [ k ][ u ]↑ [ σ ⇑[ k ] ] ≡
    t [ σ ⇑ ] [ k ][ u [ σ ⇑[ k ] ] ]↑
  [][]↑-commutes {k} {u} {σ} t =
    t [ k ][ u ]↑ [ σ ⇑[ k ] ]                                      ≡⟨ substCompEq t ⟩
    t [ (σ ⇑[ k ]) ₛ•ₛ consSubst (wkSubst k idSubst) u ]            ≡⟨ (flip substVar-to-subst t λ where
                                                                          x0     → refl
                                                                          (x +1) → lemma (var x)) ⟩
    t [ consSubst (wkSubst k idSubst) (u [ σ ⇑[ k ] ]) ₛ•ₛ (σ ⇑) ]  ≡˘⟨ substCompEq t ⟩
    t [ σ ⇑ ] [ k ][ u [ σ ⇑[ k ] ] ]↑                              ∎
    where
    lemma :
      ∀ t →
      t [ wkSubst k idSubst ] [ σ ⇑[ k ] ] ≡
      wk1 (t [ σ ]) [ k ][ u [ σ ⇑[ k ] ] ]↑
    lemma t =
      t [ wkSubst k idSubst ] [ σ ⇑[ k ] ]    ≡˘⟨ cong _[ _ ] $ wk[]≡[] k ⟩
      wk[ k ] t [ σ ⇑[ k ] ]                  ≡⟨ wk[]-⇑[] k ⟩
      wk[ k ] (t [ σ ])                       ≡⟨ wk[]≡[] k ⟩
      t [ σ ] [ wkSubst k idSubst ]           ≡˘⟨ subst-wk (t [ _ ]) ⟩
      wk1 (t [ σ ]) [ k ][ u [ σ ⇑[ k ] ] ]↑  ∎

opaque

  -- The function _[_][_]↑ commutes (in another sense) with _[_].

  [][]↑-commutes-+ :
    let cast =
          subst₂ Subst (sym $ +-assoc j k₂ n) (sym $ +-assoc j k₁ n)
    in
    (t : Term (1+ n)) →
    (∀ x → wk[ k₁ ] (var x) [ σ ] ≡ wk[ k₂ ] (var x)) →
    t [ j + k₁ ][ u ]↑ [ cast (σ ⇑[ j ]) ] ≡
    t [ j + k₂ ][ u [ cast (σ ⇑[ j ]) ] ]↑
  [][]↑-commutes-+ {j} {k₂} {n} {k₁} {σ} {u} t hyp =
    t [ consSubst (wkSubst (j + k₁) idSubst) u ] [ cast₁ (σ ⇑[ j ]) ]    ≡⟨ substCompEq t ⟩

    t [ cast₁ (σ ⇑[ j ]) ₛ•ₛ consSubst (wkSubst (j + k₁) idSubst) u ]    ≡⟨ (flip substVar-to-subst t λ where
                                                                               x0     → refl
                                                                               (_ +1) → lemma₂ _) ⟩
    t [ consSubst (wkSubst (j + k₂) idSubst) (u [ cast₁ (σ ⇑[ j ]) ]) ]  ∎
    where
    cast₁ :
      Subst (j + (k₂ + n)) (j + (k₁ + n)) →
      Subst (j + k₂ + n) (j + k₁ + n)
    cast₁ = subst₂ Subst (sym $ +-assoc j _ _) (sym $ +-assoc j _ _)

    cast₂ : Term (j + (k₂ + n)) → Term (j + k₂ + n)
    cast₂ = subst Term (sym $ +-assoc j _ _)

    lemma₁ :
      v [ subst₂ Subst eq₁ (sym eq₂) σ′ ] ≡
      subst Term eq₁ (subst Term eq₂ v [ σ′ ])
    lemma₁ {eq₁ = refl} {eq₂ = refl} = refl

    lemma₂ :
      ∀ x →
      wkSubst (j + k₁) idSubst x [ cast₁ (σ ⇑[ j ]) ] ≡
      wkSubst (j + k₂) idSubst x
    lemma₂ x =
      wkSubst (j + k₁) idSubst x [ cast₁ (σ ⇑[ j ]) ]       ≡˘⟨ cong _[ _ ] $ wk[]≡wkSubst (j + _) _ ⟩

      wk[ j + k₁ ] (var x) [ cast₁ (σ ⇑[ j ]) ]             ≡⟨ lemma₁ {eq₁ = sym $ +-assoc j _ _} {eq₂ = +-assoc j _ _} ⟩

      cast₂
        (subst Term (+-assoc j _ _) (wk[ j + k₁ ] (var x))
           [ σ ⇑[ j ] ])                                    ≡⟨ cong cast₂ $ cong _[ _ ] $ wk[]-comp j ⟩

      cast₂ (wk[ j ] (wk[ k₁ ] (var x)) [ σ ⇑[ j ] ])       ≡⟨ cong cast₂ $ wk[]-⇑[] j ⟩

      cast₂ (wk[ j ] (wk[ k₁ ] (var x) [ σ ]))              ≡⟨ cong cast₂ $ cong wk[ j ] $ hyp _ ⟩

      cast₂ (wk[ j ] (wk[ k₂ ] (var x)))                    ≡⟨ swap-subst $ wk[]-comp j ⟩

      wk[ j + k₂ ] (var x)                                  ≡⟨ wk[]≡[] (j + _) ⟩

      var x [ wkSubst (j + k₂) idSubst ]                    ≡⟨⟩

      wkSubst (j + k₂) idSubst x                            ∎

opaque

  -- A variant of [][]↑-commutes-+.

  [][]↑-[₀⇑] :
    ∀ j {u} (t : Term (1+ n)) →
    let cast =
          subst₂ Subst (sym $ +-assoc j k n) (sym $ +-assoc j (1+ k) n)
    in
    t [ j + 1+ k ][ u ]↑ [ cast (sgSubst v ⇑[ j ]) ] ≡
    t [ j + k ][ u [ cast (sgSubst v ⇑[ j ]) ] ]↑
  [][]↑-[₀⇑] {k} {v} _ t =
    [][]↑-commutes-+ t λ x →
      wk[ 1+ k ] (var x) [ v ]₀     ≡⟨⟩
      wk1 (wk[ k ] (var x)) [ v ]₀  ≡⟨ wk1-sgSubst _ _ ⟩
      wk[ k ] (var x)               ∎

private opaque

  -- An example of how [][]↑-[₀⇑] can be used. Note that the cast
  -- "disappears".

  _ :
    (t : Term (1+ n)) →
    t [ 1+ k ][ u ]↑ [ v ]₀ ≡
    t [ k ][ u [ v ]₀ ]↑
  _ = [][]↑-[₀⇑] 0

opaque

  -- A variant of [][]↑-commutes-+.

  [][]↑-[,⇑] :
    ∀ j {u} (t : Term (1+ n)) →
    let cast =
          subst₂ Subst (sym $ +-assoc j k n) (sym $ +-assoc j (2+ k) n)
    in
    t [ j + 2+ k ][ u ]↑ [ cast (consSubst (sgSubst v) w ⇑[ j ]) ] ≡
    t [ j + k ][ u [ cast (consSubst (sgSubst v) w ⇑[ j ]) ] ]↑
  [][]↑-[,⇑] {k} {v} {w} _ t =
    [][]↑-commutes-+ t λ x →
      wk[ 2+ k ] (var x) [ v , w ]₁₀  ≡⟨ wk2-[,] ⟩
      wk[ k ] (var x)                 ∎

private opaque

  -- An example of how [][]↑-[,⇑] can be used.

  _ :
    (t : Term (1+ n)) →
    t [ 2+ k ][ u ]↑ [ v , w ]₁₀ ≡
    t [ k ][ u [ v , w ]₁₀ ]↑
  _ = [][]↑-[,⇑] 0

opaque

  -- A variant of [][]↑-commutes-+.

  [][]↑-[↑⇑] :
    ∀ j {u} (t : Term (1+ n)) →
    let σ    = wk1Subst idSubst
        cast =
          subst₂ Subst (sym $ +-assoc j (1+ k) n)
            (sym $ +-assoc j (1+ k) n)
    in
    t [ j + 1+ k ][ u ]↑ [ cast (consSubst σ v ⇑[ j ]) ] ≡
    t [ j + 1+ k ][ u [ cast (consSubst σ v ⇑[ j ]) ] ]↑
  [][]↑-[↑⇑] {k} {v} _ t =
    [][]↑-commutes-+ t λ x →
      wk[ 1+ k ] (var x) [ consSubst (wk1Subst idSubst) v ]  ≡⟨ wk1-tail (wk[ k ] _) ⟩
      wk[ k ] (var x) [ wk1Subst idSubst ]                   ≡˘⟨ wk[]≡[] 1 ⟩
      wk[ 1+ k ] (var x)                                     ∎

private opaque

  -- An example of how [][]↑-[↑⇑] can be used.

  _ :
    (t : Term (1+ n)) →
    t [ 1+ k ][ u ]↑ [ v ]↑ ≡
    t [ 1+ k ][ u [ v ]↑ ]↑
  _ = [][]↑-[↑⇑] 0

opaque

  -- A weakening lemma for _[_][_]↑.

  [][wk[]′]↑ :
    (t : Term (1+ n)) →
    t [ k ][ wk[ k ]′ u ]↑ ≡ wk[ k ]′ (t [ u ]₀)
  [][wk[]′]↑ {k} {u} t =
    t [ k ][ wk[ k ]′ u ]↑                    ≡⟨ [][]↑≡ t ⟩
    wk (lift (stepn id k)) t [ wk[ k ]′ u ]₀  ≡˘⟨ wk-β t ⟩
    wk[ k ]′ (t [ u ]₀)                       ∎

opaque

  -- A weakening lemma for _[_][_]↑.

  wk[]′[][]↑ :
    ∀ j →
    let cast = subst Term (sym $ +-assoc j k n) in
    (t : Term (1+ n)) →
    cast (wk[ j ]′ (t [ k ][ u ]↑)) ≡
    t [ j + k ][ cast (wk[ j ]′ u) ]↑
  wk[]′[][]↑ {k} {n} {u} j t =
    cast (wk[ j ]′ (t [ consSubst (wkSubst k idSubst) u ]))        ≡⟨ cong cast $ wk-subst t ⟩
    cast (t [ stepn id j •ₛ consSubst (wkSubst k idSubst) u ])     ≡⟨ lemma₁ ⟩
    t [ cast ∘→ (stepn id j •ₛ consSubst (wkSubst k idSubst) u) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                                         x0     → refl
                                                                         (_ +1) → lemma₂ _) ⟩
    t [ consSubst (wkSubst (j + k) idSubst) (cast (wk[ j ]′ u)) ]  ∎
    where
    cast : Term (j + (k + n)) → Term ((j + k) + n)
    cast = subst Term (sym $ +-assoc j k n)

    lemma₁ : cast (t [ σ ]) ≡ t [ cast ∘→ σ ]
    lemma₁ rewrite +-assoc j k n = refl

    lemma₂ :
      ∀ x →
      cast (wk[ j ]′ (wkSubst k idSubst x)) ≡ wkSubst (j + k) idSubst x
    lemma₂ x =
      cast (wk[ j ]′ (wkSubst k idSubst x))   ≡˘⟨ cong cast wk[]≡wk[]′ ⟩
      cast (wk[ j ] (wkSubst k idSubst x))    ≡⟨ cong cast $ wk[]≡wkSubst j _ ⟩
      cast (wkSubst j (wkSubst k idSubst) x)  ≡⟨ swap-subst $ wkSubst-comp j _ ⟩
      wkSubst (j + k) idSubst x               ∎

private opaque

  -- An example of how wk[]′[][]↑ can be used.

  _ :
    (t : Term (1+ n)) →
    wk1 (t [ k ][ u ]↑) ≡ t [ 1+ k ][ wk1 u ]↑
  _ = wk[]′[][]↑ 1

opaque

  -- A weakening lemma for _[_][_]↑.

  wk1-[][]↑ : ∀ k {u} → wk1 t [ k ][ u ]↑ ≡ wk[ k ] t
  wk1-[][]↑ {t} k {u} =
    wk1 t [ consSubst (wkSubst k idSubst) u ]         ≡⟨ subst-wk t ⟩
    t [ consSubst (wkSubst k idSubst) u ₛ• step id ]  ≡⟨⟩
    t [ wkSubst k idSubst ]                           ≡˘⟨ wk[]≡[] k ⟩
    wk[ k ] t                                         ∎

opaque

  -- A weakening lemma for _[_][_]↑.

  wk1-[][]↑′ : wk1 t [ k ][ u ]↑ ≡ wk[ k ]′ t
  wk1-[][]↑′ {t} {k} {u} =
    wk1 t [ k ][ u ]↑  ≡⟨ wk1-[][]↑ k ⟩
    wk[ k ] t          ≡⟨ wk[]≡wk[]′ ⟩
    wk[ k ]′ t         ∎

opaque

  -- A lemma related to t [ 1+ k ][ var x0 ]↑.

  [1+][0]↑ : t [ 1+ k ][ var x0 ]↑ ≡ wk (lift (stepn id k)) t
  [1+][0]↑ {t} {k} =
    t [ 1+ k ][ var x0 ]↑                             ≡⟨ [][]↑≡ t ⟩
    wk (lift (stepn id (1+ k))) t [ var x0 ]₀         ≡⟨ subst-wk t ⟩
    t [ sgSubst (var x0) ₛ• lift (stepn id (1+ k)) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                            x0     → refl
                                                            (_ +1) → refl) ⟩
    t [ toSubst (lift (stepn id k)) ]                 ≡˘⟨ wk≡subst _ _ ⟩
    wk (lift (stepn id k)) t                          ∎

opaque

  -- The result of t [ var x0 ]↑ is equal to t.

  [0]↑ : t [ var x0 ]↑ ≡ t
  [0]↑ {t} =
    t [ var x0 ]↑   ≡⟨ [1+][0]↑ ⟩
    wk (lift id) t  ≡⟨ wk-lift-id _ ⟩
    t               ∎

------------------------------------------------------------------------
-- Some lemmas related to numerals

-- The predicate Numeral is decidable

opaque

  isNumeral? : (t : Term n) → Dec (Numeral t)
  isNumeral? zero = yes zeroₙ
  isNumeral? (suc t) =
    case isNumeral? t of λ where
      (yes n) → yes (sucₙ n)
      (no ¬n) → no (λ { (sucₙ n) → ¬n n})
  isNumeral? (var x) = no (λ ())
  isNumeral? (U _) = no (λ ())
  isNumeral? ℕ = no λ ()
  isNumeral? Empty = no λ ()
  isNumeral? Unit! = no λ ()
  isNumeral? (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = no λ ()
  isNumeral? (Id _ _ _) = no λ ()
  isNumeral? (lam _ _) = no λ ()
  isNumeral? (_ ∘ _) = no λ ()
  isNumeral? (prod! _ _) = no λ ()
  isNumeral? (fst _ _) = no λ ()
  isNumeral? (snd _ _) = no λ ()
  isNumeral? (prodrec _ _ _ _ _ _) = no λ ()
  isNumeral? (natrec _ _ _ _ _ _ _) = no λ ()
  isNumeral? star! = no λ ()
  isNumeral? (unitrec _ _ _ _ _ _) = no λ ()
  isNumeral? (emptyrec _ _ _) = no λ ()
  isNumeral? rfl = no λ ()
  isNumeral? (J _ _ _ _ _ _ _ _) = no λ ()
  isNumeral? (K _ _ _ _ _ _) = no λ ()
  isNumeral? ([]-cong! _ _ _ _) = no λ ()

opaque

  -- Applying substitutions to numerals has no effect

  subst-numeral : Numeral t → t [ σ ] ≡ t
  subst-numeral zeroₙ = refl
  subst-numeral (sucₙ n) = cong suc (subst-numeral n)

opaque

  -- The term sucᵏ k is a Numeral

  sucᵏ-Numeral : ∀ k → Numeral (sucᵏ {n} k)
  sucᵏ-Numeral 0 = zeroₙ
  sucᵏ-Numeral (1+ k) = sucₙ (sucᵏ-Numeral k)

opaque

  -- If a term is a Numeral it is equal to sucᵏ k for some k.

  Numeral→sucᵏ : Numeral t → ∃ λ k → t ≡ sucᵏ k
  Numeral→sucᵏ zeroₙ = 0 , refl
  Numeral→sucᵏ (sucₙ n) =
    case (Numeral→sucᵏ n) of
      λ (k , t≡) →
    1+ k , cong suc t≡

opaque

  -- Applying a substitution to sucᵏ k has no effect

  subst-sucᵏ : ∀ k → sucᵏ k [ σ ] ≡ sucᵏ k
  subst-sucᵏ 0 = refl
  subst-sucᵏ (1+ k) = cong suc (subst-sucᵏ k)

opaque

  -- Applying a weakening to sucᵏ k has no effect

  wk-sucᵏ : ∀ k → wk ρ (sucᵏ k) ≡ sucᵏ k
  wk-sucᵏ 0 = refl
  wk-sucᵏ (1+ k) = cong suc (wk-sucᵏ k)

------------------------------------------------------------------------
-- Injectivity of constructors with respect to propositional equality

-- BΠ is injective.

BΠ-PE-injectivity : BΠ p₁ q₁ PE.≡ BΠ p₂ q₂ → p₁ PE.≡ p₂ × q₁ PE.≡ q₂
BΠ-PE-injectivity PE.refl = PE.refl , PE.refl

-- BΣ is injective.

BΣ-PE-injectivity :
  BΣ s₁ p₁ q₁ PE.≡ BΣ s₂ p₂ q₂ → p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × s₁ PE.≡ s₂
BΣ-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- The constructor var is injective.

var-PE-injectivity : Term.var {n = n} x₁ PE.≡ var x₂ → x₁ PE.≡ x₂
var-PE-injectivity PE.refl = PE.refl

-- ΠΣ⟨_⟩_,_▷_▹_ is injective.

ΠΣ-PE-injectivity :
  ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ PE.≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
  b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × A₁ PE.≡ A₂ × B₁ PE.≡ B₂
ΠΣ-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- ⟦_⟧_▷_▹_ is injective.

B-PE-injectivity :
  ∀ W₁ W₂ → ⟦ W₁ ⟧ A₁ ▹ B₁ PE.≡ ⟦ W₂ ⟧ A₂ ▹ B₂ →
  A₁ PE.≡ A₂ × B₁ PE.≡ B₂ × W₁ PE.≡ W₂
B-PE-injectivity (BM _ _ _) (BM _ _ _) PE.refl =
  PE.refl , PE.refl , PE.refl

-- The constructor _∘⟨_⟩_ is injective.

∘-PE-injectivity :
  t₁ ∘⟨ p₁ ⟩ u₁ PE.≡ t₂ ∘⟨ p₂ ⟩ u₂ →
  p₁ PE.≡ p₂ × t₁ PE.≡ t₂ × u₁ PE.≡ u₂
∘-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- The constructor lam is injective.

lam-PE-injectivity :
  lam p₁ t₁ PE.≡ lam p₂ t₂ →
  p₁ PE.≡ p₂ × t₁ PE.≡ t₂
lam-PE-injectivity PE.refl = PE.refl , PE.refl

-- The constructor prod is injective.

prod-PE-injectivity :
  prod s₁ p₁ t₁ u₁ PE.≡ prod s₂ p₂ t₂ u₂ →
  s₁ PE.≡ s₂ × p₁ PE.≡ p₂ × t₁ PE.≡ t₂ × u₁ PE.≡ u₂
prod-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl , PE.refl

-- The constructor prodrec is injective.

prodrec-PE-injectivity :
  prodrec r₁ p₁ q₁ A₁ t₁ u₁ PE.≡ prodrec r₂ p₂ q₂ A₂ t₂ u₂ →
  r₁ PE.≡ r₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ ×
  u₁ PE.≡ u₂
prodrec-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- The constructor emptyrec is injective.

emptyrec-PE-injectivity :
  emptyrec p₁ A₁ t₁ PE.≡ emptyrec p₂ A₂ t₂ →
  p₁ PE.≡ p₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂
emptyrec-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- The constructor Unit is injective.

Unit-PE-injectivity :
  _≡_ {A = Term n} (Unit s₁ l₁) (Unit s₂ l₂) →
  s₁ ≡ s₂ × l₁ ≡ l₂
Unit-PE-injectivity refl = refl , refl

-- The constructor unitrec is injective.

unitrec-PE-injectivity :
  unitrec l₁ p₁ q₁ A₁ t₁ u₁ PE.≡ unitrec l₂ p₂ q₂ A₂ t₂ u₂ →
  l₁ PE.≡ l₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ ×
  u₁ PE.≡ u₂
unitrec-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- The constructor suc is injective.

suc-PE-injectivity : suc t₁ PE.≡ suc t₂ → t₁ PE.≡ t₂
suc-PE-injectivity PE.refl = PE.refl

-- The constructor natrec is injective.

natrec-PE-injectivity :
  natrec p₁ q₁ r₁ A₁ t₁ u₁ v₁ PE.≡ natrec p₂ q₂ r₂ A₂ t₂ u₂ v₂ →
  p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × r₁ PE.≡ r₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ ×
  u₁ PE.≡ u₂ × v₁ PE.≡ v₂
natrec-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- Id is injective.

Id-PE-injectivity :
  Id A₁ t₁ u₁ PE.≡ Id A₂ t₂ u₂ →
  A₁ PE.≡ A₂ × t₁ PE.≡ t₂ × u₁ PE.≡ u₂
Id-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- J is injective.

J-PE-injectivity :
  J p₁ q₁ A₁ t₁ B₁ u₁ v₁ w₁ PE.≡ J p₂ q₂ A₂ t₂ B₂ u₂ v₂ w₂ →
  p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ × B₁ PE.≡ B₂ ×
  u₁ PE.≡ u₂ × v₁ PE.≡ v₂ × w₁ PE.≡ w₂
J-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl ,
  PE.refl , PE.refl

-- K is injective.

K-PE-injectivity :
  K p₁ A₁ t₁ B₁ u₁ v₁ PE.≡ K p₂ A₂ t₂ B₂ u₂ v₂ →
  p₁ PE.≡ p₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ × B₁ PE.≡ B₂ × u₁ PE.≡ u₂ ×
  v₁ PE.≡ v₂
K-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- []-cong is injective.

[]-cong-PE-injectivity :
  []-cong s₁ A₁ t₁ u₁ v₁ PE.≡ []-cong s₂ A₂ t₂ u₂ v₂ →
  s₁ PE.≡ s₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ × u₁ PE.≡ u₂ × v₁ PE.≡ v₂
[]-cong-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl
