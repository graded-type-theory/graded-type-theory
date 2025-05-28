------------------------------------------------------------------------
-- Functions that can be used to replace quantities from one type with
-- quantities from another
------------------------------------------------------------------------

module Definition.Untyped.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  -- A translation function used for quantities other than those
  -- corresponding to the first components of Σ-types.
  (tr : M₁ → M₂)
  -- A translation function used for the first components of Σ-types.
  (tr-Σ : M₁ → M₂)
  where

open import Tools.Fin
open import Tools.Function
open import Tools.List
open import Tools.Nat
open import Tools.Product as Σ renaming (_,_ to _#_)
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

open import Definition.Typed.Variant

open import Definition.Untyped
open import Definition.Untyped.Neutral
import Definition.Untyped.Properties
open import Definition.Untyped.Whnf

private
  module U₁  = Definition.Untyped M₁
  module U₂  = Definition.Untyped M₂
  module UN₁ = Definition.Untyped.Neutral M₁
  module UN₂ = Definition.Untyped.Neutral M₂
  module UP₁ = Definition.Untyped.Properties M₁
  module UP₂ = Definition.Untyped.Properties M₂
  module UW₁ = Definition.Untyped.Whnf M₁
  module UW₂ = Definition.Untyped.Whnf M₂

private variable
  α m n                    : Nat
  bs                       : List _
  x                        : Fin _
  p q r                    : M₂
  s                        : Strength
  b                        : BinderMode
  ts us                    : GenTs _ _ _
  k₁ k₂                    : Kind _ _
  A B j l l′ l₁ l₂ t u v w : Term _ _
  ∇                        : DCon _ _
  ρ                        : Wk _ _
  σ                        : Subst _ _ _
  tv₁ tv₂                  : Type-variant
  V₁ V₂                    : Set _

------------------------------------------------------------------------
-- Translation

-- Mode-dependent translation of quantities.

tr-BinderMode : BinderMode → M₁ → M₂
tr-BinderMode BMΠ     = tr
tr-BinderMode (BMΣ _) = tr-Σ

-- Translation of kinds.

tr-Kind : U₁.Kind bs → U₂.Kind bs
tr-Kind (Defnkind α)        = Defnkind α
tr-Kind Ukind               = Ukind
tr-Kind (Binderkind b p q)  = Binderkind b (tr-BinderMode b p) (tr q)
tr-Kind (Lamkind p)         = Lamkind (tr p)
tr-Kind (Appkind p)         = Appkind (tr p)
tr-Kind (Prodkind s p)      = Prodkind s (tr-Σ p)
tr-Kind (Fstkind p)         = Fstkind (tr-Σ p)
tr-Kind (Sndkind p)         = Sndkind (tr-Σ p)
tr-Kind (Prodreckind r p q) = Prodreckind (tr r) (tr-Σ p) (tr q)
tr-Kind Natkind             = Natkind
tr-Kind Zerokind            = Zerokind
tr-Kind Suckind             = Suckind
tr-Kind (Natreckind p q r)  = Natreckind (tr p) (tr q) (tr r)
tr-Kind (Unitkind s)        = Unitkind s
tr-Kind (Starkind s)        = Starkind s
tr-Kind (Unitreckind p q)   = Unitreckind (tr p) (tr q)
tr-Kind Emptykind           = Emptykind
tr-Kind (Emptyreckind p)    = Emptyreckind (tr p)
tr-Kind Idkind              = Idkind
tr-Kind Reflkind            = Reflkind
tr-Kind (Jkind p q)         = Jkind (tr p) (tr q)
tr-Kind (Kkind p)           = Kkind (tr p)
tr-Kind (Boxcongkind s)     = Boxcongkind s
tr-Kind Levelkind           = Levelkind
tr-Kind Zeroᵘkind           = Zeroᵘkind
tr-Kind Sucᵘkind            = Sucᵘkind
tr-Kind Supᵘkind            = Supᵘkind
tr-Kind Liftkind            = Liftkind
tr-Kind liftkind            = liftkind
tr-Kind lowerkind           = lowerkind

mutual

  -- Translation of the alternative term representation.

  tr-Term′ : U₁.Term′ n → U₂.Term′ n
  tr-Term′ (var x)    = var x
  tr-Term′ (gen k ts) = gen (tr-Kind k) (tr-GenTs ts)

  -- Translation for GenTs.

  tr-GenTs : U₁.GenTs U₁.Term′ n bs → U₂.GenTs U₂.Term′ n bs
  tr-GenTs []        = []
  tr-GenTs (t ∷ₜ ts) = tr-Term′ t ∷ₜ tr-GenTs ts

-- Translation of terms.

tr-Term : U₁.Term n → U₂.Term n
tr-Term t = U₂.toTerm (tr-Term′ (U₁.fromTerm t))

-- Translation of contexts.

tr-Con : U₁.Con U₁.Term n → U₂.Con U₂.Term n
tr-Con ε       = ε
tr-Con (Γ ∙ A) = tr-Con Γ ∙ tr-Term A

-- Translation of definition contexts.

tr-DCon : U₁.DCon (U₁.Term m) n → U₂.DCon (U₂.Term m) n
tr-DCon ε                   = ε
tr-DCon (∇ ∙⟨ o ⟩[ t ∷ A ]) = tr-DCon ∇ ∙⟨ o ⟩[ tr-Term t ∷ tr-Term A ]

-- Translation of context pairs.

tr-Cons : U₁.Cons m n → U₂.Cons m n
tr-Cons (∇ » Γ) = tr-DCon ∇ » tr-Con Γ

-- Translation of substitutions.

tr-Subst : U₁.Subst m n → U₂.Subst m n
tr-Subst σ x = tr-Term (σ x)

------------------------------------------------------------------------
-- A lemma that applies when tr-Σ is pointwise equal to tr

module _ (tr-Σ≡tr : ∀ {p} → tr-Σ p ≡ tr p) where

  -- The function tr-BinderMode b is pointwise equal to tr.

  tr-BinderMode-one-function : ∀ {p} b → tr-BinderMode b p ≡ tr p
  tr-BinderMode-one-function BMΠ     = refl
  tr-BinderMode-one-function (BMΣ _) = tr-Σ≡tr

------------------------------------------------------------------------
-- Lemmas related to definitions

opaque

  -- The relation _↦∷_∈_ is preserved by tr-Term/tr-DCon.

  tr-↦ : α ↦∷ A ∈ ∇ → α ↦∷ tr-Term A ∈ tr-DCon ∇
  tr-↦ here       = here
  tr-↦ (there α∈) = there (tr-↦ α∈)

opaque

  -- The relation _↦_∷_∈_ is preserved by tr-Term/tr-DCon.

  tr-↦∷ : α ↦ t ∷ A ∈ ∇ → α ↦ tr-Term t ∷ tr-Term A ∈ tr-DCon ∇
  tr-↦∷ here       = here
  tr-↦∷ (there α∈) = there (tr-↦∷ α∈)

opaque

  -- The relation _↦⊘∷_∈_ is preserved by tr-Term/tr-DCon.

  tr-↦⊘∷ : α ↦⊘∷ A ∈ ∇ → α ↦⊘∷ tr-Term A ∈ tr-DCon ∇
  tr-↦⊘∷ here       = here
  tr-↦⊘∷ (there α∈) = there (tr-↦⊘∷ α∈)

------------------------------------------------------------------------
-- Lemmas related to Neutral and Whnf

module _
  -- It is assumed that Unitʷ-η holds for tv₁ if it holds for tv₂.
  (Unitʷ-η→ : Type-variant.Unitʷ-η tv₂ → Type-variant.Unitʷ-η tv₁)
  where

  -- The function tr-Term preserves neutrality (given a certain
  -- assumption).

  tr-Neutral :
    (V₁ → V₂) →
    UN₁.Neutral tv₁ V₁ ∇ t → UN₂.Neutral tv₂ V₂ (tr-DCon ∇) (tr-Term t)
  tr-Neutral f = λ where
    (defn α∈)           → defn (tr-↦⊘∷ α∈)
    (var p x)           → var (f p) x
    (supᵘˡₙ n)          → supᵘˡₙ (tr-Neutral f n)
    (supᵘʳₙ n)          → supᵘʳₙ (tr-Neutral f n)
    (lowerₙ n)          → lowerₙ (tr-Neutral f n)
    (∘ₙ n)              → ∘ₙ (tr-Neutral f n)
    (fstₙ n)            → fstₙ (tr-Neutral f n)
    (sndₙ n)            → sndₙ (tr-Neutral f n)
    (natrecₙ n)         → natrecₙ (tr-Neutral f n)
    (prodrecₙ n)        → prodrecₙ (tr-Neutral f n)
    (emptyrecₙ n)       → emptyrecₙ (tr-Neutral f n)
    (unitrecₙ not-ok n) → unitrecₙ (not-ok ∘→ Unitʷ-η→)
                            (tr-Neutral f n)
    (Jₙ n)              → Jₙ (tr-Neutral f n)
    (Kₙ n)              → Kₙ (tr-Neutral f n)
    ([]-congₙ n)        → []-congₙ (tr-Neutral f n)

  -- The function tr-Term takes WHNFs to WHNFs.

  tr-Whnf : UW₁.Whnf tv₁ ∇ t → UW₂.Whnf tv₂ (tr-DCon ∇) (tr-Term t)
  tr-Whnf Uₙ                = Uₙ
  tr-Whnf (ΠΣₙ {b = BMΠ})   = ΠΣₙ
  tr-Whnf (ΠΣₙ {b = BMΣ _}) = ΠΣₙ
  tr-Whnf ℕₙ                = ℕₙ
  tr-Whnf Unitₙ             = Unitₙ
  tr-Whnf Emptyₙ            = Emptyₙ
  tr-Whnf Idₙ               = Idₙ
  tr-Whnf lamₙ              = lamₙ
  tr-Whnf zeroₙ             = zeroₙ
  tr-Whnf sucₙ              = sucₙ
  tr-Whnf starₙ             = starₙ
  tr-Whnf prodₙ             = prodₙ
  tr-Whnf rflₙ              = rflₙ
  tr-Whnf Levelₙ            = Levelₙ
  tr-Whnf Liftₙ             = Liftₙ
  tr-Whnf zeroᵘₙ            = zeroᵘₙ
  tr-Whnf sucᵘₙ             = sucᵘₙ
  tr-Whnf liftₙ             = liftₙ
  tr-Whnf (ne n)            = ne (tr-Neutral _ n)

------------------------------------------------------------------------
-- Translation commutes with various things

mutual

  -- Weakening commutes with translation of the alternative term
  -- representation.

  tr-Term′-wk′ : ∀ {t} → U₂.wk′ ρ (tr-Term′ t) ≡ tr-Term′ (U₁.wk′ ρ t)
  tr-Term′-wk′ {t = var _}   = refl
  tr-Term′-wk′ {t = gen _ _} = cong (gen _) tr-GenTs-wkGen

  -- Weakening commutes with translation.

  tr-GenTs-wkGen : U₂.wkGen ρ (tr-GenTs ts) ≡ tr-GenTs (U₁.wkGen ρ ts)
  tr-GenTs-wkGen {ts = []}     = refl
  tr-GenTs-wkGen {ts = _ ∷ₜ _} = cong₂ _∷ₜ_ tr-Term′-wk′ tr-GenTs-wkGen

-- Weakening commutes with translation.

tr-Term-wk : U₂.wk ρ (tr-Term t) ≡ tr-Term (U₁.wk ρ t)
tr-Term-wk {ρ} {t} = begin
  U₂.wk ρ (U₂.toTerm (tr-Term′ (U₁.fromTerm t)))                            ≡⟨ UP₂.wk≡wk′ (U₂.toTerm (tr-Term′ (U₁.fromTerm t))) ⟩
  U₂.toTerm (U₂.wk′ ρ (U₂.fromTerm (U₂.toTerm (tr-Term′ (U₁.fromTerm t))))) ≡⟨ cong (λ x → U₂.toTerm (U₂.wk′ ρ x)) (UP₂.fromTerm∘toTerm _) ⟩
  U₂.toTerm (U₂.wk′ ρ (tr-Term′ (U₁.fromTerm t)))                           ≡⟨ cong U₂.toTerm tr-Term′-wk′ ⟩
  U₂.toTerm (tr-Term′ (U₁.wk′ ρ (U₁.fromTerm t)))                           ≡˘⟨ cong (λ x → U₂.toTerm (tr-Term′ x)) (UP₁.fromTerm∘toTerm _) ⟩
  U₂.toTerm (tr-Term′ (U₁.fromTerm (U₁.toTerm (U₁.wk′ ρ (U₁.fromTerm t))))) ≡˘⟨ cong (λ x → U₂.toTerm (tr-Term′ (U₁.fromTerm x))) (UP₁.wk≡wk′ t) ⟩
  U₂.toTerm (tr-Term′ (U₁.fromTerm (U₁.wk ρ t)))                            ∎

-- The function liftSubst commutes with translation.

tr-Subst-liftSubst :
  ∀ x → U₂.liftSubst (tr-Subst σ) x ≡ tr-Subst (U₁.liftSubst σ) x
tr-Subst-liftSubst x0     = refl
tr-Subst-liftSubst (_ +1) = tr-Term-wk

-- The function liftSubstn commutes with translation.

tr-Subst-liftSubstn :
  ∀ n {x} →
  U₂.liftSubstn (tr-Subst σ) n x ≡ tr-Subst (U₁.liftSubstn σ n) x
tr-Subst-liftSubstn 0                      = refl
tr-Subst-liftSubstn {σ = σ} (1+ n) {x = x} =
  U₂.liftSubst (U₂.liftSubstn (tr-Subst σ) n) x  ≡⟨ UP₂.substVar-lift (λ _ → tr-Subst-liftSubstn n) x ⟩
  U₂.liftSubst (tr-Subst (U₁.liftSubstn σ n)) x  ≡⟨ tr-Subst-liftSubst x ⟩
  tr-Subst (U₁.liftSubst (U₁.liftSubstn σ n)) x  ∎

-- The function consSubst commutes with translation.

tr-Subst-consSubst :
  ∀ x →
  U₂.consSubst (tr-Subst σ) (tr-Term t) x ≡
  tr-Subst (U₁.consSubst σ t) x
tr-Subst-consSubst x0     = refl
tr-Subst-consSubst (_ +1) = refl

-- The function idSubst commutes with translation.

tr-Subst-idSubst : U₂.idSubst x ≡ tr-Subst U₁.idSubst x
tr-Subst-idSubst = refl

-- The function sgSubst commutes with translation.

tr-Subst-sgSubst :
  ∀ x → U₂.sgSubst (tr-Term u) x ≡ tr-Subst (U₁.sgSubst u) x
tr-Subst-sgSubst = tr-Subst-consSubst

-- The function wk1Subst commutes with translation.

tr-Subst-wk1Subst :
  ∀ x → U₂.wk1Subst (tr-Subst σ) x ≡ tr-Subst (U₁.wk1Subst σ) x
tr-Subst-wk1Subst x0     = tr-Term-wk
tr-Subst-wk1Subst (_ +1) = tr-Term-wk

mutual

  -- Substitution commutes with translation of the alternative term
  -- representation.

  tr-Term′-subst′ :
    ∀ t → tr-Term′ t U₂.[ tr-Subst σ ]′ ≡ tr-Term′ (t U₁.[ σ ]′)
  tr-Term′-subst′ (var _)   = UP₂.fromTerm∘toTerm _
  tr-Term′-subst′ (gen _ _) = cong (gen _) tr-GenTs-substGen

  -- Substitution commutes with translation.

  tr-GenTs-substGen :
    U₂.substGen (tr-Subst σ) (tr-GenTs ts) ≡ tr-GenTs (U₁.substGen σ ts)
  tr-GenTs-substGen         {ts = []}               = refl
  tr-GenTs-substGen {σ = σ} {ts = _∷ₜ_ {b = b} t _} = cong₂ _∷ₜ_
    (tr-Term′ t U₂.[ U₂.liftSubstn (tr-Subst σ) b ]′  ≡⟨ UP₂.substVar-to-subst′ (λ _ → tr-Subst-liftSubstn b) (tr-Term′ t) ⟩
     tr-Term′ t U₂.[ tr-Subst (U₁.liftSubstn σ b) ]′  ≡⟨ tr-Term′-subst′ t ⟩
     tr-Term′ (t U₁.[ U₁.liftSubstn σ b ]′)           ∎)
    tr-GenTs-substGen

-- Substitution commutes with translation.

tr-Term-subst :
  ∀ t → tr-Term t U₂.[ tr-Subst σ ] ≡ tr-Term (t U₁.[ σ ])
tr-Term-subst {σ} t = begin
  U₂.toTerm (tr-Term′ (U₁.fromTerm t)) U₂.[ tr-Subst σ ]                   ≡⟨ UP₂.subst≡subst′ (U₂.toTerm (tr-Term′ (U₁.fromTerm t))) ⟩
  U₂.toTerm (U₂.fromTerm (U₂.toTerm (tr-Term′ (U₁.fromTerm t)))
     U₂.[ tr-Subst σ ]′)                                                   ≡⟨ cong (λ x → U₂.toTerm (x U₂.[ tr-Subst σ ]′))
                                                                               (UP₂.fromTerm∘toTerm (tr-Term′ (U₁.fromTerm t))) ⟩
  U₂.toTerm (tr-Term′ (U₁.fromTerm t) U₂.[ tr-Subst σ ]′)                  ≡⟨ cong U₂.toTerm (tr-Term′-subst′ (U₁.fromTerm t)) ⟩
  U₂.toTerm (tr-Term′ (U₁.fromTerm t U₁.[ σ ]′))                           ≡˘⟨ cong (λ x → U₂.toTerm (tr-Term′ x)) (UP₁.fromTerm∘toTerm _) ⟩
  U₂.toTerm (tr-Term′ (U₁.fromTerm (U₁.toTerm (U₁.fromTerm t U₁.[ σ ]′)))) ≡˘⟨ cong (λ x → U₂.toTerm (tr-Term′ (U₁.fromTerm x))) (UP₁.subst≡subst′ t) ⟩
  U₂.toTerm (tr-Term′ (U₁.fromTerm (t U₁.[ σ ])))                          ∎

-- Substitution commutes with translation.

tr-Term-[] : ∀ t → tr-Term t U₂.[ tr-Term u ]₀ ≡ tr-Term (t U₁.[ u ]₀)
tr-Term-[] {u = u} t =
  tr-Term t U₂.[ U₂.sgSubst (tr-Term u) ]   ≡⟨ UP₂.substVar-to-subst tr-Subst-sgSubst (tr-Term t) ⟩
  tr-Term t U₂.[ tr-Subst (U₁.sgSubst u) ]  ≡⟨ tr-Term-subst t ⟩
  tr-Term (t U₁.[ U₁.sgSubst u ])           ∎

private

  -- A lemma used below.

  [,]-lemma :
    ∀ x →
    U₂.consSubst (U₂.sgSubst (tr-Term t)) (tr-Term u) x ≡
    tr-Subst (U₁.consSubst (U₁.sgSubst t) u) x
  [,]-lemma {t = t} {u = u} x =
    U₂.consSubst (U₂.sgSubst (tr-Term t)) (tr-Term u) x   ≡⟨ UP₂.consSubst-cong refl tr-Subst-sgSubst x ⟩
    U₂.consSubst (tr-Subst (U₁.sgSubst t)) (tr-Term u) x  ≡⟨ tr-Subst-consSubst x ⟩
    tr-Subst (U₁.consSubst (U₁.sgSubst t) u) x            ∎

-- Substitution commutes with translation.

tr-Term-[,] :
  ∀ t →
  tr-Term t U₂.[ tr-Term u , tr-Term v ]₁₀ ≡ tr-Term (t U₁.[ u , v ]₁₀)
tr-Term-[,] {u = u} {v = v} t =
  tr-Term t
    U₂.[ U₂.consSubst (U₂.sgSubst (tr-Term u)) (tr-Term v) ]  ≡⟨ UP₂.substVar-to-subst [,]-lemma (tr-Term t) ⟩

  tr-Term t
    U₂.[ tr-Subst (U₁.consSubst (U₁.sgSubst u) v)]            ≡⟨ tr-Term-subst t ⟩

  tr-Term (t U₁.[ U₁.consSubst (U₁.sgSubst u) v ])            ∎

private

  -- A lemma used below.

  []↑-lemma :
    ∀ x →
    U₂.consSubst (U₂.wk1Subst U₂.idSubst) (tr-Term t) x ≡
    tr-Subst (U₁.consSubst (U₁.wk1Subst U₁.idSubst) t) x
  []↑-lemma {t = t} x =
    U₂.consSubst (U₂.wk1Subst U₂.idSubst) (tr-Term t) x             ≡⟨ UP₂.consSubst-cong refl tr-Subst-wk1Subst x ⟩
    U₂.consSubst (tr-Subst (U₁.wk1Subst U₁.idSubst)) (tr-Term t) x  ≡⟨ tr-Subst-consSubst x ⟩
    tr-Subst (U₁.consSubst (U₁.wk1Subst U₁.idSubst) t) x            ∎

-- Substitution commutes with translation.

tr-Term-[]↑ : ∀ t → tr-Term t U₂.[ tr-Term u ]↑ ≡ tr-Term (t U₁.[ u ]↑)
tr-Term-[]↑ {u = u} t =
  tr-Term t
    U₂.[ U₂.consSubst (U₂.wk1Subst U₂.idSubst) (tr-Term u) ]   ≡⟨ UP₂.substVar-to-subst []↑-lemma (tr-Term t) ⟩

  tr-Term t
    U₂.[ tr-Subst (U₁.consSubst (U₁.wk1Subst U₁.idSubst) u) ]  ≡⟨ tr-Term-subst t ⟩

  tr-Term (t U₁.[ U₁.consSubst (U₁.wk1Subst U₁.idSubst) u ])   ∎

private

  -- A lemma used below.

  []↑²-lemma :
    ∀ x →
    U₂.consSubst (U₂.wk1Subst (U₂.wk1Subst U₂.idSubst)) (tr-Term t) x ≡
    tr-Subst (U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) t) x
  []↑²-lemma {t = t} x =
    U₂.consSubst (U₂.wk1Subst (U₂.wk1Subst U₂.idSubst)) (tr-Term t) x   ≡⟨ UP₂.consSubst-cong refl (UP₂.wk1Subst-cong tr-Subst-wk1Subst) x ⟩

    U₂.consSubst (U₂.wk1Subst (tr-Subst (U₁.wk1Subst U₁.idSubst)))
      (tr-Term t) x                                                     ≡⟨ UP₂.consSubst-cong refl tr-Subst-wk1Subst x ⟩

    U₂.consSubst (tr-Subst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)))
      (tr-Term t) x                                                     ≡⟨ tr-Subst-consSubst x ⟩

    tr-Subst (U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) t) x  ∎

-- Substitution commutes with translation.

tr-Term-[]↑² :
  ∀ t → tr-Term t U₂.[ tr-Term u ]↑² ≡ tr-Term (t U₁.[ u ]↑²)
tr-Term-[]↑² {u = u} t =
  tr-Term t
    U₂.[ U₂.consSubst (U₂.wk1Subst (U₂.wk1Subst U₂.idSubst)) (tr-Term u) ]   ≡⟨ UP₂.substVar-to-subst []↑²-lemma (tr-Term t) ⟩

  tr-Term t
    U₂.[ tr-Subst (U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) u) ]  ≡⟨ tr-Term-subst t ⟩

  tr-Term (t U₁.[ U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) u ])   ∎

------------------------------------------------------------------------
-- Inversion lemmas for translation

-- Inversion for defn.

tr-Term-defn : tr-Term t ≡ defn α → t ≡ defn α
tr-Term-defn {t = defn _}                refl = refl
tr-Term-defn {t = var _}                 ()
tr-Term-defn {t = Level}                 ()
tr-Term-defn {t = zeroᵘ}                 ()
tr-Term-defn {t = sucᵘ _}                ()
tr-Term-defn {t = _ supᵘ _}              ()
tr-Term-defn {t = Lift _ _}              ()
tr-Term-defn {t = lift _}                ()
tr-Term-defn {t = lower _}               ()
tr-Term-defn {t = U _}                   ()
tr-Term-defn {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-defn {t = lam _ _}               ()
tr-Term-defn {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-defn {t = prod _ _ _ _}          ()
tr-Term-defn {t = fst _ _}               ()
tr-Term-defn {t = snd _ _}               ()
tr-Term-defn {t = prodrec _ _ _ _ _ _}   ()
tr-Term-defn {t = Empty}                 ()
tr-Term-defn {t = emptyrec _ _ _}        ()
tr-Term-defn {t = Unit _}                ()
tr-Term-defn {t = star _}                ()
tr-Term-defn {t = unitrec _ _ _ _ _}     ()
tr-Term-defn {t = ℕ}                     ()
tr-Term-defn {t = zero}                  ()
tr-Term-defn {t = suc _}                 ()
tr-Term-defn {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-defn {t = Id _ _ _}              ()
tr-Term-defn {t = rfl}                   ()
tr-Term-defn {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-defn {t = K _ _ _ _ _ _}         ()
tr-Term-defn {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for var.

tr-Term-var : tr-Term t ≡ var x → t ≡ var x
tr-Term-var {t = var _}                 refl = refl
tr-Term-var {t = defn _}                ()
tr-Term-var {t = Level}                 ()
tr-Term-var {t = zeroᵘ}                 ()
tr-Term-var {t = sucᵘ _}                ()
tr-Term-var {t = _ supᵘ _}              ()
tr-Term-var {t = U _}                   ()
tr-Term-var {t = Lift _ _}              ()
tr-Term-var {t = lift _}                ()
tr-Term-var {t = lower _}               ()
tr-Term-var {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-var {t = lam _ _}               ()
tr-Term-var {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-var {t = prod _ _ _ _}          ()
tr-Term-var {t = fst _ _}               ()
tr-Term-var {t = snd _ _}               ()
tr-Term-var {t = prodrec _ _ _ _ _ _}   ()
tr-Term-var {t = Empty}                 ()
tr-Term-var {t = emptyrec _ _ _}        ()
tr-Term-var {t = Unit _}                ()
tr-Term-var {t = star _}                ()
tr-Term-var {t = unitrec _ _ _ _ _}     ()
tr-Term-var {t = ℕ}                     ()
tr-Term-var {t = zero}                  ()
tr-Term-var {t = suc _}                 ()
tr-Term-var {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-var {t = Id _ _ _}              ()
tr-Term-var {t = rfl}                   ()
tr-Term-var {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-var {t = K _ _ _ _ _ _}         ()
tr-Term-var {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for Level.

tr-Term-Level :
  tr-Term t ≡ Level →
  t ≡ Level
tr-Term-Level {t = Level}                 refl = refl
tr-Term-Level {t = var _}                 ()
tr-Term-Level {t = defn _}                ()
tr-Term-Level {t = zeroᵘ}                 ()
tr-Term-Level {t = sucᵘ _}                ()
tr-Term-Level {t = _ supᵘ _}              ()
tr-Term-Level {t = U _}                   ()
tr-Term-Level {t = Lift _ _}              ()
tr-Term-Level {t = lift _}                ()
tr-Term-Level {t = lower _}               ()
tr-Term-Level {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-Level {t = lam _ _}               ()
tr-Term-Level {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-Level {t = prod _ _ _ _}          ()
tr-Term-Level {t = fst _ _}               ()
tr-Term-Level {t = snd _ _}               ()
tr-Term-Level {t = prodrec _ _ _ _ _ _}   ()
tr-Term-Level {t = Empty}                 ()
tr-Term-Level {t = emptyrec _ _ _}        ()
tr-Term-Level {t = Unit _}                ()
tr-Term-Level {t = star _}                ()
tr-Term-Level {t = unitrec _ _ _ _ _}     ()
tr-Term-Level {t = ℕ}                     ()
tr-Term-Level {t = zero}                  ()
tr-Term-Level {t = suc _}                 ()
tr-Term-Level {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-Level {t = Id _ _ _}              ()
tr-Term-Level {t = rfl}                   ()
tr-Term-Level {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-Level {t = K _ _ _ _ _ _}         ()
tr-Term-Level {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for zeroᵘ.

tr-Term-zeroᵘ :
  tr-Term t ≡ zeroᵘ →
  t ≡ zeroᵘ
tr-Term-zeroᵘ {t = zeroᵘ}                 refl = refl
tr-Term-zeroᵘ {t = var _}                 ()
tr-Term-zeroᵘ {t = defn _}                ()
tr-Term-zeroᵘ {t = Level}                 ()
tr-Term-zeroᵘ {t = sucᵘ _}                ()
tr-Term-zeroᵘ {t = _ supᵘ _}              ()
tr-Term-zeroᵘ {t = U _}                   ()
tr-Term-zeroᵘ {t = Lift _ _}              ()
tr-Term-zeroᵘ {t = lift _}                ()
tr-Term-zeroᵘ {t = lower _}               ()
tr-Term-zeroᵘ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-zeroᵘ {t = lam _ _}               ()
tr-Term-zeroᵘ {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-zeroᵘ {t = prod _ _ _ _}          ()
tr-Term-zeroᵘ {t = fst _ _}               ()
tr-Term-zeroᵘ {t = snd _ _}               ()
tr-Term-zeroᵘ {t = prodrec _ _ _ _ _ _}   ()
tr-Term-zeroᵘ {t = Empty}                 ()
tr-Term-zeroᵘ {t = emptyrec _ _ _}        ()
tr-Term-zeroᵘ {t = Unit _}                ()
tr-Term-zeroᵘ {t = star _}                ()
tr-Term-zeroᵘ {t = unitrec _ _ _ _ _}     ()
tr-Term-zeroᵘ {t = ℕ}                     ()
tr-Term-zeroᵘ {t = zero}                  ()
tr-Term-zeroᵘ {t = suc _}                 ()
tr-Term-zeroᵘ {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-zeroᵘ {t = Id _ _ _}              ()
tr-Term-zeroᵘ {t = rfl}                   ()
tr-Term-zeroᵘ {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-zeroᵘ {t = K _ _ _ _ _ _}         ()
tr-Term-zeroᵘ {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for sucᵘ.

tr-Term-sucᵘ :
  tr-Term t ≡ sucᵘ l →
  ∃ λ l′ → t ≡ sucᵘ l′ × tr-Term l′ ≡ l
tr-Term-sucᵘ {t = sucᵘ _}                refl = _ # refl # refl
tr-Term-sucᵘ {t = var _}                 ()
tr-Term-sucᵘ {t = defn _}                ()
tr-Term-sucᵘ {t = Level}                 ()
tr-Term-sucᵘ {t = zeroᵘ}                 ()
tr-Term-sucᵘ {t = _ supᵘ _}              ()
tr-Term-sucᵘ {t = U _}                   ()
tr-Term-sucᵘ {t = Lift _ _}              ()
tr-Term-sucᵘ {t = lift _}                ()
tr-Term-sucᵘ {t = lower _}               ()
tr-Term-sucᵘ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-sucᵘ {t = lam _ _}               ()
tr-Term-sucᵘ {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-sucᵘ {t = prod _ _ _ _}          ()
tr-Term-sucᵘ {t = fst _ _}               ()
tr-Term-sucᵘ {t = snd _ _}               ()
tr-Term-sucᵘ {t = prodrec _ _ _ _ _ _}   ()
tr-Term-sucᵘ {t = Empty}                 ()
tr-Term-sucᵘ {t = emptyrec _ _ _}        ()
tr-Term-sucᵘ {t = Unit _}                ()
tr-Term-sucᵘ {t = star _}                ()
tr-Term-sucᵘ {t = unitrec _ _ _ _ _}     ()
tr-Term-sucᵘ {t = ℕ}                     ()
tr-Term-sucᵘ {t = zero}                  ()
tr-Term-sucᵘ {t = suc _}                 ()
tr-Term-sucᵘ {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-sucᵘ {t = Id _ _ _}              ()
tr-Term-sucᵘ {t = rfl}                   ()
tr-Term-sucᵘ {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-sucᵘ {t = K _ _ _ _ _ _}         ()
tr-Term-sucᵘ {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for _supᵘ_.

tr-Term-supᵘ :
  tr-Term t ≡ l₁ supᵘ l₂ →
  ∃₂ λ l₁′ l₂′ →
     t ≡ l₁′ supᵘ l₂′ × tr-Term l₁′ ≡ l₁ × tr-Term l₂′ ≡ l₂
tr-Term-supᵘ {t = _ supᵘ _} refl =
  _ # _ # refl # refl # refl
tr-Term-supᵘ {t = var _}                 ()
tr-Term-supᵘ {t = defn _}                ()
tr-Term-supᵘ {t = Level}                 ()
tr-Term-supᵘ {t = zeroᵘ}                 ()
tr-Term-supᵘ {t = sucᵘ _}                ()
tr-Term-supᵘ {t = U _}                   ()
tr-Term-supᵘ {t = Lift _ _}              ()
tr-Term-supᵘ {t = lift _}                ()
tr-Term-supᵘ {t = lower _}               ()
tr-Term-supᵘ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-supᵘ {t = lam _ _}               ()
tr-Term-supᵘ {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-supᵘ {t = prod _ _ _ _}          ()
tr-Term-supᵘ {t = fst _ _}               ()
tr-Term-supᵘ {t = snd _ _}               ()
tr-Term-supᵘ {t = prodrec _ _ _ _ _ _}   ()
tr-Term-supᵘ {t = Empty}                 ()
tr-Term-supᵘ {t = emptyrec _ _ _}        ()
tr-Term-supᵘ {t = Unit _}                ()
tr-Term-supᵘ {t = star _}                ()
tr-Term-supᵘ {t = unitrec _ _ _ _ _}     ()
tr-Term-supᵘ {t = ℕ}                     ()
tr-Term-supᵘ {t = zero}                  ()
tr-Term-supᵘ {t = suc _}                 ()
tr-Term-supᵘ {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-supᵘ {t = Id _ _ _}              ()
tr-Term-supᵘ {t = rfl}                   ()
tr-Term-supᵘ {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-supᵘ {t = K _ _ _ _ _ _}         ()
tr-Term-supᵘ {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for U.

tr-Term-U :
  tr-Term t ≡ U l →
  ∃ λ l′ → t ≡ U l′ × tr-Term l′ ≡ l
tr-Term-U {t = U _}                   refl = _ # refl # refl
tr-Term-U {t = defn _}                ()
tr-Term-U {t = var _}                 ()
tr-Term-U {t = Level}                 ()
tr-Term-U {t = zeroᵘ}                 ()
tr-Term-U {t = sucᵘ _}                ()
tr-Term-U {t = _ supᵘ _}              ()
tr-Term-U {t = Lift _ _}              ()
tr-Term-U {t = lift _}                ()
tr-Term-U {t = lower _}               ()
tr-Term-U {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-U {t = lam _ _}               ()
tr-Term-U {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-U {t = prod _ _ _ _}          ()
tr-Term-U {t = fst _ _}               ()
tr-Term-U {t = snd _ _}               ()
tr-Term-U {t = prodrec _ _ _ _ _ _}   ()
tr-Term-U {t = Empty}                 ()
tr-Term-U {t = emptyrec _ _ _}        ()
tr-Term-U {t = Unit _}                ()
tr-Term-U {t = star _}                ()
tr-Term-U {t = unitrec _ _ _ _ _}     ()
tr-Term-U {t = ℕ}                     ()
tr-Term-U {t = zero}                  ()
tr-Term-U {t = suc _}                 ()
tr-Term-U {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-U {t = Id _ _ _}              ()
tr-Term-U {t = rfl}                   ()
tr-Term-U {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-U {t = K _ _ _ _ _ _}         ()
tr-Term-U {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for Lift.

tr-Term-Lift :
  tr-Term t ≡ Lift l A →
  ∃₂ λ l′ A′ → t ≡ Lift l′ A′ × tr-Term l′ ≡ l × tr-Term A′ ≡ A
tr-Term-Lift {t = Lift _ _} refl =
  _ # _ # refl # refl # refl
tr-Term-Lift {t = var _}                 ()
tr-Term-Lift {t = defn _}                ()
tr-Term-Lift {t = Level}                 ()
tr-Term-Lift {t = zeroᵘ}                 ()
tr-Term-Lift {t = sucᵘ _}                ()
tr-Term-Lift {t = _ supᵘ _}              ()
tr-Term-Lift {t = U _}                   ()
tr-Term-Lift {t = lift _}                ()
tr-Term-Lift {t = lower _}               ()
tr-Term-Lift {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-Lift {t = lam _ _}               ()
tr-Term-Lift {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-Lift {t = prod _ _ _ _}          ()
tr-Term-Lift {t = fst _ _}               ()
tr-Term-Lift {t = snd _ _}               ()
tr-Term-Lift {t = prodrec _ _ _ _ _ _}   ()
tr-Term-Lift {t = Empty}                 ()
tr-Term-Lift {t = emptyrec _ _ _}        ()
tr-Term-Lift {t = Unit _}                ()
tr-Term-Lift {t = star _}                ()
tr-Term-Lift {t = unitrec _ _ _ _ _}     ()
tr-Term-Lift {t = ℕ}                     ()
tr-Term-Lift {t = zero}                  ()
tr-Term-Lift {t = suc _}                 ()
tr-Term-Lift {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-Lift {t = Id _ _ _}              ()
tr-Term-Lift {t = rfl}                   ()
tr-Term-Lift {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-Lift {t = K _ _ _ _ _ _}         ()
tr-Term-Lift {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for lift.

tr-Term-lift :
  tr-Term t ≡ lift u →
  ∃ λ u′ → t ≡ lift u′ × tr-Term u′ ≡ u
tr-Term-lift {t = lift _}                refl = _ # refl # refl
tr-Term-lift {t = var _}                 ()
tr-Term-lift {t = defn _}                ()
tr-Term-lift {t = Level}                 ()
tr-Term-lift {t = zeroᵘ}                 ()
tr-Term-lift {t = sucᵘ _}                ()
tr-Term-lift {t = _ supᵘ _}              ()
tr-Term-lift {t = U _}                   ()
tr-Term-lift {t = Lift _ _}              ()
tr-Term-lift {t = lower _}               ()
tr-Term-lift {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-lift {t = lam _ _}               ()
tr-Term-lift {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-lift {t = prod _ _ _ _}          ()
tr-Term-lift {t = fst _ _}               ()
tr-Term-lift {t = snd _ _}               ()
tr-Term-lift {t = prodrec _ _ _ _ _ _}   ()
tr-Term-lift {t = Empty}                 ()
tr-Term-lift {t = emptyrec _ _ _}        ()
tr-Term-lift {t = Unit _}                ()
tr-Term-lift {t = star _}                ()
tr-Term-lift {t = unitrec _ _ _ _ _}     ()
tr-Term-lift {t = ℕ}                     ()
tr-Term-lift {t = zero}                  ()
tr-Term-lift {t = suc _}                 ()
tr-Term-lift {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-lift {t = Id _ _ _}              ()
tr-Term-lift {t = rfl}                   ()
tr-Term-lift {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-lift {t = K _ _ _ _ _ _}         ()
tr-Term-lift {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for lower.

tr-Term-lower :
  tr-Term t ≡ lower u →
  ∃ λ u′ → t ≡ lower u′ × tr-Term u′ ≡ u
tr-Term-lower {t = lower _}               refl = _ # refl # refl
tr-Term-lower {t = var _}                 ()
tr-Term-lower {t = defn _}                ()
tr-Term-lower {t = Level}                 ()
tr-Term-lower {t = zeroᵘ}                 ()
tr-Term-lower {t = sucᵘ _}                ()
tr-Term-lower {t = _ supᵘ _}              ()
tr-Term-lower {t = U _}                   ()
tr-Term-lower {t = Lift _ _}              ()
tr-Term-lower {t = lift _}                ()
tr-Term-lower {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-lower {t = lam _ _}               ()
tr-Term-lower {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-lower {t = prod _ _ _ _}          ()
tr-Term-lower {t = fst _ _}               ()
tr-Term-lower {t = snd _ _}               ()
tr-Term-lower {t = prodrec _ _ _ _ _ _}   ()
tr-Term-lower {t = Empty}                 ()
tr-Term-lower {t = emptyrec _ _ _}        ()
tr-Term-lower {t = Unit _}                ()
tr-Term-lower {t = star _}                ()
tr-Term-lower {t = unitrec _ _ _ _ _}     ()
tr-Term-lower {t = ℕ}                     ()
tr-Term-lower {t = zero}                  ()
tr-Term-lower {t = suc _}                 ()
tr-Term-lower {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-lower {t = Id _ _ _}              ()
tr-Term-lower {t = rfl}                   ()
tr-Term-lower {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-lower {t = K _ _ _ _ _ _}         ()
tr-Term-lower {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for ΠΣ⟨_⟩_,_▷_▹_.

tr-Term-ΠΣ :
  tr-Term t ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  ∃₄ λ p′ q′ A′ B′ →
     t ≡ ΠΣ⟨ b ⟩ p′ , q′ ▷ A′ ▹ B′ ×
     tr-BinderMode b p′ ≡ p × tr q′ ≡ q ×
     tr-Term A′ ≡ A × tr-Term B′ ≡ B
tr-Term-ΠΣ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} refl =
  _ # _ # _ # _ # refl # refl # refl # refl # refl
tr-Term-ΠΣ {t = defn _}               ()
tr-Term-ΠΣ {t = var _}                ()
tr-Term-ΠΣ {t = Level}                ()
tr-Term-ΠΣ {t = zeroᵘ}                ()
tr-Term-ΠΣ {t = sucᵘ _}               ()
tr-Term-ΠΣ {t = _ supᵘ _}             ()
tr-Term-ΠΣ {t = U _}                  ()
tr-Term-ΠΣ {t = Lift _ _}             ()
tr-Term-ΠΣ {t = lift _}               ()
tr-Term-ΠΣ {t = lower _}              ()
tr-Term-ΠΣ {t = lam _ _}              ()
tr-Term-ΠΣ {t = _ ∘⟨ _ ⟩ _}           ()
tr-Term-ΠΣ {t = prod _ _ _ _}         ()
tr-Term-ΠΣ {t = fst _ _}              ()
tr-Term-ΠΣ {t = snd _ _}              ()
tr-Term-ΠΣ {t = prodrec _ _ _ _ _ _}  ()
tr-Term-ΠΣ {t = Empty}                ()
tr-Term-ΠΣ {t = emptyrec _ _ _}       ()
tr-Term-ΠΣ {t = Unit _}               ()
tr-Term-ΠΣ {t = star _}               ()
tr-Term-ΠΣ {t = unitrec _ _ _ _ _}    ()
tr-Term-ΠΣ {t = ℕ}                    ()
tr-Term-ΠΣ {t = zero}                 ()
tr-Term-ΠΣ {t = suc _}                ()
tr-Term-ΠΣ {t = natrec _ _ _ _ _ _ _} ()
tr-Term-ΠΣ {t = Id _ _ _}             ()
tr-Term-ΠΣ {t = rfl}                  ()
tr-Term-ΠΣ {t = J _ _ _ _ _ _ _ _}    ()
tr-Term-ΠΣ {t = K _ _ _ _ _ _}        ()
tr-Term-ΠΣ {t = []-cong _ _ _ _ _ _}  ()

-- Inversion for lam.

tr-Term-lam :
  tr-Term t ≡ lam p u →
  ∃₂ λ p′ u′ → t ≡ lam p′ u′ × tr p′ ≡ p × tr-Term u′ ≡ u
tr-Term-lam {t = lam _ _} refl =
  _ # _ # refl # refl # refl
tr-Term-lam {t = defn _}                ()
tr-Term-lam {t = var _}                 ()
tr-Term-lam {t = Level}                 ()
tr-Term-lam {t = zeroᵘ}                 ()
tr-Term-lam {t = sucᵘ _}                ()
tr-Term-lam {t = _ supᵘ _}              ()
tr-Term-lam {t = U _}                   ()
tr-Term-lam {t = Lift _ _}              ()
tr-Term-lam {t = lift _}                ()
tr-Term-lam {t = lower _}               ()
tr-Term-lam {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-lam {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-lam {t = prod _ _ _ _}          ()
tr-Term-lam {t = fst _ _}               ()
tr-Term-lam {t = snd _ _}               ()
tr-Term-lam {t = prodrec _ _ _ _ _ _}   ()
tr-Term-lam {t = Empty}                 ()
tr-Term-lam {t = emptyrec _ _ _}        ()
tr-Term-lam {t = Unit _}                ()
tr-Term-lam {t = star _}                ()
tr-Term-lam {t = unitrec _ _ _ _ _}     ()
tr-Term-lam {t = ℕ}                     ()
tr-Term-lam {t = zero}                  ()
tr-Term-lam {t = suc _}                 ()
tr-Term-lam {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-lam {t = Id _ _ _}              ()
tr-Term-lam {t = rfl}                   ()
tr-Term-lam {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-lam {t = K _ _ _ _ _ _}         ()
tr-Term-lam {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for _∘⟨_⟩_.

tr-Term-∘ :
  tr-Term t ≡ u ∘⟨ p ⟩ v →
  ∃₃ λ u′ p′ v′ →
     t ≡ u′ ∘⟨ p′ ⟩ v′ × tr-Term u′ ≡ u × tr p′ ≡ p × tr-Term v′ ≡ v
tr-Term-∘ {t = _ ∘⟨ _ ⟩ _} refl =
  _ # _ # _ # refl # refl # refl # refl
tr-Term-∘ {t = defn _}                ()
tr-Term-∘ {t = var _}                 ()
tr-Term-∘ {t = Level}                 ()
tr-Term-∘ {t = zeroᵘ}                 ()
tr-Term-∘ {t = sucᵘ _}                ()
tr-Term-∘ {t = _ supᵘ _}              ()
tr-Term-∘ {t = U _}                   ()
tr-Term-∘ {t = Lift _ _}              ()
tr-Term-∘ {t = lift _}                ()
tr-Term-∘ {t = lower _}               ()
tr-Term-∘ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-∘ {t = lam _ _}               ()
tr-Term-∘ {t = prod _ _ _ _}          ()
tr-Term-∘ {t = fst _ _}               ()
tr-Term-∘ {t = snd _ _}               ()
tr-Term-∘ {t = prodrec _ _ _ _ _ _}   ()
tr-Term-∘ {t = Empty}                 ()
tr-Term-∘ {t = emptyrec _ _ _}        ()
tr-Term-∘ {t = Unit _}                ()
tr-Term-∘ {t = star _}                ()
tr-Term-∘ {t = unitrec _ _ _ _ _}     ()
tr-Term-∘ {t = ℕ}                     ()
tr-Term-∘ {t = zero}                  ()
tr-Term-∘ {t = suc _}                 ()
tr-Term-∘ {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-∘ {t = Id _ _ _}              ()
tr-Term-∘ {t = rfl}                   ()
tr-Term-∘ {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-∘ {t = K _ _ _ _ _ _}         ()
tr-Term-∘ {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for prod.

tr-Term-prod :
  tr-Term t ≡ prod s p u v →
  ∃₃ λ p′ u′ v′ →
     t ≡ prod s p′ u′ v′ ×
     tr-BinderMode (BMΣ s) p′ ≡ p × tr-Term u′ ≡ u × tr-Term v′ ≡ v
tr-Term-prod {t = prod _ _ _ _} refl =
  _ # _ # _ # refl # refl # refl # refl
tr-Term-prod {t = defn _}                ()
tr-Term-prod {t = var _}                 ()
tr-Term-prod {t = Level}                 ()
tr-Term-prod {t = zeroᵘ}                 ()
tr-Term-prod {t = sucᵘ _}                ()
tr-Term-prod {t = _ supᵘ _}              ()
tr-Term-prod {t = U _}                   ()
tr-Term-prod {t = Lift _ _}              ()
tr-Term-prod {t = lift _}                ()
tr-Term-prod {t = lower _}               ()
tr-Term-prod {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-prod {t = lam _ _}               ()
tr-Term-prod {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-prod {t = fst _ _}               ()
tr-Term-prod {t = snd _ _}               ()
tr-Term-prod {t = prodrec _ _ _ _ _ _}   ()
tr-Term-prod {t = Empty}                 ()
tr-Term-prod {t = emptyrec _ _ _}        ()
tr-Term-prod {t = Unit _}                ()
tr-Term-prod {t = star _}                ()
tr-Term-prod {t = unitrec _ _ _ _ _}     ()
tr-Term-prod {t = ℕ}                     ()
tr-Term-prod {t = zero}                  ()
tr-Term-prod {t = suc _}                 ()
tr-Term-prod {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-prod {t = Id _ _ _}              ()
tr-Term-prod {t = rfl}                   ()
tr-Term-prod {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-prod {t = K _ _ _ _ _ _}         ()
tr-Term-prod {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for fst.

tr-Term-fst :
  tr-Term t ≡ fst p u →
  ∃₂ λ p′ u′ → t ≡ fst p′ u′ × tr-Σ p′ ≡ p × tr-Term u′ ≡ u
tr-Term-fst {t = fst _ _} refl =
  _ # _ # refl # refl # refl
tr-Term-fst {t = defn _}                ()
tr-Term-fst {t = var _}                 ()
tr-Term-fst {t = Level}                 ()
tr-Term-fst {t = zeroᵘ}                 ()
tr-Term-fst {t = sucᵘ _}                ()
tr-Term-fst {t = _ supᵘ _}              ()
tr-Term-fst {t = U _}                   ()
tr-Term-fst {t = Lift _ _}              ()
tr-Term-fst {t = lift _}                ()
tr-Term-fst {t = lower _}               ()
tr-Term-fst {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-fst {t = lam _ _}               ()
tr-Term-fst {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-fst {t = prod _ _ _ _}          ()
tr-Term-fst {t = snd _ _}               ()
tr-Term-fst {t = prodrec _ _ _ _ _ _}   ()
tr-Term-fst {t = Empty}                 ()
tr-Term-fst {t = emptyrec _ _ _}        ()
tr-Term-fst {t = Unit _}                ()
tr-Term-fst {t = star _}                ()
tr-Term-fst {t = unitrec _ _ _ _ _}     ()
tr-Term-fst {t = ℕ}                     ()
tr-Term-fst {t = zero}                  ()
tr-Term-fst {t = suc _}                 ()
tr-Term-fst {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-fst {t = Id _ _ _}              ()
tr-Term-fst {t = rfl}                   ()
tr-Term-fst {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-fst {t = K _ _ _ _ _ _}         ()
tr-Term-fst {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for snd.

tr-Term-snd :
  tr-Term t ≡ snd p u →
  ∃₂ λ p′ u′ → t ≡ snd p′ u′ × tr-Σ p′ ≡ p × tr-Term u′ ≡ u
tr-Term-snd {t = snd _ _} refl =
  _ # _ # refl # refl # refl
tr-Term-snd {t = defn _}                ()
tr-Term-snd {t = var _}                 ()
tr-Term-snd {t = Level}                 ()
tr-Term-snd {t = zeroᵘ}                 ()
tr-Term-snd {t = sucᵘ _}                ()
tr-Term-snd {t = _ supᵘ _}              ()
tr-Term-snd {t = U _}                   ()
tr-Term-snd {t = Lift _ _}              ()
tr-Term-snd {t = lift _}                ()
tr-Term-snd {t = lower _}               ()
tr-Term-snd {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-snd {t = lam _ _}               ()
tr-Term-snd {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-snd {t = prod _ _ _ _}          ()
tr-Term-snd {t = fst _ _}               ()
tr-Term-snd {t = prodrec _ _ _ _ _ _}   ()
tr-Term-snd {t = Empty}                 ()
tr-Term-snd {t = emptyrec _ _ _}        ()
tr-Term-snd {t = Unit _}                ()
tr-Term-snd {t = star _}                ()
tr-Term-snd {t = unitrec _ _ _ _ _}     ()
tr-Term-snd {t = ℕ}                     ()
tr-Term-snd {t = zero}                  ()
tr-Term-snd {t = suc _}                 ()
tr-Term-snd {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-snd {t = Id _ _ _}              ()
tr-Term-snd {t = rfl}                   ()
tr-Term-snd {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-snd {t = K _ _ _ _ _ _}         ()
tr-Term-snd {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for prodrec.

tr-Term-prodrec :
  tr-Term t ≡ prodrec r p q A u v →
  ∃₆ λ r′ p′ q′ A′ u′ v′ →
     t ≡ prodrec r′ p′ q′ A′ u′ v′ × tr r′ ≡ r × tr-Σ p′ ≡ p ×
     tr q′ ≡ q × tr-Term A′ ≡ A × tr-Term u′ ≡ u × tr-Term v′ ≡ v
tr-Term-prodrec {t = prodrec _ _ _ _ _ _} refl =
  _ # _ # _ # _ # _ # _ # refl # refl # refl # refl # refl # refl # refl
tr-Term-prodrec {t = defn _}                ()
tr-Term-prodrec {t = var _}                 ()
tr-Term-prodrec {t = Level}                 ()
tr-Term-prodrec {t = zeroᵘ}                 ()
tr-Term-prodrec {t = sucᵘ _}                ()
tr-Term-prodrec {t = _ supᵘ _}              ()
tr-Term-prodrec {t = U _}                   ()
tr-Term-prodrec {t = Lift _ _}              ()
tr-Term-prodrec {t = lift _}                ()
tr-Term-prodrec {t = lower _}               ()
tr-Term-prodrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-prodrec {t = lam _ _}               ()
tr-Term-prodrec {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-prodrec {t = prod _ _ _ _}          ()
tr-Term-prodrec {t = fst _ _}               ()
tr-Term-prodrec {t = snd _ _}               ()
tr-Term-prodrec {t = Empty}                 ()
tr-Term-prodrec {t = emptyrec _ _ _}        ()
tr-Term-prodrec {t = Unit _}                ()
tr-Term-prodrec {t = star _}                ()
tr-Term-prodrec {t = unitrec _ _ _ _ _}     ()
tr-Term-prodrec {t = ℕ}                     ()
tr-Term-prodrec {t = zero}                  ()
tr-Term-prodrec {t = suc _}                 ()
tr-Term-prodrec {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-prodrec {t = Id _ _ _}              ()
tr-Term-prodrec {t = rfl}                   ()
tr-Term-prodrec {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-prodrec {t = K _ _ _ _ _ _}         ()
tr-Term-prodrec {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for Unit.

tr-Term-Unit :
  tr-Term t ≡ Unit s → t ≡ Unit s
tr-Term-Unit {t = Unit!}                 refl = refl
tr-Term-Unit {t = defn _}                ()
tr-Term-Unit {t = var _}                 ()
tr-Term-Unit {t = Level}                 ()
tr-Term-Unit {t = zeroᵘ}                 ()
tr-Term-Unit {t = sucᵘ _}                ()
tr-Term-Unit {t = _ supᵘ _}              ()
tr-Term-Unit {t = U _}                   ()
tr-Term-Unit {t = Lift _ _}              ()
tr-Term-Unit {t = lift _}                ()
tr-Term-Unit {t = lower _}               ()
tr-Term-Unit {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-Unit {t = lam _ _}               ()
tr-Term-Unit {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-Unit {t = prod _ _ _ _}          ()
tr-Term-Unit {t = fst _ _}               ()
tr-Term-Unit {t = snd _ _}               ()
tr-Term-Unit {t = prodrec _ _ _ _ _ _}   ()
tr-Term-Unit {t = Empty}                 ()
tr-Term-Unit {t = emptyrec _ _ _}        ()
tr-Term-Unit {t = star _}                ()
tr-Term-Unit {t = unitrec _ _ _ _ _}     ()
tr-Term-Unit {t = ℕ}                     ()
tr-Term-Unit {t = zero}                  ()
tr-Term-Unit {t = suc _}                 ()
tr-Term-Unit {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-Unit {t = Id _ _ _}              ()
tr-Term-Unit {t = rfl}                   ()
tr-Term-Unit {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-Unit {t = K _ _ _ _ _ _}         ()
tr-Term-Unit {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for star.

tr-Term-star : tr-Term t ≡ star s → t ≡ star s
tr-Term-star {t = star!}                 refl = refl
tr-Term-star {t = defn _}                ()
tr-Term-star {t = var _}                 ()
tr-Term-star {t = Level}                 ()
tr-Term-star {t = zeroᵘ}                 ()
tr-Term-star {t = sucᵘ _}                ()
tr-Term-star {t = _ supᵘ _}              ()
tr-Term-star {t = U _}                   ()
tr-Term-star {t = Lift _ _}              ()
tr-Term-star {t = lift _}                ()
tr-Term-star {t = lower _}               ()
tr-Term-star {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-star {t = lam _ _}               ()
tr-Term-star {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-star {t = prod _ _ _ _}          ()
tr-Term-star {t = fst _ _}               ()
tr-Term-star {t = snd _ _}               ()
tr-Term-star {t = prodrec _ _ _ _ _ _}   ()
tr-Term-star {t = Empty}                 ()
tr-Term-star {t = emptyrec _ _ _}        ()
tr-Term-star {t = Unit _}                ()
tr-Term-star {t = unitrec _ _ _ _ _}     ()
tr-Term-star {t = ℕ}                     ()
tr-Term-star {t = zero}                  ()
tr-Term-star {t = suc _}                 ()
tr-Term-star {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-star {t = Id _ _ _}              ()
tr-Term-star {t = rfl}                   ()
tr-Term-star {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-star {t = K _ _ _ _ _ _}         ()
tr-Term-star {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for unitrec.

tr-Term-unitrec :
  tr-Term t ≡ unitrec p q A u v →
  ∃₅ λ p′ q′ A′ u′ v′ →
     t ≡ unitrec p′ q′ A′ u′ v′ × tr p′ ≡ p × tr q′ ≡ q ×
     tr-Term A′ ≡ A × tr-Term u′ ≡ u × tr-Term v′ ≡ v
tr-Term-unitrec {t = unitrec _ _ _ _ _} refl =
  _ # _ # _ # _ # _ # refl # refl # refl # refl # refl # refl
tr-Term-unitrec {t = defn _}                ()
tr-Term-unitrec {t = var _}                 ()
tr-Term-unitrec {t = Level}                 ()
tr-Term-unitrec {t = zeroᵘ}                 ()
tr-Term-unitrec {t = sucᵘ _}                ()
tr-Term-unitrec {t = _ supᵘ _}              ()
tr-Term-unitrec {t = U _}                   ()
tr-Term-unitrec {t = Lift _ _}              ()
tr-Term-unitrec {t = lift _}                ()
tr-Term-unitrec {t = lower _}               ()
tr-Term-unitrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-unitrec {t = lam _ _}               ()
tr-Term-unitrec {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-unitrec {t = prod _ _ _ _}          ()
tr-Term-unitrec {t = fst _ _}               ()
tr-Term-unitrec {t = snd _ _}               ()
tr-Term-unitrec {t = prodrec _ _ _ _ _ _}   ()
tr-Term-unitrec {t = Empty}                 ()
tr-Term-unitrec {t = emptyrec _ _ _}        ()
tr-Term-unitrec {t = Unit _}                ()
tr-Term-unitrec {t = star _}                ()
tr-Term-unitrec {t = ℕ}                     ()
tr-Term-unitrec {t = zero}                  ()
tr-Term-unitrec {t = suc _}                 ()
tr-Term-unitrec {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-unitrec {t = Id _ _ _}              ()
tr-Term-unitrec {t = rfl}                   ()
tr-Term-unitrec {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-unitrec {t = K _ _ _ _ _ _}         ()
tr-Term-unitrec {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for Empty.

tr-Term-Empty : tr-Term t ≡ Empty → t ≡ Empty
tr-Term-Empty {t = Empty}                 refl = refl
tr-Term-Empty {t = defn _}                ()
tr-Term-Empty {t = var _}                 ()
tr-Term-Empty {t = Level}                 ()
tr-Term-Empty {t = zeroᵘ}                 ()
tr-Term-Empty {t = sucᵘ _}                ()
tr-Term-Empty {t = _ supᵘ _}              ()
tr-Term-Empty {t = U _}                   ()
tr-Term-Empty {t = Lift _ _}              ()
tr-Term-Empty {t = lift _}                ()
tr-Term-Empty {t = lower _}               ()
tr-Term-Empty {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-Empty {t = lam _ _}               ()
tr-Term-Empty {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-Empty {t = prod _ _ _ _}          ()
tr-Term-Empty {t = fst _ _}               ()
tr-Term-Empty {t = snd _ _}               ()
tr-Term-Empty {t = prodrec _ _ _ _ _ _}   ()
tr-Term-Empty {t = emptyrec _ _ _}        ()
tr-Term-Empty {t = Unit _}                ()
tr-Term-Empty {t = star _}                ()
tr-Term-Empty {t = unitrec _ _ _ _ _}     ()
tr-Term-Empty {t = ℕ}                     ()
tr-Term-Empty {t = zero}                  ()
tr-Term-Empty {t = suc _}                 ()
tr-Term-Empty {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-Empty {t = Id _ _ _}              ()
tr-Term-Empty {t = rfl}                   ()
tr-Term-Empty {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-Empty {t = K _ _ _ _ _ _}         ()
tr-Term-Empty {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for emptyrec.

tr-Term-emptyrec :
  tr-Term t ≡ emptyrec p A u →
  ∃₃ λ p′ A′ u′ →
     t ≡ emptyrec p′ A′ u′ × tr p′ ≡ p × tr-Term A′ ≡ A × tr-Term u′ ≡ u
tr-Term-emptyrec {t = emptyrec _ _ _} refl =
  _ # _ # _ # refl # refl # refl # refl
tr-Term-emptyrec {t = defn _}                ()
tr-Term-emptyrec {t = var _}                 ()
tr-Term-emptyrec {t = Level}                 ()
tr-Term-emptyrec {t = zeroᵘ}                 ()
tr-Term-emptyrec {t = sucᵘ _}                ()
tr-Term-emptyrec {t = _ supᵘ _}              ()
tr-Term-emptyrec {t = U _}                   ()
tr-Term-emptyrec {t = Lift _ _}              ()
tr-Term-emptyrec {t = lift _}                ()
tr-Term-emptyrec {t = lower _}               ()
tr-Term-emptyrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-emptyrec {t = lam _ _}               ()
tr-Term-emptyrec {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-emptyrec {t = prod _ _ _ _}          ()
tr-Term-emptyrec {t = fst _ _}               ()
tr-Term-emptyrec {t = snd _ _}               ()
tr-Term-emptyrec {t = prodrec _ _ _ _ _ _}   ()
tr-Term-emptyrec {t = Empty}                 ()
tr-Term-emptyrec {t = Unit _}                ()
tr-Term-emptyrec {t = star _}                ()
tr-Term-emptyrec {t = unitrec _ _ _ _ _}     ()
tr-Term-emptyrec {t = ℕ}                     ()
tr-Term-emptyrec {t = zero}                  ()
tr-Term-emptyrec {t = suc _}                 ()
tr-Term-emptyrec {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-emptyrec {t = Id _ _ _}              ()
tr-Term-emptyrec {t = rfl}                   ()
tr-Term-emptyrec {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-emptyrec {t = K _ _ _ _ _ _}         ()
tr-Term-emptyrec {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for ℕ.

tr-Term-ℕ : tr-Term t ≡ ℕ → t ≡ ℕ
tr-Term-ℕ {t = ℕ}                     refl = refl
tr-Term-ℕ {t = defn _}                ()
tr-Term-ℕ {t = var _}                 ()
tr-Term-ℕ {t = Level}                 ()
tr-Term-ℕ {t = zeroᵘ}                 ()
tr-Term-ℕ {t = sucᵘ _}                ()
tr-Term-ℕ {t = _ supᵘ _}              ()
tr-Term-ℕ {t = U _}                   ()
tr-Term-ℕ {t = Lift _ _}              ()
tr-Term-ℕ {t = lift _}                ()
tr-Term-ℕ {t = lower _}               ()
tr-Term-ℕ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-ℕ {t = lam _ _}               ()
tr-Term-ℕ {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-ℕ {t = prod _ _ _ _}          ()
tr-Term-ℕ {t = fst _ _}               ()
tr-Term-ℕ {t = snd _ _}               ()
tr-Term-ℕ {t = prodrec _ _ _ _ _ _}   ()
tr-Term-ℕ {t = Empty}                 ()
tr-Term-ℕ {t = emptyrec _ _ _}        ()
tr-Term-ℕ {t = Unit _}                ()
tr-Term-ℕ {t = star _}                ()
tr-Term-ℕ {t = unitrec _ _ _ _ _}     ()
tr-Term-ℕ {t = zero}                  ()
tr-Term-ℕ {t = suc _}                 ()
tr-Term-ℕ {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-ℕ {t = Id _ _ _}              ()
tr-Term-ℕ {t = rfl}                   ()
tr-Term-ℕ {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-ℕ {t = K _ _ _ _ _ _}         ()
tr-Term-ℕ {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for zero.

tr-Term-zero : tr-Term t ≡ zero → t ≡ zero
tr-Term-zero {t = zero}                  refl = refl
tr-Term-zero {t = defn _}                ()
tr-Term-zero {t = var _}                 ()
tr-Term-zero {t = Level}                 ()
tr-Term-zero {t = zeroᵘ}                 ()
tr-Term-zero {t = sucᵘ _}                ()
tr-Term-zero {t = _ supᵘ _}              ()
tr-Term-zero {t = U _}                   ()
tr-Term-zero {t = Lift _ _}              ()
tr-Term-zero {t = lift _}                ()
tr-Term-zero {t = lower _}               ()
tr-Term-zero {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-zero {t = lam _ _}               ()
tr-Term-zero {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-zero {t = prod _ _ _ _}          ()
tr-Term-zero {t = fst _ _}               ()
tr-Term-zero {t = snd _ _}               ()
tr-Term-zero {t = prodrec _ _ _ _ _ _}   ()
tr-Term-zero {t = Empty}                 ()
tr-Term-zero {t = emptyrec _ _ _}        ()
tr-Term-zero {t = Unit _}                ()
tr-Term-zero {t = star _}                ()
tr-Term-zero {t = unitrec _ _ _ _ _}     ()
tr-Term-zero {t = ℕ}                     ()
tr-Term-zero {t = suc _}                 ()
tr-Term-zero {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-zero {t = Id _ _ _}              ()
tr-Term-zero {t = rfl}                   ()
tr-Term-zero {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-zero {t = K _ _ _ _ _ _}         ()
tr-Term-zero {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for suc.

tr-Term-suc :
  tr-Term t ≡ suc u →
  ∃ λ u′ → t ≡ suc u′ × tr-Term u′ ≡ u
tr-Term-suc {t = suc _}                 refl = _ # refl # refl
tr-Term-suc {t = defn _}                ()
tr-Term-suc {t = var _}                 ()
tr-Term-suc {t = Level}                 ()
tr-Term-suc {t = zeroᵘ}                 ()
tr-Term-suc {t = sucᵘ _}                ()
tr-Term-suc {t = _ supᵘ _}              ()
tr-Term-suc {t = U _}                   ()
tr-Term-suc {t = Lift _ _}              ()
tr-Term-suc {t = lift _}                ()
tr-Term-suc {t = lower _}               ()
tr-Term-suc {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-suc {t = lam _ _}               ()
tr-Term-suc {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-suc {t = prod _ _ _ _}          ()
tr-Term-suc {t = fst _ _}               ()
tr-Term-suc {t = snd _ _}               ()
tr-Term-suc {t = prodrec _ _ _ _ _ _}   ()
tr-Term-suc {t = Empty}                 ()
tr-Term-suc {t = emptyrec _ _ _}        ()
tr-Term-suc {t = Unit _}                ()
tr-Term-suc {t = star _}                ()
tr-Term-suc {t = unitrec _ _ _ _ _}     ()
tr-Term-suc {t = ℕ}                     ()
tr-Term-suc {t = zero}                  ()
tr-Term-suc {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-suc {t = Id _ _ _}              ()
tr-Term-suc {t = rfl}                   ()
tr-Term-suc {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-suc {t = K _ _ _ _ _ _}         ()
tr-Term-suc {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for natrec.

tr-Term-natrec :
  tr-Term t ≡ natrec p q r A u v w →
  ∃₇ λ p′ q′ r′ A′ u′ v′ w′ →
     t ≡ natrec p′ q′ r′ A′ u′ v′ w′ ×
     tr p′ ≡ p × tr q′ ≡ q × tr r′ ≡ r ×
     tr-Term A′ ≡ A × tr-Term u′ ≡ u × tr-Term v′ ≡ v × tr-Term w′ ≡ w
tr-Term-natrec {t = natrec _ _ _ _ _ _ _} refl =
  _ # _ # _ # _ # _ # _ # _ #
    refl # refl # refl # refl # refl # refl # refl # refl
tr-Term-natrec {t = defn _}                ()
tr-Term-natrec {t = var _}                 ()
tr-Term-natrec {t = Level}                 ()
tr-Term-natrec {t = zeroᵘ}                 ()
tr-Term-natrec {t = sucᵘ _}                ()
tr-Term-natrec {t = _ supᵘ _}              ()
tr-Term-natrec {t = U _}                   ()
tr-Term-natrec {t = Lift _ _}              ()
tr-Term-natrec {t = lift _}                ()
tr-Term-natrec {t = lower _}               ()
tr-Term-natrec {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-natrec {t = lam _ _}               ()
tr-Term-natrec {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-natrec {t = prod _ _ _ _}          ()
tr-Term-natrec {t = fst _ _}               ()
tr-Term-natrec {t = snd _ _}               ()
tr-Term-natrec {t = prodrec _ _ _ _ _ _}   ()
tr-Term-natrec {t = Empty}                 ()
tr-Term-natrec {t = emptyrec _ _ _}        ()
tr-Term-natrec {t = Unit _}                ()
tr-Term-natrec {t = star _}                ()
tr-Term-natrec {t = unitrec _ _ _ _ _}     ()
tr-Term-natrec {t = ℕ}                     ()
tr-Term-natrec {t = zero}                  ()
tr-Term-natrec {t = suc _}                 ()
tr-Term-natrec {t = Id _ _ _}              ()
tr-Term-natrec {t = rfl}                   ()
tr-Term-natrec {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-natrec {t = K _ _ _ _ _ _}         ()
tr-Term-natrec {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for Id.

tr-Term-Id :
  tr-Term v ≡ Id A t u →
  ∃₃ λ A′ t′ u′ →
     v ≡ Id A′ t′ u′ ×
     tr-Term A′ ≡ A × tr-Term t′ ≡ t × tr-Term u′ ≡ u
tr-Term-Id {v = Id _ _ _} refl =
  _ # _ # _ # refl # refl # refl # refl
tr-Term-Id {v = defn _}                ()
tr-Term-Id {v = var _}                 ()
tr-Term-Id {v = Level}                 ()
tr-Term-Id {v = zeroᵘ}                 ()
tr-Term-Id {v = sucᵘ _}                ()
tr-Term-Id {v = _ supᵘ _}              ()
tr-Term-Id {v = U _}                   ()
tr-Term-Id {v = Lift _ _}              ()
tr-Term-Id {v = lift _}                ()
tr-Term-Id {v = lower _}               ()
tr-Term-Id {v = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-Id {v = lam _ _}               ()
tr-Term-Id {v = _ ∘⟨ _ ⟩ _}            ()
tr-Term-Id {v = prod _ _ _ _}          ()
tr-Term-Id {v = fst _ _}               ()
tr-Term-Id {v = snd _ _}               ()
tr-Term-Id {v = prodrec _ _ _ _ _ _}   ()
tr-Term-Id {v = Empty}                 ()
tr-Term-Id {v = emptyrec _ _ _}        ()
tr-Term-Id {v = Unit _}                ()
tr-Term-Id {v = star _}                ()
tr-Term-Id {v = unitrec _ _ _ _ _}     ()
tr-Term-Id {v = ℕ}                     ()
tr-Term-Id {v = zero}                  ()
tr-Term-Id {v = suc _}                 ()
tr-Term-Id {v = natrec _ _ _ _ _ _ _}  ()
tr-Term-Id {v = rfl}                   ()
tr-Term-Id {v = J _ _ _ _ _ _ _ _}     ()
tr-Term-Id {v = K _ _ _ _ _ _}         ()
tr-Term-Id {v = []-cong _ _ _ _ _ _}   ()

-- Inversion for rfl.

tr-Term-rfl : tr-Term t ≡ rfl → t ≡ rfl
tr-Term-rfl {t = rfl}                   refl = refl
tr-Term-rfl {t = defn _}                ()
tr-Term-rfl {t = var _}                 ()
tr-Term-rfl {t = Level}                 ()
tr-Term-rfl {t = zeroᵘ}                 ()
tr-Term-rfl {t = sucᵘ _}                ()
tr-Term-rfl {t = _ supᵘ _}              ()
tr-Term-rfl {t = U _}                   ()
tr-Term-rfl {t = Lift _ _}              ()
tr-Term-rfl {t = lift _}                ()
tr-Term-rfl {t = lower _}               ()
tr-Term-rfl {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-rfl {t = lam _ _}               ()
tr-Term-rfl {t = _ ∘⟨ _ ⟩ _}            ()
tr-Term-rfl {t = prod _ _ _ _}          ()
tr-Term-rfl {t = fst _ _}               ()
tr-Term-rfl {t = snd _ _}               ()
tr-Term-rfl {t = prodrec _ _ _ _ _ _}   ()
tr-Term-rfl {t = Empty}                 ()
tr-Term-rfl {t = emptyrec _ _ _}        ()
tr-Term-rfl {t = Unit _}                ()
tr-Term-rfl {t = star _}                ()
tr-Term-rfl {t = unitrec _ _ _ _ _}     ()
tr-Term-rfl {t = ℕ}                     ()
tr-Term-rfl {t = zero}                  ()
tr-Term-rfl {t = suc _}                 ()
tr-Term-rfl {t = natrec _ _ _ _ _ _ _}  ()
tr-Term-rfl {t = Id _ _ _}              ()
tr-Term-rfl {t = J _ _ _ _ _ _ _ _}     ()
tr-Term-rfl {t = K _ _ _ _ _ _}         ()
tr-Term-rfl {t = []-cong _ _ _ _ _ _}   ()

-- Inversion for J.

tr-Term-J :
  tr-Term j ≡ J p q A t B u v w →
  ∃₈ λ p′ q′ A′ t′ B′ u′ v′ w′ →
     j ≡ J p′ q′ A′ t′ B′ u′ v′ w′ × tr p′ ≡ p × tr q′ ≡ q ×
     tr-Term A′ ≡ A × tr-Term t′ ≡ t × tr-Term B′ ≡ B ×
     tr-Term u′ ≡ u × tr-Term v′ ≡ v × tr-Term w′ ≡ w
tr-Term-J {j = J _ _ _ _ _ _ _ _} refl =
  _ # _ # _ # _ # _ # _ # _ # _ #
    refl # refl # refl # refl # refl # refl # refl # refl # refl
tr-Term-J {j = defn _}                ()
tr-Term-J {j = var _}                 ()
tr-Term-J {j = Level}                 ()
tr-Term-J {j = zeroᵘ}                 ()
tr-Term-J {j = sucᵘ _}                ()
tr-Term-J {j = _ supᵘ _}              ()
tr-Term-J {j = U _}                   ()
tr-Term-J {j = Lift _ _}              ()
tr-Term-J {j = lift _}                ()
tr-Term-J {j = lower _}               ()
tr-Term-J {j = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-J {j = lam _ _}               ()
tr-Term-J {j = _ ∘⟨ _ ⟩ _}            ()
tr-Term-J {j = prod _ _ _ _}          ()
tr-Term-J {j = fst _ _}               ()
tr-Term-J {j = snd _ _}               ()
tr-Term-J {j = prodrec _ _ _ _ _ _}   ()
tr-Term-J {j = Empty}                 ()
tr-Term-J {j = emptyrec _ _ _}        ()
tr-Term-J {j = Unit _}                ()
tr-Term-J {j = star _}                ()
tr-Term-J {j = unitrec _ _ _ _ _}     ()
tr-Term-J {j = ℕ}                     ()
tr-Term-J {j = zero}                  ()
tr-Term-J {j = suc _}                 ()
tr-Term-J {j = natrec _ _ _ _ _ _ _}  ()
tr-Term-J {j = Id _ _ _}              ()
tr-Term-J {j = rfl}                   ()
tr-Term-J {j = K _ _ _ _ _ _}         ()
tr-Term-J {j = []-cong _ _ _ _ _ _}   ()

-- Inversion for K.

tr-Term-K :
  tr-Term w ≡ K p A t B u v →
  ∃₆ λ p′ A′ t′ B′ u′ v′ →
     w ≡ K p′ A′ t′ B′ u′ v′ × tr p′ ≡ p ×
     tr-Term A′ ≡ A × tr-Term t′ ≡ t × tr-Term B′ ≡ B ×
     tr-Term u′ ≡ u × tr-Term v′ ≡ v
tr-Term-K {w = K _ _ _ _ _ _} refl =
  _ # _ # _ # _ # _ # _ # refl # refl # refl # refl # refl # refl # refl
tr-Term-K {w = defn _}                ()
tr-Term-K {w = var _}                 ()
tr-Term-K {w = Level}                 ()
tr-Term-K {w = zeroᵘ}                 ()
tr-Term-K {w = sucᵘ _}                ()
tr-Term-K {w = _ supᵘ _}              ()
tr-Term-K {w = U _}                   ()
tr-Term-K {w = Lift _ _}              ()
tr-Term-K {w = lift _}                ()
tr-Term-K {w = lower _}               ()
tr-Term-K {w = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-K {w = lam _ _}               ()
tr-Term-K {w = _ ∘⟨ _ ⟩ _}            ()
tr-Term-K {w = prod _ _ _ _}          ()
tr-Term-K {w = fst _ _}               ()
tr-Term-K {w = snd _ _}               ()
tr-Term-K {w = prodrec _ _ _ _ _ _}   ()
tr-Term-K {w = Empty}                 ()
tr-Term-K {w = emptyrec _ _ _}        ()
tr-Term-K {w = Unit _}                ()
tr-Term-K {w = star _}                ()
tr-Term-K {w = unitrec _ _ _ _ _}     ()
tr-Term-K {w = ℕ}                     ()
tr-Term-K {w = zero}                  ()
tr-Term-K {w = suc _}                 ()
tr-Term-K {w = natrec _ _ _ _ _ _ _}  ()
tr-Term-K {w = Id _ _ _}              ()
tr-Term-K {w = rfl}                   ()
tr-Term-K {w = J _ _ _ _ _ _ _ _}     ()
tr-Term-K {w = []-cong _ _ _ _ _ _}   ()

-- Inversion for []-cong.

tr-Term-[]-cong :
  tr-Term w ≡ []-cong s l A t u v →
  ∃₅ λ l′ A′ t′ u′ v′ →
     w ≡ []-cong s l′ A′ t′ u′ v′ ×
     tr-Term l′ ≡ l × tr-Term A′ ≡ A × tr-Term t′ ≡ t × tr-Term u′ ≡ u ×
     tr-Term v′ ≡ v
tr-Term-[]-cong {w = []-cong _ _ _ _ _ _} refl =
  _ # _ # _ # _ # _ # refl # refl # refl # refl # refl # refl
tr-Term-[]-cong {w = defn _}                ()
tr-Term-[]-cong {w = var _}                 ()
tr-Term-[]-cong {w = Level}                 ()
tr-Term-[]-cong {w = zeroᵘ}                 ()
tr-Term-[]-cong {w = sucᵘ _}                ()
tr-Term-[]-cong {w = _ supᵘ _}              ()
tr-Term-[]-cong {w = U _}                   ()
tr-Term-[]-cong {w = Lift _ _}              ()
tr-Term-[]-cong {w = lift _}                ()
tr-Term-[]-cong {w = lower _}               ()
tr-Term-[]-cong {w = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} ()
tr-Term-[]-cong {w = lam _ _}               ()
tr-Term-[]-cong {w = _ ∘⟨ _ ⟩ _}            ()
tr-Term-[]-cong {w = prod _ _ _ _}          ()
tr-Term-[]-cong {w = fst _ _}               ()
tr-Term-[]-cong {w = snd _ _}               ()
tr-Term-[]-cong {w = prodrec _ _ _ _ _ _}   ()
tr-Term-[]-cong {w = Empty}                 ()
tr-Term-[]-cong {w = emptyrec _ _ _}        ()
tr-Term-[]-cong {w = Unit _}                ()
tr-Term-[]-cong {w = star _}                ()
tr-Term-[]-cong {w = unitrec _ _ _ _ _}     ()
tr-Term-[]-cong {w = ℕ}                     ()
tr-Term-[]-cong {w = zero}                  ()
tr-Term-[]-cong {w = suc _}                 ()
tr-Term-[]-cong {w = natrec _ _ _ _ _ _ _}  ()
tr-Term-[]-cong {w = Id _ _ _}              ()
tr-Term-[]-cong {w = rfl}                   ()
tr-Term-[]-cong {w = J _ _ _ _ _ _ _ _}     ()
tr-Term-[]-cong {w = K _ _ _ _ _ _}         ()

mutual

  -- Inversion for wk′.

  tr-Term′-wk′⁻¹ :
    ∀ {t u} →
    tr-Term′ t ≡ U₂.wk′ ρ u →
    ∃ λ t′ → tr-Term′ t′ ≡ u × t ≡ U₁.wk′ ρ t′
  tr-Term′-wk′⁻¹ {t = var _}   {u = var x}   refl = var x # refl # refl
  tr-Term′-wk′⁻¹ {t = var _}   {u = gen _ _} ()
  tr-Term′-wk′⁻¹ {t = gen _ _} {u = var _}   ()
  tr-Term′-wk′⁻¹ {t = gen k _} {u = gen _ _} eq   =
    case U₂.gen-cong⁻¹ eq of λ where
      (refl # refl # eq) →
        case tr-GenTs-wkGen⁻¹ eq of λ (ts′ # eq₁ # eq₂) →
        gen k ts′ # cong (gen _) eq₁ # cong (gen _) eq₂

  -- Inversion for wkGen.

  tr-GenTs-wkGen⁻¹ :
    tr-GenTs ts ≡ U₂.wkGen ρ us →
    ∃ λ ts′ → tr-GenTs ts′ ≡ us × ts ≡ U₁.wkGen ρ ts′
  tr-GenTs-wkGen⁻¹ {ts = []}     {us = []}     refl = [] # refl # refl
  tr-GenTs-wkGen⁻¹ {ts = _ ∷ₜ _} {us = _ ∷ₜ _} eq   =
    case U₂.∷-cong⁻¹ eq of λ (eq₁ # eq₂) →
    case tr-Term′-wk′⁻¹ eq₁ of λ (t′ # eq₃ # eq₄) →
    case tr-GenTs-wkGen⁻¹ eq₂ of λ (ts′ # eq₅ # eq₆) →
    t′ ∷ₜ ts′ # cong₂ _∷ₜ_ eq₃ eq₅ # cong₂ _∷ₜ_ eq₄ eq₆

-- Inversion for wk.

tr-Term-wk⁻¹ :
  tr-Term t ≡ U₂.wk ρ u →
  ∃ λ t′ → tr-Term t′ ≡ u × t ≡ U₁.wk ρ t′
tr-Term-wk⁻¹ {t} {ρ} {u} eq =
  let t′ # ≡u # t≡ = tr-Term′-wk′⁻¹ eq′
  in  U₁.toTerm t′
      # (begin
          tr-Term (U₁.toTerm t′)                            ≡⟨⟩
          U₂.toTerm (tr-Term′ (U₁.fromTerm (U₁.toTerm t′))) ≡⟨ cong (U₂.toTerm ∘→ tr-Term′) (UP₁.fromTerm∘toTerm t′) ⟩
          U₂.toTerm (tr-Term′ t′)                           ≡⟨ cong U₂.toTerm ≡u ⟩
          U₂.toTerm (U₂.fromTerm u)                         ≡⟨ UP₂.toTerm∘fromTerm u ⟩
          u ∎)
      # (begin
          t                                                 ≡˘⟨ UP₁.toTerm∘fromTerm t ⟩
          U₁.toTerm (U₁.fromTerm t)                         ≡⟨ cong U₁.toTerm t≡ ⟩
          U₁.toTerm (U₁.wk′ ρ t′)                           ≡˘⟨ cong (U₁.toTerm ∘→ U₁.wk′ ρ) (UP₁.fromTerm∘toTerm t′) ⟩
          U₁.toTerm (U₁.wk′ ρ (U₁.fromTerm (U₁.toTerm t′))) ≡˘⟨ UP₁.wk≡wk′ (U₁.toTerm t′) ⟩
          U₁.wk ρ (U₁.toTerm t′)                            ∎)
  where
  eq′ : tr-Term′ (U₁.fromTerm t) ≡ U₂.wk′ ρ (U₂.fromTerm u)
  eq′ = begin
    tr-Term′ (U₁.fromTerm t)                           ≡˘⟨ UP₂.fromTerm∘toTerm _ ⟩
    U₂.fromTerm (U₂.toTerm (tr-Term′ (U₁.fromTerm t))) ≡⟨ cong U₂.fromTerm eq ⟩
    U₂.fromTerm (U₂.wk ρ u)                            ≡⟨ cong U₂.fromTerm (UP₂.wk≡wk′ u) ⟩
    U₂.fromTerm (U₂.toTerm (U₂.wk′ ρ (U₂.fromTerm u))) ≡⟨ UP₂.fromTerm∘toTerm _ ⟩
    U₂.wk′ ρ (U₂.fromTerm u)                           ∎

------------------------------------------------------------------------
-- Some lemmas related to level literals

opaque

  -- Translation preserves level literals (in both directions).

  tr-Level-literal : U₁.Level-literal l ⇔ U₂.Level-literal (tr-Term l)
  tr-Level-literal = to # flip from refl
    where
    to : U₁.Level-literal l → U₂.Level-literal (tr-Term l)
    to zeroᵘ    = zeroᵘ
    to (sucᵘ l) = sucᵘ (to l)

    from : U₂.Level-literal l′ → tr-Term l ≡ l′ → U₁.Level-literal l
    from zeroᵘ eq =
      case tr-Term-zeroᵘ eq of λ {
        refl →
      zeroᵘ }
    from (sucᵘ l) eq =
      case tr-Term-sucᵘ eq of λ {
        (_ # refl # eq) →
      sucᵘ (from l eq) }

opaque
  unfolding size-of-Level tr-Level-literal

  -- A lemma related to size-of-Level and tr-Level-literal.

  size-of-Level-tr-Level-literal :
    {l-lit : U₁.Level-literal l} →
    U₁.size-of-Level l-lit ≡
    U₂.size-of-Level (tr-Level-literal .proj₁ l-lit)
  size-of-Level-tr-Level-literal {l-lit = zeroᵘ} =
    refl
  size-of-Level-tr-Level-literal {l-lit = sucᵘ _} =
    cong 1+ size-of-Level-tr-Level-literal

opaque

  -- The function tr-Term commutes with ↓ᵘ_.

  tr-Term-↓ᵘ : tr-Term {n = n} (U₁.↓ᵘ m) ≡ U₂.↓ᵘ m
  tr-Term-↓ᵘ {m = 0}    = refl
  tr-Term-↓ᵘ {m = 1+ _} = cong sucᵘ tr-Term-↓ᵘ

opaque
  unfolding Definition.Untyped._supᵘₗ′_

  -- The function tr-Term commutes with _supᵘₗ′_.

  tr-Term-supᵘₗ′ :
    tr-Term l₁ U₂.supᵘₗ′ tr-Term l₂ ≡
    tr-Term (l₁ U₁.supᵘₗ′ l₂)
  tr-Term-supᵘₗ′ {l₁} {l₂}
    with U₁.Level-literal? l₁ ×-dec U₁.Level-literal? l₂
  … | yes (l₁-lit # l₂-lit) =
    let l₁-lit′ = tr-Level-literal .proj₁ l₁-lit
        l₂-lit′ = tr-Level-literal .proj₁ l₂-lit
    in
    tr-Term l₁ U₂.supᵘₗ′ tr-Term l₂                                      ≡⟨ UP₂.supᵘₗ′≡↓ᵘ⊔ _ _ ⟩
    U₂.↓ᵘ (U₂.size-of-Level l₁-lit′ ⊔ U₂.size-of-Level l₂-lit′)          ≡˘⟨ cong₂ (λ m n → U₂.↓ᵘ (m ⊔ n))
                                                                               size-of-Level-tr-Level-literal
                                                                               size-of-Level-tr-Level-literal ⟩
    U₂.↓ᵘ (U₁.size-of-Level l₁-lit ⊔ U₁.size-of-Level l₂-lit)            ≡˘⟨ tr-Term-↓ᵘ ⟩
    tr-Term (U₁.↓ᵘ (U₁.size-of-Level l₁-lit ⊔ U₁.size-of-Level l₂-lit))  ∎
  … | no not-both =
    tr-Term l₁ U₂.supᵘₗ′ tr-Term l₂  ≡⟨ UP₂.supᵘₗ′≡supᵘ (not-both ∘→ Σ.map (tr-Level-literal .proj₂) (tr-Level-literal .proj₂)) ⟩
    tr-Term l₁ U₂.supᵘ tr-Term l₂    ∎

------------------------------------------------------------------------
-- Results that are proved under the assumption that the translation
-- functions tr and tr-Σ are injective

module Injective
  -- The function tr is injective.
  (tr-injective : ∀ {p q} → tr p ≡ tr q → p ≡ q)
  -- The function tr-Σ is injective.
  (tr-Σ-injective : ∀ {p q} → tr-Σ p ≡ tr-Σ q → p ≡ q)
  where

  ----------------------------------------------------------------------
  -- Certain functions are injective

  -- The function tr-BinderMode b is injective.

  tr-BinderMode-injective :
    ∀ {p q} b → tr-BinderMode b p ≡ tr-BinderMode b q → p ≡ q
  tr-BinderMode-injective BMΠ     = tr-injective
  tr-BinderMode-injective (BMΣ _) = tr-Σ-injective

  -- The function tr-Kind is injective.

  tr-Kind-injective : tr-Kind k₁ ≡ tr-Kind k₂ → k₁ ≡ k₂
  tr-Kind-injective {k₁ = Defnkind _}    {k₂ = Defnkind _}    refl = refl
  tr-Kind-injective {k₁ = Levelkind}     {k₂ = Levelkind}     refl = refl
  tr-Kind-injective {k₁ = Zeroᵘkind}     {k₂ = Zeroᵘkind}     refl = refl
  tr-Kind-injective {k₁ = Sucᵘkind}      {k₂ = Sucᵘkind}     refl = refl
  tr-Kind-injective {k₁ = Supᵘkind}      {k₂ = Supᵘkind}     refl = refl
  tr-Kind-injective {k₁ = Liftkind}      {k₂ = Liftkind}     refl = refl
  tr-Kind-injective {k₁ = liftkind}      {k₂ = liftkind}     refl = refl
  tr-Kind-injective {k₁ = lowerkind}     {k₂ = lowerkind}     refl = refl
  tr-Kind-injective {k₁ = Ukind}         {k₂ = Ukind}         refl = refl
  tr-Kind-injective {k₁ = Natkind}       {k₂ = Natkind}       refl = refl
  tr-Kind-injective {k₁ = Zerokind}      {k₂ = Zerokind}      refl = refl
  tr-Kind-injective {k₁ = Suckind}       {k₂ = Suckind}       refl = refl
  tr-Kind-injective {k₁ = Unitkind _}    {k₂ = Unitkind _}    refl = refl
  tr-Kind-injective {k₁ = Starkind _}    {k₂ = Starkind _}    refl = refl
  tr-Kind-injective {k₁ = Emptykind}     {k₂ = Emptykind}     refl = refl
  tr-Kind-injective {k₁ = Idkind}        {k₂ = Idkind}        refl = refl
  tr-Kind-injective {k₁ = Reflkind}      {k₂ = Reflkind}      refl = refl
  tr-Kind-injective {k₁ = Boxcongkind _} {k₂ = Boxcongkind _} refl =
    refl
  tr-Kind-injective {k₁ = Binderkind b p q} {k₂ = Binderkind _ _ _} eq
    with tr-BinderMode b p in tr-p≡ | tr q in tr-q≡
  tr-Kind-injective {k₁ = Binderkind b _ _} refl | _ | _ =
    cong₂ (Binderkind _)
      (tr-BinderMode-injective b tr-p≡)
      (tr-injective tr-q≡)
  tr-Kind-injective {k₁ = Lamkind p} {k₂ = Lamkind _} eq
    with tr p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Lamkind (tr-injective tr-p≡)
  tr-Kind-injective {k₁ = Appkind p} {k₂ = Appkind _} eq
    with tr p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Appkind (tr-injective tr-p≡)
  tr-Kind-injective {k₁ = Prodkind s p} {k₂ = Prodkind _ _} eq
    with tr-Σ p in tr-p≡
  tr-Kind-injective refl | _ =
    cong (Prodkind _) (tr-Σ-injective tr-p≡)
  tr-Kind-injective {k₁ = Fstkind p} {k₂ = Fstkind _} eq
    with tr-Σ p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Fstkind (tr-Σ-injective tr-p≡)
  tr-Kind-injective {k₁ = Sndkind p} {k₂ = Sndkind _} eq
    with tr-Σ p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Sndkind (tr-Σ-injective tr-p≡)
  tr-Kind-injective {k₁ = Prodreckind r p q} {k₂ = Prodreckind _ _ _} eq
    with tr r in tr-r≡ | tr-Σ p in tr-p≡ | tr q in tr-q≡
  tr-Kind-injective refl | _ | _ | _ =
    cong₃ Prodreckind (tr-injective tr-r≡) (tr-Σ-injective tr-p≡)
      (tr-injective tr-q≡)
  tr-Kind-injective {k₁ = Natreckind p q r} {k₂ = Natreckind _ _ _} eq
    with tr p in tr-p≡ | tr q in tr-q≡ | tr r in tr-r≡
  tr-Kind-injective refl | _ | _ | _ =
    cong₃ Natreckind (tr-injective tr-p≡) (tr-injective tr-q≡)
      (tr-injective tr-r≡)
  tr-Kind-injective {k₁ = Emptyreckind p} {k₂ = Emptyreckind _} eq
    with tr p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Emptyreckind (tr-injective tr-p≡)
  tr-Kind-injective {k₁ = Unitreckind p q} {k₂ = Unitreckind _ _} eq
    with tr p in tr-p≡ | tr q in tr-q≡
  tr-Kind-injective refl | _ | _ =
    cong₂ Unitreckind (tr-injective tr-p≡) (tr-injective tr-q≡)
  tr-Kind-injective {k₁ = Jkind p q} {k₂ = Jkind _ _} eq
    with tr p in tr-p≡ | tr q in tr-q≡
  tr-Kind-injective refl | _ | _ =
    cong₂ Jkind (tr-injective tr-p≡) (tr-injective tr-q≡)
  tr-Kind-injective {k₁ = Kkind p}     {k₂ = Kkind _} eq
    with tr p in tr-p≡
  tr-Kind-injective refl | _ =
    cong Kkind (tr-injective tr-p≡)
  tr-Kind-injective {k₁ = Defnkind _}     {k₂ = Levelkind}      ()
  tr-Kind-injective {k₁ = Defnkind _}     {k₂ = Zeroᵘkind}      ()
  tr-Kind-injective {k₁ = Defnkind _}     {k₂ = Natkind}        ()
  tr-Kind-injective {k₁ = Defnkind _}     {k₂ = Zerokind}       ()
  tr-Kind-injective {k₁ = Defnkind _}     {k₂ = Unitkind _}     ()
  tr-Kind-injective {k₁ = Defnkind _}     {k₂ = Starkind _}     ()
  tr-Kind-injective {k₁ = Defnkind _}     {k₂ = Emptykind}      ()
  tr-Kind-injective {k₁ = Defnkind _}     {k₂ = Reflkind}       ()
  tr-Kind-injective {k₁ = Levelkind}      {k₂ = Defnkind _}     ()
  tr-Kind-injective {k₁ = Levelkind}      {k₂ = Zeroᵘkind}      ()
  tr-Kind-injective {k₁ = Levelkind}      {k₂ = Emptykind}      ()
  tr-Kind-injective {k₁ = Levelkind}      {k₂ = Unitkind _}     ()
  tr-Kind-injective {k₁ = Levelkind}      {k₂ = Starkind _}     ()
  tr-Kind-injective {k₁ = Levelkind}      {k₂ = Natkind}        ()
  tr-Kind-injective {k₁ = Levelkind}      {k₂ = Zerokind}       ()
  tr-Kind-injective {k₁ = Levelkind}      {k₂ = Reflkind}       ()
  tr-Kind-injective {k₁ = Zeroᵘkind}      {k₂ = Defnkind _}     ()
  tr-Kind-injective {k₁ = Zeroᵘkind}      {k₂ = Levelkind}      ()
  tr-Kind-injective {k₁ = Zeroᵘkind}      {k₂ = Emptykind}      ()
  tr-Kind-injective {k₁ = Zeroᵘkind}      {k₂ = Unitkind _}     ()
  tr-Kind-injective {k₁ = Zeroᵘkind}      {k₂ = Starkind _}     ()
  tr-Kind-injective {k₁ = Zeroᵘkind}      {k₂ = Natkind}        ()
  tr-Kind-injective {k₁ = Zeroᵘkind}      {k₂ = Zerokind}       ()
  tr-Kind-injective {k₁ = Zeroᵘkind}      {k₂ = Reflkind}       ()
  tr-Kind-injective {k₁ = Sucᵘkind}       {k₂ = Ukind}          ()
  tr-Kind-injective {k₁ = Sucᵘkind}       {k₂ = liftkind}       ()
  tr-Kind-injective {k₁ = Sucᵘkind}       {k₂ = lowerkind}      ()
  tr-Kind-injective {k₁ = Sucᵘkind}       {k₂ = Fstkind _}      ()
  tr-Kind-injective {k₁ = Sucᵘkind}       {k₂ = Sndkind _}      ()
  tr-Kind-injective {k₁ = Sucᵘkind}       {k₂ = Suckind}        ()
  tr-Kind-injective {k₁ = Supᵘkind}       {k₂ = Liftkind}       ()
  tr-Kind-injective {k₁ = Supᵘkind}       {k₂ = Emptyreckind _} ()
  tr-Kind-injective {k₁ = Supᵘkind}       {k₂ = Appkind _}      ()
  tr-Kind-injective {k₁ = Supᵘkind}       {k₂ = Prodkind _ _}   ()
  tr-Kind-injective {k₁ = Ukind}          {k₂ = Sucᵘkind}       ()
  tr-Kind-injective {k₁ = Ukind}          {k₂ = liftkind}       ()
  tr-Kind-injective {k₁ = Ukind}          {k₂ = lowerkind}      ()
  tr-Kind-injective {k₁ = Ukind}          {k₂ = Fstkind _}      ()
  tr-Kind-injective {k₁ = Ukind}          {k₂ = Sndkind _}      ()
  tr-Kind-injective {k₁ = Ukind}          {k₂ = Suckind}        ()
  tr-Kind-injective {k₁ = Liftkind}       {k₂ = Supᵘkind}       ()
  tr-Kind-injective {k₁ = Liftkind}       {k₂ = Emptyreckind _} ()
  tr-Kind-injective {k₁ = Liftkind}       {k₂ = Appkind _}      ()
  tr-Kind-injective {k₁ = Liftkind}       {k₂ = Prodkind _ _}   ()
  tr-Kind-injective {k₁ = liftkind}       {k₂ = Sucᵘkind}       ()
  tr-Kind-injective {k₁ = liftkind}       {k₂ = Ukind}          ()
  tr-Kind-injective {k₁ = liftkind}       {k₂ = lowerkind}      ()
  tr-Kind-injective {k₁ = liftkind}       {k₂ = Fstkind _}      ()
  tr-Kind-injective {k₁ = liftkind}       {k₂ = Sndkind _}      ()
  tr-Kind-injective {k₁ = liftkind}       {k₂ = Suckind}        ()
  tr-Kind-injective {k₁ = lowerkind}      {k₂ = Sucᵘkind}       ()
  tr-Kind-injective {k₁ = lowerkind}      {k₂ = Ukind}          ()
  tr-Kind-injective {k₁ = lowerkind}      {k₂ = liftkind}       ()
  tr-Kind-injective {k₁ = lowerkind}      {k₂ = Fstkind _}      ()
  tr-Kind-injective {k₁ = lowerkind}      {k₂ = Sndkind _}      ()
  tr-Kind-injective {k₁ = lowerkind}      {k₂ = Suckind}        ()
  tr-Kind-injective {k₁ = Appkind _}      {k₂ = Supᵘkind}       ()
  tr-Kind-injective {k₁ = Appkind _}      {k₂ = Liftkind}       ()
  tr-Kind-injective {k₁ = Appkind _}      {k₂ = Prodkind _ _}   ()
  tr-Kind-injective {k₁ = Appkind _}      {k₂ = Emptyreckind _} ()
  tr-Kind-injective {k₁ = Prodkind _ _}   {k₂ = Supᵘkind}       ()
  tr-Kind-injective {k₁ = Prodkind _ _}   {k₂ = Liftkind}       ()
  tr-Kind-injective {k₁ = Prodkind _ _}   {k₂ = Appkind _}      ()
  tr-Kind-injective {k₁ = Prodkind _ _}   {k₂ = Emptyreckind _} ()
  tr-Kind-injective {k₁ = Fstkind _}      {k₂ = Sucᵘkind}       ()
  tr-Kind-injective {k₁ = Fstkind _}      {k₂ = Ukind}          ()
  tr-Kind-injective {k₁ = Fstkind _}      {k₂ = liftkind}       ()
  tr-Kind-injective {k₁ = Fstkind _}      {k₂ = lowerkind}      ()
  tr-Kind-injective {k₁ = Fstkind _}      {k₂ = Sndkind _}      ()
  tr-Kind-injective {k₁ = Fstkind _}      {k₂ = Suckind}        ()
  tr-Kind-injective {k₁ = Sndkind _}      {k₂ = Sucᵘkind}       ()
  tr-Kind-injective {k₁ = Sndkind _}      {k₂ = Ukind}          ()
  tr-Kind-injective {k₁ = Sndkind _}      {k₂ = liftkind}       ()
  tr-Kind-injective {k₁ = Sndkind _}      {k₂ = lowerkind}      ()
  tr-Kind-injective {k₁ = Sndkind _}      {k₂ = Fstkind _}      ()
  tr-Kind-injective {k₁ = Sndkind _}      {k₂ = Suckind}        ()
  tr-Kind-injective {k₁ = Emptykind}      {k₂ = Defnkind _}     ()
  tr-Kind-injective {k₁ = Emptykind}      {k₂ = Levelkind}      ()
  tr-Kind-injective {k₁ = Emptykind}      {k₂ = Zeroᵘkind}      ()
  tr-Kind-injective {k₁ = Emptykind}      {k₂ = Unitkind _}     ()
  tr-Kind-injective {k₁ = Emptykind}      {k₂ = Starkind _}     ()
  tr-Kind-injective {k₁ = Emptykind}      {k₂ = Natkind}        ()
  tr-Kind-injective {k₁ = Emptykind}      {k₂ = Zerokind}       ()
  tr-Kind-injective {k₁ = Emptykind}      {k₂ = Reflkind}       ()
  tr-Kind-injective {k₁ = Emptyreckind _} {k₂ = Supᵘkind}       ()
  tr-Kind-injective {k₁ = Emptyreckind _} {k₂ = Liftkind}       ()
  tr-Kind-injective {k₁ = Emptyreckind _} {k₂ = Appkind _}      ()
  tr-Kind-injective {k₁ = Emptyreckind _} {k₂ = Prodkind _ _}   ()
  tr-Kind-injective {k₁ = Unitkind _}     {k₂ = Defnkind _}     ()
  tr-Kind-injective {k₁ = Unitkind _}     {k₂ = Levelkind}      ()
  tr-Kind-injective {k₁ = Unitkind _}     {k₂ = Zeroᵘkind}      ()
  tr-Kind-injective {k₁ = Unitkind _}     {k₂ = Emptykind}      ()
  tr-Kind-injective {k₁ = Unitkind _}     {k₂ = Starkind _}     ()
  tr-Kind-injective {k₁ = Unitkind _}     {k₂ = Natkind}        ()
  tr-Kind-injective {k₁ = Unitkind _}     {k₂ = Zerokind}       ()
  tr-Kind-injective {k₁ = Unitkind _}     {k₂ = Reflkind}       ()
  tr-Kind-injective {k₁ = Starkind _}     {k₂ = Defnkind _}     ()
  tr-Kind-injective {k₁ = Starkind _}     {k₂ = Levelkind}      ()
  tr-Kind-injective {k₁ = Starkind _}     {k₂ = Zeroᵘkind}      ()
  tr-Kind-injective {k₁ = Starkind _}     {k₂ = Emptykind}      ()
  tr-Kind-injective {k₁ = Starkind _}     {k₂ = Unitkind _}     ()
  tr-Kind-injective {k₁ = Starkind _}     {k₂ = Natkind}        ()
  tr-Kind-injective {k₁ = Starkind _}     {k₂ = Zerokind}       ()
  tr-Kind-injective {k₁ = Starkind _}     {k₂ = Reflkind}       ()
  tr-Kind-injective {k₁ = Natkind}        {k₂ = Defnkind _}     ()
  tr-Kind-injective {k₁ = Natkind}        {k₂ = Levelkind}      ()
  tr-Kind-injective {k₁ = Natkind}        {k₂ = Zeroᵘkind}      ()
  tr-Kind-injective {k₁ = Natkind}        {k₂ = Emptykind}      ()
  tr-Kind-injective {k₁ = Natkind}        {k₂ = Unitkind _}     ()
  tr-Kind-injective {k₁ = Natkind}        {k₂ = Starkind _}     ()
  tr-Kind-injective {k₁ = Natkind}        {k₂ = Zerokind}       ()
  tr-Kind-injective {k₁ = Natkind}        {k₂ = Reflkind}       ()
  tr-Kind-injective {k₁ = Zerokind}       {k₂ = Defnkind _}     ()
  tr-Kind-injective {k₁ = Zerokind}       {k₂ = Levelkind}      ()
  tr-Kind-injective {k₁ = Zerokind}       {k₂ = Zeroᵘkind}      ()
  tr-Kind-injective {k₁ = Zerokind}       {k₂ = Emptykind}      ()
  tr-Kind-injective {k₁ = Zerokind}       {k₂ = Unitkind _}     ()
  tr-Kind-injective {k₁ = Zerokind}       {k₂ = Starkind _}     ()
  tr-Kind-injective {k₁ = Zerokind}       {k₂ = Natkind}        ()
  tr-Kind-injective {k₁ = Zerokind}       {k₂ = Reflkind}       ()
  tr-Kind-injective {k₁ = Suckind}        {k₂ = Sucᵘkind}       ()
  tr-Kind-injective {k₁ = Suckind}        {k₂ = Ukind}          ()
  tr-Kind-injective {k₁ = Suckind}        {k₂ = liftkind}       ()
  tr-Kind-injective {k₁ = Suckind}        {k₂ = lowerkind}      ()
  tr-Kind-injective {k₁ = Suckind}        {k₂ = Fstkind _}      ()
  tr-Kind-injective {k₁ = Suckind}        {k₂ = Sndkind _}      ()
  tr-Kind-injective {k₁ = Reflkind}       {k₂ = Defnkind _}     ()
  tr-Kind-injective {k₁ = Reflkind}       {k₂ = Levelkind}      ()
  tr-Kind-injective {k₁ = Reflkind}       {k₂ = Zeroᵘkind}      ()
  tr-Kind-injective {k₁ = Reflkind}       {k₂ = Emptykind}      ()
  tr-Kind-injective {k₁ = Reflkind}       {k₂ = Unitkind _}     ()
  tr-Kind-injective {k₁ = Reflkind}       {k₂ = Starkind _}     ()
  tr-Kind-injective {k₁ = Reflkind}       {k₂ = Natkind}        ()
  tr-Kind-injective {k₁ = Reflkind}       {k₂ = Zerokind}       ()

  mutual

    -- The function tr-Term′ is injective.

    tr-Term′-injective : {t u : U₁.Term′ n} → tr-Term′ t ≡ tr-Term′ u → t ≡ u
    tr-Term′-injective {t = var _}   {u = var _}   refl = refl
    tr-Term′-injective {t = var _}   {u = gen _ _} ()
    tr-Term′-injective {t = gen _ _} {u = var _}   ()
    tr-Term′-injective {t = gen _ _} {u = gen _ _} eq   =
      case U₂.gen-cong⁻¹ eq of λ where
        (refl # eq₁ # eq₂) →
          case tr-Kind-injective eq₁ of λ where
            refl → cong (gen _) (tr-GenTs-injective eq₂)

    -- The function tr-GenTs is injective.

    tr-GenTs-injective : tr-GenTs ts ≡ tr-GenTs us → ts ≡ us
    tr-GenTs-injective {ts = []}     {us = []}     _  = refl
    tr-GenTs-injective {ts = _ ∷ₜ _} {us = _ ∷ₜ _} eq =
      case U₂.∷-cong⁻¹ eq of λ (eq₁ # eq₂) →
      cong₂ _∷ₜ_ (tr-Term′-injective eq₁) (tr-GenTs-injective eq₂)

  -- The function tr-Term is injective.

  tr-Term-injective : tr-Term t ≡ tr-Term u → t ≡ u
  tr-Term-injective {t} {u} eq = begin
    t                         ≡˘⟨ UP₁.toTerm∘fromTerm t ⟩
    U₁.toTerm (U₁.fromTerm t) ≡⟨ cong U₁.toTerm (tr-Term′-injective eq′) ⟩
    U₁.toTerm (U₁.fromTerm u) ≡⟨ UP₁.toTerm∘fromTerm u ⟩
    u                         ∎
    where
    eq′ : tr-Term′ (U₁.fromTerm t) ≡ tr-Term′ (U₁.fromTerm u)
    eq′ = begin
      tr-Term′ (U₁.fromTerm t) ≡˘⟨ UP₂.fromTerm∘toTerm _ ⟩
      U₂.fromTerm (tr-Term t)  ≡⟨ cong U₂.fromTerm eq ⟩
      U₂.fromTerm (tr-Term u)  ≡⟨ UP₂.fromTerm∘toTerm _ ⟩
      tr-Term′ (U₁.fromTerm u) ∎

  ----------------------------------------------------------------------
  -- Inversion lemmas

  mutual

    -- Inversion for _[_]′.

    tr-Term′-subst′⁻¹ :
      ∀ {t u} →
      tr-Term′ t ≡ u U₂.[ tr-Subst σ ]′ →
      ∃ λ u′ → tr-Term′ u′ ≡ u × t ≡ u′ U₁.[ σ ]′
    tr-Term′-subst′⁻¹ {σ} {t} {u = var x} eq =
      var x # refl # tr-Term′-injective (
        tr-Term′ t                  ≡⟨ eq ⟩
        var x U₂.[ tr-Subst σ ]′    ≡⟨ tr-Term′-subst′ {σ = σ} (var x) ⟩
        tr-Term′ (var x U₁.[ σ ]′)  ∎)
    tr-Term′-subst′⁻¹ {t = gen k _} {u = gen _ _} eq =
      case U₂.gen-cong⁻¹ eq of λ where
        (refl # refl # eq) →
          case tr-Term-substGen⁻¹ eq of λ where
            (us′ # refl # refl) → gen k us′ # refl # refl
    tr-Term′-subst′⁻¹ {t = var _} {u = gen _ _} ()

    -- Inversion for substGen.

    tr-Term-substGen⁻¹ :
      tr-GenTs ts ≡ U₂.substGen (tr-Subst σ) us →
      ∃ λ us′ → tr-GenTs us′ ≡ us × ts ≡ U₁.substGen σ us′
    tr-Term-substGen⁻¹ {ts = []} {us = []} _ =
      [] # refl # refl
    tr-Term-substGen⁻¹
      {ts = _∷ₜ_ {b = b} t _} {σ = σ} {us = u ∷ₜ _} eq =
      case U₂.∷-cong⁻¹ eq of λ (eq₁ # eq₂) →
      case
        tr-Term′ t                              ≡⟨ eq₁ ⟩
        u U₂.[ U₂.liftSubstn (tr-Subst σ) b ]′  ≡⟨ UP₂.substVar-to-subst′ (λ _ → tr-Subst-liftSubstn b) u ⟩
        u U₂.[ tr-Subst (U₁.liftSubstn σ b) ]′  ∎
      of λ lemma →
      case tr-Term-substGen⁻¹ eq₂ of λ where
        (us′ # refl # refl) →
          case tr-Term′-subst′⁻¹ {u = u} lemma of λ where
            (u′ # refl # refl) → u′ ∷ₜ us′ # refl # refl

  -- Inversion for _[_]′.

  tr-Term-subst⁻¹ :
    tr-Term t ≡ u U₂.[ tr-Subst σ ] →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ σ ]
  tr-Term-subst⁻¹ {t} {u} {σ} eq =
    let u′ # eq₁ # eq₂ = tr-Term′-subst′⁻¹ {u = U₂.fromTerm u} eq′
    in  U₁.toTerm u′
        # (begin
            U₂.toTerm (tr-Term′ (U₁.fromTerm (U₁.toTerm u′))) ≡⟨ cong (U₂.toTerm ∘→ tr-Term′) (UP₁.fromTerm∘toTerm u′) ⟩
            U₂.toTerm (tr-Term′ u′)                           ≡⟨ cong U₂.toTerm eq₁ ⟩
            U₂.toTerm (U₂.fromTerm u)                         ≡⟨ UP₂.toTerm∘fromTerm u ⟩
            u                                                 ∎)
        # (begin
            t                                                ≡˘⟨ UP₁.toTerm∘fromTerm t ⟩
            U₁.toTerm (U₁.fromTerm t)                        ≡⟨ cong U₁.toTerm eq₂ ⟩
            U₁.toTerm (u′ U₁.[ σ ]′)                         ≡˘⟨ cong (λ x → U₁.toTerm (x U₁.[ σ ]′))
                                                                 (UP₁.fromTerm∘toTerm u′) ⟩
            U₁.toTerm (U₁.fromTerm (U₁.toTerm u′) U₁.[ σ ]′) ≡˘⟨ UP₁.subst≡subst′ (U₁.toTerm u′) ⟩
            U₁.toTerm u′ U₁.[ σ ]                            ∎)
    where
    eq′ : tr-Term′ (U₁.fromTerm t) ≡ U₂.fromTerm u U₂.[ tr-Subst σ ]′
    eq′ = begin
      tr-Term′ (U₁.fromTerm t)                                   ≡˘⟨ UP₂.fromTerm∘toTerm _ ⟩
      U₂.fromTerm (U₂.toTerm (tr-Term′ (U₁.fromTerm t)))         ≡⟨ cong U₂.fromTerm eq ⟩
      U₂.fromTerm (u U₂.[ tr-Subst σ ])                          ≡⟨ cong U₂.fromTerm (UP₂.subst≡subst′ u) ⟩
      U₂.fromTerm (U₂.toTerm (U₂.fromTerm u U₂.[ tr-Subst σ ]′)) ≡⟨ UP₂.fromTerm∘toTerm _ ⟩
      U₂.fromTerm u U₂.[ tr-Subst σ ]′                           ∎

  -- Inversion for _[_]₀.

  tr-Term-[]₀⁻¹ :
    ∀ u → tr-Term t ≡ u U₂.[ tr-Term v ]₀ →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ v ]₀
  tr-Term-[]₀⁻¹ {t = t} {v = v} u eq = tr-Term-subst⁻¹ (
    tr-Term t                         ≡⟨ eq ⟩
    u U₂.[ tr-Term v ]₀               ≡⟨⟩
    u U₂.[ U₂.sgSubst (tr-Term v) ]   ≡⟨ UP₂.substVar-to-subst tr-Subst-sgSubst u ⟩
    u U₂.[ tr-Subst (U₁.sgSubst v) ]  ∎)

  -- Inversion for _[_,_]₁₀.

  tr-Term-[,]⁻¹ :
    tr-Term t ≡ u U₂.[ tr-Term v , tr-Term w ]₁₀ →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ v , w ]₁₀
  tr-Term-[,]⁻¹ {t = t} {u = u} {v = v} {w = w} eq = tr-Term-subst⁻¹ (
    tr-Term t                                                   ≡⟨ eq ⟩
    u U₂.[ tr-Term v , tr-Term w ]₁₀                            ≡⟨⟩
    u U₂.[ U₂.consSubst (U₂.sgSubst (tr-Term v)) (tr-Term w) ]  ≡⟨ UP₂.substVar-to-subst [,]-lemma u ⟩
    u U₂.[ tr-Subst (U₁.consSubst (U₁.sgSubst v) w) ]           ∎)

  -- Inversion for _[_]↑.

  tr-Term-[]↑⁻¹ :
    tr-Term t ≡ u U₂.[ tr-Term v ]↑ →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ v ]↑
  tr-Term-[]↑⁻¹ {t = t} {u = u} {v = v} eq = tr-Term-subst⁻¹ (
    tr-Term t                                                    ≡⟨ eq ⟩
    u U₂.[ tr-Term v ]↑                                          ≡⟨⟩
    u U₂.[ U₂.consSubst (U₂.wk1Subst U₂.idSubst) (tr-Term v) ]   ≡⟨ UP₂.substVar-to-subst []↑-lemma u ⟩
    u U₂.[ tr-Subst (U₁.consSubst (U₁.wk1Subst U₁.idSubst) v) ]  ∎)

  -- Inversion for _[_]↑².

  tr-Term-[]↑²⁻¹ :
    tr-Term t ≡ u U₂.[ tr-Term v ]↑² →
    ∃ λ u′ → tr-Term u′ ≡ u × t ≡ u′ U₁.[ v ]↑²
  tr-Term-[]↑²⁻¹ {t = t} {u = u} {v = v} eq = tr-Term-subst⁻¹ (
    tr-Term t                                                                  ≡⟨ eq ⟩
    u U₂.[ tr-Term v ]↑²                                                       ≡⟨⟩
    u U₂.[ U₂.consSubst (U₂.wk1Subst (U₂.wk1Subst U₂.idSubst)) (tr-Term v) ]   ≡⟨ UP₂.substVar-to-subst []↑²-lemma u ⟩
    u U₂.[ tr-Subst (U₁.consSubst (U₁.wk1Subst (U₁.wk1Subst U₁.idSubst)) v) ]  ∎)
