------------------------------------------------------------------------
-- Properties for the reduction relation of the target language.
------------------------------------------------------------------------

module Graded.Erasure.Target.Properties.Reduction where

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

open import Graded.Erasure.Target
open import Graded.Erasure.Target.Properties.Substitution
open import Graded.Erasure.Target.Properties.Weakening

open import Tools.Empty
open import Tools.Function
open import Tools.List
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private
  variable
    α k n : Nat
    t t′ u u′ v : Term n
    ∇ ∇′ : List (Term _)
    ρ : Wk _ _
    s : Strictness

-- Reduction properties

-- Concatenation of reduction closure

red*concat : ∇ ⊢ t ⇒* t′ → ∇ ⊢ t′ ⇒* u → ∇ ⊢ t ⇒* u
red*concat refl t′⇒*u = t′⇒*u
red*concat (trans x t⇒*t′) t′⇒*u = trans x (red*concat t⇒*t′ t′⇒*u)

-- Closure of substitution reductions

app-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ t ∘⟨ s ⟩ u ⇒* t′ ∘⟨ s ⟩ u
app-subst* refl = refl
app-subst* (trans x t⇒*t′) = trans (app-subst x) (app-subst* t⇒*t′)

app-subst*-arg :
  Value t → ∇ ⊢ u ⇒* u′ → ∇ ⊢ t ∘⟨ strict ⟩ u ⇒* t ∘⟨ strict ⟩ u′
app-subst*-arg _   refl                = refl
app-subst*-arg val (trans u⇒u′ u′⇒*u″) =
  trans (app-subst-arg val u⇒u′) (app-subst*-arg val u′⇒*u″)

fst-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ fst t ⇒* fst t′
fst-subst* refl = refl
fst-subst* (trans x t⇒*t′) = trans (fst-subst x) (fst-subst* t⇒*t′)

snd-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ snd t ⇒* snd t′
snd-subst* refl = refl
snd-subst* (trans x t⇒*t′) = trans (snd-subst x) (snd-subst* t⇒*t′)

natrec-subst* :
  ∀ {z s} → ∇ ⊢ t ⇒* t′ → ∇ ⊢ natrec z s t ⇒* natrec z s t′
natrec-subst* refl = refl
natrec-subst* (trans x t⇒t′) = trans (natrec-subst x) (natrec-subst* t⇒t′)

prodrec-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ prodrec t u ⇒* prodrec t′ u
prodrec-subst* refl = refl
prodrec-subst* (trans x t⇒t′) = trans (prodrec-subst x) (prodrec-subst* t⇒t′)

unitrec-subst* : ∇ ⊢ t ⇒* t′ → ∇ ⊢ unitrec t u ⇒* unitrec t′ u
unitrec-subst* refl = refl
unitrec-subst* (trans x d) = trans (unitrec-subst x) (unitrec-subst* d)

-- Values do not reduce.

opaque

  Value→¬⇒ : Value t → ¬ ∇ ⊢ t ⇒ u
  Value→¬⇒ lam  ()
  Value→¬⇒ prod ()
  Value→¬⇒ zero ()
  Value→¬⇒ suc  ()
  Value→¬⇒ star ()
  Value→¬⇒ ↯    ()

opaque

  -- If t ∘⟨ s ⟩ u reduces to a value, then t reduces to a value.

  ∘⇒Value→⇒Value :
    Value v → ∇ ⊢ t ∘⟨ s ⟩ u ⇒* v → ∃ λ v′ → Value v′ × ∇ ⊢ t ⇒* v′
  ∘⇒Value→⇒Value ()      refl
  ∘⇒Value→⇒Value v-value (trans (app-subst t⇒t′) t′u⇒v) =
    let _ , v′-value , t′⇒v′ = ∘⇒Value→⇒Value v-value t′u⇒v in
    _ , v′-value , trans t⇒t′ t′⇒v′
  ∘⇒Value→⇒Value _ (trans (app-subst-arg t-value _) _) =
    _ , t-value , refl
  ∘⇒Value→⇒Value _ (trans (β-red _) _) =
    _ , lam , refl

opaque

  -- List indexing is deterministic.

  ↦∈-deterministic : α ↦ t ∈ ∇ → α ↦ u ∈ ∇ → t PE.≡ u
  ↦∈-deterministic here       here       = PE.refl
  ↦∈-deterministic (there t∈) (there u∈) = ↦∈-deterministic t∈ u∈

opaque

  -- If α points to t in ∇, then α points to t in ∇ ++ ∇′.

  ↦∈++ : α ↦ t ∈ ∇ → α ↦ t ∈ (∇ ++ ∇′)
  ↦∈++ here        = here
  ↦∈++ (there α↦t) = there (↦∈++ α↦t)

opaque

  -- The number length ∇ points to t in ∇ ++ t ∷ ∇′.

  length↦∈++∷ : length ∇ ↦ t ∈ (∇ ++ t ∷ ∇′)
  length↦∈++∷ {∇ = []}    = here
  length↦∈++∷ {∇ = _ ∷ _} = there length↦∈++∷

opaque

  -- Reduction is deterministic.

  redDet : (u : Term n) → ∇ ⊢ u ⇒ t → ∇ ⊢ u ⇒ t′ → t PE.≡ t′
  redDet _ = λ where
    (δ-red α↦t) → λ where
      (δ-red α↦t′) → PE.cong (wk _) $ ↦∈-deterministic α↦t α↦t′
    (app-subst p) → λ where
      (app-subst q)       → PE.cong (_∘⟨ _ ⟩ _) $ redDet _ p q
      (app-subst-arg v _) → ⊥-elim $ Value→¬⇒ v p
      (β-red _)           → case p of λ ()
    (app-subst-arg v p) → λ where
      (app-subst q)       → ⊥-elim $ Value→¬⇒ v q
      (app-subst-arg _ q) → PE.cong (_ ∘⟨ _ ⟩_) $ redDet _ p q
      (β-red v)           → ⊥-elim $ Value→¬⇒ v p
    (β-red v) → λ where
      (app-subst ())
      (app-subst-arg _ q) → ⊥-elim $ Value→¬⇒ v q
      (β-red _)           → PE.refl
    (fst-subst p) → λ where
      (fst-subst q) → PE.cong fst $ redDet _ p q
      Σ-β₁          → case p of λ ()
    (snd-subst p) → λ where
      (snd-subst q) → PE.cong snd $ redDet _ p q
      Σ-β₂          → case p of λ ()
    Σ-β₁ → λ where
      (fst-subst ())
      Σ-β₁           → PE.refl
    Σ-β₂ → λ where
      (snd-subst ())
      Σ-β₂           → PE.refl
    (prodrec-subst p) → λ where
      (prodrec-subst q) → PE.cong (flip prodrec _) $ redDet _ p q
      prodrec-β         → case p of λ ()
    prodrec-β → λ where
      (prodrec-subst ())
      prodrec-β          → PE.refl
    (natrec-subst p) → λ where
      (natrec-subst q) → PE.cong (natrec _ _) $ redDet _ p q
      natrec-zero      → case p of λ ()
      natrec-suc       → case p of λ ()
    natrec-zero → λ where
      (natrec-subst ())
      natrec-zero       → PE.refl
    natrec-suc → λ where
      (natrec-subst ())
      natrec-suc        → PE.refl
    (unitrec-subst p) → λ where
      (unitrec-subst q) → PE.cong (flip unitrec _) $ redDet _ p q
      unitrec-β         → case p of λ ()
    unitrec-β → λ where
      (unitrec-subst ())
      unitrec-β          → PE.refl

-- Reduction closure is deterministic
-- (there is only one reduction path)
-- If a ⇒* b and a ⇒* c then b ⇒* c or c ⇒* b

red*Det : ∇ ⊢ u ⇒* t → ∇ ⊢ u ⇒* t′ → (∇ ⊢ t ⇒* t′) ⊎ (∇ ⊢ t′ ⇒* t)
red*Det refl refl = inj₁ refl
red*Det refl (trans x u⇒t′) = inj₁ (trans x u⇒t′)
red*Det (trans x u⇒t) refl = inj₂ (trans x u⇒t)
red*Det {u = u} (trans x u⇒t) (trans x₁ u⇒t′)
  rewrite redDet u x x₁ = red*Det u⇒t u⇒t′

opaque

  -- A weakening lemma for reduction.

  wk-⇒ : ∇ ⊢ t ⇒ u → ∇ ⊢ wk ρ t ⇒ wk ρ u
  wk-⇒ {ρ} = λ where
    (δ-red {t} α↦t) →
      PE.subst (_⊢_⇒_ _ _)
        (wk wk₀ t         ≡˘⟨ PE.cong (flip wk _) $ wk₀-invariant ρ ⟩
         wk (ρ • wk₀) t   ≡˘⟨ wk-comp _ _ _ ⟩
         wk ρ (wk wk₀ t)  ∎) $
      δ-red α↦t
    (app-subst d) →
      app-subst (wk-⇒ d)
    (app-subst-arg v d) →
      app-subst-arg (wk-Value v) (wk-⇒ d)
    (β-red {t} v) →
      PE.subst (_⊢_⇒_ _ _) (PE.sym $ wk-β t) $
      β-red (wk-Value⟨⟩ v)
    (fst-subst d) →
      fst-subst (wk-⇒ d)
    (snd-subst d) →
      snd-subst (wk-⇒ d)
    Σ-β₁ →
      Σ-β₁
    Σ-β₂ →
      Σ-β₂
    (prodrec-subst d) →
      prodrec-subst (wk-⇒ d)
    (prodrec-β {u}) →
      PE.subst (_⊢_⇒_ _ _) (PE.sym $ wk-β-doubleSubst _ u _ _)
        prodrec-β
    (natrec-subst d) →
      natrec-subst (wk-⇒ d)
    natrec-zero →
      natrec-zero
    (natrec-suc {u}) →
      PE.subst (_⊢_⇒_ _ _) (PE.sym $ wk-β-doubleSubst _ u _ _)
        natrec-suc
    (unitrec-subst d) →
      unitrec-subst (wk-⇒ d)
    unitrec-β →
      unitrec-β

opaque

  -- A weakening lemma for reduction.

  wk-⇒* : ∇ ⊢ t ⇒* u → ∇ ⊢ wk ρ t ⇒* wk ρ u
  wk-⇒* = λ where
    refl →
      refl
    (trans d₁ d₂) →
      trans (wk-⇒ d₁) (wk-⇒* d₂)

opaque

  -- A strengthening lemma for reduction.

  strengthen-⇒ :
    ∇ ⊢ wk ρ t ⇒ u → ∃ λ u′ → wk ρ u′ PE.≡ u × ∇ ⊢ t ⇒ u′
  strengthen-⇒ = flip lemma PE.refl
    where
    lemma :
      ∇ ⊢ t ⇒ u → wk ρ t′ PE.≡ t → ∃ λ u′ → wk ρ u′ PE.≡ u × ∇ ⊢ t′ ⇒ u′
    lemma {ρ} = λ where
      (δ-red {t} α↦t) eq →
        case inv-wk-defn eq of λ {
          PE.refl →
        _ ,
        (wk ρ (wk wk₀ t)  ≡⟨ wk-comp _ _ _ ⟩
         wk (ρ • wk₀) t   ≡⟨ PE.cong (flip wk _) $ wk₀-invariant ρ ⟩
         wk wk₀ t         ∎) ,
        δ-red α↦t }
      (app-subst d) eq →
        case inv-wk-∘ eq of λ {
          (_ , _ , PE.refl , PE.refl , PE.refl) →
        case strengthen-⇒ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , app-subst d }}
      (app-subst-arg v d) eq →
        case inv-wk-∘ eq of λ {
          (_ , _ , PE.refl , PE.refl , PE.refl) →
        case strengthen-⇒ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , app-subst-arg (strengthen-Value v) d }}
      (β-red v) eq →
        case inv-wk-∘ eq of λ {
          (_ , u , PE.refl , eq , PE.refl) →
        case inv-wk-lam eq of λ {
          (t , PE.refl , PE.refl) →
        _ ,
        (wk ρ (t [ u ]₀)            ≡⟨ wk-β t ⟩
         wk (lift ρ) t [ wk ρ u ]₀  ∎) ,
        β-red (strengthen-Value⟨⟩ v) }}
      (fst-subst d) eq →
        case inv-wk-fst eq of λ {
          (_ , PE.refl , PE.refl) →
        case strengthen-⇒ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , fst-subst d }}
      (snd-subst d) eq →
        case inv-wk-snd eq of λ {
          (_ , PE.refl , PE.refl) →
        case strengthen-⇒ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , snd-subst d }}
      Σ-β₁ eq →
        case inv-wk-fst eq of λ {
          (_ , PE.refl , eq) →
        case inv-wk-prod eq of λ {
          (_ , _ , PE.refl , PE.refl , PE.refl) →
        _ , PE.refl , Σ-β₁ }}
      Σ-β₂ eq →
        case inv-wk-snd eq of λ {
          (_ , PE.refl , eq) →
        case inv-wk-prod eq of λ {
          (_ , _ , PE.refl , PE.refl , PE.refl) →
        _ , PE.refl , Σ-β₂ }}
      (prodrec-subst d) eq →
        case inv-wk-prodrec eq of λ {
          (_ , _ , PE.refl , PE.refl , PE.refl) →
        case strengthen-⇒ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , prodrec-subst d }}
      prodrec-β eq →
        case inv-wk-prodrec eq of λ {
          (_ , t , PE.refl , eq , PE.refl) →
        case inv-wk-prod eq of λ {
          (u , v , PE.refl , PE.refl , PE.refl) →
        _ ,
        (wk ρ (t [ u , v ]₁₀)                    ≡⟨ wk-β-doubleSubst _ t _ _ ⟩
         wk (liftn ρ 2) t [ wk ρ u , wk ρ v ]₁₀  ∎) ,
        prodrec-β }}
      (natrec-subst d) eq →
        case inv-wk-natrec eq of λ {
          (_ , _ , _ , PE.refl , PE.refl , PE.refl , PE.refl) →
        case strengthen-⇒ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , natrec-subst d }}
      natrec-zero eq →
        case inv-wk-natrec eq of λ {
          (_ , _ , _ , PE.refl , PE.refl , PE.refl , eq) →
        case inv-wk-zero eq of λ {
          PE.refl →
        _ , PE.refl , natrec-zero }}
      natrec-suc eq →
        case inv-wk-natrec eq of λ {
          (t , u , _ , PE.refl , PE.refl , PE.refl , eq) →
        case inv-wk-suc eq of λ {
          (v , PE.refl , PE.refl) →
        _ ,
        (wk ρ (u [ v , natrec t u v ]₁₀)                      ≡⟨ wk-β-doubleSubst _ u _ _ ⟩
         wk (liftn ρ 2) u [ wk ρ v , wk ρ (natrec t u v) ]₁₀  ∎) ,
        natrec-suc }}
      (unitrec-subst d) eq →
        case inv-wk-unitrec eq of λ {
          (_ , _ , PE.refl , PE.refl , PE.refl) →
        case strengthen-⇒ d of λ {
          (_ , PE.refl , d) →
        _ , PE.refl , unitrec-subst d }}
      unitrec-β eq →
        case inv-wk-unitrec eq of λ {
          (_ , _ , PE.refl , eq , PE.refl) →
        case inv-wk-star eq of λ {
          PE.refl →
        _ , PE.refl , unitrec-β }}

opaque

  -- A strengthening lemma for reduction.

  strengthen-⇒* :
    ∇ ⊢ wk ρ t ⇒* u → ∃ λ u′ → wk ρ u′ PE.≡ u × ∇ ⊢ t ⇒* u′
  strengthen-⇒* = λ where
    refl →
      _ , PE.refl , refl
    (trans d₁ d₂) →
      case strengthen-⇒ d₁ of λ {
        (_ , PE.refl , d₁) →
      case strengthen-⇒* d₂ of λ {
        (_ , PE.refl , d₂) →
      _ , PE.refl , trans d₁ d₂ }}

opaque

  -- If wk ρ t reduces to a numeral, then t reduces to the same
  -- numeral.

  strengthen-⇒*-sucᵏ : ∇ ⊢ wk ρ t ⇒* sucᵏ n → ∇ ⊢ t ⇒* sucᵏ n
  strengthen-⇒*-sucᵏ d =
    case strengthen-⇒* d of λ {
      (_ , eq , d) →
    case inv-wk-sucᵏ eq of λ {
      PE.refl →
    d }}

-- Non-reducible terms

↯-noRed : ∇ ⊢ ↯ ⇒* t → t PE.≡ ↯
↯-noRed refl         = PE.refl
↯-noRed (trans () _)

zero-noRed : ∇ ⊢ zero ⇒* t → t PE.≡ zero
zero-noRed refl         = PE.refl
zero-noRed (trans () _)

suc-noRed : ∇ ⊢ suc t ⇒* t′ → t′ PE.≡ suc t
suc-noRed refl         = PE.refl
suc-noRed (trans () _)

prod-noRed : ∇ ⊢ prod t t′ ⇒* u → u PE.≡ prod t t′
prod-noRed refl         = PE.refl
prod-noRed (trans () _)

star-noRed : ∇ ⊢ star ⇒* t → t PE.≡ star
star-noRed refl         = PE.refl
star-noRed (trans () _)

opaque

  Value→⇒*→≡ : Value t → ∇ ⊢ t ⇒* u → u PE.≡ t
  Value→⇒*→≡ = λ where
    lam  refl          → PE.refl
    prod refl          → PE.refl
    zero refl          → PE.refl
    suc  refl          → PE.refl
    star refl          → PE.refl
    ↯    refl          → PE.refl
    t-v  (trans t⇒u _) → ⊥-elim $ Value→¬⇒ t-v t⇒u

opaque

  -- If t is a value, then Value⟨ s ⟩ t holds.

  Value→Value⟨⟩ : Value t → Value⟨ s ⟩ t
  Value→Value⟨⟩ {s = strict}     v = v
  Value→Value⟨⟩ {s = non-strict} _ = _

opaque

  -- Numerals are values.

  Numeral→Value : Numeral t → Value t
  Numeral→Value zero    = zero
  Numeral→Value (suc _) = suc

opaque

  -- The term sucᵏ k is a value.

  Value-sucᵏ : Value (sucᵏ {n = n} k)
  Value-sucᵏ {k = 0}    = zero
  Value-sucᵏ {k = 1+ _} = suc
