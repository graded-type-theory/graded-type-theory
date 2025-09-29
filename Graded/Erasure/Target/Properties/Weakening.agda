------------------------------------------------------------------------
-- Laws for weakenings in the target language.
------------------------------------------------------------------------

module Graded.Erasure.Target.Properties.Weakening where

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

open import Graded.Erasure.Target renaming (refl to ⇒*-refl; trans to ⇒*-trans)

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.PropositionalEquality hiding (subst)
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

private
  variable
    α ℓ m n : Nat
    x : Fin n
    ρ ρ′ : Wk m n
    t u v w : Term n
    s : Strictness

-- Weakening properties

-- Extensionally equal weakenings, if applied to a term,
-- yield the same weakened term.  Or:
-- If two weakenings are equal under wkVar, then they are equal under wk.

mutual
  wkVar-to-wk : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
              → ∀ (t : Term n) → wk ρ t ≡ wk ρ′ t
  wkVar-to-wk eq (var x) = cong var (eq x)
  wkVar-to-wk _ (defn α) = refl
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
  wk-id (defn _) = refl
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
  wk-comp _ _ (defn _) = refl
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

opaque

  -- A weakening lemma for prod⟨_⟩.

  wk-prod⟨⟩ : wk ρ (prod⟨ s ⟩ t u) ≡ prod⟨ s ⟩ (wk ρ t) (wk ρ u)
  wk-prod⟨⟩ {s = strict}     = refl
  wk-prod⟨⟩ {s = non-strict} = refl

------------------------------------------------------------------------
-- Some lemmas related to HasX

opaque

  -- If x occurs in wk ρ t, then x is equal to wkVar ρ y for some y
  -- that occurs in t.

  HasX-wk→ : HasX x (wk ρ t) → ∃ λ y → x ≡ wkVar ρ y × HasX y t
  HasX-wk→ {x} {ρ} {t = var z} =
    HasX x (var (wkVar ρ z))                  →⟨ (λ { varₓ → refl }) ⟩
    x ≡ wkVar ρ z                             →⟨ (λ eq → _ , eq , varₓ) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (var z))  □
  HasX-wk→ {x} {ρ} {t = defn α} =
    HasX x (defn α)                            →⟨ (λ ()) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (defn α))  □
  HasX-wk→ {x} {ρ} {t = lam t} =
    HasX x (lam (wk (lift ρ) t))                  →⟨ (λ { (lamₓ has) → has }) ⟩
    HasX (x +1) (wk (lift ρ) t)                   →⟨ HasX-wk→ ⟩
    (∃ λ y → x +1 ≡ wkVar (lift ρ) y × HasX y t)  →⟨ (λ where
                                                        (x0     , ()   , _)
                                                        ((y +1) , refl , has) → y , refl , lamₓ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (lam t))      □
  HasX-wk→ {x} {ρ} {t = t ∘⟨ s ⟩ u} =
    HasX x (wk ρ t ∘⟨ s ⟩ wk ρ u)                  →⟨ (λ where
                                                         (∘ₓˡ has) → inj₁ has
                                                         (∘ₓʳ has) → inj₂ has) ⟩

    HasX x (wk ρ t) ⊎ HasX x (wk ρ u)              →⟨ ⊎.map HasX-wk→ HasX-wk→ ⟩

    (∃ λ y → x ≡ wkVar ρ y × HasX y t) ⊎
    (∃ λ y → x ≡ wkVar ρ y × HasX y u)             →⟨ (λ where
                                                         (inj₁ (_ , eq , has)) → _ , eq , ∘ₓˡ has
                                                         (inj₂ (_ , eq , has)) → _ , eq , ∘ₓʳ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (t ∘⟨ s ⟩ u))  □
  HasX-wk→ {x} {ρ} {t = prod t u} =
    HasX x (prod (wk ρ t) (wk ρ u))              →⟨ (λ where
                                                       (prodₓˡ has) → inj₁ has
                                                       (prodₓʳ has) → inj₂ has) ⟩

    HasX x (wk ρ t) ⊎ HasX x (wk ρ u)            →⟨ ⊎.map HasX-wk→ HasX-wk→ ⟩

    (∃ λ y → x ≡ wkVar ρ y × HasX y t) ⊎
    (∃ λ y → x ≡ wkVar ρ y × HasX y u)           →⟨ (λ where
                                                       (inj₁ (_ , eq , has)) → _ , eq , prodₓˡ has
                                                       (inj₂ (_ , eq , has)) → _ , eq , prodₓʳ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (prod t u))  □
  HasX-wk→ {x} {ρ} {t = fst t} =
    HasX x (fst (wk ρ t))                     →⟨ (λ { (fstₓ has) → has }) ⟩
    HasX x (wk ρ t)                           →⟨ HasX-wk→ ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y t)        →⟨ (λ (_ , eq , has) → _ , eq , fstₓ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (fst t))  □
  HasX-wk→ {x} {ρ} {t = snd t} =
    HasX x (snd (wk ρ t))                     →⟨ (λ { (sndₓ has) → has }) ⟩
    HasX x (wk ρ t)                           →⟨ HasX-wk→ ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y t)        →⟨ (λ (_ , eq , has) → _ , eq , sndₓ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (snd t))  □
  HasX-wk→ {x} {ρ} {t = prodrec t u} =
    HasX x (prodrec (wk ρ t) (wk (lift (lift ρ)) u))       →⟨ (λ where
                                                            (prodrecₓˡ has) → inj₁ has
                                                            (prodrecₓʳ has) → inj₂ has) ⟩

    HasX x (wk ρ t) ⊎ HasX (x +2) (wk (lift (lift ρ)) u)   →⟨ ⊎.map HasX-wk→ HasX-wk→ ⟩

    (∃ λ y → x ≡ wkVar ρ y × HasX y t) ⊎
    (∃ λ y → (x +2) ≡ wkVar (lift (lift ρ)) y × HasX y u)  →⟨ (λ where
                                                                 (inj₁ (_ , eq , has))         → _ , eq , prodrecₓˡ has
                                                                 (inj₂ (x0      , ()   , _))
                                                                 (inj₂ ((x0 +1) , ()   , _))
                                                                 (inj₂ ((y +2)  , refl , has)) → _ , refl , prodrecₓʳ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (prodrec t u))         □
  HasX-wk→ {x} {ρ} {t = suc t} =
    HasX x (suc (wk ρ t))                     →⟨ (λ { (sucₓ has) → has }) ⟩
    HasX x (wk ρ t)                           →⟨ HasX-wk→ ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y t)        →⟨ (λ (_ , eq , has) → _ , eq , sucₓ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (suc t))  □
  HasX-wk→ {x} {ρ} {t = natrec t u v} =
    HasX x (natrec (wk ρ t) (wk (lift (lift ρ)) u) (wk ρ v))  →⟨ (λ where
                                                                    (natrecₓᶻ has) → inj₁ has
                                                                    (natrecₓˢ has) → inj₂ (inj₁ has)
                                                                    (natrecₓⁿ has) → inj₂ (inj₂ has)) ⟩
    HasX x (wk ρ t) ⊎
    HasX (x +2) (wk (lift (lift ρ)) u) ⊎
    HasX x (wk ρ v)                                           →⟨ ⊎.map HasX-wk→ $ ⊎.map HasX-wk→ HasX-wk→ ⟩

    (∃ λ y → x ≡ wkVar ρ y × HasX y t) ⊎
    (∃ λ y → (x +2) ≡ wkVar (lift (lift ρ)) y × HasX y u) ⊎
    (∃ λ y → x ≡ wkVar ρ y × HasX y v)                        →⟨ (λ where
                                                                    (inj₁ (_ , eq , has))                → _ , eq   , natrecₓᶻ has
                                                                    (inj₂ (inj₁ (x0      , ()   , _)))
                                                                    (inj₂ (inj₁ ((x0 +1) , ()   , _)))
                                                                    (inj₂ (inj₁ ((y +2)  , refl , has))) → _ , refl , natrecₓˢ has
                                                                    (inj₂ (inj₂ (_ , eq , has)))         → _ , eq   , natrecₓⁿ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (natrec t u v))           □
  HasX-wk→ {x} {ρ} {t = unitrec t u} =
    HasX x (unitrec (wk ρ t) (wk ρ u))              →⟨ (λ where
                                                          (unitrecₓˡ has) → inj₁ has
                                                          (unitrecₓʳ has) → inj₂ has) ⟩

    HasX x (wk ρ t) ⊎ HasX x (wk ρ u)               →⟨ ⊎.map HasX-wk→ HasX-wk→ ⟩

    (∃ λ y → x ≡ wkVar ρ y × HasX y t) ⊎
    (∃ λ y → x ≡ wkVar ρ y × HasX y u)              →⟨ (λ where
                                                          (inj₁ (_ , eq , has)) → _ , eq , unitrecₓˡ has
                                                          (inj₂ (_ , eq , has)) → _ , eq , unitrecₓʳ has) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (unitrec t u))  □
  HasX-wk→ {t = zero} ()
  HasX-wk→ {t = star} ()
  HasX-wk→ {t = ↯}    ()

opaque

  -- If wkVar ρ x occurs in wk ρ t, then x occurs in t.

  HasX-wkVar-wk→ : HasX (wkVar ρ x) (wk ρ t) → HasX x t
  HasX-wkVar-wk→ {ρ} {x} {t} =
    HasX (wkVar ρ x) (wk ρ t)                   →⟨ HasX-wk→ ⟩
    (∃ λ y → wkVar ρ x ≡ wkVar ρ y × HasX y t)  →⟨ Σ.map idᶠ $ Σ.map wkVar-injective idᶠ ⟩
    (∃ λ y → x ≡ y × HasX y t)                  →⟨ (λ { (_ , refl , has) → has }) ⟩
    HasX x t                                    □

opaque

  -- The variable x does not occur in wk (step-at x) t.

  ¬-HasX-wk-step-at : ¬ HasX x (wk (step-at x) t)
  ¬-HasX-wk-step-at {x} {t} =
    HasX x (wk (step-at x) t)                     →⟨ HasX-wk→ ⟩
    (∃ λ y → x ≡ wkVar (step-at x) y × HasX y t)  →⟨ ≢wkVar-step-at ∘→ proj₁ ∘→ proj₂ ⟩
    ⊥                                             □

------------------------------------------------------------------------
-- Inversion lemmas for weakening

opaque

  -- Inversion for var.

  inv-wk-var :
    wk ρ t ≡ var x →
    ∃ λ x′ → t ≡ var x′ × wkVar ρ x′ ≡ x
  inv-wk-var {t = var _}        refl = _ , refl , refl
  inv-wk-var {t = defn _}       ()
  inv-wk-var {t = lam _}        ()
  inv-wk-var {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-var {t = prod _ _}     ()
  inv-wk-var {t = fst _}        ()
  inv-wk-var {t = snd _}        ()
  inv-wk-var {t = prodrec _ _}  ()
  inv-wk-var {t = star}         ()
  inv-wk-var {t = unitrec _ _}  ()
  inv-wk-var {t = zero}         ()
  inv-wk-var {t = suc _}        ()
  inv-wk-var {t = natrec _ _ _} ()
  inv-wk-var {t = ↯}            ()

opaque

  -- Inversion for defn.

  inv-wk-defn : wk ρ t ≡ defn α → t ≡ defn α
  inv-wk-defn {t = defn _}       refl = refl
  inv-wk-defn {t = var _}        ()
  inv-wk-defn {t = lam _}        ()
  inv-wk-defn {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-defn {t = prod _ _}     ()
  inv-wk-defn {t = fst _}        ()
  inv-wk-defn {t = snd _}        ()
  inv-wk-defn {t = prodrec _ _}  ()
  inv-wk-defn {t = star}         ()
  inv-wk-defn {t = unitrec _ _}  ()
  inv-wk-defn {t = zero}         ()
  inv-wk-defn {t = suc _}        ()
  inv-wk-defn {t = natrec _ _ _} ()
  inv-wk-defn {t = ↯}            ()

opaque

  -- Inversion for lam.

  inv-wk-lam :
    wk ρ t ≡ lam u →
    ∃ λ u′ → t ≡ lam u′ × wk (lift ρ) u′ ≡ u
  inv-wk-lam {t = lam _}        refl = _ , refl , refl
  inv-wk-lam {t = var _}        ()
  inv-wk-lam {t = defn _}       ()
  inv-wk-lam {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-lam {t = prod _ _}     ()
  inv-wk-lam {t = fst _}        ()
  inv-wk-lam {t = snd _}        ()
  inv-wk-lam {t = prodrec _ _}  ()
  inv-wk-lam {t = star}         ()
  inv-wk-lam {t = unitrec _ _}  ()
  inv-wk-lam {t = zero}         ()
  inv-wk-lam {t = suc _}        ()
  inv-wk-lam {t = natrec _ _ _} ()
  inv-wk-lam {t = ↯}            ()

opaque

  -- Inversion for _∘⟨_⟩_.

  inv-wk-∘ :
    wk ρ t ≡ u ∘⟨ s ⟩ v →
    ∃₂ λ u′ v′ → t ≡ u′ ∘⟨ s ⟩ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
  inv-wk-∘ {t = _ ∘⟨ _ ⟩ _}   refl = _ , _ , refl , refl , refl
  inv-wk-∘ {t = var _}        ()
  inv-wk-∘ {t = defn _}       ()
  inv-wk-∘ {t = lam _}        ()
  inv-wk-∘ {t = prod _ _}     ()
  inv-wk-∘ {t = fst _}        ()
  inv-wk-∘ {t = snd _}        ()
  inv-wk-∘ {t = prodrec _ _}  ()
  inv-wk-∘ {t = star}         ()
  inv-wk-∘ {t = unitrec _ _}  ()
  inv-wk-∘ {t = zero}         ()
  inv-wk-∘ {t = suc _}        ()
  inv-wk-∘ {t = natrec _ _ _} ()
  inv-wk-∘ {t = ↯}            ()

opaque

  -- Inversion for prod.

  inv-wk-prod :
    wk ρ t ≡ prod u v →
    ∃₂ λ u′ v′ → t ≡ prod u′ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
  inv-wk-prod {t = prod _ _}     refl = _ , _ , refl , refl , refl
  inv-wk-prod {t = var _}        ()
  inv-wk-prod {t = defn _}       ()
  inv-wk-prod {t = lam _}        ()
  inv-wk-prod {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-prod {t = fst _}        ()
  inv-wk-prod {t = snd _}        ()
  inv-wk-prod {t = prodrec _ _}  ()
  inv-wk-prod {t = star}         ()
  inv-wk-prod {t = unitrec _ _}  ()
  inv-wk-prod {t = zero}         ()
  inv-wk-prod {t = suc _}        ()
  inv-wk-prod {t = natrec _ _ _} ()
  inv-wk-prod {t = ↯}            ()

opaque

  -- Inversion for fst.

  inv-wk-fst :
    wk ρ t ≡ fst u →
    ∃ λ u′ → t ≡ fst u′ × wk ρ u′ ≡ u
  inv-wk-fst {t = fst _}        refl = _ , refl , refl
  inv-wk-fst {t = var _}        ()
  inv-wk-fst {t = defn _}       ()
  inv-wk-fst {t = lam _}        ()
  inv-wk-fst {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-fst {t = prod _ _}     ()
  inv-wk-fst {t = snd _}        ()
  inv-wk-fst {t = prodrec _ _}  ()
  inv-wk-fst {t = star}         ()
  inv-wk-fst {t = unitrec _ _}  ()
  inv-wk-fst {t = zero}         ()
  inv-wk-fst {t = suc _}        ()
  inv-wk-fst {t = natrec _ _ _} ()
  inv-wk-fst {t = ↯}            ()

opaque

  -- Inversion for snd.

  inv-wk-snd :
    wk ρ t ≡ snd u →
    ∃ λ u′ → t ≡ snd u′ × wk ρ u′ ≡ u
  inv-wk-snd {t = snd _}        refl = _ , refl , refl
  inv-wk-snd {t = var _}        ()
  inv-wk-snd {t = defn _}       ()
  inv-wk-snd {t = lam _}        ()
  inv-wk-snd {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-snd {t = prod _ _}     ()
  inv-wk-snd {t = fst _}        ()
  inv-wk-snd {t = prodrec _ _}  ()
  inv-wk-snd {t = star}         ()
  inv-wk-snd {t = unitrec _ _}  ()
  inv-wk-snd {t = zero}         ()
  inv-wk-snd {t = suc _}        ()
  inv-wk-snd {t = natrec _ _ _} ()
  inv-wk-snd {t = ↯}            ()

opaque

  -- Inversion for prodrec.

  inv-wk-prodrec :
    wk ρ t ≡ prodrec u v →
    ∃₂ λ u′ v′ → t ≡ prodrec u′ v′ × wk ρ u′ ≡ u × wk (liftn ρ 2) v′ ≡ v
  inv-wk-prodrec {t = prodrec _ _}  refl = _ , _ , refl , refl , refl
  inv-wk-prodrec {t = var _}        ()
  inv-wk-prodrec {t = defn _}       ()
  inv-wk-prodrec {t = lam _}        ()
  inv-wk-prodrec {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-prodrec {t = prod _ _}     ()
  inv-wk-prodrec {t = fst _}        ()
  inv-wk-prodrec {t = snd _}        ()
  inv-wk-prodrec {t = star}         ()
  inv-wk-prodrec {t = unitrec _ _}  ()
  inv-wk-prodrec {t = zero}         ()
  inv-wk-prodrec {t = suc _}        ()
  inv-wk-prodrec {t = natrec _ _ _} ()
  inv-wk-prodrec {t = ↯}            ()

opaque

  -- Inversion for star.

  inv-wk-star : wk ρ t ≡ star → t ≡ star
  inv-wk-star {t = star}         refl = refl
  inv-wk-star {t = var _}        ()
  inv-wk-star {t = defn _}       ()
  inv-wk-star {t = lam _}        ()
  inv-wk-star {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-star {t = prod _ _}     ()
  inv-wk-star {t = fst _}        ()
  inv-wk-star {t = snd _}        ()
  inv-wk-star {t = prodrec _ _}  ()
  inv-wk-star {t = unitrec _ _}  ()
  inv-wk-star {t = zero}         ()
  inv-wk-star {t = suc _}        ()
  inv-wk-star {t = natrec _ _ _} ()
  inv-wk-star {t = ↯}            ()

opaque

  -- Inversion for unitrec.

  inv-wk-unitrec :
    wk ρ t ≡ unitrec u v →
    ∃₂ λ u′ v′ → t ≡ unitrec u′ v′ × wk ρ u′ ≡ u × wk ρ v′ ≡ v
  inv-wk-unitrec {t = unitrec _ _}  refl = _ , _ , refl , refl , refl
  inv-wk-unitrec {t = var _}        ()
  inv-wk-unitrec {t = defn _}       ()
  inv-wk-unitrec {t = lam _}        ()
  inv-wk-unitrec {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-unitrec {t = prod _ _}     ()
  inv-wk-unitrec {t = fst _}        ()
  inv-wk-unitrec {t = snd _}        ()
  inv-wk-unitrec {t = prodrec _ _}  ()
  inv-wk-unitrec {t = star}         ()
  inv-wk-unitrec {t = zero}         ()
  inv-wk-unitrec {t = suc _}        ()
  inv-wk-unitrec {t = natrec _ _ _} ()
  inv-wk-unitrec {t = ↯}            ()

opaque

  -- Inversion for zero.

  inv-wk-zero : wk ρ t ≡ zero → t ≡ zero
  inv-wk-zero {t = zero}         refl = refl
  inv-wk-zero {t = var _}        ()
  inv-wk-zero {t = defn _}       ()
  inv-wk-zero {t = lam _}        ()
  inv-wk-zero {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-zero {t = prod _ _}     ()
  inv-wk-zero {t = fst _}        ()
  inv-wk-zero {t = snd _}        ()
  inv-wk-zero {t = prodrec _ _}  ()
  inv-wk-zero {t = star}         ()
  inv-wk-zero {t = unitrec _ _}  ()
  inv-wk-zero {t = suc _}        ()
  inv-wk-zero {t = natrec _ _ _} ()
  inv-wk-zero {t = ↯}            ()

opaque

  -- Inversion for suc.

  inv-wk-suc :
    wk ρ t ≡ suc u →
    ∃ λ u′ → t ≡ suc u′ × wk ρ u′ ≡ u
  inv-wk-suc {t = suc _}        refl = _ , refl , refl
  inv-wk-suc {t = var _}        ()
  inv-wk-suc {t = defn _}       ()
  inv-wk-suc {t = lam _}        ()
  inv-wk-suc {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-suc {t = prod _ _}     ()
  inv-wk-suc {t = fst _}        ()
  inv-wk-suc {t = snd _}        ()
  inv-wk-suc {t = prodrec _ _}  ()
  inv-wk-suc {t = star}         ()
  inv-wk-suc {t = unitrec _ _}  ()
  inv-wk-suc {t = zero}         ()
  inv-wk-suc {t = natrec _ _ _} ()
  inv-wk-suc {t = ↯}            ()

opaque

  -- Inversion for sucᵏ.

  inv-wk-sucᵏ : wk ρ t ≡ sucᵏ n → t ≡ sucᵏ n
  inv-wk-sucᵏ {n = 0} =
    inv-wk-zero
  inv-wk-sucᵏ {n = 1+ _} eq =
    case inv-wk-suc eq of λ {
      (_ , refl , eq) →
    cong suc (inv-wk-sucᵏ eq) }

opaque

  -- Inversion for natrec.

  inv-wk-natrec :
    wk ρ t ≡ natrec u v w →
    ∃₃ λ u′ v′ w′ →
       t ≡ natrec u′ v′ w′ ×
       wk ρ u′ ≡ u × wk (liftn ρ 2) v′ ≡ v × wk ρ w′ ≡ w
  inv-wk-natrec {t = natrec _ _ _} refl =
    _ , _ , _ , refl , refl , refl , refl
  inv-wk-natrec {t = var _}       ()
  inv-wk-natrec {t = defn _}      ()
  inv-wk-natrec {t = lam _}       ()
  inv-wk-natrec {t = _ ∘⟨ _ ⟩ _}  ()
  inv-wk-natrec {t = prod _ _}    ()
  inv-wk-natrec {t = fst _}       ()
  inv-wk-natrec {t = snd _}       ()
  inv-wk-natrec {t = prodrec _ _} ()
  inv-wk-natrec {t = star}        ()
  inv-wk-natrec {t = unitrec _ _} ()
  inv-wk-natrec {t = zero}        ()
  inv-wk-natrec {t = suc _}       ()
  inv-wk-natrec {t = ↯}           ()

opaque

  -- Inversion for ↯.

  inv-wk-↯ : wk ρ t ≡ ↯ → t ≡ ↯
  inv-wk-↯ {t = ↯}            refl = refl
  inv-wk-↯ {t = var _}        ()
  inv-wk-↯ {t = defn _}       ()
  inv-wk-↯ {t = lam _}        ()
  inv-wk-↯ {t = _ ∘⟨ _ ⟩ _}   ()
  inv-wk-↯ {t = prod _ _}     ()
  inv-wk-↯ {t = fst _}        ()
  inv-wk-↯ {t = snd _}        ()
  inv-wk-↯ {t = prodrec _ _}  ()
  inv-wk-↯ {t = star}         ()
  inv-wk-↯ {t = unitrec _ _}  ()
  inv-wk-↯ {t = zero}         ()
  inv-wk-↯ {t = suc _}        ()
  inv-wk-↯ {t = natrec _ _ _} ()

------------------------------------------------------------------------
-- Some lemmas related to Value and Value⟨_⟩

opaque

  -- Value is closed under weakening.

  wk-Value : Value t → Value (wk ρ t)
  wk-Value lam  = lam
  wk-Value prod = prod
  wk-Value zero = zero
  wk-Value suc  = suc
  wk-Value star = star
  wk-Value ↯    = ↯

opaque

  -- Value⟨ s ⟩ is closed under weakening.

  wk-Value⟨⟩ : Value⟨ s ⟩ t → Value⟨ s ⟩ (wk ρ t)
  wk-Value⟨⟩ {s = strict}     = wk-Value
  wk-Value⟨⟩ {s = non-strict} = _

opaque

  -- Value is closed under strengthening.

  strengthen-Value : Value (wk ρ t) → Value t
  strengthen-Value = flip lemma refl
    where
    lemma : Value u → wk ρ t ≡ u → Value t
    lemma = λ where
      lam eq →
        case inv-wk-lam eq of λ {
          (_ , refl , _) →
        lam }
      prod eq →
        case inv-wk-prod eq of λ {
          (_ , _ , refl , _) →
        prod }
      zero eq →
        case inv-wk-zero eq of λ {
          refl →
        zero }
      suc eq →
        case inv-wk-suc eq of λ {
          (_ , refl , _) →
        suc }
      star eq →
        case inv-wk-star eq of λ {
          refl →
        star }
      ↯ eq →
        case inv-wk-↯ eq of λ {
          refl →
        ↯ }

opaque

  -- Value⟨ s ⟩ is closed under strengthening.

  strengthen-Value⟨⟩ : Value⟨ s ⟩ (wk ρ t) → Value⟨ s ⟩ t
  strengthen-Value⟨⟩ {s = strict}     = strengthen-Value
  strengthen-Value⟨⟩ {s = non-strict} = _
