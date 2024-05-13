------------------------------------------------------------------------
-- Laws for weakenings in the target language.
------------------------------------------------------------------------

module Graded.Erasure.Target.Properties.Weakening where

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

open import Graded.Erasure.Target renaming (refl to ⇒*-refl; trans to ⇒*-trans)

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.PropositionalEquality hiding (subst)
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

private
  variable
    ℓ m n : Nat
    x : Fin n
    ρ ρ′ : Wk m n
    t u : Term n
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

opaque

  -- A weakening lemma for prod⟨_⟩.

  wk-prod⟨⟩ : wk ρ (prod⟨ s ⟩ t u) ≡ prod⟨ s ⟩ (wk ρ t) (wk ρ u)
  wk-prod⟨⟩ {s = strict}     = refl
  wk-prod⟨⟩ {s = non-strict} = refl

opaque

  -- If x occurs in wk ρ t, then x is equal to wkVar ρ y for some y
  -- that occurs in t.

  HasX-wk→ : HasX x (wk ρ t) → ∃ λ y → x ≡ wkVar ρ y × HasX y t
  HasX-wk→ {x} {ρ} {t = var z} =
    HasX x (var (wkVar ρ z))                  →⟨ (λ { varₓ → refl }) ⟩
    x ≡ wkVar ρ z                             →⟨ (λ eq → _ , eq , varₓ) ⟩
    (∃ λ y → x ≡ wkVar ρ y × HasX y (var z))  □
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
