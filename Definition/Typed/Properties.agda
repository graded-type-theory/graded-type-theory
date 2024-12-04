------------------------------------------------------------------------
-- Properties of the typing and reduction relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M

open import Definition.Typed R

open import Tools.Fin
{-

------------------------------------------------------------------------
-- Some lemmas related to the reduction relations

-- Reduction is a subset of conversion

subsetTerm : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong F (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc F z s n) = natrec-suc F z s n
subsetTerm (emptyrec-subst A n⇒n′) =
  emptyrec-cong (refl A) (subsetTerm n⇒n′)
subsetTerm (app-subst t⇒u a) =
  app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A B t a p≡p′ ok) = β-red A B t a p≡p′ ok
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (fst-subst F G x) = fst-cong F G (subsetTerm x)
subsetTerm (snd-subst F G x) = snd-cong F G (subsetTerm x)
subsetTerm (prodrec-subst F G A u t⇒t′ ok) =
  prodrec-cong F G (refl A) (subsetTerm t⇒t′) (refl u) ok
subsetTerm (prodrec-β F G A t t′ u eq ok) =
  prodrec-β F G A t t′ u eq ok
subsetTerm (Σ-β₁ F G x x₁ x₂ ok) = Σ-β₁ F G x x₁ x₂ ok
subsetTerm (Σ-β₂ F G x x₁ x₂ ok) = Σ-β₂ F G x x₁ x₂ ok
subsetTerm (J-subst ⊢A ⊢t ⊢B ⊢u ⊢t′ v⇒v′) =
  J-cong ⊢A (refl ⊢A) ⊢t (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢t′)
    (subsetTerm v⇒v′)
subsetTerm (K-subst ⊢A ⊢t ⊢B ⊢u v⇒v′ ok) =
  K-cong (refl ⊢A) ⊢t (refl ⊢t) (refl ⊢B) (refl ⊢u)
    (subsetTerm v⇒v′) ok
subsetTerm ([]-cong-subst ⊢A ⊢t ⊢u v⇒v′ ok) =
  []-cong-cong (refl ⊢A) (refl ⊢t) (refl ⊢u) (subsetTerm v⇒v′) ok
subsetTerm (J-β ⊢A ⊢t _ t≡t′ ⊢B _ ⊢u) =
  trans (sym (J-cong ⊢A (refl ⊢A) ⊢t (refl ⊢t) (refl ⊢B) (refl ⊢u)
                t≡t′ (refl (rflⱼ ⊢t))))
    (J-β ⊢A ⊢t ⊢B ⊢u PE.refl)
subsetTerm (K-β ⊢t ⊢B ⊢u ok) = K-β ⊢t ⊢B ⊢u ok
subsetTerm ([]-cong-β ⊢A ⊢t _ t≡t′ ok) =
  trans
    ([]-cong-cong (refl ⊢A) (refl ⊢t)
       (sym t≡t′)
       (conv (refl (rflⱼ ⊢t)) (Id-cong (refl ⊢A) (refl ⊢t) t≡t′))
       ok)
    (conv ([]-cong-β ⊢t PE.refl ok)
       (Id-cong (refl (Erasedⱼ ⊢A)) (refl ([]ⱼ ⊢A ⊢t))
          ([]-cong′ ⊢A t≡t′)))
  where
  open Erased ([]-cong→Erased ok)
subsetTerm (unitrec-subst l A u t⇒t′ ok no-η) =
  unitrec-cong (refl l) (refl A) (subsetTerm t⇒t′) (refl u) ok no-η
subsetTerm (unitrec-β l A u ok₁ ok₂) = unitrec-β l A u ok₁ ok₂
subsetTerm (unitrec-β-η l A t u ok₁ ok₂) =
 unitrec-β-η l A t u ok₁ ok₂

subset : Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)


-- Can extract left-part of a reduction

redFirstTerm :{Γ : Con Term n} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A
redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t⇒u a) = (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (β-red A B t a PE.refl ok) =
  conv (lamⱼ A t ok) (ΠΣ-cong A (refl A) (refl B) ok) ∘ⱼ a
redFirstTerm (natrec-subst F z s n⇒n′) = natrecⱼ F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F z s) = natrecⱼ F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc F z s n) = natrecⱼ F z s (sucⱼ n)
redFirstTerm (emptyrec-subst A n⇒n′) = emptyrecⱼ A (redFirstTerm n⇒n′)
redFirstTerm (fst-subst F G x) = fstⱼ F G (redFirstTerm x)
redFirstTerm (snd-subst F G x) = sndⱼ F G (redFirstTerm x)
redFirstTerm (prodrec-subst F G A u t⇒t′ ok) =
  prodrecⱼ F G A (redFirstTerm t⇒t′) u ok
redFirstTerm (prodrec-β F G A t t′ u PE.refl ok) =
  prodrecⱼ F G A
    (conv (prodⱼ F G t t′ ok) (ΠΣ-cong F (refl F) (refl G) ok))
    u ok
redFirstTerm (Σ-β₁ F G x x₁ PE.refl ok) =
  fstⱼ F G
    (conv (prodⱼ F G x x₁ ok) (ΠΣ-cong F (refl F) (refl G) ok))
redFirstTerm (Σ-β₂ F G x x₁ PE.refl ok) =
  sndⱼ F G
    (conv (prodⱼ F G x x₁ ok) (ΠΣ-cong F (refl F) (refl G) ok))
redFirstTerm (J-subst ⊢A ⊢t ⊢B ⊢u ⊢t′ v⇒v′) =
  Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢t′ (redFirstTerm v⇒v′)
redFirstTerm (K-subst _ ⊢t ⊢B ⊢u v⇒v′ ok) =
  Kⱼ ⊢t ⊢B ⊢u (redFirstTerm v⇒v′) ok
redFirstTerm ([]-cong-subst _ ⊢t ⊢u v⇒v′ ok) =
  []-congⱼ ⊢t ⊢u (redFirstTerm v⇒v′) ok
redFirstTerm (J-β ⊢A ⊢t ⊢t′ t≡t′ ⊢B B≡B ⊢u) =
  conv (Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢t′
          (conv (rflⱼ ⊢t) (Id-cong (refl ⊢A) (refl ⊢t) t≡t′)))
    (sym B≡B)
redFirstTerm (K-β ⊢t ⊢B ⊢u ok) =
  Kⱼ ⊢t ⊢B ⊢u (rflⱼ ⊢t) ok
redFirstTerm ([]-cong-β ⊢A ⊢t ⊢t′ t≡t′ ok) =
  []-congⱼ ⊢t ⊢t′ (conv (rflⱼ ⊢t) (Id-cong (refl ⊢A) (refl ⊢t) t≡t′)) ok
redFirstTerm (unitrec-subst l A u t⇒t′ ok _) =
  unitrecⱼ l A (redFirstTerm t⇒t′) u ok
redFirstTerm (unitrec-β l A u ok _) =
  unitrecⱼ l A (starⱼ l ok) u ok
redFirstTerm (unitrec-β-η l A t u ok _) =
  unitrecⱼ l A t u ok

redFirst : {Γ : Con Term n} → Γ ⊢ A ⇒ B → Γ ⊢ A
redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : {Γ : Con Term n} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : {Γ : Con Term n} → Γ ⊢ A ⇒* B → Γ ⊢ A
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′

opaque

  -- Neutral terms do not reduce.

  neRedTerm : Γ ⊢ t ⇒ u ∷ A → Neutral t → ⊥
  neRedTerm = λ where
    (conv d _)                  → neRedTerm d
    (app-subst d _)             → neRedTerm d ∘→ inv-ne-∘
    (β-red _ _ _ _ _ _)         → (λ ()) ∘→ inv-ne-∘
    (natrec-subst _ _ _ d)      → neRedTerm d ∘→ inv-ne-natrec
    (natrec-zero _ _ _)         → (λ ()) ∘→ inv-ne-natrec
    (natrec-suc _ _ _ _)        → (λ ()) ∘→ inv-ne-natrec
    (emptyrec-subst _ d)        → neRedTerm d ∘→ inv-ne-emptyrec
    (fst-subst _ _ d)           → neRedTerm d ∘→ inv-ne-fst
    (snd-subst _ _ d)           → neRedTerm d ∘→ inv-ne-snd
    (prodrec-subst _ _ _ _ d _) → neRedTerm d ∘→ inv-ne-prodrec
    (prodrec-β _ _ _ _ _ _ _ _) → (λ ()) ∘→ inv-ne-prodrec
    (Σ-β₁ _ _ _ _ _ _)          → (λ ()) ∘→ inv-ne-fst
    (Σ-β₂ _ _ _ _ _ _)          → (λ ()) ∘→ inv-ne-snd
    (J-subst _ _ _ _ _ d)       → neRedTerm d ∘→ inv-ne-J
    (K-subst _ _ _ _ d _)       → neRedTerm d ∘→ inv-ne-K
    ([]-cong-subst _ _ _ d _)   → neRedTerm d ∘→ inv-ne-[]-cong
    (J-β _ _ _ _ _ _ _)         → (λ ()) ∘→ inv-ne-J
    (K-β _ _ _ _)               → (λ ()) ∘→ inv-ne-K
    ([]-cong-β _ _ _ _ _)       → (λ ()) ∘→ inv-ne-[]-cong
    (unitrec-subst _ _ _ d _ _) → neRedTerm d ∘→ proj₂ ∘→ inv-ne-unitrec
    (unitrec-β _ _ _ _ _)       → (λ ()) ∘→ proj₂ ∘→ inv-ne-unitrec
    (unitrec-β-η _ _ _ _ _ ok)  → (_$ ok) ∘→ proj₁ ∘→ inv-ne-unitrec


neRed : (d : Γ ⊢ A ⇒ B) (N : Neutral A) → ⊥
neRed (univ x) N = neRedTerm x N

opaque

  -- WHNFs do not reduce.

  whnfRedTerm : Γ ⊢ t ⇒ u ∷ A → Whnf t → ⊥
  whnfRedTerm = λ where
    (conv d _)                  → whnfRedTerm d
    (app-subst d _)             → neRedTerm d ∘→ inv-whnf-∘
    (β-red _ _ _ _ _ _)         → (λ ()) ∘→ inv-whnf-∘
    (natrec-subst _ _ _ d)      → neRedTerm d ∘→ inv-whnf-natrec
    (natrec-zero _ _ _)         → (λ ()) ∘→ inv-whnf-natrec
    (natrec-suc _ _ _ _)        → (λ ()) ∘→ inv-whnf-natrec
    (emptyrec-subst _ d)        → neRedTerm d ∘→ inv-whnf-emptyrec
    (fst-subst _ _ d)           → neRedTerm d ∘→ inv-whnf-fst
    (snd-subst _ _ d)           → neRedTerm d ∘→ inv-whnf-snd
    (prodrec-subst _ _ _ _ d _) → neRedTerm d ∘→ inv-whnf-prodrec
    (prodrec-β _ _ _ _ _ _ _ _) → (λ ()) ∘→ inv-whnf-prodrec
    (Σ-β₁ _ _ _ _ _ _)          → (λ ()) ∘→ inv-whnf-fst
    (Σ-β₂ _ _ _ _ _ _)          → (λ ()) ∘→ inv-whnf-snd
    (J-subst _ _ _ _ _ d)       → neRedTerm d ∘→ inv-whnf-J
    (K-subst _ _ _ _ d _)       → neRedTerm d ∘→ inv-whnf-K
    ([]-cong-subst _ _ _ d _)   → neRedTerm d ∘→ inv-whnf-[]-cong
    (J-β _ _ _ _ _ _ _)         → (λ ()) ∘→ inv-whnf-J
    (K-β _ _ _ _)               → (λ ()) ∘→ inv-whnf-K
    ([]-cong-β _ _ _ _ _)       → (λ ()) ∘→ inv-whnf-[]-cong
    (unitrec-subst _ _ _ d _ _) → neRedTerm d ∘→ proj₂ ∘→
                                  inv-whnf-unitrec
    (unitrec-β _ _ _ _ _)       → (λ ()) ∘→ proj₂ ∘→ inv-whnf-unitrec
    (unitrec-β-η _ _ _ _ _ ok)  → (_$ ok) ∘→ proj₁ ∘→ inv-whnf-unitrec

whnfRed : (d : Γ ⊢ A ⇒ B) (w : Whnf A) → ⊥
whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : (d : Γ ⊢ t ⇒* u ∷ A) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id _)  _ = PE.refl
whnfRed*Term (d ⇨ _) w = ⊥-elim (whnfRedTerm d w)

whnfRed* : (d : Γ ⊢ A ⇒* B) (w : Whnf A) → A PE.≡ B
whnfRed* (id x) w = PE.refl
whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

opaque

  -- Single-step reduction is deterministic.

  whrDetTerm : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒ u′ ∷ A′ → u PE.≡ u′
  whrDetTerm = λ where
    (conv d _) d′ →
      whrDetTerm d d′
    (app-subst d _) d′ →
      case inv-⇒-∘ d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (_∘⟨ _ ⟩ _) (whrDetTerm d d′)
        (inj₂ (_ , PE.refl , _)) → ⊥-elim (whnfRedTerm d lamₙ)
    (β-red _ _ _ _ _ _) d′ →
      case inv-⇒-∘ d′ of λ where
        (inj₁ (_ , _ , d′ , _))        → ⊥-elim (whnfRedTerm d′ lamₙ)
        (inj₂ (_ , PE.refl , PE.refl)) → PE.refl
    (fst-subst _ _ d) d′ →
      case inv-⇒-fst d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (fst _) (whrDetTerm d d′)
        (inj₂ (_ , _ , PE.refl , _)) → ⊥-elim (whnfRedTerm d prodₙ)
    (Σ-β₁ _ _ _ _ _ _) d′ →
      case inv-⇒-fst d′ of λ where
        (inj₁ (_ , _ , d′ , _)) →
          ⊥-elim (whnfRedTerm d′ prodₙ)
        (inj₂ (_ , _ , PE.refl , PE.refl)) → PE.refl
    (snd-subst _ _ d) d′ →
      case inv-⇒-snd d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (snd _) (whrDetTerm d d′)
        (inj₂ (_ , _ , PE.refl , _)) → ⊥-elim (whnfRedTerm d prodₙ)
    (Σ-β₂ _ _ _ _ _ _) d′ →
      case inv-⇒-snd d′ of λ where
        (inj₁ (_ , _ , d′ , _)) →
          ⊥-elim (whnfRedTerm d′ prodₙ)
        (inj₂ (_ , _ , PE.refl , PE.refl)) → PE.refl
    (prodrec-subst x x₁ x₂ x₃ d x₄) d′ →
      case inv-⇒-prodrec d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (λ t → prodrec _ _ _ _ t _) (whrDetTerm d d′)
        (inj₂ (_ , _ , PE.refl , _)) → ⊥-elim (whnfRedTerm d prodₙ)
    (prodrec-β _ _ _ _ _ _ _ _) d′ →
      case inv-⇒-prodrec d′ of λ where
        (inj₁ (_ , _ , d′ , _)) →
          ⊥-elim (whnfRedTerm d′ prodₙ)
        (inj₂ (_ , _ , PE.refl , PE.refl)) → PE.refl
    (natrec-subst _ _ _ d) d′ →
      case inv-⇒-natrec d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (natrec _ _ _ _ _ _) (whrDetTerm d d′)
        (inj₂ (inj₁ (PE.refl , _))) → ⊥-elim (whnfRedTerm d zeroₙ)
        (inj₂ (inj₂ (_ , PE.refl , _))) → ⊥-elim (whnfRedTerm d sucₙ)
    (natrec-zero _ _ _) d′ →
      case inv-⇒-natrec d′ of λ where
        (inj₁ (_ , _ , d′ , _))     → ⊥-elim (whnfRedTerm d′ zeroₙ)
        (inj₂ (inj₁ (_ , PE.refl))) → PE.refl
        (inj₂ (inj₂ (_ , () , _)))
    (natrec-suc _ _ _ _) d′ →
      case inv-⇒-natrec d′ of λ where
        (inj₁ (_ , _ , d′ , _)) →
          ⊥-elim (whnfRedTerm d′ sucₙ)
        (inj₂ (inj₁ (() , _)))
        (inj₂ (inj₂ (_ , PE.refl , PE.refl))) → PE.refl
    (emptyrec-subst _ d) d′ →
      case inv-⇒-emptyrec d′ of λ where
        (_ , _ , d′ , PE.refl) →
          PE.cong (emptyrec _ _) (whrDetTerm d d′)
    (unitrec-subst _ _ _ d _ no-η) d′ →
      case inv-⇒-unitrec d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl , _)) →
          PE.cong (λ t → unitrec _ _ _ _ t _) (whrDetTerm d d′)
        (inj₂ (inj₁ (PE.refl , _))) → ⊥-elim (whnfRedTerm d starₙ)
        (inj₂ (inj₂ (_ , η)))       → ⊥-elim (no-η η)
    (unitrec-β _ _ _ _ no-η) d′ →
      case inv-⇒-unitrec d′ of λ where
        (inj₁ (_ , _ , d′ , _))         → ⊥-elim (whnfRedTerm d′ starₙ)
        (inj₂ (inj₁ (_ , PE.refl , _))) → PE.refl
        (inj₂ (inj₂ (_ , η)))           → ⊥-elim (no-η η)
    (unitrec-β-η _ _ _ _ _ η) d′ →
      case inv-⇒-unitrec d′ of λ where
        (inj₁ (_ , _ , _ , _ , no-η)) → ⊥-elim (no-η η)
        (inj₂ (inj₁ (_ , _ , no-η)))  → ⊥-elim (no-η η)
        (inj₂ (inj₂ (PE.refl , _)))   → PE.refl
    (J-subst _ _ _ _ _ d) d′ →
      case inv-⇒-J d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (J _ _ _ _ _ _ _) (whrDetTerm d d′)
        (inj₂ (PE.refl , _)) → ⊥-elim (whnfRedTerm d rflₙ)
    (J-β _ _ _ _ _ _ _) d′ →
      case inv-⇒-J d′ of λ where
        (inj₁ (_ , _ , d′ , _)) → ⊥-elim (whnfRedTerm d′ rflₙ)
        (inj₂ (_ , PE.refl))    → PE.refl
    (K-subst _ _ _ _ d _) d′ →
      case inv-⇒-K d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (K _ _ _ _ _) (whrDetTerm d d′)
        (inj₂ (PE.refl , _)) → ⊥-elim (whnfRedTerm d rflₙ)
    (K-β _ _ _ _) d′ →
      case inv-⇒-K d′ of λ where
        (inj₁ (_ , _ , d′ , _)) → ⊥-elim (whnfRedTerm d′ rflₙ)
        (inj₂ (_ , PE.refl))    → PE.refl
    ([]-cong-subst _ _ _ d _) d′ →
      case inv-⇒-[]-cong d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong ([]-cong _ _ _ _) (whrDetTerm d d′)
        (inj₂ (PE.refl , _)) → ⊥-elim (whnfRedTerm d rflₙ)
    ([]-cong-β _ _ _ _ _) d′ →
      case inv-⇒-[]-cong d′ of λ where
        (inj₁ (_ , _ , d′ , _)) → ⊥-elim (whnfRedTerm d′ rflₙ)
        (inj₂ (_ , PE.refl))    → PE.refl

whrDet : (d : Γ ⊢ A ⇒ B) (d′ : Γ ⊢ A ⇒ B′) → B PE.≡ B′
whrDet (univ x) (univ x₁) = whrDetTerm x x₁

opaque

  -- If A reduces to the WHNF B, and A also reduces to C, then C
  -- reduces to B.

  whrDet↘ : Γ ⊢ A ↘ B → Γ ⊢ A ⇒* C → Γ ⊢ C ⇒* B
  whrDet↘ (A⇒*B , _)      (id _)    = A⇒*B
  whrDet↘ (id _ , A-whnf) (A⇒D ⇨ _) =
    ⊥-elim (whnfRed A⇒D A-whnf)
  whrDet↘ (A⇒D ⇨ D⇒*B , B-whnf) (A⇒E ⇨ E⇒*C) =
    whrDet↘ (PE.subst (_ ⊢_⇒* _) (whrDet A⇒D A⇒E) D⇒*B , B-whnf) E⇒*C

opaque

  -- A variant of whrDet↘.

  whrDet:⇒*: : Whnf B → Γ ⊢ A :⇒*: B → Γ ⊢ A :⇒*: C → Γ ⊢ C :⇒*: B
  whrDet:⇒*: B-whnf [ _ , ⊢B , A⇒*B ] [ _ , ⊢C , A⇒*C ] =
    [ ⊢C , ⊢B , whrDet↘ (A⇒*B , B-whnf) A⇒*C ]

whrDet↘Term : (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ⇒* u′ ∷ A) → Γ ⊢ u′ ⇒* u ∷ A
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

opaque

  -- A variant of whrDet↘Term.

  whrDet:⇒*:Term :
    Whnf u → Γ ⊢ t :⇒*: u ∷ A → Γ ⊢ t :⇒*: v ∷ A → Γ ⊢ v :⇒*: u ∷ A
  whrDet:⇒*:Term u-whnf [ _ , ⊢u , t⇒*u ] [ _ , ⊢v , t⇒*v ] =
    [ ⊢v , ⊢u , whrDet↘Term (t⇒*u , u-whnf) t⇒*v ]

whrDet*Term : (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ↘ u′ ∷ A′) → u PE.≡ u′
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : (d : Γ ⊢ A ↘ B) (d′ : Γ ⊢ A ↘ B′) → B PE.≡ B′
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
  whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _)
                                     (whrDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , whnfB′))

-- Reduction does not include η-expansion (for WHNFs) for unit types
-- with (or without) η-equality: if a WHNF t reduces to star s l (at
-- type Unit s l), then t is equal to star s l.

no-η-expansion-Unit :
  Whnf t → Γ ⊢ t ⇒* star s l ∷ Unit s l → t PE.≡ star s l
no-η-expansion-Unit = flip whnfRed*Term

-- Reduction does not include η-expansion for strong Σ-types (for
-- WHNFs): if a WHNF t reduces to prodˢ p u v (at type
-- Σˢ p′ , q ▷ A ▹ B), then t is equal to prodˢ p u v.

no-η-expansion-Σˢ :
  Whnf t →
  Γ ⊢ t ⇒* prodˢ p u v ∷ Σˢ p′ , q ▷ A ▹ B →
  t PE.≡ prodˢ p u v
no-η-expansion-Σˢ = flip whnfRed*Term

-- Identity of syntactic reduction

idRed:*: : Γ ⊢ A → Γ ⊢ A :⇒*: A
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : Γ ⊢ t ∷ A → Γ ⊢ t :⇒*: t ∷ A
idRedTerm:*: t = [ t , t , id t ]
-}

open import Tools.PropositionalEquality

open import Definition.Typed.Properties.Admissible.Bool R public
open import Definition.Typed.Properties.Admissible.Empty R public
open import Definition.Typed.Properties.Admissible.Equality R public
open import Definition.Typed.Properties.Admissible.Erased R public
open import Definition.Typed.Properties.Admissible.Identity R public
open import Definition.Typed.Properties.Admissible.Lift R public
open import Definition.Typed.Properties.Admissible.Nat R public
open import Definition.Typed.Properties.Admissible.Pi R public
open import Definition.Typed.Properties.Admissible.Sigma R public
open import Definition.Typed.Properties.Admissible.Unit R public
open import Definition.Typed.Properties.Admissible.Var R public
open import Definition.Typed.Properties.Reduction R public
open import Definition.Typed.Properties.Well-formed R public

private variable
  x   : Fin _
  Γ   : Con Term _
  A B : Term _

------------------------------------------------------------------------
-- A lemma related to _∷_∈_

opaque

  -- If x ∷ A ∈ Γ and x ∷ B ∈ Γ both hold, then A is equal to B.

  det∈ : x ∷ A ∈ Γ → x ∷ B ∈ Γ → A ≡ B
  det∈ here      here      = refl
  det∈ (there x) (there y) = cong wk1 (det∈ x y)
