------------------------------------------------------------------------
-- Some lemmas related to the reduction relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Reduction
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Equality R
import Definition.Typed.Properties.Admissible.Erased.Primitive R as EP
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Term.Primitive R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  Γ                               : Con Term _
  A A′ B B′ C l t t′ u u′ v v₁ v₂ w : Term _
  s                               : Strength
  p p′ q r                        : M

------------------------------------------------------------------------
-- Inversion lemmas related to _⊢_⇒_∷_

opaque

  -- An inversion lemma related to lower.

  inv-⇒-lower :
    Γ ⊢ lower t ⇒ u ∷ A →
    (∃₂ λ t′ B → Γ ⊢ t ⇒ t′ ∷ B × u PE.≡ lower t′) ⊎
    (∃ λ t′ → t PE.≡ lift t′ × u PE.≡ t′)
  inv-⇒-lower (conv d _)      = inv-⇒-lower d
  inv-⇒-lower (lower-subst x) = inj₁ (_ , _ , x , PE.refl)
  inv-⇒-lower (Lift-β x₁ x₂)  = inj₂ (_ , PE.refl , PE.refl)

  -- An inversion lemma related to _∘⟨_⟩_.

  inv-⇒-∘ :
    Γ ⊢ t ∘⟨ p ⟩ u ⇒ v ∷ A →
    (∃₂ λ t′ B → Γ ⊢ t ⇒ t′ ∷ B × v PE.≡ t′ ∘⟨ p ⟩ u) ⊎
    (∃ λ t′ → t PE.≡ lam p t′ × v PE.≡ t′ [ u ]₀)
  inv-⇒-∘ (conv d _)              = inv-⇒-∘ d
  inv-⇒-∘ (app-subst d _)         = inj₁ (_ , _ , d , PE.refl)
  inv-⇒-∘ (β-red _ _ _ PE.refl _) = inj₂ (_ , PE.refl , PE.refl)

  -- An inversion lemma related to fst.

  inv-⇒-fst :
    Γ ⊢ fst p t ⇒ u ∷ A →
    (∃₂ λ t′ B → Γ ⊢ t ⇒ t′ ∷ B × u PE.≡ fst p t′) ⊎
    (∃₂ λ t′ t″ → t PE.≡ prodˢ p t′ t″ × u PE.≡ t′)
  inv-⇒-fst (conv d _)             = inv-⇒-fst d
  inv-⇒-fst (fst-subst _ d)        = inj₁ (_ , _ , d , PE.refl)
  inv-⇒-fst (Σ-β₁ _ _ _ PE.refl _) = inj₂ (_ , _ , PE.refl , PE.refl)

  -- An inversion lemma related to snd.

  inv-⇒-snd :
    Γ ⊢ snd p t ⇒ u ∷ A →
    (∃₂ λ t′ B → Γ ⊢ t ⇒ t′ ∷ B × u PE.≡ snd p t′) ⊎
    (∃₂ λ t′ t″ → t PE.≡ prodˢ p t′ t″ × u PE.≡ t″)
  inv-⇒-snd (conv d _)             = inv-⇒-snd d
  inv-⇒-snd (snd-subst _ d)        = inj₁ (_ , _ , d , PE.refl)
  inv-⇒-snd (Σ-β₂ _ _ _ PE.refl _) = inj₂ (_ , _ , PE.refl , PE.refl)

  -- An inversion lemma related to prodrec.

  inv-⇒-prodrec :
    Γ ⊢ prodrec r p q A t u ⇒ v ∷ B →
    (∃₂ λ t′ C → Γ ⊢ t ⇒ t′ ∷ C × v PE.≡ prodrec r p q A t′ u) ⊎
    (∃₂ λ t′ t″ → t PE.≡ prodʷ p t′ t″ × v PE.≡ u [ t′ , t″ ]₁₀)
  inv-⇒-prodrec (conv d _) =
    inv-⇒-prodrec d
  inv-⇒-prodrec (prodrec-subst _ _ d _) =
    inj₁ (_ , _ , d , PE.refl)
  inv-⇒-prodrec (prodrec-β _ _ _ _ PE.refl _) =
    inj₂ (_ , _ , PE.refl , PE.refl)

  -- An inversion lemma related to natrec.

  inv-⇒-natrec :
    Γ ⊢ natrec p q r A t u v ⇒ w ∷ B →
    (∃₂ λ v′ C → Γ ⊢ v ⇒ v′ ∷ C × w PE.≡ natrec p q r A t u v′) ⊎
    v PE.≡ zero × w PE.≡ t ⊎
    (∃ λ v′ → v PE.≡ suc v′ × w PE.≡ u [ v′ , natrec p q r A t u v′ ]₁₀)
  inv-⇒-natrec (conv d _) =
    inv-⇒-natrec d
  inv-⇒-natrec (natrec-subst _ _ d) =
    inj₁ (_ , _ , d , PE.refl)
  inv-⇒-natrec (natrec-zero _ _) =
    inj₂ (inj₁ (PE.refl , PE.refl))
  inv-⇒-natrec (natrec-suc _ _ _) =
    inj₂ (inj₂ (_ , PE.refl , PE.refl))

  -- An inversion lemma related to emptyrec.

  inv-⇒-emptyrec :
    Γ ⊢ emptyrec p A t ⇒ u ∷ B →
    (∃₂ λ t′ C → Γ ⊢ t ⇒ t′ ∷ C × u PE.≡ emptyrec p A t′)
  inv-⇒-emptyrec (conv d _) =
    inv-⇒-emptyrec d
  inv-⇒-emptyrec (emptyrec-subst _ d) =
    _ , _ , d , PE.refl

  -- An inversion lemma related to unitrec.

  inv-⇒-unitrec :
    Γ ⊢ unitrec p q A t u ⇒ v ∷ B →
    (∃₂ λ t′ C → Γ ⊢ t ⇒ t′ ∷ C × v PE.≡ unitrec p q A t′ u ×
     ¬ Unitʷ-η) ⊎
    (t PE.≡ starʷ × v PE.≡ u × ¬ Unitʷ-η) ⊎
    v PE.≡ u × Unitʷ-η
  inv-⇒-unitrec (conv d _) =
    inv-⇒-unitrec d
  inv-⇒-unitrec (unitrec-subst _ _ d _ no-η) =
    inj₁ (_ , _ , d , PE.refl , no-η)
  inv-⇒-unitrec (unitrec-β _ _ _ no-η) =
    inj₂ (inj₁ (PE.refl , PE.refl , no-η))
  inv-⇒-unitrec (unitrec-β-η _ _ _ _ η) =
    inj₂ (inj₂ (PE.refl , η))

  -- An inversion lemma related to J.

  inv-⇒-J :
    Γ ⊢ J p q A t B u v w ⇒ t′ ∷ C →
    (∃₂ λ w′ D → Γ ⊢ w ⇒ w′ ∷ D × t′ PE.≡ J p q A t B u v w′) ⊎
    w PE.≡ rfl × t′ PE.≡ u
  inv-⇒-J (conv d _) =
    inv-⇒-J d
  inv-⇒-J (J-subst _ _ _ _ d) =
    inj₁ (_ , _ , d , PE.refl)
  inv-⇒-J (J-β _ _ _ _ _ _) =
    inj₂ (PE.refl , PE.refl)

  -- An inversion lemma related to K.

  inv-⇒-K :
    Γ ⊢ K p A t B u v ⇒ w ∷ C →
    (∃₂ λ v′ D → Γ ⊢ v ⇒ v′ ∷ D × w PE.≡ K p A t B u v′) ⊎
    v PE.≡ rfl × w PE.≡ u
  inv-⇒-K (conv d _) =
    inv-⇒-K d
  inv-⇒-K (K-subst _ _ d _) =
    inj₁ (_ , _ , d , PE.refl)
  inv-⇒-K (K-β _ _ _) =
    inj₂ (PE.refl , PE.refl)

  -- An inversion lemma related to []-cong.

  inv-⇒-[]-cong :
    Γ ⊢ []-cong s l A t u v ⇒ w ∷ C →
    (∃₂ λ v′ D → Γ ⊢ v ⇒ v′ ∷ D × w PE.≡ []-cong s l A t u v′) ⊎
    v PE.≡ rfl × w PE.≡ rfl
  inv-⇒-[]-cong (conv d _) =
    inv-⇒-[]-cong d
  inv-⇒-[]-cong ([]-cong-subst _ _ _ d _) =
    inj₁ (_ , _ , d , PE.refl)
  inv-⇒-[]-cong ([]-cong-β _ _ _ _ _) =
    inj₂ (PE.refl , PE.refl)

  -- An inversion lemma related to sucᵘ.

  ¬sucᵘ⇒ : ¬ Γ ⊢ sucᵘ t ⇒ u ∷ A
  ¬sucᵘ⇒ (conv d _) = ¬sucᵘ⇒ d

------------------------------------------------------------------------
-- The reduction relations are contained in the equality relations

opaque

  -- The reduction relation _⊢_⇒_∷_ is contained in the conversion
  -- relation _⊢_≡_∷_.

  subsetTerm : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
  subsetTerm (supᵘ-zeroˡ ⊢l) = supᵘ-zeroˡ ⊢l
  subsetTerm (supᵘ-zeroʳ ⊢l) =
    supᵘ-zeroʳⱼ (inversion-Level-⊢ (wf-⊢∷ ⊢l)) (sucᵘⱼ ⊢l)
  subsetTerm (supᵘ-sucᵘ ⊢l₁ ⊢l₂) = supᵘ-sucᵘ ⊢l₁ ⊢l₂
  subsetTerm (supᵘ-substˡ t⇒t′ ⊢u) = supᵘ-cong (subsetTerm t⇒t′) (refl ⊢u)
  subsetTerm (supᵘ-substʳ ⊢t u⇒u′) = supᵘ-cong (refl (sucᵘⱼ ⊢t)) (subsetTerm u⇒u′)
  subsetTerm (lower-subst x) = lower-cong (subsetTerm x)
  subsetTerm (Lift-β ⊢A x₁) = Lift-β ⊢A x₁
  subsetTerm (natrec-subst z s n⇒n′) =
    natrec-cong (refl (⊢∙→⊢ (wfTerm s))) (refl z) (refl s)
      (subsetTerm n⇒n′)
  subsetTerm (natrec-zero z s) = natrec-zero z s
  subsetTerm (natrec-suc z s n) = natrec-suc z s n
  subsetTerm (emptyrec-subst A n⇒n′) =
    emptyrec-cong (refl A) (subsetTerm n⇒n′)
  subsetTerm (app-subst t⇒u a) =
    app-cong (subsetTerm t⇒u) (refl a)
  subsetTerm (β-red B t a p≡p′ ok) = β-red B t a p≡p′ ok
  subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
  subsetTerm (fst-subst G x) = fst-cong G (subsetTerm x)
  subsetTerm (snd-subst G x) = snd-cong G (subsetTerm x)
  subsetTerm (prodrec-subst A u t⇒t′ ok) =
    prodrec-cong (refl A) (subsetTerm t⇒t′) (refl u) ok
  subsetTerm (prodrec-β A t t′ u eq ok) =
    prodrec-β A t t′ u eq ok
  subsetTerm (Σ-β₁ G x x₁ x₂ ok) = Σ-β₁ G x x₁ x₂ ok
  subsetTerm (Σ-β₂ G x x₁ x₂ ok) = Σ-β₂ G x x₁ x₂ ok
  subsetTerm (J-subst ⊢t ⊢B ⊢u ⊢t′ v⇒v′) =
    J-cong (refl (⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B))))) ⊢t (refl ⊢t) (refl ⊢B)
      (refl ⊢u) (refl ⊢t′) (subsetTerm v⇒v′)
  subsetTerm (K-subst ⊢B ⊢u v⇒v′ ok) =
    let (⊢A , _) , (⊢t , _) , _ = inversion-Id-⊢ (⊢∙→⊢ (wf ⊢B)) in
    K-cong (refl ⊢A) (refl ⊢t) (refl ⊢B) (refl ⊢u) (subsetTerm v⇒v′) ok
  subsetTerm ([]-cong-subst ⊢A ⊢t ⊢u v⇒v′ ok) =
    []-cong-cong (refl-⊢≡∷L (inversion-U-Level (wf-⊢∷ ⊢A)))
      (refl ⊢A) (refl ⊢t) (refl ⊢u) (subsetTerm v⇒v′) ok
  subsetTerm (J-β {t} {A} {t′} {B} {u} {p} {q} ⊢t _ t≡t′ ⊢B _ ⊢u) =
    J p q A t B u t′ rfl  ≡⟨ sym′ $
                             J-cong (refl (⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B)))))
                               ⊢t (refl ⊢t) (refl ⊢B) (refl ⊢u) t≡t′ (refl (rflⱼ ⊢t)) ⟩⊢
    J p q A t B u t rfl   ≡⟨ J-β ⊢t ⊢B ⊢u PE.refl ⟩⊢∎
    u                     ∎
  subsetTerm (K-β ⊢B ⊢u ok) =
    K-β ⊢B ⊢u ok
  subsetTerm ([]-cong-β ⊢A ⊢t ⊢t′ t≡t′ ok) =
    let ⊢l = inversion-U-Level (wf-⊢∷ ⊢A) in
    trans
      ([]-cong-cong (refl-⊢≡∷L ⊢l) (refl ⊢A) (refl ⊢t) (sym′ t≡t′)
         (_⊢_≡_∷_.conv (refl (rflⱼ ⊢t)) $
          Id-cong (refl (univ ⊢A)) (refl ⊢t) t≡t′)
         ok)
      (conv ([]-cong-β ⊢l ⊢A ⊢t PE.refl ok)
         (Id-cong (refl (Erasedⱼ ⊢l ⊢A)) (refl ([]ⱼ ⊢l ⊢A ⊢t))
            ([]-cong′ ⊢l ⊢A ⊢t ⊢t′ t≡t′)))
    where
    open EP ([]-cong→Erased ok)
  subsetTerm (unitrec-subst A u t⇒t′ ok no-η) =
    unitrec-cong (refl A) (subsetTerm t⇒t′) (refl u) ok no-η
  subsetTerm (unitrec-β A u ok₁ ok₂) =
    unitrec-β A u ok₁ ok₂
  subsetTerm (unitrec-β-η A t u ok₁ ok₂) =
    unitrec-β-η A t u ok₁ ok₂

opaque

  -- The reduction relation _⊢_⇒_ is contained in the conversion
  -- relation _⊢_≡_.

  subset : Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
  subset (univ A⇒B) = univ (subsetTerm A⇒B)

opaque

  -- The reduction relation _⊢_⇒*_∷_ is contained in the conversion
  -- relation _⊢_≡_∷_.

  subset*Term : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
  subset*Term (id t) = refl t
  subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

opaque

  -- The reduction relation _⊢_⇒*_ is contained in the conversion
  -- relation _⊢_≡_.

  subset* : Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
  subset* (id A) = refl A
  subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)

------------------------------------------------------------------------
-- The single-step reduction relations are contained in the multi-step
-- relations

opaque

  -- If t reduces in one step to u, then t reduces in zero or more
  -- steps to u.

  redMany : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
  redMany t⇒u =
    let _ , _ , ⊢u = wf-⊢≡∷ (subsetTerm t⇒u) in
    t⇒u ⇨ id ⊢u

opaque

  -- If A reduces in one step to B, then A reduces in zero or more
  -- steps to B.

  redMany-⊢ : Γ ⊢ A ⇒ B → Γ ⊢ A ⇒* B
  redMany-⊢ A⇒B =
    let _ , ⊢B = wf-⊢≡ (subset A⇒B) in
    A⇒B ⇨ id ⊢B

------------------------------------------------------------------------
-- If something reduces, then it is well-formed/well-typed

opaque

  -- If t reduces to u, then t is well-typed.

  redFirstTerm : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A
  redFirstTerm = proj₁ ∘→ proj₂ ∘→ wf-⊢≡∷ ∘→ subsetTerm

opaque

  -- If A reduces to B, then A is well-formed.

  redFirst : Γ ⊢ A ⇒ B → Γ ⊢ A
  redFirst = proj₁ ∘→ wf-⊢≡ ∘→ subset

opaque

  -- If t reduces to u, then t is well-typed.

  redFirst*Term : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
  redFirst*Term = proj₁ ∘→ proj₂ ∘→ wf-⊢≡∷ ∘→ subset*Term

opaque

  -- If A reduces to B, then A is well-formed.

  redFirst* : Γ ⊢ A ⇒* B → Γ ⊢ A
  redFirst* = proj₁ ∘→ wf-⊢≡ ∘→ subset*

------------------------------------------------------------------------
-- Expansion and reduction lemmas

opaque

  -- An expansion lemma for ⊢_≡_.

  reduction : Γ ⊢ A ⇒* A′ → Γ ⊢ B ⇒* B′ → Γ ⊢ A′ ≡ B′ → Γ ⊢ A ≡ B
  reduction D D′ A′≡B′ =
    trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

opaque

  -- A reduction lemma for ⊢_≡_.

  reduction′ : Γ ⊢ A ⇒* A′ → Γ ⊢ B ⇒* B′ → Γ ⊢ A ≡ B → Γ ⊢ A′ ≡ B′
  reduction′ D D′ A≡B =
    trans (sym (subset* D)) (trans A≡B (subset* D′))

opaque

  -- An expansion lemma for ⊢_≡_∷_.

  reductionₜ :
    Γ ⊢ A ⇒* B →
    Γ ⊢ t ⇒* t′ ∷ B →
    Γ ⊢ u ⇒* u′ ∷ B →
    Γ ⊢ t′ ≡ u′ ∷ B →
    Γ ⊢ t ≡ u ∷ A
  reductionₜ D d d′ t′≡u′ =
    conv
      (trans (subset*Term d)
         (trans t′≡u′ (sym′ (subset*Term d′))))
      (sym (subset* D))

opaque

  -- A reduction lemma for ⊢_≡_∷_.

  reductionₜ′ :
    Γ ⊢ A ⇒* B →
    Γ ⊢ t ⇒* t′ ∷ B →
    Γ ⊢ u ⇒* u′ ∷ B →
    Γ ⊢ t ≡ u ∷ A →
    Γ ⊢ t′ ≡ u′ ∷ B
  reductionₜ′ D d d′ t≡u =
    trans (sym′ (subset*Term d))
      (trans (conv t≡u (subset* D)) (subset*Term d′))

------------------------------------------------------------------------
-- Some lemmas related to neutral terms

opaque

  -- Neutral terms do not reduce.

  neRedTerm : Γ ⊢ t ⇒ u ∷ A → ¬ Neutral t
  neRedTerm = λ where
    (conv d _)                → neRedTerm d
    (supᵘ-zeroˡ _)            → λ ()
    (supᵘ-zeroʳ _)            → λ ()
    (supᵘ-sucᵘ _ _)           → λ ()
    (supᵘ-substˡ d _)         → λ ()
    (supᵘ-substʳ _ d)         → λ ()
    (lower-subst x)           → neRedTerm x ∘→ inv-ne-lower
    (Lift-β ⊢A x₁)            → (λ ()) ∘→ inv-ne-lower
    (app-subst d _)           → neRedTerm d ∘→ inv-ne-∘
    (β-red _ _ _ _ _)         → (λ ()) ∘→ inv-ne-∘
    (natrec-subst _ _ d)      → neRedTerm d ∘→ inv-ne-natrec
    (natrec-zero _ _)         → (λ ()) ∘→ inv-ne-natrec
    (natrec-suc _ _ _)        → (λ ()) ∘→ inv-ne-natrec
    (emptyrec-subst _ d)      → neRedTerm d ∘→ inv-ne-emptyrec
    (fst-subst _ d)           → neRedTerm d ∘→ inv-ne-fst
    (snd-subst _ d)           → neRedTerm d ∘→ inv-ne-snd
    (prodrec-subst _ _ d _)   → neRedTerm d ∘→ inv-ne-prodrec
    (prodrec-β _ _ _ _ _ _)   → (λ ()) ∘→ inv-ne-prodrec
    (Σ-β₁ _ _ _ _ _)          → (λ ()) ∘→ inv-ne-fst
    (Σ-β₂ _ _ _ _ _)          → (λ ()) ∘→ inv-ne-snd
    (J-subst _ _ _ _ d)       → neRedTerm d ∘→ inv-ne-J
    (K-subst _ _ d _)         → neRedTerm d ∘→ inv-ne-K
    ([]-cong-subst _ _ _ d _) → neRedTerm d ∘→ inv-ne-[]-cong
    (J-β _ _ _ _ _ _)         → (λ ()) ∘→ inv-ne-J
    (K-β _ _ _)               → (λ ()) ∘→ inv-ne-K
    ([]-cong-β _ _ _ _ _)     → (λ ()) ∘→ inv-ne-[]-cong
    (unitrec-subst _ _ d _ _) → neRedTerm d ∘→ proj₂ ∘→ inv-ne-unitrec
    (unitrec-β _ _ _ _)       → (λ ()) ∘→ proj₂ ∘→ inv-ne-unitrec
    (unitrec-β-η _ _ _ _ ok)  → (_$ ok) ∘→ proj₁ ∘→ inv-ne-unitrec

opaque

  -- Neutral types do not reduce.

  neRed : Γ ⊢ A ⇒ B → ¬ Neutral A
  neRed (univ x) N = neRedTerm x N

------------------------------------------------------------------------
-- Some lemmas related to neutral levels

opaque

  -- Neutral levels do not reduce.

  neˡRedTerm : Γ ⊢ t ⇒ u ∷ A → ¬ Neutralˡ t
  neˡRedTerm (conv d _) n = neˡRedTerm d n
  neˡRedTerm (supᵘ-substˡ d _) (supᵘˡₙ n) = neˡRedTerm d n
  neˡRedTerm (supᵘ-zeroˡ _) (supᵘˡₙ (ne ()))
  neˡRedTerm (supᵘ-substʳ x x₁) (supᵘˡₙ (ne ()))
  neˡRedTerm (supᵘ-zeroʳ x) (supᵘˡₙ (ne ()))
  neˡRedTerm (supᵘ-sucᵘ x x₁) (supᵘˡₙ (ne ()))
  neˡRedTerm (supᵘ-substˡ d _) (supᵘʳₙ _) = ¬sucᵘ⇒ d
  neˡRedTerm (supᵘ-substʳ _ d) (supᵘʳₙ n) = neˡRedTerm d n
  neˡRedTerm (supᵘ-zeroʳ _) (supᵘʳₙ (ne ()))
  neˡRedTerm (supᵘ-sucᵘ _ _) (supᵘʳₙ (ne ()))
  neˡRedTerm d (ne n) = neRedTerm d n

------------------------------------------------------------------------
-- Some lemmas related to WHNFs

opaque

  -- WHNFs do not reduce.

  whnfRedTerm : Γ ⊢ t ⇒ u ∷ A → ¬ Whnf t
  whnfRedTerm = λ where
    (conv d _)                → whnfRedTerm d
    (supᵘ-zeroˡ _)            → λ { (ne (supᵘˡₙ (ne ()))); (ne! ()) }
    (supᵘ-zeroʳ _)            → λ { (ne (supᵘˡₙ (ne ()))); (ne (supᵘʳₙ (ne ()))); (ne! ()) }
    (supᵘ-sucᵘ _ _)           → λ { (ne (supᵘˡₙ (ne ()))); (ne (supᵘʳₙ (ne ()))); (ne! ()) }
    (supᵘ-substˡ d _)         → λ { (ne (supᵘˡₙ n)) → neˡRedTerm d n; (ne (supᵘʳₙ n)) → ¬sucᵘ⇒ d; (ne! ()) }
    (supᵘ-substʳ _ d)         → λ { (ne (supᵘˡₙ (ne ()))); (ne (supᵘʳₙ n)) → neˡRedTerm d n; (ne! ()) }
    (lower-subst x)           → neRedTerm x ∘→ inv-whnf-lower
    (Lift-β _ _)              → (λ ()) ∘→ inv-whnf-lower
    (app-subst d _)           → neRedTerm d ∘→ inv-whnf-∘
    (β-red _ _ _ _ _)         → (λ ()) ∘→ inv-whnf-∘
    (natrec-subst _ _ d)      → neRedTerm d ∘→ inv-whnf-natrec
    (natrec-zero _ _)         → (λ ()) ∘→ inv-whnf-natrec
    (natrec-suc _ _ _)        → (λ ()) ∘→ inv-whnf-natrec
    (emptyrec-subst _ d)      → neRedTerm d ∘→ inv-whnf-emptyrec
    (fst-subst _ d)           → neRedTerm d ∘→ inv-whnf-fst
    (snd-subst _ d)           → neRedTerm d ∘→ inv-whnf-snd
    (prodrec-subst _ _ d _)   → neRedTerm d ∘→ inv-whnf-prodrec
    (prodrec-β _ _ _ _ _ _)   → (λ ()) ∘→ inv-whnf-prodrec
    (Σ-β₁ _ _ _ _ _)          → (λ ()) ∘→ inv-whnf-fst
    (Σ-β₂ _ _ _ _ _)          → (λ ()) ∘→ inv-whnf-snd
    (J-subst _ _ _ _ d)       → neRedTerm d ∘→ inv-whnf-J
    (K-subst _ _ d _)         → neRedTerm d ∘→ inv-whnf-K
    ([]-cong-subst _ _ _ d _) → neRedTerm d ∘→ inv-whnf-[]-cong
    (J-β _ _ _ _ _ _)         → (λ ()) ∘→ inv-whnf-J
    (K-β _ _ _)               → (λ ()) ∘→ inv-whnf-K
    ([]-cong-β _ _ _ _ _)     → (λ ()) ∘→ inv-whnf-[]-cong
    (unitrec-subst _ _ d _ _) → neRedTerm d ∘→ proj₂ ∘→
                                inv-whnf-unitrec
    (unitrec-β _ _ _ _)       → (λ ()) ∘→ proj₂ ∘→ inv-whnf-unitrec
    (unitrec-β-η _ _ _ _ ok)  → (_$ ok) ∘→ proj₁ ∘→ inv-whnf-unitrec

opaque

  -- WHNFs do not reduce.

  whnfRed : Γ ⊢ A ⇒ B → ¬ Whnf A
  whnfRed (univ x) w = whnfRedTerm x w

opaque

  -- If a WHNF t reduces in zero or more steps to u, then t is equal
  -- to u.

  whnfRed*Term : Γ ⊢ t ⇒* u ∷ A → Whnf t → t PE.≡ u
  whnfRed*Term (id _)  _ = PE.refl
  whnfRed*Term (d ⇨ _) w = ⊥-elim (whnfRedTerm d w)

opaque

  -- If a WHNF A reduces in zero or more steps to B, then A is equal
  -- to B.

  whnfRed* : Γ ⊢ A ⇒* B → Whnf A → A PE.≡ B
  whnfRed* (id x)  w = PE.refl
  whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

------------------------------------------------------------------------
-- Reduction is deterministic

opaque

  -- Single-step reduction is deterministic.

  whrDetTerm : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒ u′ ∷ A′ → u PE.≡ u′
  whrDetTerm = λ where
    (conv d _) d′ →
      whrDetTerm d d′
    (supᵘ-zeroˡ _) (supᵘ-zeroˡ _) → PE.refl
    d@(supᵘ-zeroˡ _) (conv d′ _) → whrDetTerm d d′
    (supᵘ-zeroˡ _) (supᵘ-substˡ d _) → ⊥-elim (whnfRedTerm d zeroᵘₙ)
    (supᵘ-zeroʳ _) (supᵘ-zeroʳ _) → PE.refl
    d@(supᵘ-zeroʳ _) (conv d′ _) → whrDetTerm d d′
    (supᵘ-zeroʳ _) (supᵘ-substˡ d _) → ⊥-elim (¬sucᵘ⇒ d)
    (supᵘ-zeroʳ _) (supᵘ-substʳ _ d) → ⊥-elim (whnfRedTerm d zeroᵘₙ)
    (supᵘ-sucᵘ _ _) (supᵘ-sucᵘ _ _) → PE.refl
    d@(supᵘ-sucᵘ _ _) (conv d′ _) → whrDetTerm d d′
    (supᵘ-sucᵘ _ _) (supᵘ-substˡ d _) → ⊥-elim (whnfRedTerm d sucᵘₙ)
    (supᵘ-sucᵘ _ _) (supᵘ-substʳ _ d) → ⊥-elim (whnfRedTerm d sucᵘₙ)
    (supᵘ-substˡ d _) (supᵘ-substˡ d′ _) → PE.cong (_supᵘ _) (whrDetTerm d d′)
    d@(supᵘ-substˡ _ _) (conv d′ _) → whrDetTerm d d′
    (supᵘ-substˡ d _) (supᵘ-zeroˡ _) → ⊥-elim (whnfRedTerm d zeroᵘₙ)
    (supᵘ-substˡ d _) (supᵘ-zeroʳ _) → ⊥-elim (¬sucᵘ⇒ d)
    (supᵘ-substˡ d _) (supᵘ-sucᵘ _ _) → ⊥-elim (whnfRedTerm d sucᵘₙ)
    (supᵘ-substˡ d _) (supᵘ-substʳ _ d′) → ⊥-elim (¬sucᵘ⇒ d)
    (supᵘ-substʳ _ d) (supᵘ-substʳ _ d′) → PE.cong (_ supᵘ_) (whrDetTerm d d′)
    d@(supᵘ-substʳ _ _) (conv d′ _) → whrDetTerm d d′
    (supᵘ-substʳ _ d) (supᵘ-zeroʳ _) → ⊥-elim (whnfRedTerm d zeroᵘₙ)
    (supᵘ-substʳ _ d) (supᵘ-sucᵘ _ _) → ⊥-elim (whnfRedTerm d sucᵘₙ)
    (supᵘ-substʳ _ d) (supᵘ-substˡ d′ _) → ⊥-elim (¬sucᵘ⇒ d′)
    (lower-subst d) d′ →
      case inv-⇒-lower d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) → PE.cong lower (whrDetTerm d d′)
        (inj₂ (_ , PE.refl , PE.refl)) → ⊥-elim (whnfRedTerm d liftₙ)
    (Lift-β x₁ x₂) d′ →
      case inv-⇒-lower d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) → ⊥-elim (whnfRedTerm d′ liftₙ)
        (inj₂ (_ , PE.refl , PE.refl)) → PE.refl
    (app-subst d _) d′ →
      case inv-⇒-∘ d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (_∘⟨ _ ⟩ _) (whrDetTerm d d′)
        (inj₂ (_ , PE.refl , _)) → ⊥-elim (whnfRedTerm d lamₙ)
    (β-red _ _ _ _ _) d′ →
      case inv-⇒-∘ d′ of λ where
        (inj₁ (_ , _ , d′ , _))        → ⊥-elim (whnfRedTerm d′ lamₙ)
        (inj₂ (_ , PE.refl , PE.refl)) → PE.refl
    (fst-subst _ d) d′ →
      case inv-⇒-fst d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (fst _) (whrDetTerm d d′)
        (inj₂ (_ , _ , PE.refl , _)) → ⊥-elim (whnfRedTerm d prodₙ)
    (Σ-β₁ _ _ _ _ _) d′ →
      case inv-⇒-fst d′ of λ where
        (inj₁ (_ , _ , d′ , _)) →
          ⊥-elim (whnfRedTerm d′ prodₙ)
        (inj₂ (_ , _ , PE.refl , PE.refl)) → PE.refl
    (snd-subst _ d) d′ →
      case inv-⇒-snd d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (snd _) (whrDetTerm d d′)
        (inj₂ (_ , _ , PE.refl , _)) → ⊥-elim (whnfRedTerm d prodₙ)
    (Σ-β₂ _ _ _ _ _) d′ →
      case inv-⇒-snd d′ of λ where
        (inj₁ (_ , _ , d′ , _)) →
          ⊥-elim (whnfRedTerm d′ prodₙ)
        (inj₂ (_ , _ , PE.refl , PE.refl)) → PE.refl
    (prodrec-subst _ _ d _) d′ →
      case inv-⇒-prodrec d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (λ t → prodrec _ _ _ _ t _) (whrDetTerm d d′)
        (inj₂ (_ , _ , PE.refl , _)) → ⊥-elim (whnfRedTerm d prodₙ)
    (prodrec-β _ _ _ _ _ _) d′ →
      case inv-⇒-prodrec d′ of λ where
        (inj₁ (_ , _ , d′ , _)) →
          ⊥-elim (whnfRedTerm d′ prodₙ)
        (inj₂ (_ , _ , PE.refl , PE.refl)) → PE.refl
    (natrec-subst _ _ d) d′ →
      case inv-⇒-natrec d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (natrec _ _ _ _ _ _) (whrDetTerm d d′)
        (inj₂ (inj₁ (PE.refl , _))) → ⊥-elim (whnfRedTerm d zeroₙ)
        (inj₂ (inj₂ (_ , PE.refl , _))) → ⊥-elim (whnfRedTerm d sucₙ)
    (natrec-zero _ _) d′ →
      case inv-⇒-natrec d′ of λ where
        (inj₁ (_ , _ , d′ , _))     → ⊥-elim (whnfRedTerm d′ zeroₙ)
        (inj₂ (inj₁ (_ , PE.refl))) → PE.refl
        (inj₂ (inj₂ (_ , () , _)))
    (natrec-suc _ _ _) d′ →
      case inv-⇒-natrec d′ of λ where
        (inj₁ (_ , _ , d′ , _)) →
          ⊥-elim (whnfRedTerm d′ sucₙ)
        (inj₂ (inj₁ (() , _)))
        (inj₂ (inj₂ (_ , PE.refl , PE.refl))) → PE.refl
    (emptyrec-subst _ d) d′ →
      case inv-⇒-emptyrec d′ of λ where
        (_ , _ , d′ , PE.refl) →
          PE.cong (emptyrec _ _) (whrDetTerm d d′)
    (unitrec-subst _ _ d _ no-η) d′ →
      case inv-⇒-unitrec d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl , _)) →
          PE.cong (λ t → unitrec _ _ _ t _) (whrDetTerm d d′)
        (inj₂ (inj₁ (PE.refl , PE.refl , _))) → ⊥-elim (whnfRedTerm d starₙ)
        (inj₂ (inj₂ (_ , η)))           → ⊥-elim (no-η η)
    (unitrec-β _ _ _ no-η) d′ →
      case inv-⇒-unitrec d′ of λ where
        (inj₁ (_ , _ , d′ , _))         → ⊥-elim (whnfRedTerm d′ starₙ)
        (inj₂ (inj₁ (_ , PE.refl , _))) → PE.refl
        (inj₂ (inj₂ (_ , η)))           → ⊥-elim (no-η η)
    (unitrec-β-η _ _ _ _ η) d′ →
      case inv-⇒-unitrec d′ of λ where
        (inj₁ (_ , _ , _ , _ , no-η)) → ⊥-elim (no-η η)
        (inj₂ (inj₁ (_ , _ , no-η)))  → ⊥-elim (no-η η)
        (inj₂ (inj₂ (PE.refl , _)))   → PE.refl
    (J-subst _ _ _ _ d) d′ →
      case inv-⇒-J d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (J _ _ _ _ _ _ _) (whrDetTerm d d′)
        (inj₂ (PE.refl , _)) → ⊥-elim (whnfRedTerm d rflₙ)
    (J-β _ _ _ _ _ _) d′ →
      case inv-⇒-J d′ of λ where
        (inj₁ (_ , _ , d′ , _)) → ⊥-elim (whnfRedTerm d′ rflₙ)
        (inj₂ (_ , PE.refl))    → PE.refl
    (K-subst _ _ d _) d′ →
      case inv-⇒-K d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong (K _ _ _ _ _) (whrDetTerm d d′)
        (inj₂ (PE.refl , _)) → ⊥-elim (whnfRedTerm d rflₙ)
    (K-β _ _ _) d′ →
      case inv-⇒-K d′ of λ where
        (inj₁ (_ , _ , d′ , _)) → ⊥-elim (whnfRedTerm d′ rflₙ)
        (inj₂ (_ , PE.refl))    → PE.refl
    ([]-cong-subst _ _ _ d _) d′ →
      case inv-⇒-[]-cong d′ of λ where
        (inj₁ (_ , _ , d′ , PE.refl)) →
          PE.cong ([]-cong _ _ _ _ _) (whrDetTerm d d′)
        (inj₂ (PE.refl , _)) → ⊥-elim (whnfRedTerm d rflₙ)
    ([]-cong-β _ _ _ _ _) d′ →
      case inv-⇒-[]-cong d′ of λ where
        (inj₁ (_ , _ , d′ , _)) → ⊥-elim (whnfRedTerm d′ rflₙ)
        (inj₂ (_ , PE.refl))    → PE.refl

opaque

  -- Single-step reduction is deterministic.

  whrDet : Γ ⊢ A ⇒ B → Γ ⊢ A ⇒ B′ → B PE.≡ B′
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

  -- If t reduces to the WHNF u, and t also reduces to v, then v
  -- reduces to u.

  whrDet↘Term : Γ ⊢ t ↘ u ∷ A → Γ ⊢ t ⇒* v ∷ A → Γ ⊢ v ⇒* u ∷ A
  whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
  whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
  whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
    whrDet↘Term
      (PE.subst (_ ⊢_↘ _ ∷ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

opaque

  -- Reduction to WHNF is deterministic.

  whrDet*Term : Γ ⊢ t ↘ u ∷ A → Γ ⊢ t ↘ u′ ∷ A′ → u PE.≡ u′
  whrDet*Term (id x , proj₂) (id x₁ , proj₄) =
    PE.refl
  whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) =
    ⊥-elim (whnfRedTerm x₁ proj₂)
  whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) =
    ⊥-elim (whnfRedTerm x proj₄)
  whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
    whrDet*Term (proj₁ , proj₂)
      (PE.subst (_ ⊢_↘ _ ∷ _) (whrDetTerm x₁ x) (proj₃ , proj₄))

opaque

  -- Reduction to WHNF is deterministic.

  whrDet* : Γ ⊢ A ↘ B → Γ ⊢ A ↘ B′ → B PE.≡ B′
  whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
  whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
  whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
  whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
    whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _)
                                       (whrDet A⇒A″ A⇒A′)
                                       (A″⇒*B′ , whnfB′))

------------------------------------------------------------------------
-- Reduction does not include η-expansion (for WHNFs)

opaque

  -- Reduction does not include η-expansion (for WHNFs) for unit types
  -- with (or without) η-equality: if a WHNF t reduces to star s (at
  -- type Unit s), then t is equal to star s.

  no-η-expansion-Unit :
    Whnf t → Γ ⊢ t ⇒* star s ∷ Unit s → t PE.≡ star s
  no-η-expansion-Unit = flip whnfRed*Term

opaque

  -- Reduction does not include η-expansion for strong Σ-types (for
  -- WHNFs): if a WHNF t reduces to prodˢ p u v (at type
  -- Σˢ p′ , q ▷ A ▹ B), then t is equal to prodˢ p u v.

  no-η-expansion-Σˢ :
    Whnf t →
    Γ ⊢ t ⇒* prodˢ p u v ∷ Σˢ p′ , q ▷ A ▹ B →
    t PE.≡ prodˢ p u v
  no-η-expansion-Σˢ = flip whnfRed*Term

opaque

  -- Reduction does not include η-expansion for lifted types (for
  -- WHNFs): if a WHNF t reduces to lift u (at type Lift l A), then t
  -- is equal to lift u.

  no-η-expansion-Lift :
    Whnf t →
    Γ ⊢ t ⇒* lift u ∷ Lift l A →
    t PE.≡ lift u
  no-η-expansion-Lift = flip whnfRed*Term

------------------------------------------------------------------------
-- Transitivity

opaque

  -- The relation Γ ⊢_⇒*_ is transitive.

  _⇨*_ : Γ ⊢ A ⇒* B → Γ ⊢ B ⇒* C → Γ ⊢ A ⇒* C
  id _          ⇨* B⇒C = B⇒C
  (A⇒A′ ⇨ A′⇒B) ⇨* B⇒C = A⇒A′ ⇨ (A′⇒B ⇨* B⇒C)

opaque

  -- The relation Γ ⊢_⇒*_∷ A is transitive.

  _⇨∷*_ : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒* v ∷ A
  id _          ⇨∷* u⇒v = u⇒v
  (t⇒t′ ⇨ t′⇒u) ⇨∷* u⇒v = t⇒t′ ⇨ (t′⇒u ⇨∷* u⇒v)

opaque

  -- A variant of _⇨*_ for _⊢_⇒*_ and _⊢_↘_.

  ⇒*→↘→↘ : Γ ⊢ A ⇒* B → Γ ⊢ B ↘ C → Γ ⊢ A ↘ C
  ⇒*→↘→↘ A⇒*B (B⇒*C , C-whnf) = (A⇒*B ⇨* B⇒*C) , C-whnf

opaque

  -- A variant of _⇨∷*_ for _⊢_⇒*_∷_ and _⊢_↘_∷_.

  ⇒*∷→↘∷→↘∷ : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ↘ v ∷ A → Γ ⊢ t ↘ v ∷ A
  ⇒*∷→↘∷→↘∷ t⇒*u (u⇒*v , v-whnf) = (t⇒*u ⇨∷* u⇒*v) , v-whnf

------------------------------------------------------------------------
-- Conversion

opaque

  -- Conversion for _⊢_⇒*_.

  conv* : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ⇒* u ∷ B
  conv* (id ⊢t)     A≡B = id (conv ⊢t A≡B)
  conv* (t⇒u ⇨ u⇒v) A≡B = conv t⇒u A≡B ⇨ conv* u⇒v A≡B

opaque

  -- Conversion for _⊢_↘_∷_.

  conv↘∷ : Γ ⊢ t ↘ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ↘ u ∷ B
  conv↘∷ (t⇒*u , u-whnf) A≡B = conv* t⇒*u A≡B , u-whnf

------------------------------------------------------------------------
-- A lemma related to U

opaque

  -- A variant of univ for _⊢_⇒*_.

  univ* : Γ ⊢ A ⇒* B ∷ U l → Γ ⊢ A ⇒* B
  univ* (id ⊢A)     = id (univ ⊢A)
  univ* (A⇒B ⇨ B⇒C) = univ A⇒B ⇨ univ* B⇒C

------------------------------------------------------------------------
-- Some lemmas related to supᵘ

opaque

  -- A variant of supᵘ-substˡ.

  supᵘ-substˡ* :
    Γ ⊢ t ⇒* t′ ∷ Level →
    Γ ⊢ u ∷ Level →
    Γ ⊢ t supᵘ u ⇒* t′ supᵘ u ∷ Level
  supᵘ-substˡ* (id ⊢t) ⊢u = id (supᵘⱼ ⊢t ⊢u)
  supᵘ-substˡ* (d ⇨ t⇒*t′) ⊢u = supᵘ-substˡ d ⊢u ⇨ supᵘ-substˡ* t⇒*t′ ⊢u

opaque

  -- A variant of supᵘ-substʳ.

  supᵘ-substʳ* :
    Γ ⊢ t ∷ Level →
    Γ ⊢ u ⇒* u′ ∷ Level →
    Γ ⊢ sucᵘ t supᵘ u ⇒* sucᵘ t supᵘ u′ ∷ Level
  supᵘ-substʳ* ⊢t (id ⊢u) = id (supᵘⱼ (sucᵘⱼ ⊢t) ⊢u)
  supᵘ-substʳ* ⊢t (d ⇨ u⇒*u′) = supᵘ-substʳ ⊢t d ⇨ supᵘ-substʳ* ⊢t u⇒*u′

------------------------------------------------------------------------
-- Some lemmas related to lower

opaque

  -- A variant of lower-subst.

  lower-subst* :
    Γ ⊢ t ⇒* t′ ∷ Lift u A →
    Γ ⊢ lower t ⇒* lower t′ ∷ A
  lower-subst* (id ⊢t) = id (lowerⱼ ⊢t)
  lower-subst* (d ⇨ t⇒*t′) = lower-subst d ⇨ lower-subst* t⇒*t′
