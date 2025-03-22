------------------------------------------------------------------------
-- Escaping the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Escape
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Whnf R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term n
    l l′ : Universe-level
    b : BinderMode
    s : Strength
    p q : M

-- Reducible level equalities are well-formed.
mutual
  escapeLevelEq
    : Γ ⊩Level t ≡ u ∷Level
    → Γ ⊢ t ≅ u ∷ Level
  escapeLevelEq (Levelₜ₌ k k′ D D′ prop) =
    let lk , lk′ = lsplit prop in
    ≅ₜ-red (id (Levelⱼ (wfTerm (redFirst*Term D))) , Levelₙ) (D , lk) (D′ , lk′)
      (escapeLevel-prop (wfTerm (redFirst*Term D)) prop)

  escapeLevel-prop
    : ⊢ Γ
    → [Level]-prop Γ t u
    → Γ ⊢ t ≅ u ∷ Level
  escapeLevel-prop ⊢Γ zeroᵘᵣ = ≅ₜ-zeroᵘrefl ⊢Γ
  escapeLevel-prop ⊢Γ (sucᵘᵣ x) = ≅ₜ-sucᵘ-cong (escapeLevelEq x)
  escapeLevel-prop ⊢Γ (ne n) = escapeSneEq n

  -- Reducible semi-neutral equalities are well-formed.
  escapeSneEq
    : Γ ⊩sne t ≡ u
    → Γ ⊢ t ≅ u ∷ Level
  escapeSneEq (sneₜ₌ n₁ n₂ (maxᵘᵣ x y)) = ≅ₜ-maxᵘ-cong (escapeLevelEq x) (escapeLevelEq y)
  escapeSneEq (sneₜ₌ n₁ n₂ (ne (neNfₜ₌ _ _ _ t~u))) = ~-to-≅ₜ t~u

-- Reducible levels are well-formed.
escapeLevel
  : Γ ⊩Level t ∷Level
  → Γ ⊢ t ∷ Level
escapeLevel (Levelₜ₌ k k′ D D′ prop) = redFirst*Term D

-- Reducible types are well-formed.
escape : ∀ {l A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
escape (Levelᵣ D) = redFirst* D
escape (Uᵣ′ _ _ _ D) = redFirst* D
escape (ℕᵣ D) = redFirst* D
escape (Emptyᵣ D) = redFirst* D
escape (Unitᵣ′ _ _ _ D _) = redFirst* D
escape (ne′ _ _ D _ _) = redFirst* D
escape (Bᵣ′ _ _ _ D _ _ _ _ _) = redFirst* D
escape (Idᵣ ⊩A) = redFirst* (_⊩ₗId_.⇒*Id ⊩A)

-- Reducible type equality is contained in the equality relation.
escapeEq :
  (⊩A : Γ ⊩⟨ l ⟩ A) →
  Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
  Γ ⊢ A ≅ B

-- Reducible term equality is contained in the equality relation.
escapeTermEq :
  (⊩A : Γ ⊩⟨ l ⟩ A) →
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
  Γ ⊢ t ≅ u ∷ A

-- Reducible terms are well-formed.
escapeTerm : ∀ {l A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
escapeTerm ⊩A ⊩t = wf-⊢≡∷ (≅ₜ-eq (escapeTermEq ⊩A ⊩t)) .proj₂ .proj₁

-- If there is a well-formed equality between two identity types,
-- then the corresponding reduced identity types are equal.
Id≅Id :
  {⊩A : Γ ⊩′⟨ l ⟩Id A}
  (A≡B : Γ ⊩⟨ l ⟩ A ≡ B / Idᵣ ⊩A) →
  let open _⊩ₗId_ ⊩A
      open _⊩ₗId_≡_/_ A≡B
  in
  Γ ⊢ Id Ty lhs rhs ≅ Id Ty′ lhs′ rhs′
Id≅Id {⊩A = ⊩A} A≡B =
  ≅-Id-cong
    (escapeEq ⊩Ty Ty≡Ty′)
    (escapeTermEq ⊩Ty lhs≡lhs′)
    (escapeTermEq ⊩Ty rhs≡rhs′)
  where
  open _⊩ₗId_ ⊩A
  open _⊩ₗId_≡_/_ A≡B

escapeEq (Levelᵣ D) D′ =
  ≅-red (D , Levelₙ) (D′ , Levelₙ) (≅-Levelrefl (wf (redFirst* D)))
escapeEq (Uᵣ′ _ _ _ D) (U₌ k′ D₁ k≡k′) =
  ≅-red (D , Uₙ) (D₁ , Uₙ) (≅-univ (≅ₜ-U-cong (escapeLevelEq k≡k′)))
escapeEq (ℕᵣ D) D′ =
  ≅-red (D , ℕₙ) (D′ , ℕₙ) (≅-ℕrefl (wf (redFirst* D)))
escapeEq (Emptyᵣ D) D′ =
  ≅-red (D , Emptyₙ) (D′ , Emptyₙ) (≅-Emptyrefl (wfEq (subset* D)))
escapeEq (Unitᵣ′ _ _ _ D ok) (Unit₌ _ D′ k≡k′) =
  ≅-red (D , Unitₙ) (D′ , Unitₙ) (≅-Unit-cong (escapeLevelEq k≡k′) ok)
escapeEq (ne′ _ _ D neK _) (ne₌ _ _ D′ neM K≡M) =
  ≅-red (D , ne! neK) (D′ , ne! neM) K≡M
escapeEq (Bᵣ′ W _ _ D _ _ _ _ _) (B₌ _ _ D′ A≡B _ _) =
  ≅-red (D , ⟦ W ⟧ₙ) (D′ , ⟦ W ⟧ₙ) A≡B
escapeEq (Idᵣ ⊩A) A≡B =
  ≅-red (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (Id≅Id A≡B)

escapeTermEq (Levelᵣ D) (Levelₜ₌ k k′ d d′ prop) =
  let lk , lk′ = lsplit prop
  in ≅ₜ-red (D , Levelₙ) (d , lk) (d′ , lk′)
      (escapeLevel-prop (wf (redFirst* D)) prop)
escapeTermEq (Uᵣ′ _ _ _ D) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red (D , Uₙ) (d , typeWhnf typeA) (d′ , typeWhnf typeB)  A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ _ _ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (D , ℕₙ) (d , naturalWhnf natK)
        (d′ , naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = esplit prop
  in  ≅ₜ-red (D , Emptyₙ) (d , ne! natK) (d′ , ne! natK′) k≡k′
escapeTermEq (Unitᵣ′ k [k] k< D ok) (Unitₜ₌ _ _ d d′ prop) =
  let _ , _ , ⊢t′ = wf-⊢≡∷ (subset*Term (d .proj₁))
      _ , _ , ⊢u′ = wf-⊢≡∷ (subset*Term (d′ .proj₁))
  in
  ≅ₜ-red (D , Unitₙ) d d′
    (case prop of λ where
       (Unitₜ₌ˢ η) → ≅ₜ-η-unit (escapeLevel [k]) ⊢t′ ⊢u′ ok η
       (Unitₜ₌ʷ (starᵣ k≡k′ k′≡k″) _) →
         ≅-conv
           (≅ₜ-star-cong (escapeLevelEq k′≡k″) ok)
           (Unit-cong (≅ₜ-eq (≅ₜ-sym (escapeLevelEq k≡k′))) ok)
       (Unitₜ₌ʷ (ne (neNfₜ₌ _ _ _ t′~u′)) _) → ~-to-≅ₜ t′~u′)
escapeTermEq (ne′ _ _ D neK _) (neₜ₌ _ _ d d′ (neNfₜ₌ _ neT neU t≡u)) =
  ≅ₜ-red (D , ne! neK) (d , ne! neT) (d′ , ne! neU) (~-to-≅ₜ t≡u)
escapeTermEq
  (Bᵣ′ BΠ! _ _ D _ _ _ _ _) (Πₜ₌ _ _ d d′ funcF funcG f≡g _) =
  ≅ₜ-red (D , ΠΣₙ) (d , functionWhnf funcF) (d′ , functionWhnf funcG)
    f≡g
escapeTermEq
  (Bᵣ′ BΣ! _ _ D _ _ _ _ _) (Σₜ₌ _ _ d d′ pProd rProd p≅r _) =
  ≅ₜ-red (D , ΠΣₙ) (d , productWhnf pProd) (d′ , productWhnf rProd) p≅r
escapeTermEq {Γ = Γ} (Idᵣ ⊩A) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
  case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
    (ne _ t′-n u′-n t′~u′) →
      lemma (ne! t′-n) (ne! u′-n) (~-to-≅ₜ t′~u′)
    (rfl₌ lhs≡rhs) →
      lemma rflₙ rflₙ
        (                                   $⟨ ≅-Id-cong
                                                 (escapeEq ⊩Ty (reflEq ⊩Ty))
                                                 (escapeTermEq ⊩Ty (reflEqTerm ⊩Ty ⊩lhs))
                                                 (escapeTermEq ⊩Ty lhs≡rhs) ⟩
         Γ ⊢ Id Ty lhs lhs ≅ Id Ty lhs rhs  →⟨ ≅-eq ⟩
         Γ ⊢ Id Ty lhs lhs ≡ Id Ty lhs rhs  →⟨ ≅-conv (≅ₜ-rflrefl (escapeTerm ⊩Ty ⊩lhs)) ⟩
         (Γ ⊢≅ rfl ∷ Id Ty lhs rhs)         □)
  where
  open _⊩ₗId_ ⊩A
  lemma = λ t′-whnf u′-whnf →
            ≅ₜ-red (⇒*Id , Idₙ) (t⇒*t′ , t′-whnf) (u⇒*u′ , u′-whnf)

opaque

  -- If a unit type is reducible, then that unit type is allowed.

  ⊩Unit→Unit-allowed :
    Γ ⊩⟨ l′ ⟩ Unit s t → Unit-allowed s
  ⊩Unit→Unit-allowed = inversion-Unit-allowed ∘→ escape

opaque

  -- If the type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B is in the logical relation, then
  -- it is allowed.

  ⊩ΠΣ→ΠΣ-allowed :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ΠΣ-allowed b p q
  ⊩ΠΣ→ΠΣ-allowed = proj₂ ∘→ proj₂ ∘→ inversion-ΠΣ ∘→ escape
