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
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Whnf R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    m n : Nat
    Γ : Cons m n
    A B t u : Term n
    l l′ : Universe-level
    b : BinderMode
    s : Strength
    p q : M

-- Reducible types are well-formed.
escape : ∀ {l A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
escape (Uᵣ′ _ _ D) = redFirst* D
escape (ℕᵣ D) = redFirst* D
escape (Emptyᵣ D) = redFirst* D
escape (Unitᵣ′ _ _ D _) = redFirst* D
escape (ne′ _ D _ _) = redFirst* D
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

escapeEq (Uᵣ′ _ _ D) D₁ =
  ≅-red (D , Uₙ)  (D₁ , Uₙ) (≅-univ (≅-Urefl (wfEq (subset* D))))
escapeEq (ℕᵣ D) D′ =
  ≅-red (D , ℕₙ) (D′ , ℕₙ) (≅-ℕrefl (wfEq (subset* D)))
escapeEq (Emptyᵣ D) D′ =
  ≅-red (D , Emptyₙ) (D′ , Emptyₙ) (≅-Emptyrefl (wfEq (subset* D)))
escapeEq (Unitᵣ′ _ _ D ok) D′ =
  ≅-red (D , Unitₙ) (D′ , Unitₙ) (≅-Unitrefl (wfEq (subset* D)) ok)
escapeEq (ne′ _ D neK _) (ne₌ _ D′ neM K≡M) =
  ≅-red (D , ne-whnf neK) (D′ , ne-whnf neM) K≡M
escapeEq (Bᵣ′ W _ _ D _ _ _ _ _) (B₌ _ _ D′ A≡B _ _) =
  ≅-red (D , ⟦ W ⟧ₙ) (D′ , ⟦ W ⟧ₙ) A≡B
escapeEq (Idᵣ ⊩A) A≡B =
  ≅-red (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) (Id≅Id A≡B)

escapeTermEq (Uᵣ′ _ _ D) (Uₜ₌ _ _ d d′ typeA typeB A≡B _ _ _) =
  ≅ₜ-red (D , Uₙ) (d , typeWhnf typeA) (d′ , typeWhnf typeB)  A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ _ _ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (D , ℕₙ) (d , naturalWhnf natK)
        (d′ , naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
  let neK , neK′ = esplit prop
  in  ≅ₜ-red (D , Emptyₙ) (d , ne-whnf neK) (d′ , ne-whnf neK′) k≡k′
escapeTermEq (Unitᵣ′ _ _ D ok) (Unitₜ₌ _ _ d d′ prop) =
  let _ , _ , ⊢t′ = wf-⊢≡∷ (subset*Term (d .proj₁))
      _ , _ , ⊢u′ = wf-⊢≡∷ (subset*Term (d′ .proj₁))
  in
  ≅ₜ-red (D , Unitₙ) d d′
    (case prop of λ where
       (Unitₜ₌ˢ η)                         → ≅ₜ-η-unit ⊢t′ ⊢u′ η
       (Unitₜ₌ʷ starᵣ _)                   → ≅ₜ-starrefl (wfTerm ⊢t′) ok
       (Unitₜ₌ʷ (ne (neNfₜ₌ _ _ t′~u′)) _) → ~-to-≅ₜ t′~u′)
escapeTermEq (ne′ _ D neK _) (neₜ₌ _ _ d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (D , ne-whnf neK) (d , ne-whnf neT) (d′ , ne-whnf neU) (~-to-≅ₜ t≡u)
escapeTermEq
  (Bᵣ′ BΠ! _ _ D _ _ _ _ _) (Πₜ₌ _ _ d d′ funcF funcG f≡g _) =
  ≅ₜ-red (D , ΠΣₙ) (d , functionWhnf funcF) (d′ , functionWhnf funcG)
    f≡g
escapeTermEq
  (Bᵣ′ BΣ! _ _ D _ _ _ _ _) (Σₜ₌ _ _ d d′ pProd rProd p≅r _) =
  ≅ₜ-red (D , ΠΣₙ) (d , productWhnf pProd) (d′ , productWhnf rProd) p≅r
escapeTermEq {Γ} (Idᵣ ⊩A) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
  case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
    (ne t′-n u′-n t′~u′) →
      lemma (ne-whnf t′-n) (ne-whnf u′-n) (~-to-≅ₜ t′~u′)
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
    Γ ⊩⟨ l′ ⟩ Unit s l → Unit-allowed s
  ⊩Unit→Unit-allowed = inversion-Unit ∘→ escape

opaque

  -- If the type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B is in the logical relation, then
  -- it is allowed.

  ⊩ΠΣ→ΠΣ-allowed :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ΠΣ-allowed b p q
  ⊩ΠΣ→ΠΣ-allowed = proj₂ ∘→ proj₂ ∘→ inversion-ΠΣ ∘→ escape
