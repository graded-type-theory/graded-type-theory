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
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Whnf R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term n
    l l′ : Universe-level
    b : BinderMode
    s : Strength
    p q : M

-- Reducible types are well-formed.
escape : ∀ {l A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
escape (Levelᵣ [ ⊢A , _ , _ ]) = ⊢A
escape (Uᵣ′ _ _ _ [ ⊢A , ⊢B , D ]) = ⊢A
escape (ℕᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Emptyᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Unitᵣ (Unitₜ _ _ _ [ ⊢A , ⊢B , D ] _)) = ⊢A
escape (ne′ _ [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Bᵣ′ _ _ _ [ ⊢A , _ , _ ] _ _ _ _ _ _ _) = ⊢A
escape (Idᵣ ⊩A) = ⊢A-red (_⊩ₗId_.⇒*Id ⊩A)
escape (emb ≤ᵘ-refl A) = escape A
escape (emb (≤ᵘ-step k) A) = escape (emb k A)

-- Reducible terms are well-formed.
escapeTerm : ∀ {l A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
escapeTerm (Levelᵣ D) (Levelₜ m [ ⊢t , ⊢u , d ] m≡m prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Uᵣ′ _ _ _ ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) =
  conv ⊢t (sym ( subset* (red  ⊢Γ)))
escapeTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Emptyᵣ D) (Emptyₜ e [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Unitᵣ (Unitₜ _ _ _ D _)) (Unitₜ e [ ⊢t , ⊢u , d ] _ prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ne′ _ D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΠ! _ _ D _ _ _ _ _ _ _) (Πₜ _ [ ⊢t , _ , _ ] _ _ _ _) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΣ! _ _ D _ _ _ _ _ _ _) (Σₜ _ [ ⊢t , _ , _ ] _ _ _) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Idᵣ ⊩A) (_ , t⇒*u , _) =
  conv (⊢t-redₜ t⇒*u) (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩A))))
escapeTerm (emb ≤ᵘ-refl A) t = escapeTerm A t
escapeTerm (emb (≤ᵘ-step k) A) t = escapeTerm (emb k A) t

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

escapeLevelEq
  : Γ ⊩Level t ≡ u ∷Level
  → Γ ⊢ t ≅ u ∷ Level
escapeLevelEq (Levelₜ₌ k k′ d d′ k≡k′ prop) =
  let lk , lk′ = lsplit prop
  in ≅ₜ-red (id (Levelⱼ (wfTerm (⊢t-redₜ d))) , Levelₙ) (redₜ d , lk) (redₜ d′ , lk′) k≡k′

escapeEq (Levelᵣ [ ⊢A , ⊢B , D ]) D′ =
  ≅-red (D , Levelₙ) (D′ , Levelₙ) (≅-Levelrefl (wf ⊢A))
escapeEq (Uᵣ′ _ _ _ [ ⊢A , ⊢B , D ]) (U₌ k′ [ ⊢A₁ , ⊢B₁ , D₁ ] k≡k′) =
  ≅-red (D , Uₙ) (D₁ , Uₙ) (≅-univ (≅ₜ-U-cong (escapeLevelEq k≡k′)))
escapeEq (ℕᵣ [ ⊢A , ⊢B , D ]) D′ =
  ≅-red (D , ℕₙ) (D′ , ℕₙ) (≅-ℕrefl (wf ⊢A))
escapeEq (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ =
  ≅-red (D , Emptyₙ) (D′ , Emptyₙ) (≅-Emptyrefl (wf ⊢A))
escapeEq (Unitᵣ (Unitₜ _ (Levelₜ m [ ⊢l′ , _ , _ ] _ _) _ [ ⊢A , ⊢B , D ] ok)) D′ =
  ≅-red (D , Unitₙ) (D′ , Unitₙ) (≅-Unitrefl ⊢l′ ok)
escapeEq (ne′ _ D neK K≡K) (ne₌ M D′ neM K≡M) =
  ≅-red (red D , ne neK) (red D′ , ne neM) K≡M
escapeEq (Bᵣ′ W _ _ D _ _ _ _ _ _ _) (B₌ _ _ D′ A≡B _ _) =
  ≅-red (red D , ⟦ W ⟧ₙ) (red D′ , ⟦ W ⟧ₙ) A≡B
escapeEq (Idᵣ ⊩A) A≡B =
  ≅-red (red (_⊩ₗId_.⇒*Id ⊩A) , Idₙ) (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B) , Idₙ)
    (Id≅Id A≡B)
escapeEq (emb ≤ᵘ-refl A) A≡B = escapeEq A A≡B
escapeEq (emb (≤ᵘ-step k) A) A≡B = escapeEq (emb k A) A≡B

escapeTermEq (Levelᵣ [ ⊢A , ⊢B , D ]) (Levelₜ₌ k k′ d d′ k≡k′ prop) =
  let lk , lk′ = lsplit prop
  in ≅ₜ-red (D , Levelₙ) (redₜ d , lk) (redₜ d′ , lk′) k≡k′
escapeTermEq (Uᵣ′ _ _ _ [ ⊢A , ⊢B , D ]) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red (D , Uₙ) (redₜ d , typeWhnf typeA) (redₜ d′ , typeWhnf typeB)  A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (red D , ℕₙ) (redₜ d , naturalWhnf natK)
        (redₜ d′ , naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = esplit prop
  in  ≅ₜ-red (red D , Emptyₙ) (redₜ d , ne natK) (redₜ d′ , ne natK′)
        k≡k′
escapeTermEq (Unitᵣ (Unitₜ _ _ _ D _)) (Unitₜ₌ˢ ⊢t ⊢u ok) =
  let t≅u = ≅ₜ-η-unit ⊢t ⊢u ok
      A≡Unit = subset* (red D)
  in ≅-conv t≅u (sym A≡Unit)
escapeTermEq (Unitᵣ (Unitₜ _ _ _ D _)) (Unitₜ₌ʷ _ _ d d′ k≡k′ prop _) =
  let whK , whK′ = usplit prop
  in  ≅ₜ-red (red D , Unitₙ) (redₜ d , whK) (redₜ d′ , whK′) k≡k′
escapeTermEq (ne′ _ D neK K≡K)
                 (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (red D , ne neK) (redₜ d , ne neT) (redₜ d′ , ne neU)
         (~-to-≅ₜ t≡u)
escapeTermEq
  (Bᵣ′ BΠ! _ _ D _ _ _ _ _ _ _) (Πₜ₌ _ _ d d′ funcF funcG f≡g _ _ _) =
  ≅ₜ-red (red D , ΠΣₙ) (redₜ d , functionWhnf funcF)
    (redₜ d′ , functionWhnf funcG) f≡g
escapeTermEq
  (Bᵣ′ BΣ! _ _ D _ _ _ _ _ _ _) (Σₜ₌ _ _ d d′ pProd rProd p≅r _ _ _) =
  ≅ₜ-red (red D , ΠΣₙ) (redₜ d , productWhnf pProd)
    (redₜ d′ , productWhnf rProd) p≅r
escapeTermEq {Γ = Γ} (Idᵣ ⊩A) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
  case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
    (ne t′-n u′-n t′~u′) →
      lemma (ne t′-n) (ne u′-n) (~-to-≅ₜ t′~u′)
    (rfl₌ lhs≡rhs) →
      lemma rflₙ rflₙ
        (                                   $⟨ ≅-Id-cong
                                                 (escapeEq ⊩Ty (reflEq ⊩Ty))
                                                 (escapeTermEq ⊩Ty (reflEqTerm ⊩Ty ⊩lhs))
                                                 (escapeTermEq ⊩Ty lhs≡rhs) ⟩
         Γ ⊢ Id Ty lhs lhs ≅ Id Ty lhs rhs  →⟨ ≅-eq ⟩
         Γ ⊢ Id Ty lhs lhs ≡ Id Ty lhs rhs  →⟨ ≅-conv (≅ₜ-rflrefl (escapeTerm ⊩Ty ⊩lhs)) ⟩
         (Γ ⊢ rfl ≅ rfl ∷ Id Ty lhs rhs)    □)
  where
  open _⊩ₗId_ ⊩A
  lemma = λ t′-whnf u′-whnf →
            ≅ₜ-red (red ⇒*Id , Idₙ) (redₜ t⇒*t′ , t′-whnf)
              (redₜ u⇒*u′ , u′-whnf)

escapeTermEq (emb ≤ᵘ-refl A) t≡u = escapeTermEq A t≡u
escapeTermEq (emb (≤ᵘ-step k) A) t≡u = escapeTermEq (emb k A) t≡u

-- If a unit type is reducible, then that unit type is allowed.

⊩Unit→Unit-allowed :
  Γ ⊩⟨ l′ ⟩ Unit s t → Unit-allowed s
⊩Unit→Unit-allowed {Γ = Γ} = λ where
  (Levelᵣ [ ⊢Unit , _ , D ]) →
                      $⟨ D , Levelₙ ⟩
    Γ ⊢ Unit! ↘ Level →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    Level PE.≡ Unit!  →⟨ ((case_of λ ())) ⟩
    Unit-allowed _    □
  (Uᵣ′ k _ _ [ ⊢Unit , _ , D ]) →
                  $⟨ D , Uₙ ⟩
    Γ ⊢ Unit! ↘ U k  →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    U k PE.≡ Unit!   →⟨ (case_of λ ()) ⟩
    Unit-allowed _  □
  (ℕᵣ [ ⊢Unit , _ , D ]) →
                  $⟨ D , ℕₙ ⟩
    Γ ⊢ Unit! ↘ ℕ  →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    ℕ PE.≡ Unit!   →⟨ (case_of λ ()) ⟩
    Unit-allowed _  □
  (Emptyᵣ [ ⊢Unit , _ , D ]) →
                      $⟨ D , Emptyₙ ⟩
    Γ ⊢ Unit! ↘ Empty  →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    Empty PE.≡ Unit!   →⟨ (case_of λ ()) ⟩
    Unit-allowed _     □
  (Unitᵣ (Unitₜ _ _ _ [ _ , _ , D ] ok)) → case whnfRed* D Unitₙ of λ where
    PE.refl → ok
  (ne (ne A [ ⊢Unit , _ , D ] neA _)) →
                  $⟨ D , ne neA ⟩
    Γ ⊢ Unit! ↘ A  →⟨ whrDet* (id ⊢Unit , Unitₙ) ⟩
    Unit! PE.≡ A   →⟨ ⊥-elim ∘→ Unit≢ne neA ⟩
    Unit-allowed _  □
  (Bᵣ′ b A B [ ⊢Unit , _ , D ] _ _ _ _ _ _ _) →
                            $⟨ D , ⟦ b ⟧ₙ ⟩
    Γ ⊢ Unit! ↘ ⟦ b ⟧ A ▹ B  →⟨ whrDet* (id ⊢Unit , Unitₙ) ⟩
    Unit! PE.≡ ⟦ b ⟧ A ▹ B   →⟨ ⊥-elim ∘→ Unit≢B b ⟩
    Unit-allowed _           □
  (Idᵣ ⊩A) →
    let open _⊩ₗId_ ⊩A in
                              $⟨ red ⇒*Id , Idₙ ⟩
    Γ ⊢ Unit! ↘ Id Ty lhs rhs  →⟨ whrDet* (id (⊢A-red ⇒*Id) , Unitₙ) ⟩
    Unit! PE.≡ Id Ty lhs rhs   →⟨ (λ ()) ⟩
    Unit-allowed _             □
  (emb ≤ᵘ-refl [Unit]) → ⊩Unit→Unit-allowed [Unit]
  (emb (≤ᵘ-step k) [Unit]) →  ⊩Unit→Unit-allowed (emb k [Unit])

-- If the type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B is in the logical relation, then
-- it is allowed.

⊩ΠΣ→ΠΣ-allowed :
  Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  ΠΣ-allowed b p q
⊩ΠΣ→ΠΣ-allowed {b = b} = λ where
  (Levelᵣ [ ⊢ΠAB , _ , D ]) →
    ⊥-elim (Level≢ΠΣ b (whrDet* (D , Levelₙ) (id ⊢ΠAB , ΠΣₙ)))
  (Uᵣ′ _ _ _ [ ⊢ΠAB , _ , D ]) →
     ⊥-elim ( U≢ΠΣ b ( (whrDet* (D , Uₙ) (id ⊢ΠAB , ΠΣₙ))))
  (ℕᵣ [ ⊢ΠAB , _ , D ]) →
    ⊥-elim (ℕ≢ΠΣ b (whrDet* (D , ℕₙ) (id ⊢ΠAB , ΠΣₙ)))
  (Emptyᵣ [ ⊢ΠAB , _ , D ]) →
    ⊥-elim (Empty≢ΠΣ b (whrDet* (D , Emptyₙ) (id ⊢ΠAB , ΠΣₙ)))
  (Unitᵣ (Unitₜ _ _ _ [ ⊢ΠAB , _ , D ] _)) →
    ⊥-elim (Unit≢ΠΣ b (whrDet* (D , Unitₙ) (id ⊢ΠAB , ΠΣₙ)))
  (ne (ne _ [ ⊢ΠAB , _ , D ] neK _)) →
    ⊥-elim (ΠΣ≢ne b neK (whrDet* (id ⊢ΠAB , ΠΣₙ) (D , ne neK)))
  (Bᵣ′ (BM BMΠ _ _) _ _ [ ⊢ΠAB , _ , D ] _ _ _ _ _ _ ok) →
    case whrDet* (id ⊢ΠAB , ΠΣₙ) (D , ΠΣₙ) of λ {
      PE.refl →
    ok }
  (Bᵣ′ (BM (BMΣ _) _ _) _ _ [ ⊢ΠAB , _ , D ] _ _ _ _ _ _ ok) →
    case whrDet* (id ⊢ΠAB , ΠΣₙ) (D , ΠΣₙ) of λ {
      PE.refl →
    ok }
  (Idᵣ ⊩A) →
    let open _⊩ₗId_ ⊩A in
    ⊥-elim (Id≢ΠΣ b (whrDet* (red ⇒*Id , Idₙ) (id (⊢A-red ⇒*Id) , ΠΣₙ)))
  (emb ≤ᵘ-refl [ΠΣ]) →  ⊩ΠΣ→ΠΣ-allowed [ΠΣ]
  (emb (≤ᵘ-step k) [ΠΣ]) →  ⊩ΠΣ→ΠΣ-allowed (emb k [ΠΣ])
