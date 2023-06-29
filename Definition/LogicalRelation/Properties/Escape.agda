------------------------------------------------------------------------
-- Escaping the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Properties.Escape
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B : Term n
    l : TypeLevel
    b : BinderMode
    p q : M

-- Reducible types are well-formed.
escape : ∀ {l A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
escape (Uᵣ′ l′ l< ⊢Γ) = Uⱼ ⊢Γ
escape (ℕᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Emptyᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Unitᵣ (Unitₜ [ ⊢A , ⊢B , D ] _)) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Bᵣ′ _ _ _ [ ⊢A , _ , _ ] _ _ _ _ _ _ _) = ⊢A
escape (emb 0<1 A) = escape A

-- Reducible type equality respect the equality relation.
escapeEq : ∀ {l A B} → ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊢ A ≅ B
escapeEq (Uᵣ′ l′ l< ⊢Γ) PE.refl = ≅-Urefl ⊢Γ
escapeEq (ℕᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ ℕₙ ℕₙ (≅-ℕrefl (wf ⊢A))
escapeEq (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
escapeEq (Unitᵣ (Unitₜ [ ⊢A , ⊢B , D ] ok)) D′ =
  ≅-red D D′ Unitₙ Unitₙ (≅-Unitrefl (wf ⊢A) ok)
escapeEq (ne′ K D neK K≡K) (ne₌ M D′ neM K≡M) =
  ≅-red (red D) (red D′) (ne neK) (ne neM) (~-to-≅ K≡M)
escapeEq (Bᵣ′ W _ _ D _ _ _ _ _ _ _) (B₌ _ _ D′ A≡B _ _) =
  ≅-red (red D) D′ ⟦ W ⟧ₙ ⟦ W ⟧ₙ A≡B
escapeEq (emb 0<1 A) A≡B = escapeEq A A≡B

-- Reducible terms are well-formed.
escapeTerm : ∀ {l A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
escapeTerm (Uᵣ′ l′ l< ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) = ⊢t
escapeTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Emptyᵣ D) (Emptyₜ e [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Unitᵣ (Unitₜ D _)) (Unitₜ e [ ⊢t , ⊢u , d ] prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΠ! _ _ D _ _ _ _ _ _ _) (Πₜ _ [ ⊢t , _ , _ ] _ _ _ _) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΣ! _ _ D _ _ _ _ _ _ _) (Σₜ _ [ ⊢t , _ , _ ] _ _ _) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (emb 0<1 A) t = escapeTerm A t

-- Reducible term equality respect the equality relation.
escapeTermEq : ∀ {l A t u} → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
                → Γ ⊢ t ≅ u ∷ A
escapeTermEq (Uᵣ′ l′ l< ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red (id (Uⱼ ⊢Γ)) (redₜ d) (redₜ d′) Uₙ (typeWhnf typeA) (typeWhnf typeB) A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ℕₙ
             (naturalWhnf natK) (naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = esplit prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Emptyₙ
             (ne natK) (ne natK′) k≡k′
escapeTermEq {l} {Γ} {A} {t} {u} (Unitᵣ (Unitₜ D _)) (Unitₜ₌ ⊢t ⊢u) =
  let t≅u = ≅ₜ-η-unit ⊢t ⊢u
      A≡Unit = subset* (red D)
  in  ≅-conv t≅u (sym A≡Unit)
escapeTermEq (ne′ K D neK K≡K)
                 (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
         (~-to-≅ₜ t≡u)
escapeTermEq
  (Bᵣ′ BΠ! _ _ D _ _ _ _ _ _ _) (Πₜ₌ _ _ d d′ funcF funcG f≡g _ _ _) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ΠΣₙ
    (functionWhnf funcF) (functionWhnf funcG) f≡g
escapeTermEq
  (Bᵣ′ BΣ! _ _ D _ _ _ _ _ _ _) (Σₜ₌ _ _ d d′ pProd rProd p≅r _ _ _) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ΠΣₙ
    (productWhnf pProd) (productWhnf rProd) p≅r
escapeTermEq (emb 0<1 A) t≡u = escapeTermEq A t≡u

-- If the type Unit is in the logical relation, then the Unit type is
-- allowed.

⊩Unit→Unit-allowed :
  Γ ⊩⟨ l ⟩ Unit → Unit-allowed
⊩Unit→Unit-allowed {Γ = Γ} = λ where
  (ℕᵣ [ ⊢Unit , _ , D ]) →
                  $⟨ D , ℕₙ ⟩
    Γ ⊢ Unit ↘ ℕ  →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    ℕ PE.≡ Unit   →⟨ (case_of λ ()) ⟩
    Unit-allowed  □
  (Emptyᵣ [ ⊢Unit , _ , D ]) →
                      $⟨ D , Emptyₙ ⟩
    Γ ⊢ Unit ↘ Empty  →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    Empty PE.≡ Unit   →⟨ (case_of λ ()) ⟩
    Unit-allowed      □
  (Unitᵣ (Unitₜ _ ok)) →
    ok
  (ne (ne A [ ⊢Unit , _ , D ] neA _)) →
                  $⟨ D , ne neA ⟩
    Γ ⊢ Unit ↘ A  →⟨ whrDet* (id ⊢Unit , Unitₙ) ⟩
    Unit PE.≡ A   →⟨ ⊥-elim ∘→ Unit≢ne neA ⟩
    Unit-allowed  □
  (Bᵣ′ b A B [ ⊢Unit , _ , D ] _ _ _ _ _ _ _) →
                            $⟨ D , ⟦ b ⟧ₙ ⟩
    Γ ⊢ Unit ↘ ⟦ b ⟧ A ▹ B  →⟨ whrDet* (id ⊢Unit , Unitₙ) ⟩
    Unit PE.≡ ⟦ b ⟧ A ▹ B   →⟨ ⊥-elim ∘→ Unit≢B b ⟩
    Unit-allowed            □
  (emb 0<1 [Unit]) →
    ⊩Unit→Unit-allowed [Unit]

-- If the type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B is in the logical relation, then
-- it is allowed.

⊩ΠΣ→ΠΣ-allowed :
  Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  ΠΣ-allowed b p q
⊩ΠΣ→ΠΣ-allowed {b = b} = λ where
  (ℕᵣ [ ⊢ΠAB , _ , D ]) →
    ⊥-elim (ℕ≢ΠΣ b (whrDet* (D , ℕₙ) (id ⊢ΠAB , ΠΣₙ)))
  (Emptyᵣ [ ⊢ΠAB , _ , D ]) →
    ⊥-elim (Empty≢ΠΣ b (whrDet* (D , Emptyₙ) (id ⊢ΠAB , ΠΣₙ)))
  (Unitᵣ (Unitₜ [ ⊢ΠAB , _ , D ] _)) →
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
  (emb 0<1 [ΠΣ]) →
    ⊩ΠΣ→ΠΣ-allowed [ΠΣ]
