{-# OPTIONS --without-K --safe #-}

open import Definition.Modality.Erasure
open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Reduction {{eqrel : EqRelSet Erasure′}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure′
open import Definition.LogicalRelation.Fundamental.Reducibility  Erasure′
open import Definition.LogicalRelation.Properties.Escape Erasure′

import Definition.LogicalRelation.Fundamental Erasure′ as F
import Definition.LogicalRelation.Irrelevance Erasure′ as I
import Definition.LogicalRelation.Properties.Reduction Erasure′ as R

open import Definition.Typed Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′
open import Definition.Typed.Consequences.Syntactic Erasure′
open import Definition.Typed.Consequences.Reduction Erasure′
open import Definition.Typed.Properties Erasure′
open import Definition.Typed.RedSteps Erasure′ as RS
open import Definition.Typed.Weakening Erasure′

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure as UP using (noClosedNe ; wk-id ; wk-lift-id)

open import Erasure.LogicalRelation
open import Erasure.LogicalRelation.Conversion
open import Erasure.Target as T hiding (_⇒_; _⇒*_)
open import Erasure.Target.Properties as TP

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum hiding (id ; sym)

private
  variable
    n : Nat
    t t′ A : U.Term 0
    v v′ : T.Term 0
    Γ : Con U.Term n

-- Logical relation for erasure is preserved under a single reduction backwards on the source language term
-- If t′ ® v ∷ A and ε ⊢ t ⇒ t′ ∷ A then t ® v ∷ A

sourceRedSubstTerm : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A]
       → ε ⊢ t ⇒ t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm (Uᵣ _) (Uᵣ _) t⇒t′ = Uᵣ (redFirstTerm t⇒t′)
sourceRedSubstTerm (ℕᵣ ([ ⊢A , ⊢B , D ])) (zeroᵣ t′⇒zero v⇒v′) t⇒t′ =
  zeroᵣ ((conv t⇒t′ (subset* D)) ⇨ t′⇒zero) v⇒v′
sourceRedSubstTerm (ℕᵣ ([ ⊢A , ⊢B , D ])) (sucᵣ t′⇒suc v⇒v′ t®v) t⇒t′ =
  sucᵣ ((conv t⇒t′ (subset* D)) ⇨ t′⇒suc) v⇒v′ t®v
sourceRedSubstTerm (Unitᵣ ([ ⊢A , ⊢B , D ])) (starᵣ x v⇒star) t⇒t′ =
  starᵣ (conv (redFirstTerm t⇒t′) (subset* D)) v⇒star
sourceRedSubstTerm (ne′ K D neK K≡K) t®v t⇒t′ = ⊥-elim (noClosedNe neK)
sourceRedSubstTerm (Bᵣ′ (BΠ 𝟘 q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] =
  let t®v = t®v′ [a]
      ⊢a = escapeTerm ([F] id ε) [a]
      ⊢a′ = PE.subst (ε ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘w′ = app-subst (conv t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘w = PE.subst (_⊢_⇒_∷_ ε _ _) (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G))) t∘a⇒t′∘w′
  in sourceRedSubstTerm ([G] id ε [a]) t®v t∘a⇒t′∘w
sourceRedSubstTerm (Bᵣ′ (BΠ ω q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      ⊢a = escapeTerm ([F] id ε) [a]
      ⊢a′ = PE.subst (ε ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘w′ = app-subst (conv t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘w = PE.subst (ε ⊢ _ ⇒ _ ∷_) (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G))) t∘a⇒t′∘w′
  in sourceRedSubstTerm ([G] id ε [a]) t®v t∘a⇒t′∘w
sourceRedSubstTerm (Bᵣ′ (BΣ p) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [t₁] =
  let t₁⇒t′₁ = fst-subst ⊢F ⊢G (conv t⇒t′ (subset* D))
      t₁⇒t′₁′ = PE.subst (λ x → ε ⊢ _ ⇒ _ ∷ x) (PE.sym (UP.wk-id F)) t₁⇒t′₁
      t₂⇒t′₂ = snd-subst ⊢F ⊢G (conv t⇒t′ (subset* D))
      t₂⇒t′₂′ = PE.subst (λ x → ε ⊢ _ ⇒ _ ∷ x U.[ _ ]) (PE.sym (UP.wk-lift-id G)) t₂⇒t′₂
      _ , _ , ⊢t′ = syntacticRedTerm (redMany t₁⇒t′₁′)
      [F]′ , [t′₁]′ = reducibleTerm ⊢t′
      [t′₁] = I.irrelevanceTerm [F]′ ([F] id ε) [t′₁]′
      Gt≡Gt′ = substTypeEq (refl ⊢G) (subsetTerm t₁⇒t′₁)
      t₁®v₁ , t₂®v₂ = t®v [t′₁]
      t₂®v₂′ = convTermʳ ([G] id ε [t′₁]) ([G] id ε [t₁])
                         ((PE.subst (λ x → ε ⊢ x U.[ _ ] ≡ x U.[ _ ]) (PE.sym (UP.wk-lift-id G)) (sym Gt≡Gt′)))
                         t₂®v₂
  in  sourceRedSubstTerm ([F] id ε) t₁®v₁ t₁⇒t′₁′ , sourceRedSubstTerm ([G] id ε [t₁]) t₂®v₂′ t₂⇒t′₂′
sourceRedSubstTerm (emb 0<1 [A]) t®v t⇒t′ = sourceRedSubstTerm [A] t®v t⇒t′


-- Logical relation for erasure is preserved under reduction closure backwards on the source language term
-- If t′ ® v ∷ A and ε ⊢ t ⇒* t′ ∷ A then t ® v ∷ A

sourceRedSubstTerm* : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A]
        → ε ⊢ t ⇒* t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm* [A] t′®v (id x) = t′®v
sourceRedSubstTerm* [A] t′®v (x ⇨ t⇒t′) = sourceRedSubstTerm [A] (sourceRedSubstTerm* [A] t′®v t⇒t′) x


-- Logical relation for erasure is preserved under a single reduction backwards on the target language term
-- If t ® v′ ∷ A and v ⇒ v′ then t ® v ∷ A

targetRedSubstTerm : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A]
       → v T.⇒ v′ → t ®⟨ l ⟩ v ∷ A / [A]
targetRedSubstTerm (Uᵣ x) (Uᵣ x₁) v⇒v′ = Uᵣ x₁
targetRedSubstTerm (ℕᵣ x) (zeroᵣ t′⇒zero v′⇒zero) v⇒v′ = zeroᵣ t′⇒zero (trans v⇒v′ v′⇒zero)
targetRedSubstTerm (ℕᵣ x) (sucᵣ t′⇒suc v′⇒suc t®v) v⇒v′ = sucᵣ t′⇒suc (trans v⇒v′ v′⇒suc) t®v
targetRedSubstTerm (Unitᵣ x) (starᵣ x₁ v′⇒star) v⇒v′ = starᵣ x₁ (trans v⇒v′ v′⇒star)
targetRedSubstTerm (ne′ K D neK K≡K) t®v′ v⇒v′ = ⊥-elim (noClosedNe neK)
targetRedSubstTerm (Bᵣ′ (BΠ 𝟘 q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ {a = a} [a] =
  let t®v = t®v′ [a]
      v∘w⇒v′∘w′ = T.app-subst v⇒v′
      [G[a]] = [G] id ε [a]
  in targetRedSubstTerm [G[a]] t®v v∘w⇒v′∘w′
targetRedSubstTerm (Bᵣ′ (BΠ ω q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
       t®v′ v⇒v′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      v∘w⇒v′∘w′ = T.app-subst v⇒v′
      [G[a]] = [G] id ε [a]
  in targetRedSubstTerm [G[a]] t®v v∘w⇒v′∘w′
targetRedSubstTerm (Bᵣ′ (BΣ q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ [t₁] =
  let t₁®v′₁ , t₂®v′₂ = t®v′ [t₁]
  in  targetRedSubstTerm ([F] id ε) t₁®v′₁ (T.fst-subst v⇒v′) , targetRedSubstTerm ([G] id ε [t₁]) t₂®v′₂ (T.snd-subst v⇒v′)
targetRedSubstTerm (emb 0<1 [A]) t®v′ v⇒v′ = targetRedSubstTerm [A] t®v′ v⇒v′


-- Logical relation for erasure is preserved under reduction closure backwards on the target language term
-- If t ® v′ ∷ A and v ⇒* v′ then t ® v ∷ A

targetRedSubstTerm* : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A] → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
targetRedSubstTerm* [A] t®v′ refl = t®v′
targetRedSubstTerm* [A] t®v′ (trans x v⇒v′) = targetRedSubstTerm [A] (targetRedSubstTerm* [A] t®v′ v⇒v′) x


-- Logical relation for erasure is preserved under reduction backwards
-- If t′ ® v′ ∷ A and ε ⊢ t ⇒ t′ ∷ A and v ⇒ v′ then t ® v ∷ A

redSubstTerm : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A]
      → ε ⊢ t ⇒ t′ ∷ A → v T.⇒ v′ → t ®⟨ l ⟩ v ∷ A / [A]
redSubstTerm [A] t′®v′ t⇒t′ v⇒v′ = targetRedSubstTerm [A] (sourceRedSubstTerm [A] t′®v′ t⇒t′) v⇒v′


-- Logical relation for erasure is preserved under reduction closure backwards
-- If t′ ® v′ ∷ A and ε ⊢ t ⇒* t′ ∷ A and v ⇒* v′ then t ® v ∷ A

redSubstTerm* : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A]
       → ε ⊢ t ⇒* t′ ∷ A → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
redSubstTerm* [A] t′®v′ t⇒t′ v⇒v′ = targetRedSubstTerm* [A] (sourceRedSubstTerm* [A] t′®v′ t⇒t′) v⇒v′


-- Logical relation for erasure is preserved under one reduction step on the source language term
-- If t ® v ∷ A and ε ⊢ t ⇒ t′ ∷ A  then t′ ® v ∷ A

sourceRedSubstTerm′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
        → ε ⊢ t ⇒ t′ ∷ A → t′ ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm′ (Uᵣ x) (Uᵣ x₁) t⇒t′ with syntacticRedTerm (redMany t⇒t′)
... | _ , _ , ε⊢t′∷U = Uᵣ ε⊢t′∷U
sourceRedSubstTerm′ (ℕᵣ [ ⊢A , ⊢B , D ]) (zeroᵣ t⇒zero v⇒zero) t⇒t′ with whrDet↘Term (t⇒zero , zeroₙ) (conv* (redMany t⇒t′) (subset* D))
... | t′⇒zero = zeroᵣ t′⇒zero v⇒zero
sourceRedSubstTerm′ (ℕᵣ [ ⊢A , ⊢B , D ]) (sucᵣ t⇒suc v⇒suc t®v) t⇒t′ with whrDet↘Term (t⇒suc , sucₙ) (conv* (redMany t⇒t′) (subset* D))
... | t′⇒suc = sucᵣ t′⇒suc v⇒suc t®v
sourceRedSubstTerm′ (Unitᵣ x) (starᵣ x₁ v⇒star) t⇒t′ with syntacticRedTerm (redMany t⇒t′)
... | _ , _ , ε⊢t′∷Unit = starᵣ (conv ε⊢t′∷Unit (subset* (red x))) v⇒star
sourceRedSubstTerm′ (ne′ K D neK K≡K) t®v t⇒t′ = ⊥-elim (noClosedNe neK)
sourceRedSubstTerm′ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] =
  let t®v = t®v′ [a]
      ⊢a = escapeTerm ([F] id ε) [a]
      ⊢a′ = PE.subst (ε ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘a′ = app-subst (conv t⇒t′ (subset* (red D))) ⊢a′
      t∘a⇒t′∘a = PE.subst (_⊢_⇒_∷_ ε _ _)
                          (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G)))
                          t∘a⇒t′∘a′
  in  sourceRedSubstTerm′ ([G] id ε [a]) t®v t∘a⇒t′∘a
sourceRedSubstTerm′ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      ⊢a = escapeTerm ([F] id ε) [a]
      ⊢a′ = PE.subst (ε ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘a′ = app-subst (conv t⇒t′ (subset* (red D))) ⊢a′
      t∘a⇒t′∘a = PE.subst (_⊢_⇒_∷_ ε _ _)
                          (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G)))
                          t∘a⇒t′∘a′
  in  sourceRedSubstTerm′ ([G] id ε [a]) t®v t∘a⇒t′∘a
sourceRedSubstTerm′ (Bᵣ′ (BΣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [t₁] =
  let t₁⇒t′₁ = fst-subst ⊢F ⊢G (conv t⇒t′ (subset* (red D)))
      t₁⇒t′₁′ = PE.subst (λ x → ε ⊢ _ ⇒ _ ∷ x) (PE.sym (UP.wk-id F)) t₁⇒t′₁
      t₂⇒t′₂ = snd-subst ⊢F ⊢G (conv t⇒t′ (subset* (red D)))
      Gt≡Gt′ = substTypeEq (refl ⊢G) (subsetTerm t₁⇒t′₁)
      t₂⇒t′₂′ = PE.subst (λ x → ε ⊢ _ ⇒ _ ∷ x U.[ _ ]) (PE.sym (UP.wk-lift-id G)) (conv t₂⇒t′₂ Gt≡Gt′)
      [t₁]′ = proj₁ (R.redSubstTerm t₁⇒t′₁′ ([F] id ε) [t₁])
      t₁®v₁ , t₂®v₂ = t®v [t₁]′
      t₂®v₂′ = convTermʳ ([G] id ε [t₁]′) ([G] id ε [t₁])
                         (PE.subst (λ x → ε ⊢ x U.[ _ ] ≡ x U.[ _ ]) (PE.sym (UP.wk-lift-id G)) Gt≡Gt′ )
                         t₂®v₂
  in  (sourceRedSubstTerm′ ([F] id ε) t₁®v₁ t₁⇒t′₁′) , sourceRedSubstTerm′ ([G] id ε [t₁]) t₂®v₂′ t₂⇒t′₂′
sourceRedSubstTerm′ (emb 0<1 [A]) t®v t⇒t′ = sourceRedSubstTerm′ [A] t®v t⇒t′


-- Logical relation for erasure is preserved under reduction closure on the source language term
-- If t ® v ∷ A and ε ⊢ t ⇒* t′ ∷ A  then t′ ® v ∷ A

sourceRedSubstTerm*′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
         → ε ⊢ t ⇒* t′ ∷ A → t′ ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm*′ [A] t®v (id x) = t®v
sourceRedSubstTerm*′ [A] t®v (x ⇨ t⇒t′) = sourceRedSubstTerm*′ [A] (sourceRedSubstTerm′ [A] t®v x) t⇒t′


-- Logical relation for erasure is preserved under one reduction step on the target language term
-- If t ® v ∷ A and v ⇒ v′  then t ® v′ ∷ A

targetRedSubstTerm′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
        → v T.⇒ v′ → t ®⟨ l ⟩ v′ ∷ A / [A]
targetRedSubstTerm′ (Uᵣ x) (Uᵣ x₁) v⇒v′ = Uᵣ x₁
targetRedSubstTerm′ (ℕᵣ x) (zeroᵣ x₁ v⇒zero) v⇒v′ with red*Det v⇒zero (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite zero-noRed x₂ = zeroᵣ x₁ T.refl
... | inj₂ x₂ = zeroᵣ x₁ x₂
targetRedSubstTerm′ (ℕᵣ x) (sucᵣ x₁ v⇒suc t®v) v⇒v′ with red*Det v⇒suc (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite suc-noRed x₂ = sucᵣ x₁ T.refl t®v
... | inj₂ x₂ = sucᵣ x₁ x₂ t®v
targetRedSubstTerm′ (Unitᵣ x) (starᵣ x₁ v⇒star) v⇒v′ with red*Det v⇒star (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite star-noRed x₂ = starᵣ x₁ T.refl
... | inj₂ x₂ = starᵣ x₁ x₂
targetRedSubstTerm′ (ne′ K D neK K≡K) t®v v⇒v′ = ⊥-elim (noClosedNe neK)
targetRedSubstTerm′ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ [a] =
  let t®v = t®v′ [a]
      v∘w⇒v′∘w = T.app-subst v⇒v′
  in  targetRedSubstTerm′ ([G] id ε [a]) t®v v∘w⇒v′∘w
targetRedSubstTerm′ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ [a] a®w =
  let t®v = t®v′ [a] a®w
      v∘w⇒v′∘w = T.app-subst v⇒v′
  in  targetRedSubstTerm′ ([G] id ε [a]) t®v v∘w⇒v′∘w
targetRedSubstTerm′ (Bᵣ′ (BΣ p) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ [t₁] =
    let v₁⇒v′₁ = T.fst-subst v⇒v′
        v₂⇒v′₂ = T.snd-subst v⇒v′
        t₁®v′₁ , t₂®v′₂ = t®v′ [t₁]
    in  targetRedSubstTerm′ ([F] id ε) t₁®v′₁ v₁⇒v′₁ , targetRedSubstTerm′ ([G] id ε [t₁]) t₂®v′₂ v₂⇒v′₂
targetRedSubstTerm′ (emb 0<1 [A]) t®v v⇒v′ = targetRedSubstTerm′ [A] t®v v⇒v′


-- Logical relation for erasure is preserved under reduction closure on the target language term
-- If t ® v ∷ A and v ⇒* v′ then t ® v′ ∷ A

targetRedSubstTerm*′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
         → v T.⇒* v′ → t ®⟨ l ⟩ v′ ∷ A / [A]
targetRedSubstTerm*′ [A] t®v refl = t®v
targetRedSubstTerm*′ [A] t®v (trans x v⇒v′) = targetRedSubstTerm*′ [A] (targetRedSubstTerm′ [A] t®v x) v⇒v′

-- Logical relation for erasure is preserved under reduction
-- If t ® v ∷ A and ε ⊢ t ⇒ t′ ∷ A and v ⇒ v′ then t′ ® v′ ∷ A

redSubstTerm′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
       → ε ⊢ t ⇒ t′ ∷ A → v T.⇒ v′ → t′ ®⟨ l ⟩ v′ ∷ A / [A]
redSubstTerm′ [A] t®v t⇒t′ v⇒v′ = targetRedSubstTerm′ [A] (sourceRedSubstTerm′ [A] t®v t⇒t′) v⇒v′

-- Logical relation for erasure is preserved under reduction closure
-- If t ® v ∷ A and ε ⊢ t ⇒* t′ ∷ A and v ⇒* v′ then t′ ® v′ ∷ A

redSubstTerm*′ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
       → ε ⊢ t ⇒* t′ ∷ A → v T.⇒* v′ → t′ ®⟨ l ⟩ v′ ∷ A / [A]
redSubstTerm*′ [A] t®v t⇒t′ v⇒v′ = targetRedSubstTerm*′ [A] (sourceRedSubstTerm*′ [A] t®v t⇒t′) v⇒v′
